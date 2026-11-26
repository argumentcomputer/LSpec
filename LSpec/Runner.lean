module
public import LSpec.Core
public import Std.Sync.Mutex
public import Init.Data.Queue
public import Init.System.Promise

/-!
# Bounded-Thread Parallel Test Runner (`LSpec.Runner`)

Executes a `TestTree` with:
- Pre-execution filtering by path pattern, exact path, exclusions, and tags
  (filtered-out subtrees never execute and their `withResource` specs are never acquired).
- A pure, total `ExecPlan` compiler (`compilePlan`) shared by both sequential and
  parallel execution so context propagation (`options`, `path`, `tags`, `seed`,
  `aroundEach`, `ExecutionMode`) and report tree reconstruction are identical
  regardless of thread count.
- Bounded concurrency via a fixed-size `WorkerPool` (`threads` dedicated workers
  pulling from a mutex+condvar `Std.Queue`). At most `threads` tests execute
  concurrently, letting CI jobs cap peak memory (RSS) while maximizing speed.
- Eager memory reclamation: jobs are popped from the queue before execution and
  dropped immediately upon completion, keeping only lightweight `LeafReport`s.
- Respect for `ExecutionMode.sequential` (runs a subtree as one sequential unit)
  and `TestTree.withResource` (acquired once before its subtree, released in
  `finally` after all subtree tests finish; skipped without acquisition when
  `failFast` has already tripped).
- Per-test `IO.FS.withIsolatedStreams` stdout/stderr capture, uncaught `IO.Error`
  handling, wall-clock timing, and deterministic per-test seed derivation.

All pure tree/filter/report/plan functions are total (non-`partial`) and
`@[expose]`d so `LSpecProofs` proves their correctness directly against the
executable code.
-/

namespace LSpec
public section

/-- Filter criteria applied to a `TestTree` before execution or listing. -/
structure TestFilter where
  /-- Substring patterns: if non-empty, at least one must match the test path. -/
  includes : Array String := #[]
  /-- Exact path matches (slash-separated, e.g. `"Math/Addition/commutes"`). -/
  exact : Array String := #[]
  /-- Substring patterns to exclude. -/
  excludes : Array String := #[]
  /-- If non-empty, the test must carry at least one of these tags. -/
  includeTags : Array String := #[]
  /-- Exclude any test carrying any of these tags. -/
  excludeTags : Array String := #[]
  deriving BEq, Repr

/-- Substring predicate used by `TestFilter`. -/
@[expose] def containsSubstr (haystack needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

namespace TestFilter

@[expose] def isEmpty (f : TestFilter) : Bool :=
  f.includes.isEmpty && f.exact.isEmpty && f.excludes.isEmpty &&
  f.includeTags.isEmpty && f.excludeTags.isEmpty

/-- Check whether a leaf at `path` with `tags` passes the filter. -/
@[expose] def matchesTest (f : TestFilter) (path : Array String) (tags : Array String) : Bool :=
  let fullPath := "/".intercalate path.toList
  let hasIncludeFilter := !f.includes.isEmpty || !f.exact.isEmpty
  let included :=
    if !hasIncludeFilter then true
    else
      f.exact.any (· == fullPath) ||
      f.includes.any (containsSubstr fullPath ·)
  let excluded := f.excludes.any (containsSubstr fullPath ·)
  let tagIncluded :=
    if f.includeTags.isEmpty then true
    else f.includeTags.any (tags.contains ·)
  let tagExcluded := f.excludeTags.any (tags.contains ·)
  included && !excluded && tagIncluded && !tagExcluded

end TestFilter

private theorem array_toList_sizeOf_lt [SizeOf α] (a : Array α) :
    sizeOf a.toList < sizeOf a := by
  cases a; simp

mutual

/-- Total structural worker for `filterTree`. -/
@[expose] def filterTreeGo (filter : TestFilter) (path : Array String) (tags : Array String) :
    TestTree → Option TestTree
  | .leaf name leafTags exec =>
    let fullPath := if name.isEmpty then path else path.push name
    let allTags := tags ++ leafTags
    if filter.matchesTest fullPath allTags then
      some (.leaf name leafTags exec)
    else
      none
  | .group name children =>
    let nextPath := if name.isEmpty then path else path.push name
    let kept := filterTreeChildren filter nextPath tags children.toList
    if kept.isEmpty then none else some (.group name kept.toArray)
  | .withMode mode child =>
    (filterTreeGo filter path tags child).map (.withMode mode)
  | .withTags more child =>
    (filterTreeGo filter path (tags ++ more) child).map (.withTags more)
  | .withOptions f child =>
    (filterTreeGo filter path tags child).map (.withOptions f)
  | .aroundEach wrap child =>
    (filterTreeGo filter path tags child).map (.aroundEach wrap)
  | .withResource desc acq child =>
    (filterTreeGo filter path tags child).map (.withResource desc acq)
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Total child-list helper for `filterTreeGo`. -/
@[expose] def filterTreeChildren (filter : TestFilter) (path : Array String) (tags : Array String) :
    List TestTree → List TestTree
  | [] => []
  | c :: cs =>
    match filterTreeGo filter path tags c with
    | some c' => c' :: filterTreeChildren filter path tags cs
    | none => filterTreeChildren filter path tags cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

/-- Prune a `TestTree` to only the leaves matching `filter`.
    Returns `none` if no leaves match, ensuring filtered-out `withResource`
    blocks are never acquired. -/
@[expose] def filterTree (filter : TestFilter) (tree : TestTree) : Option TestTree :=
  if filter.isEmpty then some tree
  else filterTreeGo filter #[] #[] tree

/-- Metadata for a single discovered test (returned by `listTests` without running tests). -/
structure ListedTest where
  path : Array String
  tags : Array String
  mode : ExecutionMode
  deriving BEq, Repr

namespace ListedTest

@[expose] def pathString (t : ListedTest) : String :=
  "/".intercalate t.path.toList

end ListedTest

mutual

/-- Total structural worker for `listTests`, returning tests in declaration order. -/
@[expose] def listTestsGo (path : Array String) (tags : Array String) (mode : ExecutionMode) :
    TestTree → List ListedTest
  | .leaf name leafTags _ =>
    let fullPath := if name.isEmpty then path else path.push name
    [{ path := fullPath, tags := tags ++ leafTags, mode }]
  | .group name children =>
    let nextPath := if name.isEmpty then path else path.push name
    listTestsChildren nextPath tags mode children.toList
  | .withMode m child =>
    listTestsGo path tags (ExecutionMode.combine mode m) child
  | .withTags more child =>
    listTestsGo path (tags ++ more) mode child
  | .withOptions _ child =>
    listTestsGo path tags mode child
  | .aroundEach _ child =>
    listTestsGo path tags mode child
  | .withResource _ _ child =>
    listTestsGo path tags mode child
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Total child-list helper for `listTestsGo`. -/
@[expose] def listTestsChildren (path : Array String) (tags : Array String) (mode : ExecutionMode) :
    List TestTree → List ListedTest
  | [] => []
  | c :: cs => listTestsGo path tags mode c ++ listTestsChildren path tags mode cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

/-- Enumerate all leaves in a `TestTree` without executing any test or acquiring resources. -/
@[expose] def listTests (tree : TestTree) (defaultMode : ExecutionMode := .parallel) :
    Array ListedTest :=
  (listTestsGo #[] #[] defaultMode tree).toArray

/-- Execution report for a single leaf test. -/
structure LeafReport where
  name : String
  path : Array String
  tags : Array String
  result : TestResult
  durationMs : Nat
  capturedOutput : String := ""
  deriving BEq, Repr, Inhabited

/-- Hierarchical execution report mirroring the executed `TestTree`. -/
inductive ReportTree where
  | leaf (report : LeafReport)
  | group (name : String) (children : Array ReportTree)
  deriving BEq, Repr, Inhabited

/-- Aggregate statistics over a `ReportTree`. -/
structure RunSummary where
  passed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0
  totalDurationMs : Nat := 0
  seed : UInt64 := 0
  threads : Nat := 1
  deriving BEq, Repr, Inhabited

namespace RunSummary

@[expose] def total (s : RunSummary) : Nat := s.passed + s.failed + s.skipped

@[expose] def allPassed (s : RunSummary) : Bool := s.failed == 0

end RunSummary

namespace ReportTree

mutual

/-- Collect all leaf reports in declaration order as a `List`. -/
@[expose] def leavesList : ReportTree → List LeafReport
  | .leaf rep => [rep]
  | .group _ children => leavesChildren children.toList
termination_by r => sizeOf r
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Helper collecting leaf reports from a list of child `ReportTree`s. -/
@[expose] def leavesChildren : List ReportTree → List LeafReport
  | [] => []
  | c :: cs => leavesList c ++ leavesChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

/-- Collect all leaf reports in declaration order. -/
@[expose] def leaves (r : ReportTree) : Array LeafReport :=
  r.leavesList.toArray

mutual

/-- Count the total number of leaves in a `ReportTree`. -/
@[expose] def leafCount : ReportTree → Nat
  | .leaf _ => 1
  | .group _ children => leafCountChildren children.toList
termination_by r => sizeOf r
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Helper counting leaves across a list of child `ReportTree`s. -/
@[expose] def leafCountChildren : List ReportTree → Nat
  | [] => 0
  | c :: cs => leafCount c + leafCountChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

mutual

/-- Collect all failing leaf reports in tree order as a `List`. -/
@[expose] def failuresList : ReportTree → List LeafReport
  | .leaf rep => if rep.result.isFailed then [rep] else []
  | .group _ children => failuresChildren children.toList
termination_by r => sizeOf r
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Helper collecting failing leaf reports from child `ReportTree`s. -/
@[expose] def failuresChildren : List ReportTree → List LeafReport
  | [] => []
  | c :: cs => failuresList c ++ failuresChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

/-- Collect all failing leaf reports in tree order. -/
@[expose] def failures (r : ReportTree) : Array LeafReport :=
  r.failuresList.toArray

mutual

/-- Compute `(passed, failed, skipped)` counts over a `ReportTree`. -/
@[expose] def summarizeGo : ReportTree → Nat × Nat × Nat
  | .leaf rep =>
    match rep.result.outcome with
    | .passed => (1, 0, 0)
    | .failed _ => (0, 1, 0)
    | .skipped _ => (0, 0, 1)
  | .group _ children => summarizeChildren children.toList
termination_by r => sizeOf r
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Helper summing `(passed, failed, skipped)` counts over child `ReportTree`s. -/
@[expose] def summarizeChildren : List ReportTree → Nat × Nat × Nat
  | [] => (0, 0, 0)
  | c :: cs =>
    let (p1, f1, s1) := summarizeGo c
    let (p2, f2, s2) := summarizeChildren cs
    (p1 + p2, f1 + f2, s1 + s2)
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

/-- Compute pass/fail/skip counts over a `ReportTree`. -/
@[expose] def summarize (r : ReportTree) (totalDurationMs : Nat := 0)
    (seed : UInt64 := 0) (threads : Nat := 1) : RunSummary :=
  let (p, f, s) := summarizeGo r
  { passed := p, failed := f, skipped := s, totalDurationMs, seed, threads }

end ReportTree

/-! ## Resolved Execution Plan (`ExecPlan`) -/

/-- Pure execution plan compiled from a `TestTree`.
    All context propagation (`options`, `path`, `tags`, `seed`, `aroundEach`, and
    `ExecutionMode`) is resolved once by `compilePlan`, so sequential (`-j 1`)
    and parallel (`-j N`) execution share the exact same resolved plan. -/
inductive ExecPlan : Type where
  | leaf (name : String) (path : Array String) (tags : Array String)
         (opts : TestOptions) (seed : UInt64)
         (exec : TestContext → IO TestResult)
  | group (name : String) (children : Array ExecPlan)
  | seq (child : ExecPlan)
  | resource (desc : String) (path : Array String) (tags : Array String)
             (acquire : IO (IO Unit)) (child : ExecPlan)

mutual

/-- Total compiler from `TestTree` to `ExecPlan`. -/
@[expose] def compilePlanGo (masterSeed : UInt64) (opts : TestOptions)
    (path : Array String) (tags : Array String) (mode : ExecutionMode)
    (wrap : (TestContext → IO TestResult) → TestContext → IO TestResult) :
    TestTree → ExecPlan
  | .leaf name leafTags exec =>
    let fullPath := if name.isEmpty then path else path.push name
    let allTags := tags ++ leafTags
    let seed := deriveTestSeed masterSeed fullPath
    .leaf name fullPath allTags opts seed (wrap exec)
  | .group name children =>
    let nextPath := if name.isEmpty then path else path.push name
    .group name (compilePlanChildren masterSeed opts nextPath tags mode wrap children.toList).toArray
  | .withMode m child =>
    let nextMode := ExecutionMode.combine mode m
    let sub := compilePlanGo masterSeed opts path tags nextMode wrap child
    match mode, nextMode with
    | .parallel, .sequential => .seq sub
    | _, _ => sub
  | .withTags more child =>
    compilePlanGo masterSeed opts path (tags ++ more) mode wrap child
  | .withOptions f child =>
    compilePlanGo masterSeed (f opts) path tags mode wrap child
  | .aroundEach w child =>
    compilePlanGo masterSeed opts path tags mode (fun inner => wrap (w inner)) child
  | .withResource desc acq child =>
    .resource desc path tags acq (compilePlanGo masterSeed opts path tags mode wrap child)
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Total child-list helper for `compilePlanGo`. -/
@[expose] def compilePlanChildren (masterSeed : UInt64) (opts : TestOptions)
    (path : Array String) (tags : Array String) (mode : ExecutionMode)
    (wrap : (TestContext → IO TestResult) → TestContext → IO TestResult) :
    List TestTree → List ExecPlan
  | [] => []
  | c :: cs =>
    compilePlanGo masterSeed opts path tags mode wrap c ::
      compilePlanChildren masterSeed opts path tags mode wrap cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

/-- Compile a `TestTree` into an `ExecPlan` with resolved paths, tags, options,
    seeds, `aroundEach` wrappers, and `seq` boundaries. -/
@[expose] def compilePlan (masterSeed : UInt64) (opts : TestOptions)
    (defaultMode : ExecutionMode) (tree : TestTree) : ExecPlan :=
  let plan := compilePlanGo masterSeed opts #[] #[] defaultMode id tree
  match defaultMode with
  | .sequential => .seq plan
  | .parallel => plan

namespace ExecPlan

mutual

/-- Enumerate the leaves of an `ExecPlan` in declaration order (matches `listTests`). -/
@[expose] def toListedList (mode : ExecutionMode) : ExecPlan → List ListedTest
  | .leaf _ path tags _ _ _ => [{ path, tags, mode }]
  | .group _ children => toListedChildren mode children.toList
  | .seq child => toListedList .sequential child
  | .resource _ _ _ _ child => toListedList mode child
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Child-list helper for `ExecPlan.toListedList`. -/
@[expose] def toListedChildren (mode : ExecutionMode) : List ExecPlan → List ListedTest
  | [] => []
  | c :: cs => toListedList mode c ++ toListedChildren mode cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

/-- Enumerate the leaves of an `ExecPlan` as an `Array`. -/
@[expose] def toListed (p : ExecPlan) (defaultMode : ExecutionMode := .parallel) :
    Array ListedTest :=
  (p.toListedList defaultMode).toArray

mutual

/-- Build a skipped `ReportTree` for every leaf in an `ExecPlan` without executing
    any test or acquiring any resource (used when `failFast` has already tripped). -/
@[expose] def skipAll (reason : String) : ExecPlan → ReportTree
  | .leaf name path tags _ _ _ =>
    .leaf {
      name, path, tags
      result := .skip (some reason)
      durationMs := 0
    }
  | .group name children =>
    .group name (skipAllChildren reason children.toList).toArray
  | .seq child => skipAll reason child
  | .resource _ _ _ _ child => skipAll reason child
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

/-- Child-list helper for `ExecPlan.skipAll`. -/
@[expose] def skipAllChildren (reason : String) : List ExecPlan → List ReportTree
  | [] => []
  | c :: cs => skipAll reason c :: skipAllChildren reason cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

end

end ExecPlan

/-- Compute the number of worker threads to start for `threads` and `totalLeaves`.
    Always in `[1, max 1 threads]` and capped at `max 1 totalLeaves`. -/
@[expose] def computeWorkerCount (threads totalLeaves : Nat) : Nat :=
  min (max 1 threads) (max 1 totalLeaves)

/-- Runner configuration. -/
structure RunConfig where
  /-- Maximum number of tests running concurrently (`1` = strictly sequential on main thread). -/
  threads : Nat := 1
  /-- Default execution mode when no `parallel`/`sequential` modifier is present. -/
  defaultMode : ExecutionMode := .parallel
  /-- Optional master seed for property tests. If `none`, generated from OS randomness. -/
  seed : Option UInt64 := none
  /-- Filter applied before execution. -/
  filter : TestFilter := {}
  /-- Base `TestOptions` merged into every test's `TestContext`. -/
  options : TestOptions := {}
  /-- If `true`, skip remaining queued tests after the first failure. -/
  failFast : Bool := false
  /-- If `true`, capture per-test stdout/stderr via `IO.FS.withIsolatedStreams`. -/
  isolateStreams : Bool := true

/-- Bounded-concurrency worker pool backed by `Std.Mutex` + `Std.Condvar`. -/
private structure PoolState where
  queue : Std.Queue (IO Unit) := ∅
  closed : Bool := false
  deriving Nonempty

private structure WorkerPool where
  state : Std.Mutex PoolState
  condvar : Std.Condvar
  workers : Array (Task (Except IO.Error Unit))

private def WorkerPool.popJob (pool : WorkerPool) : BaseIO (Option (IO Unit)) :=
  pool.state.atomicallyOnce pool.condvar
    (do let st ← get; return !st.queue.isEmpty || st.closed)
    (do
      let st ← get
      match st.queue.dequeue? with
      | some (job, rest) =>
        set { st with queue := rest }
        return some job
      | none => return none)

private partial def WorkerPool.workerLoop (state : Std.Mutex PoolState) (condvar : Std.Condvar) :
    IO Unit := do
  let pool : WorkerPool := { state, condvar, workers := #[] }
  while true do
    match ← pool.popJob with
    | none => break
    | some job => job

private def WorkerPool.start (numWorkers : Nat) : IO WorkerPool := do
  let state ← Std.Mutex.new ({} : PoolState)
  let condvar ← Std.Condvar.new
  let mut workers := Array.mkEmpty numWorkers
  for _ in [:numWorkers] do
    let t ← IO.asTask (WorkerPool.workerLoop state condvar) .dedicated
    workers := workers.push t
  return { state, condvar, workers }

private def WorkerPool.submit [Nonempty α] (pool : WorkerPool) (action : IO α) :
    BaseIO (IO.Promise (Except IO.Error α)) := do
  let promise ← IO.Promise.new
  let job : IO Unit := do
    let res ← try
      pure (.ok (← action))
    catch e =>
      pure (.error e)
    promise.resolve res
  pool.state.atomically do
    let st ← get
    set { st with queue := st.queue.enqueue job }
  pool.condvar.notifyOne
  return promise

private def WorkerPool.shutdown (pool : WorkerPool) : IO Unit := do
  pool.state.atomically do
    let st ← get
    set { st with closed := true }
  pool.condvar.notifyAll
  for w in pool.workers do
    let _ ← IO.wait w

/-- Await a `Promise (Except IO.Error α)` safely. -/
private def awaitPromise (p : IO.Promise (Except IO.Error α)) : IO α := do
  match ← IO.wait p.result? with
  | none => throw (IO.userError "worker dropped task promise without resolving")
  | some (.error e) => throw e
  | some (.ok a) => return a

/-- Generate a 64-bit random seed from OS entropy. -/
def generateRandomSeed : IO UInt64 := do
  let bytes ← IO.getRandomBytes 8
  if bytes.size ≥ 8 then
    return bytes.toUInt64LE!
  else
    return (← IO.monoNanosNow).toUInt64

/-- Environment threaded through plan execution. -/
private structure ExecEnv where
  pool? : Option WorkerPool
  failFast : Bool
  isolateStreams : Bool
  failedFlag : IO.Ref Bool

/-- Execute a single resolved leaf test on the current thread (with stream isolation,
    exception handling, timing, and fail-fast short-circuiting). -/
private def execPlanLeaf (env : ExecEnv) (name : String) (path : Array String)
    (tags : Array String) (opts : TestOptions) (seed : UInt64)
    (exec : TestContext → IO TestResult) : IO LeafReport := do
  if env.failFast && (← env.failedFlag.get) then
    return {
      name, path, tags
      result := .skip (some "skipped (fail-fast)")
      durationMs := 0
    }
  let ctx : TestContext := { options := opts, path, seed }
  let start ← IO.monoMsNow
  let runOne : IO TestResult := do
    try
      exec ctx
    catch e =>
      pure (.fail "uncaught IO exception" s!"IO error: {e}" (.exception e.toString))
  let (captured, res) ←
    if env.isolateStreams then
      IO.FS.withIsolatedStreams runOne
    else
      pure ("", ← runOne)
  let stop ← IO.monoMsNow
  if res.isFailed then
    env.failedFlag.set true
  return {
    name, path, tags
    result := res
    durationMs := stop - start
    capturedOutput := captured
  }

/-- Execute an `ExecPlan` strictly sequentially on the current thread. -/
private partial def execPlanSeq (env : ExecEnv) : ExecPlan → IO ReportTree
  | .leaf name path tags opts seed exec => do
    let rep ← execPlanLeaf env name path tags opts seed exec
    return .leaf rep
  | .group name children => do
    let mut reports := Array.mkEmpty children.size
    for c in children do
      reports := reports.push (← execPlanSeq env c)
    return .group name reports
  | .seq child =>
    execPlanSeq env child
  | .resource desc path tags acq child => do
    if env.failFast && (← env.failedFlag.get) then
      return child.skipAll "skipped (fail-fast)"
    let release? : Except IO.Error (IO Unit) ← try
      pure (Except.ok (← acq))
    catch e =>
      pure (Except.error e)
    match release? with
    | .error e =>
      env.failedFlag.set true
      return .leaf {
        name := s!"resource: {desc}"
        path := path.push desc
        tags := tags
        result := .fail s!"failed to acquire resource '{desc}'"
          s!"IO error: {e}" (.exception e.toString)
        durationMs := 0
      }
    | .ok release =>
      try
        execPlanSeq env child
      finally
        try release catch _ => pure ()

/-- A handle representing in-flight asynchronous execution of an `ExecPlan`. -/
private inductive PendingReport where
  | ready (r : ReportTree)
  | promise (p : IO.Promise (Except IO.Error ReportTree))
  | task (t : Task (Except IO.Error ReportTree))
  | group (name : String) (children : Array PendingReport)

private partial def PendingReport.await : PendingReport → IO ReportTree
  | .ready r => pure r
  | .promise p => awaitPromise p
  | .task t => do IO.ofExcept (← IO.wait t)
  | .group name children => do
    let mut out := Array.mkEmpty children.size
    for c in children do
      out := out.push (← c.await)
    return .group name out

/-- Dispatch a compiled `ExecPlan` using the shared `WorkerPool` (when `env.pool?` is `some`).
    - Parallel leaves are submitted individually to the pool.
    - `.seq` subtrees are submitted as a single bounded worker job.
    - `.resource` nodes acquire once (skipping if `failFast` already tripped),
      dispatch their child plan across the pool, await completion, and release
      in `finally`. -/
private partial def dispatchPlan (env : ExecEnv) (plan : ExecPlan) : IO PendingReport := do
  match env.pool? with
  | none =>
    return .ready (← execPlanSeq env plan)
  | some pool =>
    match plan with
    | .leaf name path tags opts seed exec =>
      let p ← pool.submit do
        let rep ← execPlanLeaf env name path tags opts seed exec
        return ReportTree.leaf rep
      return .promise p
    | .group name children =>
      let mut pending := Array.mkEmpty children.size
      for c in children do
        pending := pending.push (← dispatchPlan env c)
      return .group name pending
    | .seq child =>
      let p ← pool.submit (execPlanSeq env child)
      return .promise p
    | .resource desc path tags acq child =>
      -- Lightweight coordinator task for the resource lifecycle; all actual
      -- leaf executions inside `child` still flow through the bounded `pool`,
      -- preventing worker-pool starvation on nested `withResource` scopes.
      let t ← IO.asTask (do
        if env.failFast && (← env.failedFlag.get) then
          return child.skipAll "skipped (fail-fast)"
        let release? : Except IO.Error (IO Unit) ← try
          pure (Except.ok (← acq))
        catch e =>
          pure (Except.error e)
        match release? with
        | .error e =>
          env.failedFlag.set true
          return ReportTree.leaf {
            name := s!"resource: {desc}"
            path := path.push desc
            tags := tags
            result := .fail s!"failed to acquire resource '{desc}'"
              s!"IO error: {e}" (.exception e.toString)
            durationMs := 0
          }
        | .ok release =>
          try
            let sub ← dispatchPlan env child
            sub.await
          finally
            try release catch _ => pure ())
      return .task t

/-- Run a `TestTree` according to `cfg`, returning `(reportTree, summary)`. -/
def runTree (tree : TestTree) (cfg : RunConfig := {}) : IO (ReportTree × RunSummary) := do
  let seed ← match cfg.seed with
    | some s => pure s
    | none => generateRandomSeed
  let threads := max 1 cfg.threads
  let start ← IO.monoMsNow
  match filterTree cfg.filter tree with
  | none =>
    let stop ← IO.monoMsNow
    return (.group "" #[], {
      passed := 0, failed := 0, skipped := 0,
      totalDurationMs := stop - start, seed, threads
    })
  | some filtered =>
    let plan := compilePlan seed cfg.options cfg.defaultMode filtered
    let failedFlag ← IO.mkRef false
    let pool? ←
      if threads > 1 then
        let totalLeaves := (listTests filtered cfg.defaultMode).size
        let numWorkers := computeWorkerCount threads totalLeaves
        if numWorkers > 1 then some <$> WorkerPool.start numWorkers
        else pure none
      else
        pure none
    let env : ExecEnv := {
      pool?
      failFast := cfg.failFast
      isolateStreams := cfg.isolateStreams
      failedFlag
    }
    let report ← try
      let pending ← dispatchPlan env plan
      pending.await
    finally
      if let some pool := pool? then
        pool.shutdown
    let stop ← IO.monoMsNow
    let summary := report.summarize (stop - start) seed threads
    return (report, summary)

end
end LSpec
