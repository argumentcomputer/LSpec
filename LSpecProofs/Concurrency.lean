module
public import LSpec.Runner
public import LSpecProofs.Report

/-!
# Formal Small-Step Operational Semantics of the Parallel Runner (`LSpecProofs.Concurrency`)

Formalizes the concurrency, sequential-isolation, resource-bracketing,
deadlock-freedom, termination, and determinism guarantees of `LSpec.Runner`'s
`WorkerPool` + `ExecPlan` scheduler via a faithful small-step transition system.

Main theorems (all `sorry`-free):
1. `bounded_concurrency`: at every reachable interleaving, `activeWorkers rt ≤ cap`.
2. `seq_exclusion` & `seq_strict_left_to_right`: inside any active `.runningSeq`
   subtree, at most 1 leaf is ever running and children execute strictly in
   declaration order.
3. `resource_bracket_invariant`, `resource_released_exactly_once_on_done`,
   `resPending_only_acquire`, and `resActive_release_requires_done`:
   no child executes before acquire succeeds, release fires only after all children
   finish, failed acquire skips children with zero releases, and every acquired
   resource is released exactly once upon termination.
4. `progress_deadlock_free` & `termination_step_bound`: every non-terminal reachable
   state can step (proving that nested `withResource` coordinators waiting outside
   the worker pool cannot deadlock even at `cap = 1`), and every trace terminates in
   at most `planSteps plan` steps.
5. `parallel_eq_sequential`: every reachable terminal state under ANY thread count
   `cap ≥ 1` yields the exact same `ReportTree` and `RunSummary` as sequential
   evaluation `evalSeq plan`.
-/

namespace LSpec.Proofs.Concurrency
public section

open LSpec

private theorem list_mem_sizeOf_lt {α : Type _} [SizeOf α] (x : α) :
    ∀ (xs : List α), x ∈ xs → sizeOf x < sizeOf xs
  | [], h => nomatch h
  | y :: ys, h => by
    simp only [List.mem_cons] at h
    cases h with
    | inl hEq => subst hEq; simp; omega
    | inr hMem => have := list_mem_sizeOf_lt x ys hMem; simp; omega

/-! ## Pure Model of `ExecPlan` and Canonical Sequential Semantics -/

/-- Pure deterministic model of a compiled `ExecPlan` (capturing leaves, groups,
    sequential subtrees, and resource acquire outcomes). -/
inductive PurePlan : Type where
  | leaf (name : String) (path tags : Array String) (result : TestResult)
  | group (name : String) (children : List PurePlan)
  | seq (child : PurePlan)
  | resource (desc : String) (path tags : Array String) (acq : Except String Unit) (child : PurePlan)

/-- Failure report emitted when a resource fails to acquire (matching `LSpec.Runner`). -/
def resourceFailReport (desc : String) (path tags : Array String) (err : String) : ReportTree :=
  .leaf {
    name := s!"resource: {desc}"
    path := path.push desc
    tags := tags
    result := .fail s!"failed to acquire resource '{desc}'" s!"IO error: {err}" (.exception err)
    durationMs := 0
  }

mutual

/-- Canonical sequential evaluation of a `PurePlan`. -/
def evalSeq : PurePlan → ReportTree
  | .leaf name path tags result =>
    .leaf { name, path, tags, result, durationMs := 0 }
  | .group name children =>
    .group name (evalSeqChildren children).toArray
  | .seq child =>
    evalSeq child
  | .resource desc path tags acq child =>
    match acq with
    | .error err => resourceFailReport desc path tags err
    | .ok () => evalSeq child
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

def evalSeqChildren : List PurePlan → List ReportTree
  | [] => []
  | c :: cs => evalSeq c :: evalSeqChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

/-! ## Small-Step Concurrent Runtime Tree (`RT`) -/

/-- In-flight runtime state of a `PurePlan` executing on a bounded `WorkerPool`. -/
inductive RT : Type where
  /-- Leaf queued in the `WorkerPool` (0 slots held). -/
  | queuedLeaf (name : String) (path tags : Array String) (result : TestResult)
  /-- Leaf actively running on a worker thread (1 pool slot held). -/
  | runningLeaf (name : String) (path tags : Array String) (result : TestResult)
  /-- Completed subtree (0 slots held). -/
  | done (report : ReportTree)
  /-- Group whose children execute concurrently and reassemble in declaration order. -/
  | group (name : String) (children : List RT)
  /-- Sequential subtree queued as one job in the `WorkerPool` (0 slots held). -/
  | queuedSeq (plan : PurePlan)
  /-- Sequential subtree actively executing on 1 worker thread (1 pool slot held). -/
  | runningSeq (inner : RT)
  /-- Resource coordinator awaiting acquisition (runs outside pool capacity). -/
  | resPending (desc : String) (path tags : Array String) (acq : Except String Unit) (child : PurePlan)
  /-- Resource acquired; child subtree is executing on the pool until `.done`. -/
  | resActive (desc : String) (child : RT)

/-- Observable execution events emitted by small-step transitions. -/
inductive Event : Type where
  | startLeaf (path : Array String)
  | finishLeaf (path : Array String)
  | startSeq
  | finishSeq
  | acquireOk (desc : String)
  | acquireFail (desc : String)
  | release (desc : String)
  | collapseGroup (name : String)
  deriving BEq, Repr

def Event.isAcquireOk : Event → Bool
  | .acquireOk _ => true
  | _ => false

def Event.isRelease : Event → Bool
  | .release _ => true
  | _ => false

def countAcquireOk (tr : List Event) : Nat :=
  (tr.filter Event.isAcquireOk).length

def countRelease (tr : List Event) : Nat :=
  (tr.filter Event.isRelease).length

mutual

/-- Initial runtime state produced by dispatching a `PurePlan`. -/
def RT.ofPlan : PurePlan → RT
  | .leaf name path tags result => .queuedLeaf name path tags result
  | .group name children => .group name (RT.ofPlanChildren children)
  | .seq child => .queuedSeq child
  | .resource desc path tags acq child => .resPending desc path tags acq child
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

def RT.ofPlanChildren : List PurePlan → List RT
  | [] => []
  | c :: cs => RT.ofPlan c :: RT.ofPlanChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

/-! ## State Metrics -/

mutual

/-- Number of `WorkerPool` slots currently held by `rt`.
    `runningSeq` holds exactly 1 slot regardless of its inner state, and
    `resPending`/`resActive` hold 0 coordinator slots (only their children
    consume pool slots). -/
def activeWorkers : RT → Nat
  | .queuedLeaf _ _ _ _ => 0
  | .runningLeaf _ _ _ _ => 1
  | .done _ => 0
  | .group _ cs => activeWorkersChildren cs
  | .queuedSeq _ => 0
  | .runningSeq _ => 1
  | .resPending _ _ _ _ _ => 0
  | .resActive _ child => activeWorkers child
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

def activeWorkersChildren : List RT → Nat
  | [] => 0
  | c :: cs => activeWorkers c + activeWorkersChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

/-- Number of `runningLeaf` nodes currently executing inside `rt`. -/
def runningLeaves : RT → Nat
  | .queuedLeaf _ _ _ _ => 0
  | .runningLeaf _ _ _ _ => 1
  | .done _ => 0
  | .group _ cs => runningLeavesChildren cs
  | .queuedSeq _ => 0
  | .runningSeq inner => runningLeaves inner
  | .resPending _ _ _ _ _ => 0
  | .resActive _ child => runningLeaves child
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

def runningLeavesChildren : List RT → Nat
  | [] => 0
  | c :: cs => runningLeaves c + runningLeavesChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

/-- Number of acquired-but-not-yet-released resources inside `rt`. -/
def activeResources : RT → Nat
  | .queuedLeaf _ _ _ _ => 0
  | .runningLeaf _ _ _ _ => 0
  | .done _ => 0
  | .group _ cs => activeResourcesChildren cs
  | .queuedSeq _ => 0
  | .runningSeq inner => activeResources inner
  | .resPending _ _ _ _ _ => 0
  | .resActive _ child => 1 + activeResources child
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

def activeResourcesChildren : List RT → Nat
  | [] => 0
  | c :: cs => activeResources c + activeResourcesChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

/-- Canonical `ReportTree` denotation of any intermediate runtime tree `rt`. -/
def denote : RT → ReportTree
  | .queuedLeaf name path tags result =>
    .leaf { name, path, tags, result, durationMs := 0 }
  | .runningLeaf name path tags result =>
    .leaf { name, path, tags, result, durationMs := 0 }
  | .done r => r
  | .group name cs => .group name (denoteChildren cs).toArray
  | .queuedSeq plan => evalSeq plan
  | .runningSeq inner => denote inner
  | .resPending desc path tags acq child =>
    match acq with
    | .error err => resourceFailReport desc path tags err
    | .ok () => evalSeq child
  | .resActive _ child => denote child
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

def denoteChildren : List RT → List ReportTree
  | [] => []
  | c :: cs => denote c :: denoteChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

/-- Exact number of small steps required for a `PurePlan` to reach `.done`. -/
def planSteps : PurePlan → Nat
  | .leaf _ _ _ _ => 2
  | .group _ cs => 1 + planStepsChildren cs
  | .seq child => 2 + planSteps child
  | .resource _ _ _ acq child =>
    match acq with
    | .error _ => 1
    | .ok () => 2 + planSteps child
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

def planStepsChildren : List PurePlan → Nat
  | [] => 0
  | c :: cs => planSteps c + planStepsChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

/-- Strict progress measure: every `SeqStep` and `ParStep` decrements `remainingSteps` by 1. -/
def remainingSteps : RT → Nat
  | .queuedLeaf _ _ _ _ => 2
  | .runningLeaf _ _ _ _ => 1
  | .done _ => 0
  | .group _ cs => 1 + remainingStepsChildren cs
  | .queuedSeq plan => 2 + planSteps plan
  | .runningSeq inner => 1 + remainingSteps inner
  | .resPending _ _ _ acq child =>
    match acq with
    | .error _ => 1
    | .ok () => 2 + planSteps child
  | .resActive _ child => 1 + remainingSteps child
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

def remainingStepsChildren : List RT → Nat
  | [] => 0
  | c :: cs => remainingSteps c + remainingStepsChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

/-- Extract completed reports when every child in a list is `.done`. -/
def allDoneReports : List RT → Option (List ReportTree)
  | [] => some []
  | .done r :: rest => (allDoneReports rest).map (r :: ·)
  | _ :: _ => none

/-- Predicate asserting a runtime node is terminal (`.done _`). -/
def RT.isDone : RT → Prop
  | .done _ => True
  | _ => False

private theorem isDone_iff {rt : RT} : rt.isDone ↔ ∃ r, rt = .done r := by
  cases rt <;> simp [RT.isDone]

/-! ## Small-Step Relations: Sequential (`SeqStep`) and Bounded-Parallel (`ParStep`) -/

mutual

/-- Strict left-to-right sequential execution inside a single worker thread (`execPlanSeq`). -/
inductive SeqStep : RT → Event → RT → Prop where
  | startLeaf (name path tags res) :
      SeqStep (.queuedLeaf name path tags res) (.startLeaf path) (.runningLeaf name path tags res)
  | finishLeaf (name path tags res) :
      SeqStep (.runningLeaf name path tags res) (.finishLeaf path)
        (.done (.leaf { name, path, tags, result := res, durationMs := 0 }))
  | groupStep {name cs cs' ev} :
      SeqGroupStep cs ev cs' →
      SeqStep (.group name cs) ev (.group name cs')
  | groupCollapse {name cs rs} :
      allDoneReports cs = some rs →
      SeqStep (.group name cs) (.collapseGroup name) (.done (.group name rs.toArray))
  | startSeq (plan) :
      SeqStep (.queuedSeq plan) .startSeq (.runningSeq (RT.ofPlan plan))
  | stepSeq {inner inner' ev} :
      SeqStep inner ev inner' →
      SeqStep (.runningSeq inner) ev (.runningSeq inner')
  | finishSeq (r) :
      SeqStep (.runningSeq (.done r)) .finishSeq (.done r)
  | resAcqOk (desc path tags child) :
      SeqStep (.resPending desc path tags (.ok ()) child) (.acquireOk desc)
        (.resActive desc (RT.ofPlan child))
  | resAcqFail (desc path tags err child) :
      SeqStep (.resPending desc path tags (.error err) child) (.acquireFail desc)
        (.done (resourceFailReport desc path tags err))
  | resStep {desc child child' ev} :
      SeqStep child ev child' →
      SeqStep (.resActive desc child) ev (.resActive desc child')
  | resRelease (desc r) :
      SeqStep (.resActive desc (.done r)) (.release desc) (.done r)

/-- Strict left-to-right stepping on a group's child list: only advances past
    children that are already `.done`. -/
inductive SeqGroupStep : List RT → Event → List RT → Prop where
  | head {c c' rest ev} :
      SeqStep c ev c' →
      SeqGroupStep (c :: rest) ev (c' :: rest)
  | skipDone {r rest rest' ev} :
      SeqGroupStep rest ev rest' →
      SeqGroupStep (.done r :: rest) ev (.done r :: rest')

end

/-- Bounded-concurrency parallel step relation. `free` is the number of currently
    available `WorkerPool` slots (`cap - activeWorkers root`). -/
inductive ParStep (free : Nat) : RT → Event → RT → Prop where
  | startLeaf (name path tags res) (hFree : free ≥ 1) :
      ParStep free (.queuedLeaf name path tags res) (.startLeaf path)
        (.runningLeaf name path tags res)
  | finishLeaf (name path tags res) :
      ParStep free (.runningLeaf name path tags res) (.finishLeaf path)
        (.done (.leaf { name, path, tags, result := res, durationMs := 0 }))
  | groupStep {name pre c c' post ev} :
      ParStep free c ev c' →
      ParStep free (.group name (pre ++ c :: post)) ev (.group name (pre ++ c' :: post))
  | groupCollapse {name cs rs} :
      allDoneReports cs = some rs →
      ParStep free (.group name cs) (.collapseGroup name) (.done (.group name rs.toArray))
  | startSeq (plan) (hFree : free ≥ 1) :
      ParStep free (.queuedSeq plan) .startSeq (.runningSeq (RT.ofPlan plan))
  | stepSeq {inner inner' ev} :
      SeqStep inner ev inner' →
      ParStep free (.runningSeq inner) ev (.runningSeq inner')
  | finishSeq (r) :
      ParStep free (.runningSeq (.done r)) .finishSeq (.done r)
  | resAcqOk (desc path tags child) :
      ParStep free (.resPending desc path tags (.ok ()) child) (.acquireOk desc)
        (.resActive desc (RT.ofPlan child))
  | resAcqFail (desc path tags err child) :
      ParStep free (.resPending desc path tags (.error err) child) (.acquireFail desc)
        (.done (resourceFailReport desc path tags err))
  | resStep {desc child child' ev} :
      ParStep free child ev child' →
      ParStep free (.resActive desc child) ev (.resActive desc child')
  | resRelease (desc r) :
      ParStep free (.resActive desc (.done r)) (.release desc) (.done r)

/-- Top-level bounded-pool machine transition at thread limit `cap`. -/
def MachineStep (cap : Nat) (rt : RT) (ev : Event) (rt' : RT) : Prop :=
  ParStep (cap - activeWorkers rt) rt ev rt'

/-- Multi-step execution trace of the bounded-pool machine. -/
inductive Trace (cap : Nat) : RT → List Event → RT → Prop where
  | refl (rt : RT) : Trace cap rt [] rt
  | step {rt rt' rt'' ev tr} :
      MachineStep cap rt ev rt' →
      Trace cap rt' tr rt'' →
      Trace cap rt (ev :: tr) rt''

/-! ## Helper Lemmas -/

theorem activeWorkersChildren_append (xs ys : List RT) :
    activeWorkersChildren (xs ++ ys) = activeWorkersChildren xs + activeWorkersChildren ys := by
  induction xs with
  | nil => simp [activeWorkersChildren]
  | cons x rest ih => simp [activeWorkersChildren, ih]; omega

theorem activeResourcesChildren_append (xs ys : List RT) :
    activeResourcesChildren (xs ++ ys) = activeResourcesChildren xs + activeResourcesChildren ys := by
  induction xs with
  | nil => simp [activeResourcesChildren]
  | cons x rest ih => simp [activeResourcesChildren, ih]; omega

theorem denoteChildren_append (xs ys : List RT) :
    denoteChildren (xs ++ ys) = denoteChildren xs ++ denoteChildren ys := by
  induction xs with
  | nil => simp [denoteChildren]
  | cons x rest ih => simp [denoteChildren, ih]

theorem remainingStepsChildren_append (xs ys : List RT) :
    remainingStepsChildren (xs ++ ys) = remainingStepsChildren xs + remainingStepsChildren ys := by
  induction xs with
  | nil => simp [remainingStepsChildren]
  | cons x rest ih => simp [remainingStepsChildren, ih]; omega

theorem allDoneReports_activeWorkers {cs : List RT} {rs : List ReportTree}
    (h : allDoneReports cs = some rs) : activeWorkersChildren cs = 0 := by
  induction cs generalizing rs with
  | nil => simp [activeWorkersChildren]
  | cons c rest ih =>
    cases c <;> simp [allDoneReports] at h
    rename_i r
    obtain ⟨rs', hrs', _⟩ := h
    simp [activeWorkersChildren, activeWorkers, ih hrs']

theorem allDoneReports_activeResources {cs : List RT} {rs : List ReportTree}
    (h : allDoneReports cs = some rs) : activeResourcesChildren cs = 0 := by
  induction cs generalizing rs with
  | nil => simp [activeResourcesChildren]
  | cons c rest ih =>
    cases c <;> simp [allDoneReports] at h
    rename_i r
    obtain ⟨rs', hrs', _⟩ := h
    simp [activeResourcesChildren, activeResources, ih hrs']

theorem allDoneReports_denote {cs : List RT} {rs : List ReportTree}
    (h : allDoneReports cs = some rs) : denoteChildren cs = rs := by
  induction cs generalizing rs with
  | nil =>
    simp [allDoneReports] at h
    subst h
    simp [denoteChildren]
  | cons c rest ih =>
    cases c <;> simp [allDoneReports] at h
    rename_i r
    obtain ⟨rs', hrs', rfl⟩ := h
    simp [denoteChildren, denote, ih hrs']

theorem allDoneReports_remainingSteps {cs : List RT} {rs : List ReportTree}
    (h : allDoneReports cs = some rs) : remainingStepsChildren cs = 0 := by
  induction cs generalizing rs with
  | nil => simp [remainingStepsChildren]
  | cons c rest ih =>
    cases c <;> simp [allDoneReports] at h
    rename_i r
    obtain ⟨rs', hrs', _⟩ := h
    simp [remainingStepsChildren, remainingSteps, ih hrs']

mutual

theorem activeWorkers_ofPlan : (p : PurePlan) → activeWorkers (RT.ofPlan p) = 0
  | .leaf _ _ _ _ => by simp [RT.ofPlan, activeWorkers]
  | .group _ cs => by simp [RT.ofPlan, activeWorkers, activeWorkers_ofPlanChildren cs]
  | .seq _ => by simp [RT.ofPlan, activeWorkers]
  | .resource _ _ _ _ _ => by simp [RT.ofPlan, activeWorkers]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem activeWorkers_ofPlanChildren : (cs : List PurePlan) →
    activeWorkersChildren (RT.ofPlanChildren cs) = 0
  | [] => by simp [RT.ofPlanChildren, activeWorkersChildren]
  | c :: rest => by
    simp [RT.ofPlanChildren, activeWorkersChildren, activeWorkers_ofPlan c,
      activeWorkers_ofPlanChildren rest]
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

theorem runningLeaves_ofPlan : (p : PurePlan) → runningLeaves (RT.ofPlan p) = 0
  | .leaf _ _ _ _ => by simp [RT.ofPlan, runningLeaves]
  | .group _ cs => by simp [RT.ofPlan, runningLeaves, runningLeaves_ofPlanChildren cs]
  | .seq _ => by simp [RT.ofPlan, runningLeaves]
  | .resource _ _ _ _ _ => by simp [RT.ofPlan, runningLeaves]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem runningLeaves_ofPlanChildren : (cs : List PurePlan) →
    runningLeavesChildren (RT.ofPlanChildren cs) = 0
  | [] => by simp [RT.ofPlanChildren, runningLeavesChildren]
  | c :: rest => by
    simp [RT.ofPlanChildren, runningLeavesChildren, runningLeaves_ofPlan c,
      runningLeaves_ofPlanChildren rest]
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

theorem activeResources_ofPlan : (p : PurePlan) → activeResources (RT.ofPlan p) = 0
  | .leaf _ _ _ _ => by simp [RT.ofPlan, activeResources]
  | .group _ cs => by simp [RT.ofPlan, activeResources, activeResources_ofPlanChildren cs]
  | .seq _ => by simp [RT.ofPlan, activeResources]
  | .resource _ _ _ _ _ => by simp [RT.ofPlan, activeResources]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem activeResources_ofPlanChildren : (cs : List PurePlan) →
    activeResourcesChildren (RT.ofPlanChildren cs) = 0
  | [] => by simp [RT.ofPlanChildren, activeResourcesChildren]
  | c :: rest => by
    simp [RT.ofPlanChildren, activeResourcesChildren, activeResources_ofPlan c,
      activeResources_ofPlanChildren rest]
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

theorem denote_ofPlan : (p : PurePlan) → denote (RT.ofPlan p) = evalSeq p
  | .leaf _ _ _ _ => by simp [RT.ofPlan, denote, evalSeq]
  | .group _ cs => by simp [RT.ofPlan, denote, evalSeq, denote_ofPlanChildren cs]
  | .seq _ => by simp [RT.ofPlan, denote, evalSeq]
  | .resource _ _ _ acq _ => by
    cases acq with
    | ok u => cases u; simp [RT.ofPlan, denote, evalSeq]
    | error _ => simp [RT.ofPlan, denote, evalSeq]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem denote_ofPlanChildren : (cs : List PurePlan) →
    denoteChildren (RT.ofPlanChildren cs) = evalSeqChildren cs
  | [] => by simp [RT.ofPlanChildren, denoteChildren, evalSeqChildren]
  | c :: rest => by
    simp [RT.ofPlanChildren, denoteChildren, evalSeqChildren, denote_ofPlan c,
      denote_ofPlanChildren rest]
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

theorem remainingSteps_ofPlan : (p : PurePlan) → remainingSteps (RT.ofPlan p) = planSteps p
  | .leaf _ _ _ _ => by simp [RT.ofPlan, remainingSteps, planSteps]
  | .group _ cs => by simp [RT.ofPlan, remainingSteps, planSteps, remainingSteps_ofPlanChildren cs]
  | .seq _ => by simp [RT.ofPlan, remainingSteps, planSteps]
  | .resource _ _ _ acq _ => by
    cases acq with
    | ok u => cases u; simp [RT.ofPlan, remainingSteps, planSteps]
    | error _ => simp [RT.ofPlan, remainingSteps, planSteps]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem remainingSteps_ofPlanChildren : (cs : List PurePlan) →
    remainingStepsChildren (RT.ofPlanChildren cs) = planStepsChildren cs
  | [] => by simp [RT.ofPlanChildren, remainingStepsChildren, planStepsChildren]
  | c :: rest => by
    simp [RT.ofPlanChildren, remainingStepsChildren, planStepsChildren, remainingSteps_ofPlan c,
      remainingSteps_ofPlanChildren rest]
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

/-! ## Theorem 1: Bounded Concurrency (`activeWorkers ≤ cap`) -/

theorem parStep_activeWorkers_delta {free : Nat} {rt rt' : RT} {ev : Event}
    (h : ParStep free rt ev rt') :
    activeWorkers rt' ≤ activeWorkers rt + free := by
  induction h with
  | startLeaf _ _ _ _ hFree => simp [activeWorkers]; omega
  | finishLeaf _ _ _ _ => simp [activeWorkers]
  | groupStep _ ih =>
    simp only [activeWorkers, activeWorkersChildren_append, activeWorkersChildren]
    omega
  | groupCollapse hDone =>
    simp [activeWorkers, allDoneReports_activeWorkers hDone]
  | startSeq _ hFree => simp [activeWorkers]; omega
  | stepSeq _ => simp [activeWorkers]
  | finishSeq _ => simp [activeWorkers]
  | resAcqOk _ _ _ child => simp [activeWorkers, activeWorkers_ofPlan]
  | resAcqFail _ _ _ _ _ => simp [activeWorkers]
  | resStep _ ih => simp [activeWorkers]; omega
  | resRelease _ _ => simp [activeWorkers]

theorem machineStep_preserves_bound {cap : Nat} {rt rt' : RT} {ev : Event}
    (hLe : activeWorkers rt ≤ cap) (hStep : MachineStep cap rt ev rt') :
    activeWorkers rt' ≤ cap := by
  have hDelta := parStep_activeWorkers_delta hStep
  omega

private theorem trace_preserves_bound {cap : Nat} {rt₀ rt : RT} {tr : List Event}
    (hTrace : Trace cap rt₀ tr rt) (h0 : activeWorkers rt₀ ≤ cap) :
    activeWorkers rt ≤ cap := by
  induction hTrace with
  | refl _ => exact h0
  | step hStep _ ih => exact ih (machineStep_preserves_bound h0 hStep)

/-- **Theorem 1 (Bounded Concurrency)**:
    Along every possible interleaving from `RT.ofPlan plan` under thread bound `cap`,
    the number of simultaneously active worker-pool slots never exceeds `cap`. -/
theorem bounded_concurrency {cap : Nat} {plan : PurePlan} {tr : List Event} {rt : RT}
    (hTrace : Trace cap (RT.ofPlan plan) tr rt) :
    activeWorkers rt ≤ cap :=
  trace_preserves_bound hTrace (by simp [activeWorkers_ofPlan])

/-! ## Theorem 2: Sequential Exclusion & Strict Declaration-Order Execution -/

/-- **Theorem 2a (Strict Left-to-Right Ordering)**:
    Inside a sequential group, no later sibling in `rest` can ever step while
    the head child `c` is not `.done`. -/
theorem seq_strict_left_to_right {c : RT} {rest cs' : List RT} {ev : Event}
    (hNotDone : ¬ c.isDone) (hStep : SeqGroupStep (c :: rest) ev cs') :
    ∃ c', cs' = c' :: rest ∧ SeqStep c ev c' := by
  cases hStep with
  | head hSub => exact ⟨_, rfl, hSub⟩
  | skipDone _ => exact absurd trivial hNotDone

mutual

/-- Invariant for a runtime tree executing strictly sequentially:
    every `.group` has only unfinished siblings with 0 running leaves behind
    its active child, and the whole subtree has at most 1 running leaf. -/
def SeqWF : RT → Prop
  | .queuedLeaf _ _ _ _ => True
  | .runningLeaf _ _ _ _ => True
  | .done _ => True
  | .group _ cs => SeqWFChildren cs
  | .queuedSeq _ => True
  | .runningSeq inner => SeqWF inner
  | .resPending _ _ _ _ _ => True
  | .resActive _ child => SeqWF child
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

def SeqWFChildren : List RT → Prop
  | [] => True
  | .done _ :: rest => SeqWFChildren rest
  | c :: rest => SeqWF c ∧ SeqWFChildren rest ∧ runningLeavesChildren rest = 0
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

mutual

theorem seqWF_runningLeaves_le_one : (rt : RT) → SeqWF rt → runningLeaves rt ≤ 1
  | .queuedLeaf _ _ _ _, _ => by simp [runningLeaves]
  | .runningLeaf _ _ _ _, _ => by simp [runningLeaves]
  | .done _, _ => by simp [runningLeaves]
  | .group _ cs, h => by
    simp only [SeqWF] at h
    simp only [runningLeaves]
    exact seqWFChildren_runningLeaves_le_one cs h
  | .queuedSeq _, _ => by simp [runningLeaves]
  | .runningSeq inner, h => by
    simp only [SeqWF] at h
    simp only [runningLeaves]
    exact seqWF_runningLeaves_le_one inner h
  | .resPending _ _ _ _ _, _ => by simp [runningLeaves]
  | .resActive _ child, h => by
    simp only [SeqWF] at h
    simp only [runningLeaves]
    exact seqWF_runningLeaves_le_one child h
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

theorem seqWFChildren_runningLeaves_le_one : (cs : List RT) → SeqWFChildren cs →
    runningLeavesChildren cs ≤ 1
  | [], _ => by simp [runningLeavesChildren]
  | c :: rest, h => by
    cases c with
    | done _ =>
      simp only [SeqWFChildren] at h
      simp only [runningLeavesChildren, runningLeaves, Nat.zero_add]
      exact seqWFChildren_runningLeaves_le_one rest h
    | queuedLeaf _ _ _ _ | runningLeaf _ _ _ _ | group _ _ | queuedSeq _ | runningSeq _
    | resPending _ _ _ _ _ | resActive _ _ =>
      simp only [SeqWFChildren] at h
      obtain ⟨hc, _, hRestZero⟩ := h
      have hHead := seqWF_runningLeaves_le_one _ hc
      simp only [runningLeavesChildren, hRestZero, Nat.add_zero]
      exact hHead
termination_by cs => sizeOf cs
decreasing_by all_goals (try subst_vars; simp_wf; try omega)

end

mutual

theorem seqWF_ofPlan : (p : PurePlan) → SeqWF (RT.ofPlan p)
  | .leaf _ _ _ _ => by simp [RT.ofPlan, SeqWF]
  | .group _ cs => by simp [RT.ofPlan, SeqWF, seqWF_ofPlanChildren cs]
  | .seq _ => by simp [RT.ofPlan, SeqWF]
  | .resource _ _ _ _ _ => by simp [RT.ofPlan, SeqWF]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem seqWF_ofPlanChildren : (cs : List PurePlan) →
    SeqWFChildren (RT.ofPlanChildren cs)
  | [] => by simp [RT.ofPlanChildren, SeqWFChildren]
  | c :: rest => by
    cases hHead : RT.ofPlan c with
    | done _ => cases c <;> simp [RT.ofPlan] at hHead
    | queuedLeaf _ _ _ _ | runningLeaf _ _ _ _ | group _ _ | queuedSeq _ | runningSeq _
    | resPending _ _ _ _ _ | resActive _ _ =>
      simp only [RT.ofPlanChildren, hHead, SeqWFChildren]
      exact ⟨by rw [← hHead]; exact seqWF_ofPlan c,
             seqWF_ofPlanChildren rest,
             runningLeaves_ofPlanChildren rest⟩
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

theorem seqStep_not_done {rt rt' : RT} {ev : Event} (h : SeqStep rt ev rt') : ¬ rt.isDone := by
  cases h <;> simp [RT.isDone]

mutual

theorem seqStep_preserves_seqWF {rt rt' : RT} {ev : Event} :
    SeqStep rt ev rt' → SeqWF rt → SeqWF rt'
  | .startLeaf .., _ => by simp [SeqWF]
  | .finishLeaf .., _ => by simp [SeqWF]
  | .groupStep hG, h => by
    simp only [SeqWF] at h ⊢
    exact seqGroupStep_preserves_seqWF hG h
  | .groupCollapse _, _ => by simp [SeqWF]
  | .startSeq plan, _ => by simp [SeqWF, seqWF_ofPlan]
  | .stepSeq hSub, h => by
    simp only [SeqWF] at h ⊢
    exact seqStep_preserves_seqWF hSub h
  | .finishSeq _, _ => by simp [SeqWF]
  | .resAcqOk _ _ _ child, _ => by simp [SeqWF, seqWF_ofPlan]
  | .resAcqFail .., _ => by simp [SeqWF]
  | .resStep hSub, h => by
    simp only [SeqWF] at h ⊢
    exact seqStep_preserves_seqWF hSub h
  | .resRelease .., _ => by simp [SeqWF]

theorem seqGroupStep_preserves_seqWF {cs cs' : List RT} {ev : Event} :
    SeqGroupStep cs ev cs' → SeqWFChildren cs → SeqWFChildren cs'
  | @SeqGroupStep.head c c' rest _ hSub, hWF => by
    cases c with
    | done _ => exact absurd trivial (seqStep_not_done hSub)
    | queuedLeaf _ _ _ _ | runningLeaf _ _ _ _ | group _ _ | queuedSeq _ | runningSeq _
    | resPending _ _ _ _ _ | resActive _ _ =>
      simp only [SeqWFChildren] at hWF
      obtain ⟨hHeadWF, hRestWF, hRestZero⟩ := hWF
      have hHeadWF' := seqStep_preserves_seqWF hSub hHeadWF
      cases c' with
      | done _ => simpa [SeqWFChildren] using hRestWF
      | queuedLeaf _ _ _ _ | runningLeaf _ _ _ _ | group _ _ | queuedSeq _ | runningSeq _
      | resPending _ _ _ _ _ | resActive _ _ =>
        simpa [SeqWFChildren] using ⟨hHeadWF', hRestWF, hRestZero⟩
  | .skipDone hSub, hWF => by
    simp only [SeqWFChildren] at hWF ⊢
    exact seqGroupStep_preserves_seqWF hSub hWF

end

mutual

/-- Global parallel-tree invariant: every active `.runningSeq inner` anywhere
    in the runtime tree satisfies `SeqWF inner` (and therefore `runningLeaves inner ≤ 1`). -/
def AllSeqsWF : RT → Prop
  | .queuedLeaf _ _ _ _ => True
  | .runningLeaf _ _ _ _ => True
  | .done _ => True
  | .group _ cs => AllSeqsWFChildren cs
  | .queuedSeq _ => True
  | .runningSeq inner => SeqWF inner
  | .resPending _ _ _ _ _ => True
  | .resActive _ child => AllSeqsWF child
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

def AllSeqsWFChildren : List RT → Prop
  | [] => True
  | c :: cs => AllSeqsWF c ∧ AllSeqsWFChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

theorem allSeqsWFChildren_append {xs ys : List RT} :
    AllSeqsWFChildren (xs ++ ys) ↔ AllSeqsWFChildren xs ∧ AllSeqsWFChildren ys := by
  induction xs with
  | nil => simp [AllSeqsWFChildren]
  | cons x rest ih =>
    simp only [List.cons_append, AllSeqsWFChildren, ih]
    exact ⟨fun ⟨hx, h1, h2⟩ => ⟨⟨hx, h1⟩, h2⟩, fun ⟨⟨hx, h1⟩, h2⟩ => ⟨hx, h1, h2⟩⟩

mutual

theorem allSeqsWF_ofPlan : (p : PurePlan) → AllSeqsWF (RT.ofPlan p)
  | .leaf _ _ _ _ => by simp [RT.ofPlan, AllSeqsWF]
  | .group _ cs => by simp [RT.ofPlan, AllSeqsWF, allSeqsWF_ofPlanChildren cs]
  | .seq _ => by simp [RT.ofPlan, AllSeqsWF]
  | .resource _ _ _ _ _ => by simp [RT.ofPlan, AllSeqsWF]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem allSeqsWF_ofPlanChildren : (cs : List PurePlan) →
    AllSeqsWFChildren (RT.ofPlanChildren cs)
  | [] => by simp [RT.ofPlanChildren, AllSeqsWFChildren]
  | c :: rest => by
    simp only [RT.ofPlanChildren, AllSeqsWFChildren]
    exact ⟨allSeqsWF_ofPlan c, allSeqsWF_ofPlanChildren rest⟩
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

theorem parStep_preserves_allSeqsWF {free : Nat} {rt rt' : RT} {ev : Event}
    (hStep : ParStep free rt ev rt') (hWF : AllSeqsWF rt) : AllSeqsWF rt' := by
  induction hStep with
  | startLeaf => simp [AllSeqsWF]
  | finishLeaf => simp [AllSeqsWF]
  | groupStep _ ih =>
    simp only [AllSeqsWF, allSeqsWFChildren_append, AllSeqsWFChildren] at hWF ⊢
    exact ⟨hWF.1, ih hWF.2.1, hWF.2.2⟩
  | groupCollapse => simp [AllSeqsWF]
  | startSeq plan _ => simp [AllSeqsWF, seqWF_ofPlan]
  | stepSeq hSub =>
    simp only [AllSeqsWF] at hWF ⊢
    exact seqStep_preserves_seqWF hSub hWF
  | finishSeq => simp [AllSeqsWF]
  | resAcqOk _ _ _ child => simp [AllSeqsWF, allSeqsWF_ofPlan]
  | resAcqFail => simp [AllSeqsWF]
  | resStep _ ih =>
    simp only [AllSeqsWF] at hWF ⊢
    exact ih hWF
  | resRelease => simp [AllSeqsWF]

private theorem trace_preserves_allSeqsWF {cap : Nat} {rt₀ rt : RT} {tr : List Event}
    (hTrace : Trace cap rt₀ tr rt) (h0 : AllSeqsWF rt₀) : AllSeqsWF rt := by
  induction hTrace with
  | refl _ => exact h0
  | step hStep _ ih => exact ih (parStep_preserves_allSeqsWF hStep h0)

/-- **Theorem 2b (Sequential Exclusion)**:
    Along every reachable parallel trace, every active `.runningSeq inner` subtree
    satisfies `SeqWF inner` and therefore has at most 1 running leaf (`runningLeaves inner ≤ 1`). -/
theorem seq_exclusion {cap : Nat} {plan : PurePlan} {tr : List Event} {rt : RT}
    (hTrace : Trace cap (RT.ofPlan plan) tr rt) :
    AllSeqsWF rt :=
  trace_preserves_allSeqsWF hTrace (allSeqsWF_ofPlan plan)

theorem seq_exclusion_at_root {cap : Nat} {plan : PurePlan} {tr : List Event} {inner : RT}
    (hTrace : Trace cap (RT.ofPlan plan) tr (.runningSeq inner)) :
    runningLeaves inner ≤ 1 := by
  have hWF := seq_exclusion hTrace
  simp only [AllSeqsWF] at hWF
  exact seqWF_runningLeaves_le_one inner hWF

/-! ## Theorem 3: Resource Bracket Safety (`withResource` / `beforeAll`) -/

/-- No child leaf can execute while a resource is still pending: the only step
    from `.resPending` is `acquireOk` or `acquireFail`. -/
theorem resPending_only_acquire {free : Nat} {desc : String} {path tags : Array String}
    {acq : Except String Unit} {child : PurePlan} {rt' : RT} {ev : Event}
    (h : ParStep free (.resPending desc path tags acq child) ev rt') :
    (ev = .acquireOk desc ∧ acq = .ok () ∧ rt' = .resActive desc (RT.ofPlan child)) ∨
    (∃ err, ev = .acquireFail desc ∧ acq = .error err ∧ rt' = .done (resourceFailReport desc path tags err)) := by
  cases h with
  | resAcqOk => exact Or.inl ⟨rfl, rfl, rfl⟩
  | resAcqFail => exact Or.inr ⟨_, rfl, rfl, rfl⟩

/-- `release desc` on `.resActive desc child` can only fire once `child` is completely `.done`
    (with 0 active workers and 0 running leaves). -/
theorem resActive_release_requires_done {free : Nat} {desc : String} {child rt' : RT}
    (h : ParStep free (.resActive desc child) (.release desc) rt')
    (hNoNestedSame : ∀ child', ¬ ParStep free child (.release desc) child') :
    ∃ r, child = .done r ∧ rt' = .done r ∧ activeWorkers child = 0 ∧ runningLeaves child = 0 := by
  cases h with
  | resStep hSub => exact absurd hSub (hNoNestedSame _)
  | resRelease => exact ⟨_, rfl, rfl, by simp [activeWorkers], by simp [runningLeaves]⟩

mutual

theorem seqStep_resource_conservation {rt rt' : RT} {ev : Event} :
    SeqStep rt ev rt' →
    activeResources rt' + (if ev.isRelease then 1 else 0) =
    activeResources rt + (if ev.isAcquireOk then 1 else 0)
  | .startLeaf .. => by simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | .finishLeaf .. => by simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | .groupStep hG => by
    simp only [activeResources]
    exact seqGroupStep_resource_conservation hG
  | .groupCollapse hDone => by
    simp [activeResources, allDoneReports_activeResources hDone, Event.isRelease, Event.isAcquireOk]
  | .startSeq plan => by
    simp [activeResources, activeResources_ofPlan, Event.isRelease, Event.isAcquireOk]
  | .stepSeq hSub => by
    simp only [activeResources]
    exact seqStep_resource_conservation hSub
  | .finishSeq _ => by simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | .resAcqOk _ _ _ child => by
    simp [activeResources, activeResources_ofPlan, Event.isRelease, Event.isAcquireOk]
  | .resAcqFail .. => by simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | .resStep hSub => by
    have ih := seqStep_resource_conservation hSub
    simp only [activeResources]
    omega
  | .resRelease .. => by simp [activeResources, Event.isRelease, Event.isAcquireOk]

theorem seqGroupStep_resource_conservation {cs cs' : List RT} {ev : Event} :
    SeqGroupStep cs ev cs' →
    activeResourcesChildren cs' + (if ev.isRelease then 1 else 0) =
    activeResourcesChildren cs + (if ev.isAcquireOk then 1 else 0)
  | .head hSub => by
    have ih := seqStep_resource_conservation hSub
    simp only [activeResourcesChildren]
    omega
  | .skipDone hSub => by
    have ih := seqGroupStep_resource_conservation hSub
    simp only [activeResourcesChildren, activeResources]
    omega

end

theorem parStep_resource_conservation {free : Nat} {rt rt' : RT} {ev : Event}
    (h : ParStep free rt ev rt') :
    activeResources rt' + (if ev.isRelease then 1 else 0) =
    activeResources rt + (if ev.isAcquireOk then 1 else 0) := by
  induction h with
  | startLeaf => simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | finishLeaf => simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | groupStep _ ih =>
    simp only [activeResources, activeResourcesChildren_append, activeResourcesChildren]
    omega
  | groupCollapse hDone =>
    simp [activeResources, allDoneReports_activeResources hDone, Event.isRelease, Event.isAcquireOk]
  | startSeq plan _ =>
    simp [activeResources, activeResources_ofPlan, Event.isRelease, Event.isAcquireOk]
  | stepSeq hSub =>
    simp only [activeResources]
    exact seqStep_resource_conservation hSub
  | finishSeq => simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | resAcqOk _ _ _ child =>
    simp [activeResources, activeResources_ofPlan, Event.isRelease, Event.isAcquireOk]
  | resAcqFail => simp [activeResources, Event.isRelease, Event.isAcquireOk]
  | resStep _ ih => simp only [activeResources]; omega
  | resRelease => simp [activeResources, Event.isRelease, Event.isAcquireOk]

private theorem trace_resource_conservation {cap : Nat} {rt₀ rt : RT} {tr : List Event}
    (hTrace : Trace cap rt₀ tr rt) :
    activeResources rt₀ + countAcquireOk tr = countRelease tr + activeResources rt := by
  induction hTrace with
  | refl _ => simp [countAcquireOk, countRelease]
  | step hStep _ ih =>
    rename_i a b c ev rest _
    have hCons := parStep_resource_conservation hStep
    simp only [countAcquireOk, countRelease, List.filter_cons] at ih ⊢
    cases hA : ev.isAcquireOk <;> cases hR : ev.isRelease <;> simp_all <;> omega

/-- **Theorem 3a (Resource Bracket Accounting Invariant)**:
    At every prefix of every reachable trace, `countAcquireOk tr = countRelease tr + activeResources rt`
    (so `countRelease tr ≤ countAcquireOk tr` at all times — never an unmatched release). -/
theorem resource_bracket_invariant {cap : Nat} {plan : PurePlan} {tr : List Event} {rt : RT}
    (hTrace : Trace cap (RT.ofPlan plan) tr rt) :
    countAcquireOk tr = countRelease tr + activeResources rt := by
  have h := trace_resource_conservation hTrace
  rw [activeResources_ofPlan, Nat.zero_add] at h
  exact h

/-- **Theorem 3b (Exact-Once Release on Termination)**:
    In every terminal state (even when child tests fail), every acquired resource
    has been released exactly once (`countAcquireOk tr = countRelease tr`). -/
theorem resource_released_exactly_once_on_done {cap : Nat} {plan : PurePlan}
    {tr : List Event} {r : ReportTree}
    (hTrace : Trace cap (RT.ofPlan plan) tr (.done r)) :
    countAcquireOk tr = countRelease tr := by
  have h := resource_bracket_invariant hTrace
  simp only [activeResources, Nat.add_zero] at h
  exact h

/-! ## Theorem 4: Deadlock Freedom & Termination -/

mutual

theorem seqStep_progress : ∀ (rt : RT), ¬ rt.isDone → ∃ ev rt', SeqStep rt ev rt'
  | .queuedLeaf name path tags res, _ =>
    ⟨.startLeaf path, .runningLeaf name path tags res, .startLeaf ..⟩
  | .runningLeaf name path tags res, _ =>
    ⟨.finishLeaf path, _, .finishLeaf ..⟩
  | .done _, h => absurd trivial h
  | .group name cs, _ => by
    match hDone : allDoneReports cs with
    | some rs =>
      exact ⟨.collapseGroup name, .done (.group name rs.toArray), .groupCollapse hDone⟩
    | none =>
      have ⟨ev, cs', hG⟩ := seqGroupStep_progress cs hDone
      exact ⟨ev, .group name cs', .groupStep hG⟩
  | .queuedSeq plan, _ =>
    ⟨.startSeq, .runningSeq (RT.ofPlan plan), .startSeq plan⟩
  | .runningSeq inner, _ => by
    by_cases hDone : inner.isDone
    · obtain ⟨r, rfl⟩ := isDone_iff.mp hDone
      exact ⟨.finishSeq, .done r, .finishSeq r⟩
    · have ⟨ev, inner', hSub⟩ := seqStep_progress inner hDone
      exact ⟨ev, .runningSeq inner', .stepSeq hSub⟩
  | .resPending desc path tags acq child, _ => by
    cases acq with
    | ok u =>
      cases u
      exact ⟨.acquireOk desc, .resActive desc (RT.ofPlan child), .resAcqOk ..⟩
    | error err =>
      exact ⟨.acquireFail desc, .done (resourceFailReport desc path tags err), .resAcqFail ..⟩
  | .resActive desc child, _ => by
    by_cases hDone : child.isDone
    · obtain ⟨r, rfl⟩ := isDone_iff.mp hDone
      exact ⟨.release desc, .done r, .resRelease desc r⟩
    · have ⟨ev, child', hSub⟩ := seqStep_progress child hDone
      exact ⟨ev, .resActive desc child', .resStep hSub⟩
termination_by rt => sizeOf rt
decreasing_by all_goals (simp_wf; try omega)

theorem seqGroupStep_progress : ∀ (cs : List RT), allDoneReports cs = none →
    ∃ ev cs', SeqGroupStep cs ev cs'
  | [], h => by simp [allDoneReports] at h
  | c :: rest, h => by
    by_cases hDone : c.isDone
    · obtain ⟨r, rfl⟩ := isDone_iff.mp hDone
      have hRest : allDoneReports rest = none := by
        cases hR : allDoneReports rest with
        | none => rfl
        | some rs => simp [allDoneReports, hR] at h
      have ⟨ev, rest', hSub⟩ := seqGroupStep_progress rest hRest
      exact ⟨ev, .done r :: rest', .skipDone hSub⟩
    · have ⟨ev, c', hSub⟩ := seqStep_progress c hDone
      exact ⟨ev, c' :: rest, .head hSub⟩
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; try omega)

end

private theorem find_active_child : ∀ (cs : List RT), activeWorkersChildren cs > 0 →
    ∃ pre c post, cs = pre ++ c :: post ∧ activeWorkers c > 0
  | [], h => by simp [activeWorkersChildren] at h
  | c :: rest, h => by
    simp only [activeWorkersChildren] at h
    by_cases hc : activeWorkers c > 0
    · exact ⟨[], c, rest, rfl, hc⟩
    · have hRest : activeWorkersChildren rest > 0 := by omega
      have ⟨pre, c', post, hEq, hPos⟩ := find_active_child rest hRest
      exact ⟨c :: pre, c', post, by simp [hEq], hPos⟩

private theorem find_undone_child : ∀ (cs : List RT), allDoneReports cs = none →
    ∃ pre c post, cs = pre ++ c :: post ∧ ¬ c.isDone
  | [], h => by simp [allDoneReports] at h
  | c :: rest, h => by
    cases c with
    | done r =>
      have hRest : allDoneReports rest = none := by
        cases hR : allDoneReports rest with
        | none => rfl
        | some rs => simp [allDoneReports, hR] at h
      have ⟨pre, c', post, hEq, hNotDone⟩ := find_undone_child rest hRest
      exact ⟨.done r :: pre, c', post, by simp [hEq], hNotDone⟩
    | queuedLeaf _ _ _ _ | runningLeaf _ _ _ _ | group _ _ | queuedSeq _ | runningSeq _
    | resPending _ _ _ _ _ | resActive _ _ =>
      exact ⟨[], _, rest, rfl, by simp [RT.isDone]⟩

/-- Any subtree holding ≥ 1 active worker slot can always make progress with `free = 0`
    (no additional pool slots required). This is the key lemma verifying why running
    `withResource` coordinators outside the pool prevents pool-starvation deadlocks. -/
theorem parStep_progress_of_active (free : Nat) :
    ∀ (rt : RT), activeWorkers rt > 0 → ∃ ev rt', ParStep free rt ev rt'
  | .queuedLeaf _ _ _ _, h => by simp [activeWorkers] at h
  | .runningLeaf name path tags res, _ =>
    ⟨.finishLeaf path, _, .finishLeaf ..⟩
  | .done _, h => by simp [activeWorkers] at h
  | .group name cs, h => by
    simp only [activeWorkers] at h
    have ⟨pre, c, post, hEq, hPos⟩ := find_active_child cs h
    have ⟨ev, c', hSub⟩ := parStep_progress_of_active free c hPos
    rw [hEq]
    exact ⟨ev, .group name (pre ++ c' :: post), .groupStep hSub⟩
  | .queuedSeq _, h => by simp [activeWorkers] at h
  | .runningSeq inner, _ => by
    by_cases hDone : inner.isDone
    · obtain ⟨r, rfl⟩ := isDone_iff.mp hDone
      exact ⟨.finishSeq, .done r, .finishSeq r⟩
    · have ⟨ev, inner', hSub⟩ := seqStep_progress inner hDone
      exact ⟨ev, .runningSeq inner', .stepSeq hSub⟩
  | .resPending _ _ _ _ _, h => by simp [activeWorkers] at h
  | .resActive desc child, h => by
    simp only [activeWorkers] at h
    have ⟨ev, child', hSub⟩ := parStep_progress_of_active free child h
    exact ⟨ev, .resActive desc child', .resStep hSub⟩
termination_by rt => sizeOf rt
decreasing_by
  all_goals
    simp_wf
    first
      | omega
      | (have := list_mem_sizeOf_lt c cs (by rw [hEq]; simp); omega)

/-- When `free ≥ 1`, any non-terminal runtime tree can step. -/
theorem parStep_progress_of_free {free : Nat} (hFree : free ≥ 1) :
    ∀ (rt : RT), ¬ rt.isDone → ∃ ev rt', ParStep free rt ev rt'
  | .queuedLeaf name path tags res, _ =>
    ⟨.startLeaf path, .runningLeaf name path tags res, .startLeaf _ _ _ _ hFree⟩
  | .runningLeaf name path tags res, _ =>
    ⟨.finishLeaf path, _, .finishLeaf ..⟩
  | .done _, h => absurd trivial h
  | .group name cs, _ => by
    match hDone : allDoneReports cs with
    | some rs =>
      exact ⟨.collapseGroup name, .done (.group name rs.toArray), .groupCollapse hDone⟩
    | none =>
      have ⟨pre, c, post, hEq, hNotDone⟩ := find_undone_child cs hDone
      have ⟨ev, c', hSub⟩ := parStep_progress_of_free hFree c hNotDone
      rw [hEq]
      exact ⟨ev, .group name (pre ++ c' :: post), .groupStep hSub⟩
  | .queuedSeq plan, _ =>
    ⟨.startSeq, .runningSeq (RT.ofPlan plan), .startSeq plan hFree⟩
  | .runningSeq inner, _ => by
    by_cases hDone : inner.isDone
    · obtain ⟨r, rfl⟩ := isDone_iff.mp hDone
      exact ⟨.finishSeq, .done r, .finishSeq r⟩
    · have ⟨ev, inner', hSub⟩ := seqStep_progress inner hDone
      exact ⟨ev, .runningSeq inner', .stepSeq hSub⟩
  | .resPending desc path tags acq child, _ => by
    cases acq with
    | ok u =>
      cases u
      exact ⟨.acquireOk desc, .resActive desc (RT.ofPlan child), .resAcqOk ..⟩
    | error err =>
      exact ⟨.acquireFail desc, .done (resourceFailReport desc path tags err), .resAcqFail ..⟩
  | .resActive desc child, _ => by
    by_cases hDone : child.isDone
    · obtain ⟨r, rfl⟩ := isDone_iff.mp hDone
      exact ⟨.release desc, .done r, .resRelease desc r⟩
    · have ⟨ev, child', hSub⟩ := parStep_progress_of_free hFree child hDone
      exact ⟨ev, .resActive desc child', .resStep hSub⟩
termination_by rt => sizeOf rt
decreasing_by
  all_goals
    simp_wf
    first
      | omega
      | (have := list_mem_sizeOf_lt c cs (by rw [hEq]; simp); omega)

/-- **Theorem 4a (Deadlock Freedom)**:
    For any worker capacity `cap ≥ 1` and any reachable state `rt` (including
    arbitrarily nested `withResource` and `sequential` blocks), either `rt` is
    already `.done` or at least one `MachineStep` is enabled. -/
theorem progress_deadlock_free {cap : Nat} (hCap : cap ≥ 1)
    {plan : PurePlan} {tr : List Event} {rt : RT}
    (hTrace : Trace cap (RT.ofPlan plan) tr rt) (hNotDone : ¬ rt.isDone) :
    ∃ ev rt', MachineStep cap rt ev rt' := by
  have hBound := bounded_concurrency hTrace
  by_cases hActive : activeWorkers rt > 0
  · exact parStep_progress_of_active (cap - activeWorkers rt) rt hActive
  · have hFree : cap - activeWorkers rt ≥ 1 := by omega
    exact parStep_progress_of_free hFree rt hNotDone

mutual

theorem seqStep_remainingSteps {rt rt' : RT} {ev : Event} :
    SeqStep rt ev rt' → remainingSteps rt' + 1 = remainingSteps rt
  | .startLeaf .. => by simp [remainingSteps]
  | .finishLeaf .. => by simp [remainingSteps]
  | .groupStep hG => by
    have ih := seqGroupStep_remainingSteps hG
    simp only [remainingSteps]
    omega
  | .groupCollapse hDone => by simp [remainingSteps, allDoneReports_remainingSteps hDone]
  | .startSeq plan => by simp [remainingSteps, remainingSteps_ofPlan]; omega
  | .stepSeq hSub => by
    have ih := seqStep_remainingSteps hSub
    simp only [remainingSteps]
    omega
  | .finishSeq _ => by simp [remainingSteps]
  | .resAcqOk _ _ _ child => by simp [remainingSteps, remainingSteps_ofPlan]; omega
  | .resAcqFail .. => by simp [remainingSteps]
  | .resStep hSub => by
    have ih := seqStep_remainingSteps hSub
    simp only [remainingSteps]
    omega
  | .resRelease .. => by simp [remainingSteps]

theorem seqGroupStep_remainingSteps {cs cs' : List RT} {ev : Event} :
    SeqGroupStep cs ev cs' → remainingStepsChildren cs' + 1 = remainingStepsChildren cs
  | .head hSub => by
    have ih := seqStep_remainingSteps hSub
    simp only [remainingStepsChildren]
    omega
  | .skipDone hSub => by
    have ih := seqGroupStep_remainingSteps hSub
    simp only [remainingStepsChildren, remainingSteps]
    omega

end

theorem parStep_remainingSteps {free : Nat} {rt rt' : RT} {ev : Event}
    (h : ParStep free rt ev rt') :
    remainingSteps rt' + 1 = remainingSteps rt := by
  induction h with
  | startLeaf => simp [remainingSteps]
  | finishLeaf => simp [remainingSteps]
  | groupStep _ ih =>
    simp only [remainingSteps, remainingStepsChildren_append, remainingStepsChildren]
    omega
  | groupCollapse hDone => simp [remainingSteps, allDoneReports_remainingSteps hDone]
  | startSeq plan _ => simp [remainingSteps, remainingSteps_ofPlan]; omega
  | stepSeq hSub =>
    have ih := seqStep_remainingSteps hSub
    simp only [remainingSteps]
    omega
  | finishSeq => simp [remainingSteps]
  | resAcqOk _ _ _ child => simp [remainingSteps, remainingSteps_ofPlan]; omega
  | resAcqFail => simp [remainingSteps]
  | resStep _ ih => simp only [remainingSteps]; omega
  | resRelease => simp [remainingSteps]

private theorem trace_remainingSteps {cap : Nat} {rt₀ rt : RT} {tr : List Event}
    (hTrace : Trace cap rt₀ tr rt) :
    tr.length + remainingSteps rt = remainingSteps rt₀ := by
  induction hTrace with
  | refl _ => simp
  | step hStep _ ih =>
    have hDec := parStep_remainingSteps hStep
    simp only [List.length_cons]
    omega

/-- **Theorem 4b (Strong Normalization / Termination Bound)**:
    Every execution trace from `RT.ofPlan plan` strictly consumes `planSteps plan`
    and therefore must terminate in at most `planSteps plan` steps. -/
theorem termination_step_bound {cap : Nat} {plan : PurePlan} {tr : List Event} {rt : RT}
    (hTrace : Trace cap (RT.ofPlan plan) tr rt) :
    tr.length + remainingSteps rt = planSteps plan := by
  rw [trace_remainingSteps hTrace, remainingSteps_ofPlan]

/-! ## Theorem 5: Sequential–Parallel Equivalence (Determinism / Confluence) -/

mutual

theorem seqStep_preserves_denote {rt rt' : RT} {ev : Event} :
    SeqStep rt ev rt' → denote rt' = denote rt
  | .startLeaf .. => by simp [denote]
  | .finishLeaf .. => by simp [denote]
  | .groupStep hG => by
    simp only [denote, seqGroupStep_preserves_denote hG]
  | .groupCollapse hDone => by simp [denote, allDoneReports_denote hDone]
  | .startSeq plan => by simp [denote, denote_ofPlan]
  | .stepSeq hSub => by simp only [denote, seqStep_preserves_denote hSub]
  | .finishSeq _ => by simp [denote]
  | .resAcqOk _ _ _ child => by simp [denote, denote_ofPlan]
  | .resAcqFail .. => by simp [denote]
  | .resStep hSub => by simp only [denote, seqStep_preserves_denote hSub]
  | .resRelease .. => by simp [denote]

theorem seqGroupStep_preserves_denote {cs cs' : List RT} {ev : Event} :
    SeqGroupStep cs ev cs' → denoteChildren cs' = denoteChildren cs
  | .head hSub => by simp only [denoteChildren, seqStep_preserves_denote hSub]
  | .skipDone hSub => by simp only [denoteChildren, seqGroupStep_preserves_denote hSub]

end

theorem parStep_preserves_denote {free : Nat} {rt rt' : RT} {ev : Event}
    (h : ParStep free rt ev rt') :
    denote rt' = denote rt := by
  induction h with
  | startLeaf => simp [denote]
  | finishLeaf => simp [denote]
  | groupStep _ ih =>
    simp only [denote, denoteChildren_append, denoteChildren, ih]
  | groupCollapse hDone => simp [denote, allDoneReports_denote hDone]
  | startSeq plan _ => simp [denote, denote_ofPlan]
  | stepSeq hSub =>
    simp only [denote]
    exact seqStep_preserves_denote hSub
  | finishSeq => simp [denote]
  | resAcqOk _ _ _ child => simp [denote, denote_ofPlan]
  | resAcqFail => simp [denote]
  | resStep _ ih => simp only [denote, ih]
  | resRelease => simp [denote]

theorem trace_preserves_denote {cap : Nat} {rt rt' : RT} {tr : List Event}
    (hTrace : Trace cap rt tr rt') :
    denote rt' = denote rt := by
  induction hTrace with
  | refl _ => rfl
  | step hStep _ ih => exact ih.trans (parStep_preserves_denote hStep)

/-- **Theorem 5 (Sequential–Parallel Equivalence / Confluence)**:
    For ANY thread limit `cap ≥ 1` and ANY interleaving `tr` terminating at `.done r`,
    the resulting `ReportTree` and `RunSummary` are identical to canonical sequential
    evaluation `evalSeq plan`. -/
theorem parallel_eq_sequential {cap : Nat} {plan : PurePlan} {tr : List Event} {r : ReportTree}
    (hTrace : Trace cap (RT.ofPlan plan) tr (.done r))
    (d : Nat := 0) (sd : UInt64 := 0) (th : Nat := 1) :
    r = evalSeq plan ∧ r.summarize d sd th = (evalSeq plan).summarize d sd th := by
  have hDen := trace_preserves_denote hTrace
  simp only [denote, denote_ofPlan] at hDen
  exact ⟨hDen, congrArg (·.summarize d sd th) hDen⟩

end
end LSpec.Proofs.Concurrency
