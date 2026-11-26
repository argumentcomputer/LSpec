module
public import LSpec.Runner

/-!
# Formal Correctness of `ReportTree`, `RunSummary`, `compilePlan`, and Worker Bounds

Direct kernel-checked theorems on the executable functions in `LSpec.Runner`:
- Exact report accounting: `passed + failed + skipped = leafCount = leaves.size`
- Exact failure accounting: `summary.failed = report.failures.size` and
  `summary.allPassed = true ↔ report.failures.isEmpty`
- Permutation invariance of `summarizeChildren` (parallel completion order cannot
  alter aggregate counts)
- `compilePlan` preserves the exact `(path, tags, mode)` sequence of `listTests`
  and assigns deterministic seeds `deriveTestSeed masterSeed path` to every leaf
- `ExecPlan.skipAll` produces zero passes/failures and skips every leaf
- `computeWorkerCount` bounds: `1 ≤ workers ≤ max 1 threads` and `workers ≤ max 1 leaves`
-/

namespace LSpec.Proofs
public section

open LSpec

private theorem array_toList_sizeOf_lt [SizeOf α] (a : Array α) :
    sizeOf a.toList < sizeOf a := by
  cases a; simp

/-! ## `ReportTree` Accounting Invariants -/

mutual

theorem leafCount_eq_leavesList_length (r : ReportTree) :
    r.leafCount = r.leavesList.length := by
  cases r with
  | leaf rep => simp [ReportTree.leafCount, ReportTree.leavesList]
  | group _ children =>
    simp only [ReportTree.leafCount, ReportTree.leavesList]
    exact leafCountChildren_eq_leavesChildren_length children.toList
termination_by sizeOf r
decreasing_by all_goals (simp_wf; first | done | (have := array_toList_sizeOf_lt children; omega))

theorem leafCountChildren_eq_leavesChildren_length (cs : List ReportTree) :
    ReportTree.leafCountChildren cs = (ReportTree.leavesChildren cs).length := by
  cases cs with
  | nil => simp [ReportTree.leafCountChildren, ReportTree.leavesChildren]
  | cons c rest =>
    simp only [ReportTree.leafCountChildren, ReportTree.leavesChildren, List.length_append]
    rw [leafCount_eq_leavesList_length c, leafCountChildren_eq_leavesChildren_length rest]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

theorem leafCount_eq_leaves_size (r : ReportTree) :
    r.leafCount = r.leaves.size := by
  simp [ReportTree.leaves, leafCount_eq_leavesList_length]

mutual

theorem failuresList_eq_filter_leavesList (r : ReportTree) :
    r.failuresList = r.leavesList.filter (·.result.isFailed) := by
  cases r with
  | leaf rep =>
    simp only [ReportTree.failuresList, ReportTree.leavesList, List.filter]
    cases rep.result.isFailed <;> rfl
  | group _ children =>
    simp only [ReportTree.failuresList, ReportTree.leavesList]
    exact failuresChildren_eq_filter_leavesChildren children.toList
termination_by sizeOf r
decreasing_by all_goals (simp_wf; first | done | (have := array_toList_sizeOf_lt children; omega))

theorem failuresChildren_eq_filter_leavesChildren (cs : List ReportTree) :
    ReportTree.failuresChildren cs = (ReportTree.leavesChildren cs).filter (·.result.isFailed) := by
  cases cs with
  | nil => simp [ReportTree.failuresChildren, ReportTree.leavesChildren]
  | cons c rest =>
    simp only [ReportTree.failuresChildren, ReportTree.leavesChildren, List.filter_append]
    rw [failuresList_eq_filter_leavesList c, failuresChildren_eq_filter_leavesChildren rest]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

theorem failures_eq_filter_leaves (r : ReportTree) :
    r.failures = r.leaves.filter (·.result.isFailed) := by
  unfold ReportTree.failures ReportTree.leaves
  apply Array.ext'
  simp [failuresList_eq_filter_leavesList]

mutual

theorem summarizeGo_total (r : ReportTree) :
    let (p, f, s) := r.summarizeGo
    p + f + s = r.leafCount := by
  cases r with
  | leaf rep =>
    simp only [ReportTree.summarizeGo, ReportTree.leafCount]
    cases rep.result.outcome <;> rfl
  | group _ children =>
    simp only [ReportTree.summarizeGo, ReportTree.leafCount]
    exact summarizeChildren_total children.toList
termination_by sizeOf r
decreasing_by all_goals (simp_wf; first | done | (have := array_toList_sizeOf_lt children; omega))

theorem summarizeChildren_total (cs : List ReportTree) :
    let (p, f, s) := ReportTree.summarizeChildren cs
    p + f + s = ReportTree.leafCountChildren cs := by
  cases cs with
  | nil => simp [ReportTree.summarizeChildren, ReportTree.leafCountChildren]
  | cons c rest =>
    have ih1 := summarizeGo_total c
    have ih2 := summarizeChildren_total rest
    simp only [ReportTree.summarizeChildren, ReportTree.leafCountChildren]
    omega
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

/-- Every leaf in a `ReportTree` is accounted for in `passed + failed + skipped`. -/
theorem summarize_total_eq_leafCount (r : ReportTree) (d : Nat) (sd : UInt64) (th : Nat) :
    (r.summarize d sd th).total = r.leafCount := by
  simp only [ReportTree.summarize, RunSummary.total]
  exact summarizeGo_total r

mutual

theorem summarizeGo_failed (r : ReportTree) :
    r.summarizeGo.2.1 = r.failuresList.length := by
  cases r with
  | leaf rep =>
    rcases rep with ⟨_, _, _, ⟨out, _, _⟩, _, _⟩
    cases out <;> simp [ReportTree.summarizeGo, ReportTree.failuresList, TestResult.isFailed]
  | group _ children =>
    simp only [ReportTree.summarizeGo, ReportTree.failuresList]
    exact summarizeChildren_failed children.toList
termination_by sizeOf r
decreasing_by all_goals (simp_wf; first | done | (have := array_toList_sizeOf_lt children; omega))

theorem summarizeChildren_failed (cs : List ReportTree) :
    (ReportTree.summarizeChildren cs).2.1 = (ReportTree.failuresChildren cs).length := by
  cases cs with
  | nil => simp [ReportTree.summarizeChildren, ReportTree.failuresChildren]
  | cons c rest =>
    have ih1 := summarizeGo_failed c
    have ih2 := summarizeChildren_failed rest
    simp only [ReportTree.summarizeChildren, ReportTree.failuresChildren, List.length_append]
    rw [ih1, ih2]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

/-- The summary's `failed` count equals `report.failures.size`. -/
theorem summarize_failed_eq_failures_size (r : ReportTree) (d : Nat) (sd : UInt64) (th : Nat) :
    (r.summarize d sd th).failed = r.failures.size := by
  simp only [ReportTree.summarize, ReportTree.failures, List.size_toArray]
  exact summarizeGo_failed r

/-- `allPassed` holds iff `report.failures` is empty. -/
theorem summarize_allPassed_iff_failures_empty (r : ReportTree) (d : Nat) (sd : UInt64) (th : Nat) :
    (r.summarize d sd th).allPassed = true ↔ r.failures.isEmpty = true := by
  simp only [RunSummary.allPassed, beq_iff_eq, summarize_failed_eq_failures_size,
    Array.isEmpty_iff_size_eq_zero]

/-- `allPassed` holds iff no leaf in `report` failed. -/
theorem summarize_allPassed_iff_forall (r : ReportTree) (d : Nat) (sd : UInt64) (th : Nat) :
    (r.summarize d sd th).allPassed = true ↔
      ∀ rep ∈ r.leaves.toList, rep.result.isFailed = false := by
  rw [summarize_allPassed_iff_failures_empty]
  simp only [ReportTree.failures, ReportTree.leaves, Array.isEmpty_iff_size_eq_zero,
    List.size_toArray, List.toList_toArray, List.length_eq_zero_iff,
    failuresList_eq_filter_leavesList, List.filter_eq_nil_iff, Bool.not_eq_true]

/-! ## Order-Independence (Permutation Invariance) of Summary Counts -/

theorem summarizeChildren_append (xs ys : List ReportTree) :
    ReportTree.summarizeChildren (xs ++ ys) =
      let (p1, f1, s1) := ReportTree.summarizeChildren xs
      let (p2, f2, s2) := ReportTree.summarizeChildren ys
      (p1 + p2, f1 + f2, s1 + s2) := by
  induction xs with
  | nil => simp [ReportTree.summarizeChildren]
  | cons x rest ih =>
    simp only [List.cons_append, ReportTree.summarizeChildren, ih]
    simp only [Prod.mk.injEq]
    omega

theorem summarizeChildren_perm {xs ys : List ReportTree} (h : List.Perm xs ys) :
    ReportTree.summarizeChildren xs = ReportTree.summarizeChildren ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [ReportTree.summarizeChildren, ih]
  | swap x y l =>
    simp only [ReportTree.summarizeChildren, Prod.mk.injEq]
    omega
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

/-! ## `compilePlan` Consistency with `listTests` and Seed Determinism -/

mutual

theorem toListedList_compilePlanGo (masterSeed : UInt64) (opts : TestOptions)
    (path tags : Array String) (mode : ExecutionMode)
    (wrap : (TestContext → IO TestResult) → TestContext → IO TestResult)
    (t : TestTree) :
    (compilePlanGo masterSeed opts path tags mode wrap t).toListedList mode =
      listTestsGo path tags mode t := by
  cases t with
  | leaf name leafTags exec =>
    simp [compilePlanGo, ExecPlan.toListedList, listTestsGo]
  | group name children =>
    simp only [compilePlanGo, ExecPlan.toListedList, listTestsGo]
    exact toListedChildren_compilePlanChildren masterSeed opts
      (if name.isEmpty then path else path.push name) tags mode wrap children.toList
  | withMode m child =>
    have ih := toListedList_compilePlanGo masterSeed opts path tags
      (ExecutionMode.combine mode m) wrap child
    cases mode <;> cases m <;>
      · unfold compilePlanGo
        simp only [listTestsGo, ExecutionMode.combine, ExecPlan.toListedList] at ih ⊢
        exact ih
  | withTags more child =>
    simp only [compilePlanGo, listTestsGo]
    exact toListedList_compilePlanGo masterSeed opts path (tags ++ more) mode wrap child
  | withOptions f child =>
    simp only [compilePlanGo, listTestsGo]
    exact toListedList_compilePlanGo masterSeed (f opts) path tags mode wrap child
  | aroundEach w child =>
    simp only [compilePlanGo, listTestsGo]
    exact toListedList_compilePlanGo masterSeed opts path tags mode (fun inner => wrap (w inner)) child
  | withResource desc acq child =>
    simp only [compilePlanGo, ExecPlan.toListedList, listTestsGo]
    exact toListedList_compilePlanGo masterSeed opts path tags mode wrap child
termination_by sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

theorem toListedChildren_compilePlanChildren (masterSeed : UInt64) (opts : TestOptions)
    (path tags : Array String) (mode : ExecutionMode)
    (wrap : (TestContext → IO TestResult) → TestContext → IO TestResult)
    (cs : List TestTree) :
    ExecPlan.toListedChildren mode (compilePlanChildren masterSeed opts path tags mode wrap cs) =
      listTestsChildren path tags mode cs := by
  cases cs with
  | nil => simp [compilePlanChildren, ExecPlan.toListedChildren, listTestsChildren]
  | cons c rest =>
    simp only [compilePlanChildren, ExecPlan.toListedChildren, listTestsChildren]
    rw [toListedList_compilePlanGo, toListedChildren_compilePlanChildren]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

/-- **Unified Plan Equivalence**: compiling a `TestTree` with `compilePlan` produces
    the exact same sequence of `(path, tags, mode)` leaves as `listTests`. -/
theorem toListed_compilePlan (masterSeed : UInt64) (opts : TestOptions)
    (defaultMode : ExecutionMode) (tree : TestTree) :
    (compilePlan masterSeed opts defaultMode tree).toListed defaultMode =
      listTests tree defaultMode := by
  unfold compilePlan ExecPlan.toListed listTests
  cases defaultMode with
  | parallel =>
    simp [toListedList_compilePlanGo]
  | sequential =>
    simp [ExecPlan.toListedList, toListedList_compilePlanGo]

mutual

/-- Predicate asserting every leaf in an `ExecPlan` carries its deterministic seed
    `deriveTestSeed masterSeed path`. -/
def PlanSeedsDeterministic (masterSeed : UInt64) : ExecPlan → Prop
  | .leaf _ path _ _ seed _ => seed = deriveTestSeed masterSeed path
  | .group _ children => PlanSeedsDeterministicChildren masterSeed children.toList
  | .seq child => PlanSeedsDeterministic masterSeed child
  | .resource _ _ _ _ child => PlanSeedsDeterministic masterSeed child
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

def PlanSeedsDeterministicChildren (masterSeed : UInt64) : List ExecPlan → Prop
  | [] => True
  | c :: cs => PlanSeedsDeterministic masterSeed c ∧ PlanSeedsDeterministicChildren masterSeed cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

mutual

theorem compilePlanGo_seeds_deterministic (masterSeed : UInt64) (opts : TestOptions)
    (path tags : Array String) (mode : ExecutionMode)
    (wrap : (TestContext → IO TestResult) → TestContext → IO TestResult)
    (t : TestTree) :
    PlanSeedsDeterministic masterSeed (compilePlanGo masterSeed opts path tags mode wrap t) := by
  cases t with
  | leaf name leafTags exec =>
    simp [compilePlanGo, PlanSeedsDeterministic]
  | group name children =>
    simp only [compilePlanGo, PlanSeedsDeterministic]
    exact compilePlanChildren_seeds_deterministic masterSeed opts
      (if name.isEmpty then path else path.push name) tags mode wrap children.toList
  | withMode m child =>
    have ih := compilePlanGo_seeds_deterministic masterSeed opts path tags
      (ExecutionMode.combine mode m) wrap child
    cases mode <;> cases m <;>
      · unfold compilePlanGo
        simp only [ExecutionMode.combine, PlanSeedsDeterministic] at ih ⊢
        exact ih
  | withTags more child =>
    simp only [compilePlanGo]
    exact compilePlanGo_seeds_deterministic masterSeed opts path (tags ++ more) mode wrap child
  | withOptions f child =>
    simp only [compilePlanGo]
    exact compilePlanGo_seeds_deterministic masterSeed (f opts) path tags mode wrap child
  | aroundEach w child =>
    simp only [compilePlanGo]
    exact compilePlanGo_seeds_deterministic masterSeed opts path tags mode (fun inner => wrap (w inner)) child
  | withResource desc acq child =>
    simp only [compilePlanGo, PlanSeedsDeterministic]
    exact compilePlanGo_seeds_deterministic masterSeed opts path tags mode wrap child
termination_by sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

theorem compilePlanChildren_seeds_deterministic (masterSeed : UInt64) (opts : TestOptions)
    (path tags : Array String) (mode : ExecutionMode)
    (wrap : (TestContext → IO TestResult) → TestContext → IO TestResult)
    (cs : List TestTree) :
    PlanSeedsDeterministicChildren masterSeed
      (compilePlanChildren masterSeed opts path tags mode wrap cs) := by
  cases cs with
  | nil => simp [compilePlanChildren, PlanSeedsDeterministicChildren]
  | cons c rest =>
    simp only [compilePlanChildren, PlanSeedsDeterministicChildren]
    exact ⟨compilePlanGo_seeds_deterministic masterSeed opts path tags mode wrap c,
           compilePlanChildren_seeds_deterministic masterSeed opts path tags mode wrap rest⟩
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

/-- Every leaf in a compiled plan receives `deriveTestSeed masterSeed path`,
    independent of thread count, scheduling order, or sibling tests. -/
theorem compilePlan_seeds_deterministic (masterSeed : UInt64) (opts : TestOptions)
    (defaultMode : ExecutionMode) (tree : TestTree) :
    PlanSeedsDeterministic masterSeed (compilePlan masterSeed opts defaultMode tree) := by
  unfold compilePlan
  cases defaultMode <;>
    simpa [PlanSeedsDeterministic] using
      compilePlanGo_seeds_deterministic masterSeed opts #[] #[] _ id tree

/-! ## `ExecPlan.skipAll` Accounting -/

mutual

theorem skipAll_summarizeGo (reason : String) (mode : ExecutionMode) (p : ExecPlan) :
    (p.skipAll reason).summarizeGo = (0, 0, (p.toListedList mode).length) := by
  cases p with
  | leaf name path tags opts seed exec =>
    simp [ExecPlan.skipAll, ReportTree.summarizeGo, TestResult.skip, ExecPlan.toListedList]
  | group name children =>
    simp only [ExecPlan.skipAll, ReportTree.summarizeGo, ExecPlan.toListedList]
    exact skipAllChildren_summarizeChildren reason mode children.toList
  | seq child =>
    simp only [ExecPlan.skipAll, ExecPlan.toListedList]
    exact skipAll_summarizeGo reason .sequential child
  | resource desc path tags acq child =>
    simp only [ExecPlan.skipAll, ExecPlan.toListedList]
    exact skipAll_summarizeGo reason mode child
termination_by sizeOf p
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

theorem skipAllChildren_summarizeChildren (reason : String) (mode : ExecutionMode)
    (cs : List ExecPlan) :
    ReportTree.summarizeChildren (ExecPlan.skipAllChildren reason cs) =
      (0, 0, (ExecPlan.toListedChildren mode cs).length) := by
  cases cs with
  | nil => simp [ExecPlan.skipAllChildren, ReportTree.summarizeChildren, ExecPlan.toListedChildren]
  | cons c rest =>
    simp only [ExecPlan.skipAllChildren, ReportTree.summarizeChildren,
      ExecPlan.toListedChildren, List.length_append]
    rw [skipAll_summarizeGo reason mode c, skipAllChildren_summarizeChildren reason mode rest]
    simp
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

theorem skipAll_summary (reason : String) (p : ExecPlan) (d : Nat) (sd : UInt64) (th : Nat)
    (mode : ExecutionMode := .parallel) :
    let s := (p.skipAll reason).summarize d sd th
    s.passed = 0 ∧ s.failed = 0 ∧ s.skipped = (p.toListed mode).size ∧ s.allPassed = true := by
  simp only [ReportTree.summarize, ExecPlan.toListed, List.size_toArray,
    skipAll_summarizeGo reason mode p, RunSummary.allPassed]
  simp

/-! ## Worker Pool Size Bounds -/

theorem computeWorkerCount_bounds (threads totalLeaves : Nat) :
    1 ≤ computeWorkerCount threads totalLeaves ∧
    computeWorkerCount threads totalLeaves ≤ max 1 threads ∧
    computeWorkerCount threads totalLeaves ≤ max 1 totalLeaves := by
  unfold computeWorkerCount
  omega

end
end LSpec.Proofs
