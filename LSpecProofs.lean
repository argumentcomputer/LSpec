module
public import LSpecProofs.Filter
public import LSpecProofs.Report
public import LSpecProofs.Concurrency
public import LSpecProofs.Axioms

/-!
# LSpec Formal Verification Suite (`LSpecProofs`)

Zero-`sorry`, zero-dependency formal proofs of `LSpec.Runner`:
- `LSpecProofs.Filter`: Direct proofs on executable `TestFilter`, `filterTree`, and `listTests`
  (soundness, completeness, idempotence, non-empty surviving `withResource` scopes).
- `LSpecProofs.Report`: Direct proofs on executable `ReportTree`, `RunSummary`, `compilePlan`,
  and `computeWorkerCount` (exact pass/fail/skip accounting, permutation invariance, unified
  plan equivalence with `listTests`, deterministic per-test seed assignment, worker bounds).
- `LSpecProofs.Concurrency`: Small-step operational semantics of the bounded-thread `WorkerPool`
  and `ExecPlan` scheduler (bounded concurrency `≤ cap`, sequential exclusion & left-to-right
  ordering, `withResource` acquire/release bracketing, deadlock freedom & termination, and
  sequential–parallel equivalence).
-/
