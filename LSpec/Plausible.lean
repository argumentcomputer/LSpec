module
public meta import LSpec.LSpec
public meta import Plausible

/-!
# Plausible integration for `LSpec`

This module provides an alternative property-based testing backend for `LSpec`
built on Lean's official [Plausible](https://github.com/leanprover-community/plausible)
library.

For backwards-compatibility reasons, the functions in this module live alongside LSpec's
SlimCheck-based `check`/`checkIO`functions, as opposed to replacing them.

The new entry points are:

- **`checkPlausible`/`checkPlausible'`**: compile-time property tests
- **`checkPlausibleIO`/`checkPlausibleIO'`**: runtime property tests with configurable seeds
-/

namespace LSpec
public meta section

/-- Variant of `Plausible.Testable.runSuiteAux`: tries `n` times to find a counter-example to `p`,
    and reports the no. of trials that succeeded before a counterexample was found. -/
def runPlausibleSuiteAux (p : Prop) [Plausible.Testable p] (cfg : Plausible.Configuration) :
    Plausible.TestResult p → Nat → Plausible.Gen (Plausible.TestResult p × Nat)
  | r, 0 => return (r, cfg.numInst)
  | r, n + 1 => do
    let size (_ : Nat) := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    let x ← Plausible.retry ((Plausible.Testable.runProp p cfg true).resize size) cfg.numRetries
    match x with
    | .success (PSum.inl ()) => runPlausibleSuiteAux p cfg x n
    | .gaveUp g => runPlausibleSuiteAux p cfg (Plausible.giveUp g r) n
    | _ => return (x, cfg.numInst - n - 1)

/-- Variant of `Plausible.Testable.runSuite` (tries to find a counter-example to `p`),
    but also tracks the no. of trials that succeeded before a counterexample was found. -/
def runPlausibleSuite (p : Prop) [Plausible.Testable p] (cfg : Plausible.Configuration := {}) :
    Plausible.Gen (Plausible.TestResult p × Nat) :=
  runPlausibleSuiteAux p cfg (.gaveUp 0) cfg.numInst

/-- Variant of `Plausible.Testable.checkIO` (run a test suite for `p` in `IO` using the global RNG
    in `stdGenRef`), but also tracks the no. of trials that succeeded. -/
def runPlausibleSuiteIO (p : Prop) [Plausible.Testable p] (cfg : Plausible.Configuration := {}) :
    IO (Plausible.TestResult p × Nat) :=
  match cfg.randomSeed with
  | none => Plausible.Gen.run (runPlausibleSuite p cfg) 0
  | some seed => Plausible.runRandWith seed (runPlausibleSuite p cfg)

/-- Bridges a `Plausible.Testable` instance into LSpec's `Testable` result type,
    running the suite at compile time with a fixed seed for deterministic results. -/
abbrev instTestableOfPlausible (p : Prop) (cfg : Plausible.Configuration) [Plausible.Testable p] :
    Testable p :=
  match ReaderT.run (Plausible.runRandWith 0 (runPlausibleSuite p cfg)) ⟨0⟩ with
  | .error _ => .isFailure 0 cfg.numInst "Generation failure"
  | .ok (.success (.inr h), _) => .isTrue h
  | .ok (.success (.inl _), _) => .isPassed cfg.numInst
  | .ok (.gaveUp n, _) => .isFailure 0 cfg.numInst s!"Gave up {n} times"
  | .ok (.failure h xs n, numSamples) =>
    .isFalse h (numSamples + 1) cfg.numInst $ Plausible.Testable.formatFailure "Found problems!" xs n

open Plausible.Decorations in
/--
Property-based test evaluated at compile time, using Plausible.

This is the Plausible-based counterpart to `check`, which uses SlimCheck.
Generates random test cases and checks the property during elaboration with a fixed random seed,
making results deterministic across compilations.

- `descr`: Description shown in test output (can be empty if propString is provided)
- `p`: The property to check (e.g., `∀ n m : Nat, n + m = m + n`)
- `next`: Next test in the sequence (default: `.done`)
- `cfg`: Plausible configuration (number of tests, etc.)
- `propString`: Optional string representation of the property for display

```lean
#lspec checkPlausible "addition commutes" (∀ n m : Nat, n + m = m + n)
#lspec checkPlausible "with config" (∀ n : Nat, n + 0 = n) .done { numInst := 50 }
```

For runtime evaluation with configurable seeds, use `checkPlausibleIO` instead.
-/
def checkPlausible (descr : String) (p : Prop) (next : TestSeq := .done)
    (cfg : Plausible.Configuration := {}) (propString : Option String := none)
    (p' : DecorationsOf p := by mk_decorations) [Plausible.Testable p'] : TestSeq :=
  haveI : Testable p' := instTestableOfPlausible p' cfg
  .individual descr p' propString inferInstance next

open Plausible.Decorations in
/--
Property-based test evaluated at runtime, using Plausible.

This is the Plausible-based analog to `checkIO`. Unlike `checkPlausible`, which runs during
compilation, `checkPlausibleIO` defers test execution until the test suite is run, enabling
configurable random seeds via `cfg.randomSeed` and fresh random values on each run.

- `descr`: Description shown in test output (can be empty if propString is provided)
- `p`: The property to check (e.g., `∀ n m : Nat, n + m = m + n`)
- `next`: Next test in the sequence (default: `.done`)
- `cfg`: Plausible configuration including optional `randomSeed`
- `propString`: Optional string representation of the property for display

```lean
def tests : TestSeq :=
  checkPlausibleIO "addition commutes" (∀ n m : Nat, n + m = m + n)

def reproducible : TestSeq :=
  checkPlausibleIO "deterministic" (∀ n : Nat, n * 1 = n) .done { randomSeed := some 42 }

def main : IO UInt32 := lspecIO (.ofList [("tests", [tests])]) []
```

Note: `checkPlausibleIO` tests are skipped when run via `#lspec` (which uses the pure runner).
Use `lspecIO` or `lspecEachIO` to execute them.
-/
def checkPlausibleIO (descr : String) (p : Prop) (next : TestSeq := .done)
    (cfg : Plausible.Configuration := {}) (propString : Option String := none)
    (p' : DecorationsOf p := by mk_decorations) [Plausible.Testable p'] : TestSeq :=
  let action : IO (Bool × Nat × Nat × Option String) := do
    match ← runPlausibleSuiteIO p' cfg with
    | (.success _, _) => pure (true, cfg.numInst, cfg.numInst, none)
    | (.gaveUp n, _) => pure (false, 0, cfg.numInst, some s!"Gave up {n} times")
    | (.failure _ xs n, numSamples) =>
      pure (false, numSamples, cfg.numInst, some $ Plausible.Testable.formatFailure "Found problems!" xs n)
  .individualIO descr propString action next

section SyntaxCapturingMacros
open Lean in
/--
Macro for `checkPlausible` that automatically captures the property syntax for display.

This produces output like:
```
✓ ∃₁₀₀: "add_comm" (∀ n m : Nat, n + m = m + n)
```

Usage:
```lean
#lspec checkPlausible' "add_comm" (∀ n m : Nat, n + m = m + n)
```
-/
scoped macro "checkPlausible'" descr:str prop:term : term => do
  let propStr := prop.raw.reprint.getD s!"{prop}"
  `((checkPlausible $descr $prop .done {} (some $(Lean.quote propStr)) : TestSeq))

open Lean in
/--
Macro for `checkPlausibleIO` that automatically captures the property syntax for display.
This is the Plausible counterpart to LSpec's `checkIO'` macro that currently uses SlimCheck.

This produces output like:
```
✓ ∃₁₀₀: "add_comm" (∀ n m : Nat, n + m = m + n)
```

Usage:
```lean
def tests : TestSeq :=
  checkPlausibleIO' "add_comm" (∀ n m : Nat, n + m = m + n)
```
-/
scoped macro "checkPlausibleIO'" descr:str prop:term : term => do
  let propStr := prop.raw.reprint.getD s!"{prop}"
  `((checkPlausibleIO $descr $prop .done {} (some $(Lean.quote propStr)) : TestSeq))

end SyntaxCapturingMacros

end
end LSpec
