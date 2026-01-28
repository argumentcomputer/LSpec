import Lean
import LSpec.SlimCheck.Checkable

/-!
# The core `LSpec` framework

A lightweight testing framework for Lean 4, inspired by Hspec.

## Overview

LSpec provides three main ways to define tests:

- **`test`**: For simple decidable propositions (unit tests)
- **`check`/`check'`**: For property-based tests using SlimCheck, evaluated at compile time
- **`checkIO`/`checkIO'`**: For property-based tests evaluated at runtime with configurable seeds

## Quick Start

```lean
import LSpec

-- Simple unit tests using #lspec
#lspec test "basic arithmetic" (2 + 2 = 4)

-- Property tests with syntax capture (shows the property in output)
#lspec check' "addition is commutative" (∀ n m : Nat, n + m = m + n)

-- Runtime tests via main function
def myTests : TestSeq :=
  test "equality" (1 = 1) ++
  checkIO' "commutativity" (∀ n m : Nat, n + m = m + n)

def main : IO UInt32 := lspecIO (.ofList [("myTests", [myTests])]) []
```

## Output Format

LSpec uses logical quantifier notation to indicate verification level:

| Symbol | Meaning | Example |
|--------|---------|---------|
| `✓ ∃:` | Unit test passed (single case verified) | `✓ ∃: basic arithmetic` |
| `✓ ∀:` | Property test with formal proof | `✓ ∀: "name" (∀ n, n = n)` |
| `✓ ∃ₙ:` | Property test passed n samples (no proof) | `✓ ∃₁₀₀: "add_comm" (∀ n m, ...)` |
| `× ∃ⁿ/ₘ:` | Property test failed on sample n of m | `× ∃²/₁₀₀: "fails" (∀ n, ...)` |

The `check'` and `checkIO'` macros capture the property syntax for display.
Use `check` and `checkIO` (without apostrophe) for simpler output.

## Test Functions

| Function   | Evaluation | Syntax Capture | Use Case                          |
|------------|------------|----------------|-----------------------------------|
| `test`     | Compile    | No             | Simple decidable propositions     |
| `check`    | Compile    | No             | Property tests (description only) |
| `check'`   | Compile    | Yes            | Property tests (shows property)   |
| `checkIO`  | Runtime    | No             | Runtime property tests            |
| `checkIO'` | Runtime    | Yes            | Runtime tests (shows property)    |

## References

  * https://hackage.haskell.org/package/hspec
  * https://hackage.haskell.org/package/QuickCheck
-/

namespace LSpec

/--
The main typeclass of propositions that can be tested by `LSpec`.

| Constructor | Symbol | Meaning |
|-------------|--------|---------|
| `isTrue`    | `✓ ∃:` | Unit test passed with formal proof |
| `isPassed`  | `✓ ∃ₙ:` | Property test passed n samples (no formal proof) |
| `isMaybe`   | `?`    | Inconclusive |
| `isFalse`   | `× ∃ⁿ/ₘ:` | Property test failed on sample n of m with formal refutation |
| `isFailure` | `×`    | Failed without formal refutation |

For success: `numSamples` = total tests passed
For failure: `failedAt` = which test failed (1-indexed), `totalTests` = total configured
-/
class inductive Testable (p : Prop) where
  | isTrue  (h : p)
  | isPassed (numSamples : Nat := 0) (msg : Option String := none)
  | isMaybe (msg : Option String := none)
  | isFalse (h : ¬ p) (failedAt : Nat := 0) (totalTests : Nat := 0) (msg : Option String := none)
  | isFailure (failedAt : Nat := 0) (totalTests : Nat := 0) (msg : Option String := none)

/-- A default `Testable` instance with low priority. -/
instance (priority := 25) (p : Prop) [d : Decidable p] : Testable p :=
  match d with
  | isFalse h => .isFalse h 0 0 "Evaluated to false"
  | isTrue  h => .isTrue  h

open SlimCheck in
instance instTestableOfCheckable (p : Prop) (cfg : Configuration) [Checkable p] : Testable p :=
  let ((res, numSamples), _) := ReaderT.run (Checkable.runSuite p cfg) (.up mkStdGen)
  match res with
  | .success (.inr h) => .isTrue h
  | .success (.inl _) => .isPassed numSamples
  | .gaveUp n => .isFailure 0 cfg.numInst s!"Gave up {n} times"
  | .failure h xs n => .isFalse h (numSamples + 1) cfg.numInst $ Checkable.formatFailure "Found problems!" xs n

/-- Formats the extra error message from `Testable` failures. -/
def formatErrorMsg : Option String → String
  | some msg => s!"\n    {msg}"
  | none     => ""

section TestSequences

/--
A sequence of tests to be executed.

Constructors:
- `individual`: A compile-time test with a description, proposition, optional property string, and proof of testability
- `individualIO`: A deferred IO test that runs at execution time (used by `checkIO`)
- `group`: A named group of tests for organized output
- `done`: Marks the end of a test sequence

Tests can be chained using the `next` parameter or appended with `++`:
```lean
def tests : TestSeq :=
  test "first" (1 = 1) $
  test "second" (2 = 2)

-- Equivalent using append
def tests' : TestSeq :=
  test "first" (1 = 1) ++ test "second" (2 = 2)
```

The `propString` field allows property tests to display the original property syntax.
For `individualIO`, the action returns `(success, numSamples, totalTests, errorMsg)`.
-/
inductive TestSeq
  | individual : String → (prop : Prop) → (propString : Option String) → Testable prop → TestSeq → TestSeq
  | individualIO : String → (propString : Option String) → IO (Bool × Nat × Nat × Option String) → TestSeq → TestSeq
  | group : String → TestSeq → TestSeq → TestSeq
  | done

/-- Appends two sequences of tests. -/
def TestSeq.append : TestSeq → TestSeq → TestSeq
  | done, t => t
  | individual d p ps i n, t' => individual d p ps i $ n.append t'
  | individualIO d ps action n, t' => individualIO d ps action $ n.append t'
  | group d ts n, t' => group d ts $ n.append t'

instance : Append TestSeq where
  append := TestSeq.append

/--
Allows the composition of tests with propositions for which a `Testable`
instance exists. Used for unit tests (existential checks).
-/
def test (descr : String) (p : Prop) [Testable p]
    (next : TestSeq := .done) : TestSeq :=
  .individual descr p none inferInstance next

/-- Allows collecting a `TestSeq` into a test group to print results in a group. -/
def group (descr : String) (groupTests : TestSeq)
    (next : TestSeq := .done) : TestSeq :=
  .group descr groupTests next

/-- Alias for `group`. Groups related tests under a descriptive label.
    Use for describing a component or function being tested. -/
def describe (descr : String) (groupTests : TestSeq) (next : TestSeq := .done) : TestSeq :=
  group descr groupTests next

/-- Alias for `group`. Groups related tests under a contextual label.
    Use for describing circumstances under which tests run. -/
def context (descr : String) (groupTests : TestSeq) (next : TestSeq := .done) : TestSeq :=
  group descr groupTests next

open SlimCheck Decorations in
/--
Property-based test evaluated at **compile time**.

Uses SlimCheck to generate random test cases and check the property. The test runs
during elaboration with a fixed random seed (`mkStdGen`), making results deterministic
across compilations.

- `descr`: Description shown in test output (can be empty if propString is provided)
- `propString`: Optional string representation of the property for display
- `p`: The property to check (e.g., `∀ n m : Nat, n + m = m + n`)
- `next`: Next test in the sequence (default: `.done`)
- `cfg`: SlimCheck configuration (number of tests, etc.)

```lean
#lspec check "addition commutes" (∀ n m : Nat, n + m = m + n)
#lspec check "with config" (∀ n : Nat, n + 0 = n) .done { numInst := 50 }
```

For runtime evaluation with configurable seeds, use `checkIO` instead.
-/
def check (descr : String) (p : Prop) (next : TestSeq := .done) (cfg : Configuration := {})
    (propString : Option String := none)
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : TestSeq :=
  haveI : Testable p' := instTestableOfCheckable p' cfg
  .individual descr p' propString inferInstance next

open SlimCheck Decorations in
/--
Property-based test evaluated at **runtime**.

Unlike `check`, which runs during compilation, `checkIO` defers test execution until
the test suite is run. This enables:
- Configurable random seeds via `cfg.randomSeed` for reproducible test runs
- Different random values on each execution (when no seed is specified)
- Integration with CI systems that may want deterministic test runs

- `descr`: Description shown in test output (can be empty if propString is provided)
- `propString`: Optional string representation of the property for display
- `p`: The property to check (e.g., `∀ n m : Nat, n + m = m + n`)
- `next`: Next test in the sequence (default: `.done`)
- `cfg`: SlimCheck configuration including optional `randomSeed`

```lean
-- Runtime test with random seed (different each run)
def tests : TestSeq :=
  checkIO "addition commutes" (∀ n m : Nat, n + m = m + n)

-- Reproducible test with fixed seed
def reproducible : TestSeq :=
  checkIO "deterministic" (∀ n : Nat, n * 1 = n) .done { randomSeed := some 42 }

-- Run via main
def main : IO UInt32 := lspecIO (.ofList [("tests", [tests])]) []
```

Note: `checkIO` tests are skipped when run via `#lspec` (which uses the pure runner).
Use `lspecIO` or `lspecEachIO` to execute them.
-/
def checkIO (descr : String) (p : Prop) (next : TestSeq := .done) (cfg : Configuration := {})
    (propString : Option String := none)
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : TestSeq :=
  let action : IO (Bool × Nat × Nat × Option String) := do
    let (result, numSamples) ← Checkable.checkIO p' cfg
    match result with
    | .success _ => pure (true, numSamples, cfg.numInst, none)
    | .gaveUp n => pure (false, 0, cfg.numInst, some s!"Gave up {n} times")
    | .failure _ xs n => pure (false, numSamples, cfg.numInst, some $ Checkable.formatFailure "Found problems!" xs n)
  .individualIO descr propString action next

section SyntaxCapturingMacros
open Lean in
/--
Macro for `check` that automatically captures the property syntax for display.

This produces output like:
```
✓ ∃₁₀₀: "add_comm" (∀ n m : Nat, n + m = m + n)
```

Usage:
```lean
#lspec check' "add_comm" (∀ n m : Nat, n + m = m + n)

-- Can be chained:
def tests : TestSeq :=
  check' "test1" (∀ n : Nat, n = n) ++
  check' "test2" (∀ n : Nat, n + 0 = n)
```
-/
scoped macro "check'" descr:str prop:term : term => do
  let propStr := prop.raw.reprint.getD s!"{prop}"
  `((check $descr $prop .done {} (some $(Lean.quote propStr)) : TestSeq))

/--
Macro for `checkIO` that automatically captures the property syntax for display.

This produces output like:
```
✓ ∃₁₀₀: "add_comm" (∀ n m : Nat, n + m = m + n)
```

Usage:
```lean
def tests : TestSeq :=
  checkIO' "add_comm" (∀ n m : Nat, n + m = m + n)
```
-/
scoped macro "checkIO'" descr:str prop:term : term => do
  let propStr := prop.raw.reprint.getD s!"{prop}"
  `((checkIO $descr $prop .done {} (some $(Lean.quote propStr)) : TestSeq))

end SyntaxCapturingMacros

inductive ExpectationFailure (exp got : String) : Prop

instance : Testable (ExpectationFailure exp got) :=
  .isFailure 0 0 s!"Expected '{repr exp}' but got '{repr got}'"

/-- A test pipeline to run a function assuming that `opt` is `Option.some _` -/
def withOptionSome (descr : String) (opt : Option α) (f : α → TestSeq) :
    TestSeq :=
  match opt with
  | none   => test descr (ExpectationFailure "some _" "none")
  | some a => test descr true $ f a

/-- A test pipeline to run a function assuming that `opt` is `Option.none` -/
def withOptionNone (descr : String) (opt : Option α) [ToString α]
    (f : TestSeq) : TestSeq :=
  match opt with
  | none   => test descr true $ f
  | some a => test descr (ExpectationFailure "none" s!"some {a}")

/-- A test pipeline to run a function assuming that `exc` is `Except.ok _` -/
def withExceptOk (descr : String) (exc : Except ε α) [ToString ε]
    (f : α → TestSeq) : TestSeq :=
  match exc with
  | .error e => test descr (ExpectationFailure "ok _" s!"error {e}")
  | .ok    a => test descr true $ f a

/-- A test pipeline to run a function assuming that `exc` is `Except.error _` -/
def withExceptError (descr : String) (exc : Except ε α) [ToString α]
    (f : ε → TestSeq) : TestSeq :=
  match exc with
  | .error e => test descr true $ f e
  | .ok    a => test descr (ExpectationFailure "error _" s!"ok {a}")

/--
Format test output line for successful tests.

Output formats:
- Unit test: `∃: description`
- Property test with proof: `∀: "description" (property)`
- Property test without proof: `∃₁₀₀: "description" (property)`

The subscript indicates how many samples were tested.
-/
def formatSuccessLine (descr : String) (propString : Option String)
    (hasProof : Bool) (numSamples : Nat) : String :=
  match propString with
  | some ps =>
    -- Property test: show both description and property
    if hasProof then
      -- Universal proof: ✓ ∀: "descr" propStr
      s!"∀: \"{descr}\" {ps}"
    else
      -- Existential (sampled): ✓ ∃ₙ: "descr" propStr
      s!"∃{numSamples.toSubscriptString}: \"{descr}\" {ps}"
  | none =>
    -- Unit test: ✓ ∃: descr
    s!"∃: {descr}"

/--
Format test output line for failed tests.

Output formats:
- Unit test failure: `∃: description`
- Property test failure: `∃²/₁₀₀: "description" (property)`

The superscript indicates which sample failed (1-indexed).
The subscript indicates the total number of samples configured.
-/
def formatFailureLine (descr : String) (propString : Option String)
    (failedAt : Nat) (totalTests : Nat) : String :=
  match propString with
  | some ps =>
    -- Property test failure: × ∃ⁿ/ₘ: "descr" propStr
    if totalTests > 0 then
      s!"∃{failedAt.toSuperscriptString}/{totalTests.toSubscriptString}: \"{descr}\" {ps}"
    else
      s!"∃: \"{descr}\" {ps}"
  | none =>
    -- Unit test failure: × ∃: descr
    s!"∃: {descr}"

/--
Pure runner for `TestSeq`. Returns `(success, output)` where `success` is `true`
if all tests passed.

This runner executes `individual` tests but **skips** `individualIO` tests (marking them
with "?"). Used by `#lspec` for compile-time test execution.

For runtime tests including `checkIO`, use `TestSeq.runIO` instead.

Output format:
- Unit tests: `✓ ∃: test name`
- Property tests with universal proof: `✓ ∀: "descr" ∀ n m, ...`
- Property tests without proof: `✓ ∃₁₀₀: "descr" ∀ n m, ...`
- Failed property tests: `× ∃ₙ: "descr" ∀ n m, ... (counter-example)`
-/
def TestSeq.run (tSeq : TestSeq) (indent := 0) : Bool × String :=
  let pad := String.ofList $ List.replicate indent ' '
  let rec aux (acc : String) : TestSeq → Bool × String
    | .done => (true, acc)
    | .group d ts n =>
      let (pass, msg) := ts.run (indent + 2)
      let (b, m) := aux s!"{acc}{pad}{d}:\n{msg}" n
      (pass && b, m)
    -- Test with formal proof
    | .individual d _ propStr (.isTrue _) n =>
      let line := formatSuccessLine d propStr true 0
      aux s!"{acc}{pad}✓ {line}\n" n
    -- Property test passed without formal proof: ✓ ∃ₙ: "descr" prop
    | .individual d _ propStr (.isPassed numSamples _) n =>
      let line := formatSuccessLine d propStr false numSamples
      aux s!"{acc}{pad}✓ {line}\n" n
    -- Inconclusive test: ?
    | .individual d _ propStr (.isMaybe msg) n =>
      let line := formatSuccessLine d propStr false 0
      aux s!"{acc}{pad}? {line}{formatErrorMsg msg}\n" n
    -- Failed property test with refutation: × ∃ⁿ/ₘ: "descr" prop
    | .individual d _ propStr (.isFalse _ failedAt totalTests msg) n =>
      let line := formatFailureLine d propStr failedAt totalTests
      let (_b, m) := aux s!"{acc}{pad}× {line}{formatErrorMsg msg}\n" n
      (false, m)
    -- Failed test without refutation
    | .individual d _ propStr (.isFailure failedAt totalTests msg) n =>
      let line := formatFailureLine d propStr failedAt totalTests
      let (_b, m) := aux s!"{acc}{pad}× {line}{formatErrorMsg msg}\n" n
      (false, m)
    -- IO test skipped in pure runner
    | .individualIO d propStr _ n =>
      let line := formatSuccessLine d propStr false 0
      aux s!"{acc}{pad}? {line} (IO test skipped in pure runner)\n" n
  aux "" tSeq

/--
IO runner for `TestSeq`. Returns `(success, output)` where `success` is `true`
if all tests passed.

Unlike `TestSeq.run`, this runner executes both `individual` and `individualIO` tests,
making it suitable for running `checkIO` property tests at runtime.

Used by `lspecIO` and `lspecEachIO` for runtime test execution.

Output format:
- Unit tests: `✓ ∃: test name`
- Property tests with universal proof: `✓ ∀: "descr" ∀ n m, ...`
- Property tests without proof: `✓ ∃₁₀₀: "descr" ∀ n m, ...`
- Failed property tests: `× ∃ₙ: "descr" ∀ n m, ... (counter-example)`
-/
def TestSeq.runIO (tSeq : TestSeq) (indent := 0) : IO (Bool × String) := do
  let pad := String.ofList $ List.replicate indent ' '
  let rec aux (acc : String) : TestSeq → IO (Bool × String)
    | .done => pure (true, acc)
    | .group d ts n => do
      let (pass, msg) ← ts.runIO (indent + 2)
      let (b, m) ← aux s!"{acc}{pad}{d}:\n{msg}" n
      pure (pass && b, m)
    -- Test with formal proof
    | .individual d _ propStr (.isTrue _) n =>
      let line := formatSuccessLine d propStr true 0
      aux s!"{acc}{pad}✓ {line}\n" n
    -- Property test passed without formal proof: ✓ ∃ₙ: "descr" prop
    | .individual d _ propStr (.isPassed numSamples _) n =>
      let line := formatSuccessLine d propStr false numSamples
      aux s!"{acc}{pad}✓ {line}\n" n
    -- Inconclusive test: ?
    | .individual d _ propStr (.isMaybe msg) n =>
      let line := formatSuccessLine d propStr false 0
      aux s!"{acc}{pad}? {line}{formatErrorMsg msg}\n" n
    -- Failed property test with refutation: × ∃ⁿ/ₘ: "descr" prop
    | .individual d _ propStr (.isFalse _ failedAt totalTests msg) n => do
      let line := formatFailureLine d propStr failedAt totalTests
      let (_b, m) ← aux s!"{acc}{pad}× {line}{formatErrorMsg msg}\n" n
      pure (false, m)
    -- Failed test without refutation
    | .individual d _ propStr (.isFailure failedAt totalTests msg) n => do
      let line := formatFailureLine d propStr failedAt totalTests
      let (_b, m) ← aux s!"{acc}{pad}× {line}{formatErrorMsg msg}\n" n
      pure (false, m)
    -- IO property test
    | .individualIO d propStr action n => do
      let (success, numSamples, totalTests, msgOpt) ← action
      if success then
        let line := formatSuccessLine d propStr false numSamples
        aux s!"{acc}{pad}✓ {line}\n" n
      else
        -- numSamples is tests passed before failure, so failedAt = numSamples + 1
        let line := formatFailureLine d propStr (numSamples + 1) totalTests
        let (_b, m) ← aux s!"{acc}{pad}× {line}{formatErrorMsg msgOpt}\n" n
        pure (false, m)
  aux "" tSeq

end TestSequences

/--
Runs a `TestSeq` with an output meant for the Lean Infoview.
This function is meant to be called from a custom command. It runs in
`TermElabM` to have access to `logInfo` and `throwError`.
-/
def runInTermElabMAsUnit (tSeq : TestSeq) : Lean.Elab.TermElabM Unit :=
  match tSeq.run with
  | (true,  msg) => Lean.logInfo msg
  | (false, msg) => throwError msg

/--
A custom command to run `LSpec` tests. Example:

```lean
#lspec test "four equals four" (4 = 4)
```
-/
macro "#lspec " term:term : command =>
  `(#eval LSpec.runInTermElabMAsUnit $term)

open Std (HashMap) in
/--
Runs test suites from a CLI-style main function. Returns `0` on success, `1` on failure.

- `map`: A map from suite names to lists of `TestSeq`
- `args`: Command-line arguments to filter which suites run

If `args` is empty, all suites run. Otherwise, only suites whose names start with
one of the arguments will run.

Supports both `test`/`check` (compile-time) and `checkIO` (runtime) tests.

```lean
def mathTests : TestSeq :=
  test "addition" (1 + 1 = 2) $
  checkIO "commutativity" (∀ n m : Nat, n + m = m + n)

def stringTests : TestSeq :=
  test "concat" ("a" ++ "b" = "ab")

def main (args : List String) : IO UInt32 :=
  lspecIO (.ofList [("math", [mathTests]), ("string", [stringTests])]) args

-- Run all tests:     ./test
-- Run math only:     ./test math
-- Run string only:   ./test string
```
-/
def lspecIO (map : HashMap String (List TestSeq)) (args : List String) : IO UInt32 := do
  -- Compute the filtered map containing the test suites to run
  let filteredMap :=
    if args.isEmpty then map
    else Id.run do
      let mut acc := .emptyWithCapacity args.length
      for arg in args do
        for (key, tSeq) in map do
          if key.startsWith arg then
            acc := acc.insert key tSeq
      pure acc

  -- Accumulate error messages
  let mut testsWithErrors : HashMap String (Array String) := .emptyWithCapacity map.size
  for (key, tSeqs) in filteredMap do
    IO.println key
    for tSeq in tSeqs do
      let (success, msg) ← tSeq.runIO (indent := 2)
      if success then IO.println msg
      else
        IO.eprintln msg
        if let some msgs := testsWithErrors[key]? then
          testsWithErrors := testsWithErrors.insert key $ msgs.push msg
        else
          testsWithErrors := testsWithErrors.insert key #[msg]

  -- Early return 0 when there are no errors
  if testsWithErrors.isEmpty then return 0

  -- Print error messages and then return 1
  IO.eprintln "-------------------------------- Failing tests ---------------------------------"
  for (key, msgs) in testsWithErrors do
    IO.eprintln key
    for msg in msgs do
      IO.eprintln msg
  return 1

/--
Runs tests lazily from a list, alternating between test creation and execution.
Returns `0` on success, `1` on failure.

Unlike `lspecIO` which builds all test suites upfront, this function creates and runs
tests one at a time. Useful when test creation involves expensive IO operations
(e.g., reading files, network calls).

Supports both `test`/`check` (compile-time) and `checkIO` (runtime) tests.

```lean
def main : IO UInt32 :=
  lspecEachIO ["file1.json", "file2.json"] fun path => do
    let contents ← IO.FS.readFile path
    pure $ test s!"{path} is valid" (contents.length > 0)
```
-/
def lspecEachIO (l : List α) (f : α → IO TestSeq) : IO UInt32 := do
  let success ← l.foldlM (init := true) fun acc a => do
    match ← (← f a).runIO with
    | (true, msg) => IO.println msg; pure acc
    | (false, msg) => IO.eprintln msg; pure false
  if success then return 0 else return 1

end LSpec
