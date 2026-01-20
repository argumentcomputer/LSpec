import Lean
import LSpec.SlimCheck.Checkable

/-!
# The core `LSpec` framework

A lightweight testing framework for Lean 4, inspired by Hspec.

## Overview

LSpec provides three main ways to define tests:

- **`test`**: For simple decidable propositions evaluated at compile time
- **`check`**: For property-based tests using SlimCheck, evaluated at compile time
- **`checkIO`**: For property-based tests evaluated at runtime with configurable random seeds

## Quick Start

```lean
import LSpec

-- Simple compile-time tests using #lspec
#lspec test "basic arithmetic" (2 + 2 = 4)
#lspec check "addition is commutative" (∀ n m : Nat, n + m = m + n)

-- Runtime tests via main function
def myTests : TestSeq :=
  test "equality" (1 = 1) $
  checkIO "commutativity" (∀ n m : Nat, n + m = m + n)

def main : IO UInt32 := lspecIO (.ofList [("myTests", [myTests])]) []
```

## Test Evaluation

| Function  | Evaluation | Random Seed   | Use Case                          |
|-----------|------------|---------------|-----------------------------------|
| `test`    | Compile    | N/A           | Simple decidable propositions     |
| `check`   | Compile    | Fixed default | Deterministic property tests      |
| `checkIO` | Runtime    | Configurable  | Reproducible property tests       |

## References

  * https://hackage.haskell.org/package/hspec
-/

namespace LSpec

/--
The main typeclass of propositions that can be tested by `LSpec`.

| Constructor | Symbol | Meaning |
|-------------|--------|---------|
| `isTrue`    | `✓`    | Passed with formal proof |
| `isPassed`  | `✓*`   | Passed without formal proof (e.g., property test passed all samples) |
| `isMaybe`   | `?`    | Inconclusive |
| `isFalse`   | `×`    | Failed with formal refutation |
| `isFailure` | `×`    | Failed without formal refutation |
-/
class inductive Testable (p : Prop) where
  | isTrue  (h : p)
  | isPassed (msg : Option String := none)
  | isMaybe (msg : Option String := none)
  | isFalse (h : ¬ p) (msg : Option String := none)
  | isFailure (msg : Option String := none)

/-- A default `Testable` instance with low priority. -/
instance (priority := 25) (p : Prop) [d : Decidable p] : Testable p :=
  match d with
  | isFalse h => .isFalse h "Evaluated to false"
  | isTrue  h => .isTrue  h

open SlimCheck in
instance instTestableOfCheckable (p : Prop) (cfg : Configuration) [Checkable p] : Testable p :=
  let (res, _) := ReaderT.run (Checkable.runSuite p cfg) (.up mkStdGen)
  match res with
  | .success (.inr h) => .isTrue h
  | .success (.inl _) => .isPassed
  | .gaveUp n => .isFailure s!"Gave up {n} times"
  | .failure h xs n => .isFalse h $ Checkable.formatFailure "Found problems!" xs n

/-- Formats the extra error message from `Testable` failures. -/
def formatErrorMsg : Option String → String
  | some msg => s!"\n    {msg}"
  | none     => ""

section TestSequences

/--
A sequence of tests to be executed.

Constructors:
- `individual`: A compile-time test with a description, proposition, and proof of testability
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
-/
inductive TestSeq
  | individual : String → (prop : Prop) → Testable prop → TestSeq → TestSeq
  | individualIO : String → IO (Bool × Option String) → TestSeq → TestSeq
  | group : String → TestSeq → TestSeq → TestSeq
  | done

/-- Appends two sequences of tests. -/
def TestSeq.append : TestSeq → TestSeq → TestSeq
  | done, t => t
  | individual d p i n, t' => individual d p i $ n.append t'
  | individualIO d action n, t' => individualIO d action $ n.append t'
  | group d ts n, t' => group d ts $ n.append t'

instance : Append TestSeq where
  append := TestSeq.append

/--
Allows the composition of tests with propositions for which a `Testable`
instance exists.
-/
def test (descr : String) (p : Prop) [Testable p]
    (next : TestSeq := .done) : TestSeq :=
  .individual descr p inferInstance next

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

- `descr`: Description shown in test output
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
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : TestSeq :=
  haveI : Testable p' := instTestableOfCheckable p' cfg
  test descr p' next

open SlimCheck Decorations in
/--
Property-based test evaluated at **runtime**.

Unlike `check`, which runs during compilation, `checkIO` defers test execution until
the test suite is run. This enables:
- Configurable random seeds via `cfg.randomSeed` for reproducible test runs
- Different random values on each execution (when no seed is specified)
- Integration with CI systems that may want deterministic test runs

- `descr`: Description shown in test output
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
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : TestSeq :=
  let action : IO (Bool × Option String) := do
    let result ← Checkable.checkIO p' cfg
    match result with
    | .success _ => pure (true, none)
    | .gaveUp n => pure (false, some s!"Gave up {n} times")
    | .failure _ xs n => pure (false, some $ Checkable.formatFailure "Found problems!" xs n)
  .individualIO descr action next

inductive ExpectationFailure (exp got : String) : Prop

instance : Testable (ExpectationFailure exp got) :=
  .isFailure s!"Expected '{repr exp}' but got '{repr got}'"

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
Pure runner for `TestSeq`. Returns `(success, output)` where `success` is `true`
if all tests passed.

This runner executes `individual` tests but **skips** `individualIO` tests (marking them
with "?"). Used by `#lspec` for compile-time test execution.

For runtime tests including `checkIO`, use `TestSeq.runIO` instead.
-/
def TestSeq.run (tSeq : TestSeq) (indent := 0) : Bool × String :=
  let pad := String.ofList $ List.replicate indent ' '
  let rec aux (acc : String) : TestSeq → Bool × String
    | .done => (true, acc)
    | .group d ts n =>
      let (pass, msg) := ts.run (indent + 2)
      let (b, m) := aux s!"{acc}{pad}{d}:\n{msg}" n
      (pass && b, m)
    | .individual d _ (.isTrue _) n => aux s!"{acc}{pad}✓ {d}\n" n
    | .individual d _ (.isPassed _) n => aux s!"{acc}{pad}✓* {d}\n" n
    | .individual d _ (.isMaybe msg) n =>
      aux s!"{acc}{pad}? {d}{formatErrorMsg msg}\n" n
    | .individual d _ (.isFalse _ msg) n
    | .individual d _ (.isFailure msg) n =>
      let (_b, m) := aux s!"{acc}{pad}× {d}{formatErrorMsg msg}\n" n
      (false, m)
    | .individualIO d _ n =>
      aux s!"{acc}{pad}? {d} (IO test skipped in pure runner)\n" n
  aux "" tSeq

/--
IO runner for `TestSeq`. Returns `(success, output)` where `success` is `true`
if all tests passed.

Unlike `TestSeq.run`, this runner executes both `individual` and `individualIO` tests,
making it suitable for running `checkIO` property tests at runtime.

Used by `lspecIO` and `lspecEachIO` for runtime test execution.
-/
def TestSeq.runIO (tSeq : TestSeq) (indent := 0) : IO (Bool × String) := do
  let pad := String.ofList $ List.replicate indent ' '
  let rec aux (acc : String) : TestSeq → IO (Bool × String)
    | .done => pure (true, acc)
    | .group d ts n => do
      let (pass, msg) ← ts.runIO (indent + 2)
      let (b, m) ← aux s!"{acc}{pad}{d}:\n{msg}" n
      pure (pass && b, m)
    | .individual d _ (.isTrue _) n => aux s!"{acc}{pad}✓ {d}\n" n
    | .individual d _ (.isPassed _) n => aux s!"{acc}{pad}✓* {d}\n" n
    | .individual d _ (.isMaybe msg) n =>
      aux s!"{acc}{pad}? {d}{formatErrorMsg msg}\n" n
    | .individual d _ (.isFalse _ msg) n
    | .individual d _ (.isFailure msg) n => do
      let (_b, m) ← aux s!"{acc}{pad}× {d}{formatErrorMsg msg}\n" n
      pure (false, m)
    | .individualIO d action n => do
      let (success, msgOpt) ← action
      if success then
        aux s!"{acc}{pad}✓ {d}\n" n
      else
        let (_b, m) ← aux s!"{acc}{pad}× {d}{formatErrorMsg msgOpt}\n" n
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
