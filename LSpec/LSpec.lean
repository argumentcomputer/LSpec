import Lean
import LSpec.SlimCheck.Checkable

/-!
# The core `LSpec` framework

## Add all relavent documentation

Check [here](./LSpec/Examples.lean) for examples of uses

## Tags

testing frameworks

## References

  * https://hackage.haskell.org/package/hspec
-/

namespace LSpec

/--
The main typeclass of propositions that can be tested by `LSpec`.

In non-succeeding cases, it may contain an explanatory message.
-/
class inductive Testable (p : Prop) where
  | isTrue  (h : p)
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
  | .success (.inl _) => .isMaybe
  | .gaveUp n => .isFailure s!"Gave up {n} times"
  | .failure h xs n => .isFalse h $ Checkable.formatFailure "Found problems!" xs n

/-- Formats the extra error message from `Testable` failures. -/
def formatErrorMsg : Option String → String
  | some msg => s!"\n    {msg}"
  | none     => ""

section TestSequences

/--
  The datatype used to represent a sequence of tests.
  The `group` constructor represents a purely decorative concept
  of a test group, allowing to print tests results more prettily.
-/
inductive TestSeq
  | individual : String → (prop : Prop) → Testable prop → TestSeq → TestSeq
  | group : String → TestSeq → TestSeq → TestSeq
  | done

/-- Appends two sequences of tests. -/
def TestSeq.append : TestSeq → TestSeq → TestSeq
  | done, t => t
  | individual d p i n, t' => individual d p i $ n.append t'
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

open SlimCheck Decorations in
/--
Checks a `Checkable` prop. Note that `mk_decorations` is here simply to improve error messages
and if `p` is Checkable, then so is `p'`.
-/
def check (descr : String) (p : Prop) (next : TestSeq := .done) (cfg : Configuration := {})
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : TestSeq :=
  haveI : Testable p' := instTestableOfCheckable p' cfg
  test descr p' next

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

/-- A generic runner for `TestSeq` -/
def TestSeq.run (tSeq : TestSeq) (indent := 0) : Bool × String :=
  let pad := String.ofList $ List.replicate indent ' '
  let rec aux (acc : String) : TestSeq → Bool × String
    | .done => (true, acc)
    | .group d ts n =>
      let (pass, msg) := ts.run (indent + 2)
      let (b, m) := aux s!"{acc}{pad}{d}:\n{msg}" n
      (pass && b, m)
    | .individual d _ (.isTrue _) n => aux s!"{acc}{pad}✓ {d}\n" n
    | .individual d _ (.isMaybe   msg) n =>
      aux s!"{acc}{pad}? {d}{formatErrorMsg msg}\n" n
    | .individual d _ (.isFalse _ msg) n
    | .individual d _ (.isFailure msg) n =>
      let (_b, m) := aux s!"{acc}{pad}× {d}{formatErrorMsg msg}\n" n
      (false, m)
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
Consumes a map of string-keyed test suites and returns a test function meant to
be used via CLI.

The arguments `args` are matched against the test suite keys. If a key starts
with one of the elements in `args`, then its respective test suite will be
marked to run.

If the empty list is provided, all test suites will run.
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
      let (success, msg) := tSeq.run (indent := 2)
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
Runs a sequence of tests that are created from a `List α` and a function
`α → IO TestSeq`. Instead of creating all tests and running them consecutively,
this function alternates between test creation and test execution.

It's useful when the test creation process involves heavy computations in `IO`
(e.g. when `f` reads data from files and processes it).
-/
def lspecEachIO (l : List α) (f : α → IO TestSeq) : IO UInt32 := do
  let success ← l.foldlM (init := true) fun acc a => do
    match (← f a).run with
    | (true, msg) => IO.println msg; pure acc
    | (false, msg) => IO.eprintln msg; pure false
  if success then return 0 else return 1

end LSpec
