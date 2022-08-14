import Lean
import LSpec.SlimCheck.Checkable

/-!

# The core `LSpec` framework

## TODO: Add all relevant documentation

## Tags

testing frameworks

## References

  * https://hackage.haskell.org/package/hspec

-/

namespace LSpec

/--
# TODO: No longer accurate

A variant of `Decidable` for tests.

In the failing case, it may contain an explanatory message.
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

open SlimCheck Decorations in
instance (priority := 25) (p : Prop) [Checkable p] : Testable p :=
  let (res, _) := ReaderT.run (Checkable.runSuite p) (.up mkStdGen)
  match res with
  | .success (.inr h) => .isTrue h
  | .success (.inl _) => .isMaybe
  | .gaveUp n => .isFailure s!"Gave up {n} times"
  | .failure h xs n =>
    .isFalse h $ Checkable.formatFailure "Found problems!" xs n

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

/-
  Allows collecting a `TestSeq` into a test group to print results
  in an indented group.
-/
def group (descr : String) (groupTests : TestSeq)
    (next : TestSeq := .done) : TestSeq :=
  .group descr groupTests next

open SlimCheck Decorations in
/-- TODO: Add documentation -/
def check (descr : String) (p : Prop)
  (p' : Decorations.DecorationsOf p := by mk_decorations) [Checkable p']
    (next : TestSeq := .done) : TestSeq :=
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

end TestSequences

section PureTesting

/-- A generic runner for `TestSeq` -/
def TestSeq.run (tSeq : TestSeq) (indent := 0) : Bool × String :=
  let pad := String.mk $ List.replicate indent ' '
  let rec aux (acc : String) : TestSeq → Bool × String
    | .done => (true, acc)
    | .group d ts n =>
      let (pass, msg) := ts.run (indent + 2)
      let (b, m) := aux s!"{acc}{pad}{d}:\n{msg}" n
      (pass && b, m)
    | .individual d _ (.isTrue _) n =>
      let (b, m) := aux s!"{acc}{pad}✓ {d}\n" n
      (true && b, m)
    | .individual d _ (.isMaybe   msg) n =>
      let (b, m) := aux s!"{acc}{pad}? {d}{formatErrorMsg msg}\n" n
      (true && b, m)
    | .individual d _ (.isFalse _ msg) n
    | .individual d _ (.isFailure msg) n =>
      let (b, m) := aux s!"{acc}{pad}× {d}{formatErrorMsg msg}\n" n
      (false && b, m)
  aux "" tSeq

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

end PureTesting

section MonadicTesting

class MonadEmit (m) [Monad m] where
  emit : String → m Unit

export MonadEmit (emit)

/-- A monadic runner that emits test outputs as they're produced. -/
def TestSeq.runM (tSeq : TestSeq) (indent := 0)
  [Monad m] [MonadEmit m] : m Bool :=
  let pad := String.mk $ List.replicate indent ' '
  match tSeq with
  | .done => return true
  | .group d ts n => do
    emit s!"{d}:"
    let gb ← ts.runM (indent + 2)
    return gb && (← n.runM indent)
  | .individual d _ (.isTrue _) n => do
    emit $ s!"{pad}✓ {d}"
    return true && (← n.runM indent)
  | .individual d _ (.isMaybe msg) n => do
    emit $ s!"{pad}? {d}{formatErrorMsg msg}"
    return true && (← n.runM indent)
  | .individual d _ (.isFalse _ msg) n
  | .individual d _ (.isFailure msg) n => do
    emit $ s!"{pad}× {d}{formatErrorMsg msg}"
    return false && (← n.runM indent)

class MonadTest (m) [Monad m] (α) where
  success : α
  failure : α
  nEq     : success ≠ failure

def succeed [Monad m] [inst : MonadTest m α] : m α :=
  return inst.success

def fail [Monad m] [inst : MonadTest m α] : m α :=
  return inst.failure

/-- Runs a `TestSeq` in a monad with `MonadEmit` and `MonadTest`. -/
def lspecM [Monad m] [MonadEmit m] [MonadTest m α] (t : TestSeq) : m α := do
  if ← t.runM then succeed
  else fail

/--
Interspersedly creates a `TestSeq` from each element `β` of a list with a
function `β → m TestSeq` and runs the test sequence.
-/
def lspecEachM [Monad m] [MonadEmit m] [MonadTest m α]
    (l : List β) (f : β → m TestSeq) : m α := do
  let success ← l.foldlM (init := true) fun acc a => do
    pure $ acc && (← ( ← f a).runM)
  if success then succeed else fail

section IOTesting

instance : MonadEmit IO :=
  ⟨IO.println⟩

instance : MonadTest IO UInt32 :=
  ⟨0, 1, by decide⟩

/--
Runs a `TestSeq` with an output meant for the terminal.

This function is designed to be plugged to a `main` function from a Lean file
that can be compiled. Example:

```lean
def main := lspecIO $
  test "four equals four" (4 = 4)
```
-/
def lspecIO (t : TestSeq) : IO UInt32 :=
  lspecM t

/--
Runs a sequence of tests that are created from a `List α` and a function
`α → IO TestSeq`. Instead of creating all tests and running them consecutively,
this function alternates between test creation and test execution.

It's rather useful for when the test creation process involves heavy
computations in `IO` (e.g. when `f` reads data from files and processes it).
-/
def lspecEachIO (l : List α) (f : α → IO TestSeq) : IO UInt32 :=
  lspecEachM l f

end IOTesting

end MonadicTesting

end LSpec
