import Lean
import LSpec.SlimCheck.Checkable

/-!

# The core `LSpec` framework

## Creating Customized Instances

The type classes `Checkable`, `SampleableExt` and `Shrinkable` are the
means by which `SlimCheck` creates samples and tests them. For instance,
the proposition `∀ i j : ℕ, i ≤ j` has a `Checkable` instance because `ℕ`
is sampleable and `i ≤ j` is decidable. Once `SlimCheck` finds the `Checkable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. Once it has found a
counter-example it will then use a `Shrinkable` instance to reduce the
example. This allows the user to create new instances and apply
`SlimCheck` to new situations.

### What do I do if I'm testing a property about my newly defined type?

Let us consider a type made for a new formalization:
```lean
structure MyType where
  x : ℕ
  y : ℕ
  h : x ≤ y
  deriving Repr
```
How do we test a property about `MyType`? For instance, let us consider
`Checkable.check $ ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `Shrinkable MyType` and `SampleableExt MyType`. We can define one as follows:
```lean
instance : Shrinkable MyType where
  shrink := λ ⟨x,y,h⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (λ ⟨⟨fst, snd⟩, ha⟩ => ⟨⟨fst, fst + snd, sorry⟩, sorry⟩)
instance : SampleableExt MyType :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    pure $ ⟨x, x + xyDiff, sorry⟩
```
Again, we take advantage of the fact that other types have useful
`Shrinkable` implementations, in this case `Prod`. Note that the second
proof is heavily based on `WellFoundedRelation` since its used for termination so
the first step you want to take is almost always to `simp_wf` in order to
get through the `WellFoundedRelation`.

## Main definitions

  * `Checkable` class
  * `Checkable.check`: a way to test a proposition using random examples

## Tags

random testing

## References

  * https://hackage.haskell.org/package/hspec

-/

namespace LSpec

abbrev Checkable := SlimCheck.Checkable

/--
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
  | TestResult.success (.inr h) => .isTrue h
  | TestResult.success (.inl _) => .isMaybe
  | TestResult.gaveUp n => .isFailure s!"Gave up {n} times"
  | TestResult.failure h xs n => 
    .isFalse h $ Checkable.formatFailure "Found problems!" xs n

/-- Formats the extra error message from `Testable` failures. -/
def formatErrorMsg : Option String → String
  | some msg => s!"\n    {msg}"
  | none     => ""

section TestSequences

/-- The datatype used to represent a sequence of tests -/
inductive TestSeq
  | more : String → (prop : Prop) → Testable prop → TestSeq → TestSeq
  | done

/-- Appends two sequences of tests. -/
def TestSeq.append : TestSeq → TestSeq → TestSeq
  | done, t => t
  | more d p i n, t' => more d p i $ n.append t'

instance : Append TestSeq where
  append := TestSeq.append

/--
Allows the composition of tests with propositions for which a `Testable`
instance exists.
-/
def test (descr : String) (p : Prop) [Testable p]
    (next : TestSeq := .done) : TestSeq :=
  .more descr p inferInstance next

open SlimCheck Decorations in
/-- todo -/
def check (descr : String) (p : Prop)
  (p' : Decorations.DecorationsOf p := by mk_decorations) [Checkable p']
    (next : TestSeq := .done) : TestSeq :=
  test descr p' next

inductive ExpectationFailure (exp got : String) : Prop

def formatExpectedButGotMsg [Repr α] (exp got : α) : String :=
  s!"Expected '{repr exp}' but got '{repr got}'"

instance : Testable (ExpectationFailure exp got) :=
  .isFailure $ formatExpectedButGotMsg exp got

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
def TestSeq.run (tSeq : TestSeq) : Bool × String :=
  let rec aux (acc : String) : TestSeq → Bool × String
    | .done => (true, acc)
    | .more d _ (.isTrue _) n =>
      let (b, m) := aux s!"{acc}✓ {d}\n" n
      (true && b, m)
    | .more d _ (.isMaybe   msg) n => 
      let (b, m) := aux s!"{acc}? {d}{formatErrorMsg msg}\n" n
      (false && b, m)
    | .more d _ (.isFalse _ msg) n
    | .more d _ (.isFailure msg) n =>
      let (b, m) := aux s!"{acc}× {d}{formatErrorMsg msg}\n" n
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
def TestSeq.runM [Monad m] [MonadEmit m] : TestSeq → m Bool
  | .done => pure true
  | .more d _ (.isTrue _) n => do emit s!"✓ {d}"; return true && (← n.runM)
  | .more d _ (.isMaybe msg) n => do
    emit s!"? {d}{formatErrorMsg msg}"; return true && (← n.runM)
  | .more d _ (.isFalse _ msg) n
  | .more d _ (.isFailure msg) n => do
    emit s!"× {d}{formatErrorMsg msg}"; return false && (← n.runM)

class MonadTest (m) [Monad m] (α) where
  success : α
  failure : α
  nEq     : success ≠ failure

def succeed [Monad m] [inst : MonadTest m α] : m α :=
  return inst.success

def fail [Monad m] [inst : MonadTest m α] : m α :=
  return inst.failure

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
def lspec (t : TestSeq) : IO UInt32 := do
  if ← t.runM then succeed
  else fail

/--
Runs a sequence of tests that are created from a `List α` and a function
`α → IO TestSeq`. Instead of creating all tests and running them consecutively,
this function alternates between test creation and test execution.

It's rather useful for when the test creation process involves heavy
computations in `IO` (e.g. when `f` reads data from files and processes it).
-/
def lspecEachWith (l : List α) (f : α → IO TestSeq) : IO UInt32 := do
  let success ← l.foldlM (init := true) fun acc a => do
    pure $ acc && (← ( ← f a).runM)
  if success then succeed else fail

end IOTesting

end MonadicTesting

end LSpec
