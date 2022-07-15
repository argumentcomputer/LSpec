import Lean

/--
A variant of `Decidable` for tests. In the failing case, it may contain an
explanatory message.
-/
class inductive TDecidable (p : Prop) where
  | isTrue  (h : p)
  | isFalse (h : ¬ p) (msg : Option String := none)
  | isFailure (msg : Option String := none)

/-- A default `TDecidable` instance with low priority. -/
instance (priority := 25) (p : Prop) [d : Decidable p] : TDecidable p :=
  match d with
  | isFalse h => .isFalse h "Evaluated to false"
  | isTrue  h => .isTrue  h

/-- The datatype used to represent a sequence of tests. -/
inductive TestSeq
  | more : String → (prop : Prop) → TDecidable prop → TestSeq → TestSeq
  | done

/-- Appends two sequences of tests. -/
def TestSeq.append : TestSeq → TestSeq → TestSeq
  | done, t => t
  | more d p i n, t' => more d p i $ n.append t'

instance : Append TestSeq where
  append := TestSeq.append

/-- `test` allows the composition of tests. -/
def test (descr : String) (p : Prop) [TDecidable p]
    (next : TestSeq := .done) : TestSeq :=
  .more descr p inferInstance next

/-- Formats the extra error message from `TDecidable` failures. -/
def formatErrorMsg : Option String → String
  | some msg => s!"\n    {msg}"
  | none     => ""

/-- A generic runner for `TestSeq` -/
def TestSeq.run (tSeq : TestSeq) : Bool × String :=
  let rec aux (acc : String) : TestSeq → Bool × String
    | .done => (true, acc)
    | .more d _ (.isTrue _) n =>
      let (b, m) := aux s!"{acc}✓ {d}\n" n
      (true && b, m)
    | .more d _ (.isFalse _ msg) n
    | .more d _ (.isFailure msg) n =>
      let (b, m) := aux s!"{acc}× {d}{formatErrorMsg msg}\n" n
      (false && b, m)
  aux "" tSeq

/-- A runner for `IO` that prints test outputs instead of storing them. -/
def TestSeq.runIO : TestSeq → IO Bool
  | .done => pure true
  | .more d _ (.isTrue _) n => do
    IO.println s!"✓ {d}"
    return true && (← n.runIO)
  | .more d _ (.isFalse _ msg) n
  | .more d _ (.isFailure msg) n => do
    IO.println s!"× {d}{formatErrorMsg msg}"
    return false && (← n.runIO)

/--
Runs a `TestSeq` with an output meant for the Lean Infoview.
This function is meant to be called from a custom command. It runs in
`TermElabM` to have access to `logInfo` and `throwError`.
-/
def LSpec.runInTermElabMAsUnit (tSeq : TestSeq) : Lean.Elab.TermElabM Unit :=
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
  if ← t.runIO then return 0
  return 1

/--
Runs a sequence of tests that are created from a `List α` and a function
`α → IO TestSeq`. Instead of creating all tests and running them consecutively,
this function alternates between test creation and test execution.

It's rather useful for when the test creation process involves heavy
computations in `IO` (e.g. when `f` reads data from files and processes it).
-/
def lspecEachWith (l : List α) (f : α → IO TestSeq) : IO UInt32 := do
  let success ← l.foldlM (init := true) fun acc a => do
    pure $ acc && (← ( ← f a).runIO)
  return if success then 0 else 1

inductive ExpectationFailure (exp got : String) : Prop

def formatExpectedButGotMsg [Repr α] (exp got : α) : String :=
  s!"Expected '{repr exp}' but got '{repr got}'"

instance : TDecidable (ExpectationFailure exp got) :=
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
