import Lean

/--
A variant of `Decidable` for tests. In the failing case, it may contain an
explanatory message.
-/
class inductive TDecidable (p : Prop) where
  | isFalse (h : ¬ p) (msg : Option Std.Format := none)
  | isTrue  (h : p)

/-- A default `TDecidable` instance with low priority. -/
instance (priority := low) (p : Prop) [d : Decidable p] : TDecidable p :=
  match d with
  | isFalse h => .isFalse h f!"Evaluated to false"
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

abbrev LSpecResult := String × Bool × Option Std.Format

/-- `LSpec` is the monad used to run tests and record their results. -/
abbrev LSpec := StateT (List LSpecResult) Id

/-- Runs a sequence of test in the `LSpec` monad -/
def TestSeq.toLSpec : TestSeq → LSpec Unit
  | .more d _ (.isTrue _) n    => do set ((d, true, none) :: (← get)); n.toLSpec
  | .more d _ (.isFalse _ m) n => do set ((d, false, m) :: (← get));   n.toLSpec
  | .done                      => pure ()

instance : Coe TestSeq (LSpec Unit) where
  coe := TestSeq.toLSpec

/--
Runs a set of `LSpec` tests and appends the results to another list of results
(given as input by the caller).
-/
def LSpec.run (tests : LSpec Unit) : List LSpecResult :=
  (StateT.run tests []).2.reverse

/-- Formats the result of a test for printing. -/
def formatLSpecResult : LSpecResult → String
  | (d, b, msg) =>
    let head := if b then s!"✓ {d}" else s!"× {d}"
    match msg with
    | some m => head ++ m.indentD.pretty
    | none   => head

/--
Generates a report for all the results in a `LSpec` test, returning `true` if
all tests passed and `false` otherwise.
-/
def LSpec.runAndCompile (t : LSpec Unit) : Bool × String :=
  let res := t.run
  (res.foldl (init := true) fun acc (_, r, _) => acc && r,
    "\n".intercalate <| res.map formatLSpecResult)

/-- Runs a `LSpec` for generic purposes. -/
def lspec (t : LSpec Unit) : Except String String :=
  match t.runAndCompile with
  | (true,  msg) => return msg
  | (false, msg) => throw msg

/--
Runs a `LSpec` with an output meant for the Lean Infoview.

This function is meant to be called from a custom command. It runs in
`TermElabM` to have access to `logInfo` and `throwError`.
-/
def LSpec.runInTermElabMAsUnit (t : LSpec Unit) : Lean.Elab.TermElabM Unit :=
  match lspec t with
  | .ok    msg => Lean.logInfo msg
  | .error msg => throwError msg

/--
A custom command to run `LSpec` tests. Example:

```lean
#lspec test "four equals four" (4 = 4)
```
-/
macro "#lspec " term:term : command =>
  `(#eval (LSpec.runInTermElabMAsUnit $term:term))

/--
Runs a `LSpec` with an output meant for the terminal.

This function is designed to be plugged to a `main` function from a Lean file
that can be compiled. Example:

```lean
def main := lspecIO $
  test "four equals four" (4 = 4)
```
-/
def lspecIO (t : LSpec Unit) : IO UInt32 := do
  match lspec t with
  | .ok    msg => IO.println  msg; return 0
  | .error msg => IO.eprintln msg; return 1

inductive ExpectationFailure (exp got : String) : Prop

instance : TDecidable (ExpectationFailure exp got) :=
  have failure : ¬ ExpectationFailure exp got := sorry
  .isFalse failure s!"Expected '{exp}' but got '{got}'"

/-- A test pipeline to run a function assuming that `opt` is `Option.some _` -/
def withOptionSome (descr : String) (opt : Option α) (f : α → TestSeq) :
    LSpec (Option α) :=
  match opt with
  | none   => do set ((s!"Expected 'some _' but got 'none'", false, none) :: (← get)); pure none
  | some a => do set ((descr, true, none) :: (← get)); pure (some a)

/-- A test pipeline to run a function assuming that `opt` is `Option.none` -/
def withOptionNone (descr : String) (opt : Option α) [ToString α] : LSpec Unit :=
  match opt with
  | none   => do set ((descr, true, none) :: (← get)); pure ()
  | some a => do set ((s!"Expected 'none' but got 'some {a}'", false, none) :: (← get)); pure ()

/-- A test pipeline to run a function assuming that `exc` is `Except.ok _` -/
def withExceptOk (descr : String) (exc : Except ε α) [ToString ε]
    : LSpec (Option α) :=
  match exc with
  | .error e => do set ((s!"Expected 'ok _' but got 'error {e}'", false, none) :: (← get)); pure none
  | .ok    a => do set ((descr, true, none) :: (← get)); pure (some a)

/-- A test pipeline to run a function assuming that `exc` is `Except.error _` -/
def withExceptError (descr : String) (exc : Except ε α) [ToString α]
    : LSpec (Option ε) :=
  match exc with
  | .error e => do set ((descr, true, none) :: (← get)); pure (some e)
  | .ok    a => do set ((s!"Expected 'error _' but got 'ok {a}'", false, none) :: (← get)); pure none
