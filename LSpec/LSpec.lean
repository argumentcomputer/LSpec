import Lean

/--
A variant of `Decidable` for tests. In the failing case, it may contain an
explanatory message.
-/
class inductive TDecidable (p : Prop) where
  | isTrue  (h : p)
  | isFalse (h : ¬ p) (msg : Option Std.Format := none)
  | isFailure (msg : Option Std.Format := none)

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
abbrev LSpec := StateT (List LSpecResult) Id Unit

/-- Runs a sequence of test in the `LSpec` monad -/
def TestSeq.toLSpec : TestSeq → LSpec
  | .more d _ (.isTrue _) n    => do set ((d, true, none) :: (← get)); n.toLSpec
  | .more d _ (.isFalse _ m) n => do set ((d, false, m) :: (← get));   n.toLSpec
  | .more d _ (.isFailure m) n => do set ((d, false, m) :: (← get));   n.toLSpec
  | .done                      => pure ()

instance : Coe TestSeq LSpec where
  coe := TestSeq.toLSpec

/--
Runs a set of `LSpec` tests and appends the results to another list of results
(given as input by the caller).
-/
def LSpec.run (tests : LSpec) : List LSpecResult :=
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
def LSpec.runAndCompile (t : LSpec) : Bool × String :=
  let res := t.run
  (res.foldl (init := true) fun acc (_, r, _) => acc && r,
    "\n".intercalate <| res.map formatLSpecResult)

/-- Runs a `LSpec` for generic purposes. -/
def lspec (t : LSpec) : Except String String :=
  match t.runAndCompile with
  | (true,  msg) => return msg
  | (false, msg) => throw msg

/--
Runs a `LSpec` with an output meant for the Lean Infoview.

This function is meant to be called from a custom command. It runs in
`TermElabM` to have access to `logInfo` and `throwError`.
-/
def LSpec.runInTermElabMAsUnit (t : LSpec) : Lean.Elab.TermElabM Unit :=
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
def lspecIO (t : LSpec) : IO UInt32 := do
  match lspec t with
  | .ok    msg => IO.println  msg; return 0
  | .error msg => IO.eprintln msg; return 1

inductive ExpectationFailure (exp got : String) : Prop

instance : TDecidable (ExpectationFailure exp got) :=
  .isFailure s!"Expected '{exp}' but got '{got}'"

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
