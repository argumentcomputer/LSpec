import Lean

/--
A variant of `Decidable` for tests. In the failing case, may give an explanatory
message.
-/
class inductive TDecidable (p : Prop) where
  | isFalse (h : ¬ p) (msg : Option Std.Format := none)
  | isTrue  (h : p)

instance (priority := low) (p : Prop) [d : Decidable p] : TDecidable p :=
  match d with
  | isFalse h => .isFalse h f!"Evaluated to false"
  | isTrue  h => .isTrue  h

/-- The basic structure used to encode a specification. -/
structure LSpecTest where
  descr : String
  prop  : Prop
  inst  : TDecidable prop

/-- `test` is a single basic test. -/
def test (descr : String) (p : Prop) [TDecidable p] : LSpecTest :=
  ⟨descr, p, inferInstance⟩

abbrev LSpecResult := String × Bool × Option Std.Format

/--
Prints the result of a test.
-/
def printLSpecResult : LSpecResult → String
  | (d, b, msg) =>
    let head := if b then s!"✓ {d}" else s!"× {d}"
    match msg with
    | some m => head ++ m.indentD.pretty
    | none   => head

/--
The LSpec monad, records tests and whether they passed, along with an optional
additional message.
-/
abbrev LSpec := StateT (List LSpecResult) Id Unit

def LSpec.addResult (d : String) (b : Bool) (m : Option Std.Format) : LSpec :=
  StateT.modifyGet fun l => ((), (d, b, m) :: l)

instance : Coe LSpecTest LSpec where coe
  | ⟨d, _, .isTrue _⟩    => LSpec.addResult d true  none
  | ⟨d, _, .isFalse _ m⟩ => LSpec.addResult d false m

/--
Runs a set of `LSpec` tests and appends the results to another list of results
(given as input by the caller).
-/
def LSpec.run (tests : LSpec) : List (String × Bool × Option Lean.Format) :=
  (StateT.run tests []).2.reverse

/--
Generates a report for all the results in a `LSpec` test, returning `true` if
all tests passed and `false` otherwise.
-/
def LSpec.runAndCompile (t : LSpec) : Bool × String :=
  let res := t.run
  (res.foldl (init := true) fun acc (_, r, _) => acc && r,
    "\n".intercalate <| res.map printLSpecResult)

open Lean.Elab in
def LSpec.toIOUnit (t : LSpec) : TermElabM Unit := do
  let (success?, msg) := t.runAndCompile
  if success? then
    logInfo msg
  else
    throwError msg

/-- todo -/
macro "#lspec " term:term : command =>
  `(#eval (LSpec.toIOUnit $term))

/-- Runs a `LSpec` test suite and pretty prints the results. -/
def lspec (t : LSpec) (_ : List String := []) : IO UInt32 := do
  let (success?, msg) := t.runAndCompile
  if success? then
    IO.println  msg; return 0
  else
    IO.eprintln msg; return 1
