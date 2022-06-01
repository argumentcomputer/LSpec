import Lean

abbrev Rel (α : Type _) := α → Bool 

/-- 
The basic structure used to encode specifications. 
It represents a list of tests, with each test consisting of 
a description `descr`, some value `a`, and a test `rel` for `a`.
-/
inductive LSpec
  | done
  | more (descr : String) (a : α) (rel : Rel α) (next : LSpec)
  deriving Inhabited

/-- 
`it` adds a single test to the testing suite.
This is the same as the projection `LSpec.more`, but extracting it out 
allows us to set `next` with the default value `done`.
-/
def it (descr : String) (a : α) (rel : Rel α) (next : LSpec := LSpec.done) :=
  LSpec.more descr a rel next

/-- 
Prints the result of a test.
-/
def printMsg : String × Bool → String
  | (d, true)  => s!"✓ it {d}"
  | (d, false) => s!"× it {d}"

/--
Runs a set of `LSpec` tests and appends the results to 
another list of results (given as input by the caller).
-/
def runLSpec (results : List (String × Bool)) : LSpec → List (String × Bool)
  | .more d a rel next => (d, rel a) :: (runLSpec results next)
  | .done              => results.reverse

/--
Generates a report for all the results in a `LSpec` test,
returning `true` if all tests passed and `false` otherwise.
-/
def compileLSpecResult (t : LSpec) : Bool × String :=
  let res := runLSpec [] t
  (res.foldl (init := true) fun acc (_, r) => acc && r,
    "\n".intercalate $ res.map printMsg)

/-- 
Runs a `LSpec` test and pretty prints the results.
-/
def lspec (s : String) (t : LSpec) (_ : List String) : IO UInt32 := do
  IO.println s!"Testing that: {s}"
  let (success?, msg) := compileLSpecResult t
  if success?
    then IO.println  msg; return 0
    else IO.eprintln msg; return 1
