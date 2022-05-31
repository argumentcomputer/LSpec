import Lean

abbrev Rel (α : Type _) := α → Bool

inductive LSpec
  | done
  | more (descr : String) (a : α) (rel : Rel α) (and : LSpec)
  deriving Inhabited

def it (descr : String) (a : α) (rel : Rel α) (and : LSpec := LSpec.done) :=
  LSpec.more descr a rel and

def printMsg : String × Bool → String
  | (d, true)  => s!"✓ it {d}"
  | (d, false) => s!"× it {d}"

def runLSpec (results : List (String × Bool)) : LSpec → List (String × Bool)
  | .more d a rel and => (d, rel a) :: (runLSpec results and)
  | .done             => results.reverse

def compileLSpecResult (t : LSpec) : Bool × String :=
  let res := runLSpec [] t
  (res.foldl (init := true) fun acc (_, r) => acc && r,
    "\n".intercalate $ res.map printMsg)

def lspec (s : String) (t : LSpec) (_ : List String) : IO UInt32 := do
  IO.println s!"Testing that: {s}"
  let (success?, msg) := compileLSpecResult t
  if success?
    then IO.println  msg; return 0
    else IO.eprintln msg; return 1
