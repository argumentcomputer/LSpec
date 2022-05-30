inductive Rel (α : Type)
  | shouldBe [BEq α] (t : α)
  | hasProperty (p : α → Bool)

inductive LSpec
  | done
  | it (descr : String) (a : α) (rel : Rel α) (and : LSpec)
  deriving Inhabited

def Result.toMsg : String × Bool → String
  | (d, true)  => s!"✓ {d}"
  | (d, false) => s!"× {d}"

open LSpec Rel in
def runSpec (results : List (String × Bool)) : LSpec → List (String × Bool)
  | done => results.reverse
  | it d a rel and => match rel with
    | shouldBe b => (d, a == b) :: (runSpec results and)
    | hasProperty p => (d, p a) :: (runSpec results and)

def lspec (s : String) (t : LSpec) (_ : List String) : IO UInt32 := do
  IO.println s!"Testing that: {s}"
  let res := runSpec [] t
  let msg := "\n".intercalate $ res.map Result.toMsg
  if res.foldl (init := true) fun acc (_, r) => acc && r then
    IO.println msg
    return 0
  else
    IO.eprintln msg
    return 1
