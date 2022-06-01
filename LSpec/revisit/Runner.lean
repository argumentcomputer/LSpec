import LSpec.revisit.Spec
import LSpec.revisit.Meta
import LSpec.revisit.WriterT
import LSpec.revisit.Tree

/-
Structure for a test item in a test suite. Contains everything needed to run a test.
We need to store the type of the specification target and the target
itself because the specification depends on them.
-/
structure Item where
  -- The type of the target of the specification
  α : Type
  -- The specification target
  s : α
  -- The specification
  spec : SpecOn s
  -- An runnable example for the specification
  examp : ExampleOf spec

/-
A tree of test items. Each node has a description.
This tree is used to define test suites.
-/
def SpecTree := Tree String Item
-- A monad for constructing test suites.
def SpecM := Writer (List SpecTree)
  deriving Monad
def Spec := SpecM Unit

/-
Adds a test item to the test suite.
-/
def it {α : Type} {a : α} (spec : SpecOn a) (t : ExampleOf spec) : SpecM Unit :=
  let item : Item := ⟨α, a, spec, t⟩
  tell [Tree.leaf item]

/-
Like `it`, but takes the spec as an implicit argument. Useful for
when the example syntax from Meta.lean is used. That gives us
an `ExampleOf` from which `spec` can be inferred.
-/
def it' {α : Type} {a : α} {spec : SpecOn a} (t : ExampleOf spec) : SpecM Unit := it spec t

/-
Combines a list of test items (represented with `SpecM` monad) into a single branch.
-/
def describe {α : Type u} (s : String) (m : SpecM α) : SpecM α := do
  tell [Tree.node s m.run]
  pure m.fst

/-
Indents a string by prepending it with spaces.
-/
def indentString (n : Nat) (s : String) : String :=
  ⟨List.replicate n ' '⟩ ++ s

/-
A collection of pretty printing functions for the test tree.
We're printing each test item separately instead of constructing
a string for the entire tree because certain test items can
potentially run for a long time.
-/
def printLeaf (indent : Nat) (i : Item) :=
  IO.println ∘ indentString (indent*2) $
    let ⟨descr, res, str⟩ := i.examp.run
    match descr with
    | .none => str
    | .some descr => descr ++ ": " ++ str

def printNode (indent : Nat) (t : String) := IO.println ∘ indentString (indent*2) $ t

def printTree (t : SpecTree) : IO Unit := traverseTree 0 printLeaf printNode t

/-
Runs a test spec, printing the results.
-/
def Spec.run (spec : Spec) : IO Unit :=
  let forest := Writer.run spec
  for t in forest do
    printTree t
