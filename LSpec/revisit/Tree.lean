/-
A simple tree data structure where both leaves and internal nodes have some
data attached.
-/
inductive Tree (τ : Type u) (α : Type v) where
  -- A tree leaf, contains α
  | leaf : α → Tree τ α
  -- A tree node. Contains τ and a list of children.
  | node : τ → List (Tree τ α) → Tree τ α
  deriving Repr

/-
A function that traverses a tree. Takes two functions: one that is
applied on leaves and another one that is applied on nodes.
-/
def traverseTree {α : Type u} {τ : Type v} [Monad m] (n : Nat) (leafF : Nat → α → m Unit) (nodeF : Nat → τ → m β) : Tree τ α → m Unit
  | .leaf x => leafF n x
  | .node t xs => do
    let b ← nodeF n t
    for x in xs do
      traverseTree (n+1) leafF nodeF x
decreasing_by sorry -- FIXME: Lean is not convinced that this function terminates and I couldn't prove it, so here's this stub for now.
