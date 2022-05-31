/-
A very simple Writer monad as Lean standard library doesn't have one.
-/
def Writer (ε : Type u) (α : Type w) := α × ε


-- Append and EmptyCollection instead of Monoid because there's
-- no Monoid type class in the standard library.
instance [Append ε] [EmptyCollection ε] : Monad (Writer ε) where
  pure x := ⟨ x, EmptyCollection.emptyCollection ⟩
  bind x f :=
    let (a, e1) := x
    let (b, e2) := f a
    (b, e1 ++ e2)

/-
Write a value to the Writer monad.
-/
def tell {ε : Type u} (e : ε) : Writer ε PUnit :=
  ⟨PUnit.unit, e⟩

/-
Run a Writer action and return the result plus the output of the Writer.
-/
def listen {ε : Type u} {α : Type v} (x : Writer ε α) : Writer ε (α × ε) :=
  let (a, e) := x
  ((a, e), e)

/-
Run a Writer action and return the written output.
-/
def Writer.run {ε : Type u} {α : Type v} (x : Writer ε α) : ε := x.snd

/-
structure WriterT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) where
  run: m (α × ε)

def listen {ε : Type u} {m : Type u → Type v} [Monad.{u, v} m] [EmptyCollection.{u} ε] {α : Type u} (f : WriterT.{u,v} ε m α) : WriterT ε m (a × ε) := sorry

instance [Monad m] : Functor (WriterT ε m) where
  map f x := ⟨do
    let (a, e) ← x.run
    pure (f a, e) ⟩

instance [Append ε] [EmptyCollection ε] [Monad m] : Monad (WriterT ε m) where
  pure x := ⟨pure ⟨x, EmptyCollection.emptyCollection⟩⟩
  bind x f := ⟨do
    let (a, e1) ← x.run
    have go := f a -- if I change this 'have' to 'let' it asks me to implement map for the instance. I don't know why.
    let (b, e2) ← go.run
    pure ⟨b, e2⟩
  ⟩

instance [EmptyCollection ε] [Monad m] : MonadLiftT m (WriterT ε m) where
  monadLift m := ⟨do
    let v ← m
    pure ⟨v, EmptyCollection.emptyCollection⟩⟩

def tell [Monad m] (e : ε) : WriterT ε m Unit := ⟨pure ⟨(), e⟩⟩
-/