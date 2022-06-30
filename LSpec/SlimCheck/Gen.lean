/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import LSpec.Control.Random

/-!
# `Gen` Monad
This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.
This is a port of the Haskell QuickCheck library.
## Main definitions
  * `Gen` monad
## Tags
random testing
## References
  * https://hackage.haskell.org/package/QuickCheck
-/

namespace SlimCheck

open Random

/-- Monad to generate random examples to test properties with.
It has a `Nat` parameter so that the caller can decide on the
size of the examples. -/
abbrev Gen (α : Type u) := ReaderT (ULift Nat) Rand α

namespace Gen

/-- Lift `Random.random` to the `Gen` monad. -/
def chooseAny (α : Type u) [Random α] [DefaultRange α] : Gen α :=
  λ _ => rand α

/-- Lift `BoundedRandom.randomR` to the `Gen` monad. -/
def choose (α : Type u) [Random α] (lo hi : α) : Gen α :=
  λ _ => randBound α lo hi

/-- Generate a `Nat` example between `x` and `y` (exclusively). -/
def chooseNatLt (lo hi : Nat) : Gen Nat :=
  choose Nat (lo.succ) hi

/-- Get access to the size parameter of the `Gen` monad. -/
def getSize : Gen Nat :=
  return (← read).down

/-- Apply a function to the size parameter. -/
def resize (f : Nat → Nat) (x : Gen α) : Gen α :=
  withReader (ULift.up ∘ f ∘ ULift.down) x

/-- Create an `Array` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def arrayOf (x : Gen α) : Gen (Array α) := do
  let sz ← choose Nat 0 (← getSize)
  let mut res := #[]
  for _ in [0:sz] do
    res := res.push (← x)
  pure res

/-- Create an `List` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def listOf (x : Gen α) : Gen (List α) :=
  arrayOf x >>= pure ∘ Array.toList

/-- Given a list of example generators, choose one to create an example. -/
def oneOf [Inhabited α] (xs : Array (Gen α)) : Gen α := do
  let x ← chooseNatLt 0 xs.size
  xs.get! x

/-- Given a list of examples, choose one to create an example. -/
def elements [Inhabited α] (xs : List α) : Gen α := do
  let x ← chooseNatLt 0 xs.length
  pure $ xs.get! x

open List in
/-- Generate a random permutation of a given list. -/
def permutationOf : (xs : List α) → Gen (List α)
| [] => pure []
| x::xs => do
  let ys ← permutationOf xs
  let n ← choose Nat 0 ys.length
  pure $ ys.take n ++ [x] ++ ys.drop n

/-- Given two generators produces a tuple consisting out of the result of both -/
def prodOf {α β : Type u} (x : Gen α) (y : Gen β) : Gen (α × β) := do
  pure (←x, ←y)

end Gen

/-- Execute a `Gen` inside the `IO` monad using `size` as the example size-/
def Gen.run (x : Gen α) (size : Nat) : BaseIO α :=
  IO.runRand $ ReaderT.run x ⟨size⟩

end SlimCheck