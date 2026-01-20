/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import LSpec.SlimCheck.Control.Random

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
  fun _ => rand α

/-- Lift `BoundedRandom.randomR` to the `Gen` monad. -/
def choose (α : Type u) [Random α] (lo hi : α) : Gen α :=
  fun _ => randBound α lo hi

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

/-- Given an array of example generators, choose one to create an example. -/
def oneOf [Inhabited α] (xs : Array (Gen α)) : Gen α := do
  let i ← choose Nat 0 (xs.size - 1)
  if h : i < xs.size then
    xs[i]
  else -- The array is empty
    pure default

/-- Choose from generators with weighted probability.
    Each pair is (weight, generator). Higher weights are more likely to be chosen.

    Example:
    ```
    Gen.frequency #[(1, pure 0), (9, choose Nat 1 100)] (pure 0)  -- 10% zeros, 90% 1-100
    ```
-/
def frequency (weighted : Array (Nat × Gen α)) (fallback : Gen α) : Gen α := do
  if weighted.isEmpty then
    fallback
  else
    let totalWeight := weighted.foldl (fun acc (w, _) => acc + w) 0
    if totalWeight == 0 then
      fallback
    else
      let choice ← choose Nat 0 (totalWeight - 1)
      let mut cumulative := 0
      for (weight, gen) in weighted do
        cumulative := cumulative + weight
        if choice < cumulative then
          return ← gen
      -- Fallback (should not reach here)
      fallback

/-- Given an array of examples, choose one. -/
def elements [Inhabited α] (xs : Array α) : Gen α := do
  let i ← choose Nat 0 (xs.size - 1)
  if h : i < xs.size then
    return xs[i]
  else -- The array is empty
    pure default

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
