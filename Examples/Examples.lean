import LSpec

section LSpec
/- In this section we demonstrate the basic usage of `LSpec`. -/

open LSpec

/- The simplest way to invoke `LSpec` is in a file via the `#lspec` command -/
#lspec test "Nat equality" (4 ≠ 5)

/-
`#lspec` runs a sequence of tests which are encoded with the inductive type `TestSeq` which allows
for tests to be composable
-/
#lspec test "bool equality" (42 == 42) $
  test "list length" ([42].length = 2) $
  test "list nonempty" ¬ [42].isEmpty

/-
Tests that can be tested are of the `Testable` typeclass, which have a low-priority instance
`(p : Prop) : Decidable p → Testable p` which can be over-ridden to allow for more intricate
failure or success messages.

This instance is generic enough that tests like `∀ n, n < 10 → n - 5 < 5` can be evaluated
-/
#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5

/-
It is also possible to run tests inside the `IO` monad. The purpose of these tests is to plug in
`LSpec` into a testing script for a `lake script`
-/

def fourIO : IO Nat :=
  return 4

def fiveIO : IO Nat :=
  return 5

def main := do
  let four ← fourIO
  let five ← fiveIO
  lspecIO $
    test "fourIO equals 4" (four = 4) $
    test "fiveIO equals 5" (five = 5)

#eval main
-- ✓ fourIO equals 4
-- ✓ fiveIO equals 5
-- 0

/-
There are even more ways to invoke LSpec tests (`lspecEachIO` for example) for more intricate moandic
testing
 -/

end LSpec

section SlimCheck
/-
In this section we demonstrate the usage of `SlimCheck` in the Lspec library.
-/

open LSpec SlimCheck

/-
In this case `Nat` has a `SampleableExt` instance which allows the below examples to be run
-/
example : SampleableExt Nat := by infer_instance

/- SlimCheck tests are invoked with `check`, and are composable in the same way `test` is -/
#lspec check "add_comm" (∀ n m : Nat, n + m = m + n) $
       check "mul_comm" $ ∀ n m : Nat, n * m = m * m
-- ? add_comm
-- × mul_comm

-- ===================
-- Found problems!
-- n := 1
-- m := 2
-- issue: 2 = 4 does not hold
-- (2 shrinks)
-- -------------------
/-
We can also apply Slimcheck to custom structures if we define the appropriate instances
-/
structure Pairs where
  left : Nat
  right : Nat
deriving Repr

private def mkPairs (as : List α) (bs : List β) : List (α × β) :=
  let mkPairsAux (a : α) (bs : List β) : List (α × β) := bs.map fun b => (a, b)
  as.foldl (fun abs a => mkPairsAux a bs ++ abs) []

/- An instance of `Shrinkable` is needed -/
open Shrinkable in
instance : Shrinkable Pairs where
  shrink := fun p =>
    let shrinkl := shrink p.left
    let shrinkr := shrink p.right
    mkPairs shrinkl shrinkr |>.map fun (a, b) => ⟨a, b⟩

/-
As is one for `SampleableExt`.

In both of these cases we are using the instances already written for more primitive types like
`Nat`, but it's possible to write a these instances by hand if we want more fine-grained behavior.
-/
open SampleableExt

def pairsGen : Gen Pairs := return ⟨← Gen.chooseAny Nat, ← Gen.chooseAny Nat⟩

/-
To generate the instance of `SampleableExt α` we use the `mkSelfContained` function which relies only
on having a `Gen α`.

It is possible to define more tailored instances of `SampleableExt` by writing it by hand.
-/
instance : SampleableExt Pairs := mkSelfContained pairsGen

/- Now we can conduct the tests just as we did before for `Nat` -/
#lspec check "left + 2 is less than right" $ ∀ pair : Pairs, pair.left + 2 ≤ pair.right

/-
You always have to be careful with your implementation for `shrink` and `SampleableExt` because
Slimcheck may not flag tests that should fail, in this case `⟨0, 0⟩` should fail the test but
isn't detected
-/
#lspec check "left + right > right" $ ∀ pair : Pairs, pair.left + pair.right > pair.right

end SlimCheck
