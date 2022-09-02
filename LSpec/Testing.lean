import LSpec

open LSpec 

#lspec
  test "Nat equality" (4 = 5) $
  test "Nat inequality" (4 ≠ 5) $
  test "bool equality" (42 == 42) $
  test "list length" ([42].length = 1) $
  test "list nonempty" ¬ [42].isEmpty
-- × Nat equality
--     Expected to be equal: '4' and '5'
-- ✓ Nat inequality
-- ✓ bool equality
-- ✓ list length
-- ✓ list nonempty

/--
Testing using `#lspec` with something of type `LSpec`.
-/
def test1 : TestSeq :=
  test "Nat equality" (4 = 4) $
  test "Nat inequality" (4 ≠ 5) $
  test "bool equality" (42 == 42) $
  test "list length" ([42].length = 1) $
  test "list nonempty" ¬ [42].isEmpty

#lspec test1

#eval lspecIO test1

/--
Testing using `#lspec` with something of type `LSpecTest`.
-/
def test2 := test "true" true

#lspec test2

#lspec test "true" <| true

#lspec
  test "a" (4 = 4) $
  test "b" (4 ≠ 5)

#lspec
  test "array eq" <| #[1,2,3] = (List.range 3).toArray
-- × array eq
--     Expected to be equal: '#[1, 2, 3]' and '#[0, 1, 2]'


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

section slimcheck_tests
/-
In this section we demonstrate the usage of `SlimCheck` in the Lspec library.
-/

open SlimCheck
/-
In this case `Nat` has a `SampleableExt` instance which allows the below examples to be run
-/
example : SampleableExt Nat := by infer_instance

#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
-- ✓ all lt

#lspec test "all lt" $ ∀ n, n < 15 → n - 10 = 0
-- × all lt
--     Fails on input 11. Expected to be equal: '1' and '0'

/-
For Slimcheck tests `check` is a synonym for `test`. 
-/
#lspec check "add_comm" $ ∀ n m : Nat, n + m = m + n

#lspec check "add_comm" $ ∀ n m : Nat, n + m = m + m
-- × add_comm

-- ===================
-- Found problems!
-- n := 1
-- m := 0
-- issue: 1 = 0 does not hold
-- (0 shrinks)
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

/- Now we can conduct the tests just as we did before -/
#lspec check "left + 2 is less than right" $ ∀ pair : Pairs, pair.left + 2 ≤ pair.right

end slimcheck_tests