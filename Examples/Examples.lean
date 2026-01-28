import LSpec

/-!
# LSpec Examples

This file provides comprehensive examples of using LSpec for testing in Lean 4.

## Quick Reference

| Function | Use Case | Output |
|----------|----------|--------|
| `test` | Unit tests | `✓ ∃: name` |
| `check` | Property tests (simple) | `✓ ∃: name` |
| `check'` | Property tests (with syntax) | `✓ ∃₁₀₀: "name" (property)` |
| `checkIO` | Runtime property tests | Same as check |
| `checkIO'` | Runtime tests (with syntax) | Same as check' |
-/

section LSpec

open LSpec

/-! ## Basic Usage

The simplest way to run tests is with the `#lspec` command.
-/

#lspec test "Nat equality" (4 ≠ 5)
-- ✓ ∃: Nat equality

/-!
Tests can be composed into sequences using `$` or `++`.
The output shows `✓ ∃:` for each passing unit test.
-/

#lspec test "bool equality" (42 == 42) $
  test "list length" ([42].length = 2) $    -- This fails
  test "list nonempty" ¬ [42].isEmpty
-- ✓ ∃: bool equality
-- × ∃: list length
--     Expected to be equal: '1' and '2'
-- ✓ ∃: list nonempty

/-!
## Bounded Universal Quantification

Tests like `∀ n, n < 10 → P n` are automatically iterated.
-/

#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
-- ✓ ∃: all lt

/-!
## IO-based Tests

For runtime tests, use `lspecIO` with a HashMap of test suites.
-/

def fourIO : IO Nat := return 4
def fiveIO : IO Nat := return 5

def main := do
  let four ← fourIO
  let five ← fiveIO
  lspecIO (.ofList [("IO tests", [
    test "fourIO equals 4" (four = 4) $
    test "fiveIO equals 5" (five = 5)])]) []

#eval main
-- IO tests
--   ✓ ∃: fourIO equals 4
--   ✓ ∃: fiveIO equals 5
-- 0

end LSpec

section SlimCheck
/-!
## Property-Based Testing with SlimCheck

SlimCheck generates random test cases to verify properties.
The output shows how many samples were tested.

### Basic Property Tests

Use `check` for simple output or `check'` to see the property syntax.
-/

open LSpec SlimCheck

-- Nat has a SampleableExt instance for random generation
example : SampleableExt Nat := by infer_instance

/-!
### Using `check'` (Recommended)

The `check'` macro captures the property syntax for display:
- Success shows: `✓ ∃₁₀₀: "name" (∀ n m : Nat, n + m = m + n)`
- Failure shows: `× ∃²/₁₀₀: "name" (property)` with counterexample

The superscript indicates which sample failed, subscript shows total samples.
-/

#lspec check' "add_comm" (∀ n m : Nat, n + m = m + n)
-- ✓ ∃₁₀₀: "add_comm" (∀ n m : Nat, n + m = m + n)

#lspec check' "mul_comm_wrong" (∀ n m : Nat, n * m = m * m)
-- × ∃⁶/₁₀₀: "mul_comm_wrong" (∀ n m : Nat, n * m = m * m)
--     ===================
--     Found problems!
--     n := 1
--     m := 2
--     issue: 2 = 4 does not hold
--     (2 shrinks)
--     -------------------

/-!
### Custom Types with SlimCheck

To use SlimCheck with custom types, define `Shrinkable` and `SampleableExt` instances.
-/

structure Pairs where
  left : Nat
  right : Nat
deriving Repr

private def mkPairs (as : List α) (bs : List β) : List (α × β) :=
  let mkPairsAux (a : α) (bs : List β) : List (α × β) := bs.map fun b => (a, b)
  as.foldl (fun abs a => mkPairsAux a bs ++ abs) []

-- Shrinkable instance for reducing counterexamples
open Shrinkable in
instance : Shrinkable Pairs where
  shrink := fun p =>
    let shrinkl := shrink p.left
    let shrinkr := shrink p.right
    mkPairs shrinkl shrinkr |>.map fun (a, b) => ⟨a, b⟩

-- SampleableExt instance for random generation
open SampleableExt

def pairsGen : Gen Pairs := return ⟨← Gen.chooseAny Nat, ← Gen.chooseAny Nat⟩

instance : SampleableExt Pairs := mkSelfContained pairsGen

-- Now we can test properties over Pairs
#lspec check' "left + 2 ≤ right" (∀ pair : Pairs, pair.left + 2 ≤ pair.right)
-- × ∃¹/₁₀₀: "left + 2 ≤ right" (∀ pair : Pairs, pair.left + 2 ≤ pair.right)
--     ===================
--     Found problems!
--     pair := { left := 0, right := 1 }
--     issue: 2 ≤ 1 does not hold
--     ...

-- This passes (but note: ⟨0, 0⟩ would fail, showing shrink limitations)
#lspec check' "left + right > right" (∀ pair : Pairs, pair.left + pair.right > pair.right)
-- ✓ ∃₁₀₀: "left + right > right" (∀ pair : Pairs, pair.left + pair.right > pair.right)

/-!
### Weighted Random Generation with Gen.frequency

`Gen.frequency` creates weighted random generators for more realistic test data.
-/

inductive Command where
  | noop
  | read
  | write
  | delete
deriving Repr, DecidableEq

/--
Weighted command generator:
- noop: 10%, read: 50%, write: 30%, delete: 10%
-/
def commandGen : Gen Command :=
  Gen.frequency #[
    (1, pure Command.noop),
    (5, pure Command.read),
    (3, pure Command.write),
    (1, pure Command.delete)
  ] (pure Command.noop)

instance : Shrinkable Command where
  shrink := fun _ => []

instance : SampleableExt Command := mkSelfContained commandGen

#lspec check' "commands are valid" (∀ cmd : Command,
  cmd = Command.noop ∨ cmd = Command.read ∨ cmd = Command.write ∨ cmd = Command.delete)
-- ✓ ∃₁₀₀: "commands are valid" (∀ cmd : Command, ...)

/-!
### Biased Number Generation

Generate numbers with custom distributions.
-/

def biasedSmallGen : Gen Nat :=
  Gen.frequency #[
    (5, Gen.choose Nat 0 10),     -- 50%: small (0-10)
    (3, Gen.choose Nat 11 100),   -- 30%: medium (11-100)
    (2, Gen.choose Nat 101 1000)  -- 20%: larger (101-1000)
  ] (pure 0)

structure BiasedNat where
  val : Nat
deriving Repr

instance : Shrinkable BiasedNat where
  shrink := fun n => (Shrinkable.shrink n.val).map BiasedNat.mk

instance : SampleableExt BiasedNat := mkSelfContained (BiasedNat.mk <$> biasedSmallGen)

#lspec check' "biased numbers bounded" (∀ n : BiasedNat, n.val ≤ 1000)
-- ✓ ∃₁₀₀: "biased numbers bounded" (∀ n : BiasedNat, n.val ≤ 1000)

end SlimCheck
