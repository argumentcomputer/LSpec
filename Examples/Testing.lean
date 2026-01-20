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

-- Testing a test group. Indents are important!
def tGroup : TestSeq := group "test group test" $
  test "Nat inequality" (4 ≠ 5) $
  test "Nat inequality" (3 ≠ 5) $
  test "Nat equality" (42 == 42)

#lspec (tGroup ++ tGroup ++ test "Nat equality" (42 = 42))
#lspec (
  test "Nat equality" (42 = 42) $
  group "manual group" (
    test "Nat equality inside group" (4 = 4)) $
  tGroup
  )

-- Testing describe/context aliases (hspec-style grouping)
section describe_context_tests

/-- Using `describe` for component-level organization -/
def parserTests : TestSeq :=
  describe "Parser" $
    context "when parsing numbers" $
      test "parses single digits" (true) $
      test "parses multi-digit numbers" (true) $
    context "when parsing strings" $
      test "handles empty strings" (true) $
      test "handles quoted strings" (true)

#lspec parserTests
-- Parser:
--   when parsing numbers:
--     ✓ parses single digits
--     ✓ parses multi-digit numbers
--   when parsing strings:
--     ✓ handles empty strings
--     ✓ handles quoted strings

/-- Nested describe/context blocks -/
def mathTests : TestSeq :=
  describe "Math operations" $
    describe "Addition" $
      test "0 + n = n" (0 + 5 = 5) $
      test "commutativity" (3 + 4 = 4 + 3) $
    describe "Multiplication" $
      test "0 * n = 0" (0 * 5 = 0) $
      test "1 * n = n" (1 * 5 = 5)

#lspec mathTests

/-- Mixing describe, context, and group -/
def mixedGrouping : TestSeq :=
  describe "List operations" $
    context "with empty list" $
      test "length is 0" (([] : List Nat).length = 0) $
      test "isEmpty is true" (([] : List Nat).isEmpty) $
    group "non-empty list tests" $
      test "length is positive" ([1,2,3].length > 0)

#lspec mixedGrouping

end describe_context_tests

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
    tGroup ++ (
    test "fourIO equals 4" (four = 4) $
    test "fiveIO equals 5" (five = 5))

#eval main
-- ✓ fourIO equals 4
-- ✓ fiveIO equals 5
-- 0

#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
-- ✓ all lt

#lspec test "all lt" $ ∀ n, n < 15 → n - 10 = 0
-- × all lt
--     Fails on input 11. Expected to be equal: '1' and '0'

section slimcheck_tests

#lspec check "add_comm" (∀ n m : Nat, n + m = m + n)
-- ? add_comm

#lspec check "add_comm" (∀ n m : Nat, n + m = m + m) $ check "mul_comm" $ ∀ n m : Nat, n * m = m * n
-- × add_comm

-- ===================
-- Found problems!
-- n := 1
-- m := 0
-- issue: 1 = 0 does not hold
-- (0 shrinks)
-------------------
-- ? mul_comm

end slimcheck_tests
