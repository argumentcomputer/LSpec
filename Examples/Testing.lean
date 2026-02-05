import LSpec

/-!
# LSpec Testing Examples

This file demonstrates the various testing capabilities of LSpec,
including unit tests, property-based tests, and output formatting.

## Output Format

LSpec uses logical quantifier notation to clearly indicate the verification level:

- `✓ ∃:` - Unit test passed (verified a single specific case)
- `✓ ∀:` - Property test with formal proof (universal quantification proven)
- `✓ ∃ₙ:` - Property test passed n samples without formal proof
- `× ∃ⁿ/ₘ:` - Property test failed on sample n of m total

The `check'` and `checkIO'` macros capture the property syntax for display,
producing richer output like: `✓ ∃₁₀₀: "name" (∀ n m : Nat, n + m = m + n)`
-/

open LSpec

/-! ## Unit Tests

Unit tests verify specific decidable propositions. They use `∃:` notation
because we're verifying the existence of a specific case that holds.
-/

#lspec
  test "Nat equality" (4 = 5) $      -- This will fail
  test "Nat inequality" (4 ≠ 5) $    -- ✓ ∃: Nat inequality
  test "bool equality" (42 == 42) $  -- ✓ ∃: bool equality
  test "list length" ([42].length = 1) $
  test "list nonempty" ¬ [42].isEmpty

/-! ## Test Groups

Tests can be organized into groups using `group`, `describe`, or `context`.
These are aliases that help document intent:
- `describe`: for describing a component being tested
- `context`: for describing circumstances under which tests run
- `group`: general-purpose grouping
-/

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

/-! ## Describe/Context Style (Hspec-inspired)

Using `describe` for component-level and `context` for circumstance-level
organization creates readable, hierarchical test output.
-/
section describe_context_tests

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
--     ✓ ∃: parses single digits
--     ✓ ∃: parses multi-digit numbers
--     when parsing strings:
--       ✓ ∃: handles empty strings
--       ✓ ∃: handles quoted strings

def mathTests : TestSeq :=
  describe "Math operations" $
    describe "Addition" $
      test "0 + n = n" (0 + 5 = 5) $
      test "commutativity" (3 + 4 = 4 + 3) $
    describe "Multiplication" $
      test "0 * n = 0" (0 * 5 = 0) $
      test "1 * n = n" (1 * 5 = 5)

#lspec mathTests

def mixedGrouping : TestSeq :=
  describe "List operations" $
    context "with empty list" $
      test "length is 0" (([] : List Nat).length = 0) $
      test "isEmpty is true" (([] : List Nat).isEmpty) $
    group "non-empty list tests" $
      test "length is positive" ([1,2,3].length > 0)

#lspec mixedGrouping

end describe_context_tests

/-! ## Basic Test Definitions -/

def test1 : TestSeq :=
  test "Nat equality" (4 = 4) $
  test "Nat inequality" (4 ≠ 5) $
  test "bool equality" (42 == 42) $
  test "list length" ([42].length = 1) $
  test "list nonempty" ¬ [42].isEmpty

#lspec test1

-- Running tests via lspecIO for runtime execution
#eval lspecIO (.ofList [("test1", [test1])]) []

def test2 := test "true" true

#lspec test2
#lspec test "true" <| true

#lspec
  test "a" (4 = 4) $
  test "b" (4 ≠ 5)

#lspec
  test "array eq" <| #[1,2,3] = (List.range 3).toArray
-- × ∃: array eq
--     Expected to be equal: '#[1, 2, 3]' and '#[0, 1, 2]'

/-! ## IO-based Tests

For tests that require IO operations (file reading, network, etc.),
use `lspecIO` with a HashMap of test suites.
-/

def fourIO : IO Nat := return 4
def fiveIO : IO Nat := return 5

def main := do
  let four ← fourIO
  let five ← fiveIO
  lspecIO (.ofList [("IO tests", [
    tGroup ++ (
    test "fourIO equals 4" (four = 4) $
    test "fiveIO equals 5" (five = 5))])]) []

#eval main

/-! ## Bounded Universal Quantification

LSpec supports bounded quantification with automatic iteration.
-/

#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
-- ✓ ∃: all lt

#lspec test "all lt" $ ∀ n, n < 15 → n - 10 = 0
-- × ∃: all lt
--     Fails on input 11. Expected to be equal: '1' and '0'

/-! ## Property-Based Testing with SlimCheck

Property tests use random sampling to verify properties over many inputs.

### Using `check'` (with syntax capture)

The `check'` macro captures the property syntax for display:
- Success: `✓ ∃₁₀₀: "name" (∀ n m : Nat, n + m = m + n)`
- Failure: `× ∃²/₁₀₀: "name" (∀ n m : Nat, n + m = m + m)`

The subscript shows samples tested, superscript shows which sample failed.
-/

section slimcheck_tests

-- Property test with syntax capture - shows the property in output
#lspec check' "add_comm" (∀ n m : Nat, n + m = m + n)
-- ✓ ∃₁₀₀: "add_comm" (∀ n m : Nat, n + m = m + n)

-- Test that fails - shows which sample failed (superscript) out of total (subscript)
#lspec check' "add_fails" (∀ n m : Nat, n + m = m + m)
-- × ∃²/₁₀₀: "add_fails" (∀ n m : Nat, n + m = m + m)
--     ===================
--     Found problems!
--     n := 1
--     m := 0
--     ...

-- Chaining property tests
def slimTests : TestSeq :=
  let t1 : TestSeq := check' "mul_comm" (∀ n m : Nat, n * m = m * n)
  let t2 : TestSeq := check' "add_zero" (∀ n : Nat, n + 0 = n)
  t1 ++ t2

#lspec slimTests
-- ✓ ∃₁₀₀: "mul_comm" (∀ n m : Nat, n * m = m * n)
-- ✓ ∃₁₀₀: "add_zero" (∀ n : Nat, n + 0 = n)

-- Standard check (without syntax capture) - simpler output
#lspec check "standard_check" (∀ n m : Nat, n + m = m + n)
-- ✓ ∃: standard_check

end slimcheck_tests
