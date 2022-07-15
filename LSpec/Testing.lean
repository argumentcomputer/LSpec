import LSpec

#lspec
  test "Nat equality" (4 = 5) $
  test "Nat inequality" (4 ≠ 5) $
  test "bool equality" (42 == 42) $
  test "list length" ([42].length = 1) $
  test "list nonempty" ¬ [42].isEmpty

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

#eval lspec test1

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

#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
-- ✓ all lt

-- All tests succeeded

#lspec test "all lt" $ ∀ n, n < 15 → n - 10 = 0
-- × all lt
--   Fails on input 11. Expected to be equal:
--     1
--   and
--     0

def fourIO : IO Nat :=
  return 4

def fiveIO : IO Nat :=
  return 5

def main : IO UInt32 := do
  let four ← fourIO
  let five ← fiveIO
  lspec $
    test "fourIO equals 4" (four = 4) $
    test "fiveIO equals 5" (five = 5)

#eval main
-- ✓ fourIO equals 4
-- ✓ fiveIO equals 5
-- 0
