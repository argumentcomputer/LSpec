import LSpec

#lspec do
  test "Nat equality" (4 = 4)
  test "Nat inequality" (4 ≠ 5)
  test "bool equality" (42 == 42)
  test "list length" ([42].length = 1)
  test "list nonempty" ¬ [42].isEmpty

#lspec
  test' "Nat equality" (4 = 4) $
  test' "Nat inequality" (4 ≠ 5) $
  test' "bool equality" (42 == 42) $
  test' "list length" ([42].length = 1) $
  test' "list nonempty" ¬ [42].isEmpty

/--
Testing using `#lspec` with something of type `LSpec`.
-/
private def test1 : LSpec := do
  test "Nat equality" <| 4 = 4
  test "Nat inequality" <| 4 ≠ 5
  test "bool equality" <| 42 == 42
  test "list length" <| [42].length = 1
  test "list nonempty" <| ¬ [42].isEmpty

#lspec test1

#eval lspec test1

/--
Testing using `#lspec` with something of type `LSpecTest`.
-/
private def test2 := test "true" true

#lspec test2

#lspec test "true" <| true

#lspec do
  test "a" <| 4 = 4
  test "b" <| 4 ≠ 5

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
