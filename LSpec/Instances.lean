module
public import LSpec.LSpec

/-!
# Testable Instances

This module provides `Testable` instances for common types, enabling
LSpec to test equality, inequality, and bounded quantification directly.

## Provided Instances

- `Testable (x = y)` for `DecidableEq` types
- `Testable (x == y)` for `BEq` types
- `Testable (x ≠ y)` for `DecidableEq` types
- `Testable (x != y)` for `BEq` types
- `Testable (∀ n, n < b → p n)` for bounded natural number quantification
-/

namespace LSpec
public section

/-- Testable instance for decidable equality. -/
instance (priority := 50) (x y : α) [DecidableEq α] [Repr α] : Testable (x = y) :=
  if h : x = y then
    .isTrue h
  else
    .isFalse h 0 0 $ s!"Expected to be equal: '{repr x}' and '{repr y}'"

/-- Testable instance for boolean equality. -/
instance (priority := 50) (x y : α) [BEq α] [Repr α] : Testable (x == y) :=
  if h : x == y then
    .isTrue h
  else
    .isFalse h 0 0 $ s!"Expected to be equal: '{repr x}' and '{repr y}'"

/-- Testable instance for decidable inequality. -/
instance (priority := 50) (x y : α) [DecidableEq α] [Repr α] : Testable (x ≠ y) :=
  if h : x ≠ y then
    .isTrue h
  else
    .isFalse h 0 0 s!"Expected to be different but both equal to '{repr x}'"

/-- Testable instance for boolean inequality. -/
instance (priority := 50) (x y : α) [BEq α] [Repr α] : Testable (x != y) :=
  if h : x != y then
    .isTrue h
  else
    .isFalse h 0 0 s!"Expected to be different but both equal to '{repr x}'"

/--
Testable instance for bounded universal quantification over natural numbers.

This enables tests like:
```lean
#lspec test "all small" $ ∀ n, n < 10 → n * n < 100
```

The bound `b` determines how many values are tested (0 to b-1).
If any value fails, the output shows which input caused the failure.
-/
instance Nat.Testable_forall_lt
  (b : Nat) (p : Nat → Prop)
  [d : (n : Nat) → Testable (p n)] :
    Testable (∀ n, n < b → p n) :=
  match b with
  | 0     => .isTrue (by simp [Nat.not_lt_zero])
  | b + 1 =>
    match Testable_forall_lt b p with
    | .isTrue h =>
      match d b with
      | .isTrue hb =>
        .isTrue $ by
          intros n hn
          cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hn) with
          | inl hl => cases hl; assumption
          | inr => apply h; assumption
      | .isPassed numSamples msg => .isPassed numSamples msg
      | .isMaybe msg => .isMaybe msg
      | .isFalse hb failedAt totalTests msg =>
        .isFalse (λ h => hb (h _ (Nat.lt_succ_self _))) failedAt totalTests $
          match msg with
          | some msg => s!"Fails on input {b}. {msg}"
          | none     => s!"Fails on input {b}."
      | .isFailure failedAt totalTests msg => .isFailure failedAt totalTests msg
    | .isPassed numSamples msg => .isPassed numSamples msg
    | .isMaybe msg => .isMaybe msg
    | .isFalse h failedAt totalTests msg => .isFalse (λ h' => h λ n hn => h' _ (Nat.le_succ_of_le hn)) failedAt totalTests msg
    | .isFailure failedAt totalTests msg => .isFailure failedAt totalTests msg

end
end LSpec
