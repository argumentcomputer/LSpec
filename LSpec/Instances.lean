import LSpec.LSpec

instance (priority := 50) (x y : α) [DecidableEq α] [Repr α] : TDecidable (x = y) :=
  if h : x = y then
    .isTrue h
  else
    .isFalse h $ formatExpectedButGotMsg x y

instance (priority := 50) (x y : α) [BEq α] [Repr α] : TDecidable (x == y) :=
  if h : x == y then
    .isTrue h
  else
    .isFalse h $ formatExpectedButGotMsg x y

instance (priority := 50) (x y : α) [DecidableEq α] [Repr α] : TDecidable (x ≠ y) :=
  if h : x ≠ y then
    .isTrue h
  else
    .isFalse h s!"Expected to be different but both equal to '{repr x}'"

instance (priority := 50) (x y : α) [BEq α] [Repr α] : TDecidable (x != y) :=
  if h : x != y then
    .isTrue h
  else
    .isFalse h s!"Expected to be different but both equal to '{repr x}'"

/--
A fancier example of `TDecidable` instance that allows us to write:

```lean
#lspec test "forall n < 10, n - 5 < 5" $ ∀ n, n < 10 → n - 5 < 5
```
-/
instance Nat.tdecidable_forall_lt
  (b : Nat) (p : Nat → Prop)
  [d : (n : Nat) → TDecidable (p n)] :
    TDecidable (∀ n, n < b → p n) :=
  match b with
  | 0     => .isTrue (by simp [Nat.not_lt_zero])
  | b + 1 =>
    match tdecidable_forall_lt b p with
    | .isTrue h =>
      match d b with
      | .isTrue hb =>
        .isTrue $ by
          intros n hn
          cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hn) with
          | inl hl => cases hl; assumption
          | inr => apply h; assumption
      | .isFalse hb msg =>
        .isFalse (λ h => hb (h _ (Nat.lt_succ_self _))) $
          match msg with
          | some msg => s!"Fails on input {b}. {msg}"
          | none     => s!"Fails on input {b}."
      | .isFailure msg => .isFailure msg
    | .isFalse h msg => .isFalse (λ h' => h λ n hn => h' _ (Nat.le_step hn)) msg
    | .isFailure msg => .isFailure msg
