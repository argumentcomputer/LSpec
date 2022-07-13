import LSpec.LSpec

def formatBinaryError (m : String) (x y : α) [Repr α] : Std.Format :=
  s!"{m}{(repr x).indentD}\nand{(repr y).indentD}"

instance (x y : α) [DecidableEq α] [Repr α] : TDecidable (x = y) :=
  if h : x = y then
    .isTrue (.inr h)
  else
    .isFalse (.inr h) $ formatBinaryError "Expected to be equal:" x y

instance (x y : α) [BEq α] [Repr α] : TDecidable (x == y) :=
  if h : x == y then
    .isTrue (.inr h)
  else
    .isFalse (.inr h) $ formatBinaryError "Expected to be equal:" x y

instance (x y : α) [DecidableEq α] [Repr α] : TDecidable (x ≠ y) :=
  if h : x ≠ y then
    .isTrue (.inr h)
  else
    .isFalse (.inr h) s!"Both equal to:{(repr x).indentD}"

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
  | 0     => .isTrue $ .inr (by simp [Nat.not_lt_zero])
  | b + 1 =>
    match tdecidable_forall_lt b p with
    | .isTrue h =>
      match h, d b with
      | .inr h, .isTrue hb =>
        .isTrue $ match hb with 
        | .inl u => .inl () 
        | .inr hb => .inr $ by
          intros n hn
          cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hn) with
          | inl hl => cases hl; assumption
          | inr => apply h; assumption
      | .inr h, .isFalse hb msg =>
        .isFalse (match hb with 
        | .inl u => .inl u
        | .inr hb => .inr $ λ h => hb (h _ (Nat.lt_succ_self _))) $
          match msg with
          | some msg => s!"Fails on input {b}. {msg}"
          | none     => s!"Fails on input {b}."
      | .inl u, .isTrue hb => .isTrue $ .inl () 
      | .inl u, .isFalse hb msg => 
        .isFalse (.inl ()) $ 
        match msg with
        | some msg => s!"Fails on input {b}. {msg}"
        | none     => s!"Fails on input {b}."
    | .isFalse h msg => .isFalse (
        match h with 
        | .inl u => .inl u
        | .inr h => .inr $ λ h' => h λ n hn => h' _ (Nat.le_step hn)
      ) msg
