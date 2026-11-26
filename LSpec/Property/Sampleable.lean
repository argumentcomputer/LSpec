module
public import LSpec.Property.Gen

/-!
# `Sampleable` and `Shrinkable`

Pure typeclasses for generating and shrinking random values for Bool-based
property testing. No `WellFoundedRelation` proof obligation is required;
shrinking terminates via a configurable fuel bound.
-/

namespace LSpec.Prop
public section

/-- Generates random values of type `α`. -/
class Sampleable (α : Type u) where
  sample : Gen α

/-- Produces strictly simpler candidate values for counterexample minimization. -/
class Shrinkable (α : Type u) where
  shrink : α → List α := fun _ => []

/-- Wrapper disabling shrinking for a type. -/
structure NoShrink (α : Type u) where
  val : α
  deriving BEq, Repr, Inhabited

instance : Shrinkable (NoShrink α) where
  shrink _ := []

instance [Sampleable α] : Sampleable (NoShrink α) where
  sample := NoShrink.mk <$> Sampleable.sample

/-! ## Built-in `Shrinkable` instances -/

def natShrinkAux (fuel n : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if n == 0 then []
    else
      let half := n / 2
      if half == 0 then [0]
      else half :: natShrinkAux fuel half

instance : Shrinkable Nat where
  shrink n :=
    if n == 0 then []
    else if n == 1 then [0]
    else 0 :: (natShrinkAux 64 n ++ [n - 1]).eraseDups.filter (· < n)

instance : Shrinkable Int where
  shrink i :=
    if i == 0 then []
    else
      let base := Shrinkable.shrink i.natAbs
      if i < 0 then
        -- Try positive counterpart first, then smaller negatives and positives
        Int.ofNat i.natAbs :: base.map (fun n => -Int.ofNat n)
      else
        base.map Int.ofNat

instance : Shrinkable Bool where
  shrink
    | true => [false]
    | false => []

instance : Shrinkable UInt8 where
  shrink n := (Shrinkable.shrink n.toNat).map Nat.toUInt8

instance : Shrinkable UInt16 where
  shrink n := (Shrinkable.shrink n.toNat).map Nat.toUInt16

instance : Shrinkable UInt32 where
  shrink n := (Shrinkable.shrink n.toNat).map Nat.toUInt32

instance : Shrinkable UInt64 where
  shrink n := (Shrinkable.shrink n.toNat).map Nat.toUInt64

instance : Shrinkable USize where
  shrink n := (Shrinkable.shrink n.toNat).map Nat.toUSize

instance {n : Nat} [NeZero n] : Shrinkable (Fin n) where
  shrink x := (Shrinkable.shrink x.val).map (Fin.ofNat n)

instance : Shrinkable Char where
  shrink c :=
    if c == 'a' then []
    else if c == ' ' then ['a']
    else ['a', '0', ' '].filter (· != c)

instance [Shrinkable α] : Shrinkable (Option α) where
  shrink
    | none => []
    | some a => none :: (Shrinkable.shrink a).map some

instance [Shrinkable α] [Shrinkable β] : Shrinkable (α × β) where
  shrink
    | (a, b) =>
      (Shrinkable.shrink a).map (·, b) ++
      (Shrinkable.shrink b).map (a, ·)

instance [Shrinkable α] [Shrinkable β] : Shrinkable (Sum α β) where
  shrink
    | .inl a => (Shrinkable.shrink a).map .inl
    | .inr b => (Shrinkable.shrink b).map .inr

instance [Shrinkable ε] [Shrinkable α] : Shrinkable (Except ε α) where
  shrink
    | .error e => (Shrinkable.shrink e).map .error
    | .ok a => (Shrinkable.shrink a).map .ok

/-- Shrink a list by removing chunks (halves, single elements) and then shrinking elements. -/
def shrinkList [Shrinkable α] (xs : List α) : List (List α) :=
  match xs with
  | [] => []
  | [x] => [] :: (Shrinkable.shrink x).map (fun x' => [x'])
  | _ =>
    let n := xs.length
    let half := n / 2
    let drops := [
      [],
      xs.take half,
      xs.drop half
    ]
    let dropOne := (List.range n).map fun i => xs.take i ++ xs.drop (i + 1)
    let shrinkElems := (xs.zipIdx).flatMap fun (x, i) =>
      (Shrinkable.shrink x).map fun x' => xs.set i x'
    drops ++ dropOne ++ shrinkElems

instance [Shrinkable α] : Shrinkable (List α) where
  shrink := shrinkList

instance [Shrinkable α] : Shrinkable (Array α) where
  shrink xs := (shrinkList xs.toList).map List.toArray

instance : Shrinkable String where
  shrink s := (shrinkList s.toList).map String.ofList

instance : Shrinkable ByteArray where
  shrink bs := (shrinkList bs.data.toList).map (fun l => ByteArray.mk l.toArray)

/-! ## Built-in `Sampleable` instances -/

instance : Sampleable Bool where
  sample := Gen.bool

instance : Sampleable Nat where
  sample := do
    let sz ← Gen.getSize
    Gen.chooseNat 0 sz

instance : Sampleable Int where
  sample := do
    let sz ← Gen.getSize
    Gen.chooseInt (-Int.ofNat sz) (Int.ofNat sz)

instance : Sampleable UInt8 where
  sample := do
    let sz ← Gen.getSize
    Gen.chooseUInt8 0 (Nat.toUInt8 (min sz 255))

instance : Sampleable UInt16 where
  sample := do
    let sz ← Gen.getSize
    Gen.frequency #[
      (3, Gen.chooseUInt16 0 (Nat.toUInt16 (min sz 65535))),
      (1, Gen.chooseUInt16)
    ] (pure 0)

instance : Sampleable UInt32 where
  sample := do
    let sz ← Gen.getSize
    Gen.frequency #[
      (3, Gen.chooseUInt32 0 (Nat.toUInt32 sz)),
      (1, Gen.chooseUInt32)
    ] (pure 0)

instance : Sampleable UInt64 where
  sample := do
    let sz ← Gen.getSize
    Gen.frequency #[
      (3, Gen.chooseUInt64 0 (Nat.toUInt64 sz)),
      (1, Gen.chooseUInt64)
    ] (pure 0)

instance : Sampleable USize where
  sample := do
    let sz ← Gen.getSize
    Nat.toUSize <$> Gen.chooseNat 0 sz

instance {n : Nat} [NeZero n] : Sampleable (Fin n) where
  sample := Gen.chooseFin n

def defaultChars : Array Char :=
  #[' ', '0', '1', '2', '3', '9', 'a', 'b', 'c', 'z', 'A', 'B', 'Z',
    ':', ',', ';', '.', '_', '-', '/', '\\', '\n']

instance : Sampleable Char where
  sample := Gen.frequency #[
    (3, Gen.elements defaultChars 'a'),
    (1, Char.ofNat <$> Gen.chooseNat 32 126)
  ] (pure 'a')

instance : Sampleable String where
  sample := String.ofList <$> Gen.listOf Sampleable.sample

instance : Sampleable ByteArray where
  sample := Gen.byteArray

instance [Sampleable α] : Sampleable (Option α) where
  sample := Gen.optionOf Sampleable.sample

instance {α β : Type u} [Sampleable α] [Sampleable β] : Sampleable (α × β) where
  sample := Gen.prodOf Sampleable.sample Sampleable.sample

instance [Sampleable α] [Sampleable β] : Sampleable (Sum α β) where
  sample := Gen.frequency #[
    (1, Sum.inl <$> Sampleable.sample),
    (1, Sum.inr <$> Sampleable.sample)
  ] (Sum.inl <$> Sampleable.sample)

instance [Sampleable ε] [Sampleable α] : Sampleable (Except ε α) where
  sample := Gen.frequency #[
    (1, Except.error <$> Sampleable.sample),
    (3, Except.ok <$> Sampleable.sample)
  ] (Except.ok <$> Sampleable.sample)

instance [Sampleable α] : Sampleable (List α) where
  sample := Gen.listOf Sampleable.sample

instance [Sampleable α] : Sampleable (Array α) where
  sample := Gen.arrayOf Sampleable.sample

end
end LSpec.Prop
