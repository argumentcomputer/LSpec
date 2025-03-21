/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import LSpec.SlimCheck.Gen

/-!
# `SampleableExt` Class
This class permits the creation samples of a given type
controlling the size of those values using the `Gen` monad`.
# `Shrinkable` Class
This class helps minimize examples by creating smaller versions of
given values.
When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`SlimCheck` requires that `ℕ` have an instance of `SampleableExt` and for
`prime n` to be decidable.  `SlimCheck` will then use the instance of
`SampleableExt` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`SlimCheck` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `SlimCheck` moves on to trying more examples.
This is a port of the Haskell QuickCheck library.
## Main definitions
  * `SampleableExt` class
  * `Shrinkable` class
### `SampleableExt`
`SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.
Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. If you
are using it in the first way, this proxy type will simply be the type
itself and the `interp` function `id`.
### `Shrinkable
Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples.
## Shrinking
Shrinking happens when `SlimCheck` find a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `SlimCheck` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.
The `Shrinkable` class, , has a `shrink` function so that we can use
specialized knowledge while shrinking a value. It is not responsible
for the whole shrinking process however. It only has to take one step
in the shrinking process. `SlimCheck` will repeatedly call `shrink`
until no more steps can be taken. Because `shrink` guarantees that the
size of the candidates it produces is strictly smaller than the
argument, we know that `SlimCheck` is guaranteed to terminate.
## Tags
random testing
## References
  * https://hackage.haskell.org/package/QuickCheck
-/

namespace SlimCheck

open Random

/-- Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples. -/
class Shrinkable (α : Type u) extends WellFoundedRelation α where
  shrink : (x : α) → List α := fun _ => []

/-- `SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.
Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class SampleableExt (α : Sort u) where
  proxy : Type v
  [proxyRepr : Repr proxy]
  [shrink : Shrinkable proxy]
  sample : Gen proxy
  interp : proxy → α

attribute [instance] SampleableExt.proxyRepr
attribute [instance] SampleableExt.shrink

namespace SampleableExt

/-- Use to generate instance whose purpose is to simply generate values
of a type directly using the `Gen` monad -/
def mkSelfContained [Repr α] [Shrinkable α] (sample : Gen α) : SampleableExt α where
  proxy := α
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := sample
  interp := id

/-- First samples a proxy value and interprets it. Especially useful if
the proxy and target type are the same. -/
def interpSample (α : Type u) [SampleableExt α] : Gen α :=
  SampleableExt.interp <$> SampleableExt.sample

end SampleableExt

section Shrinkers

/-- `Nat.shrink' n` creates a list of smaller natural numbers by
successively dividing `n` by 2 . For example, `Nat.shrink 5 = [2, 1, 0]`. -/
partial def Nat.shrink (n : Nat) : List Nat :=
  if 0 < n then
    let m := n / 2
    let rest := shrink m
    m :: rest
  else
    []

instance Nat.shrinkable : Shrinkable Nat where
  shrink := Nat.shrink

/-- `Fin.shrink` works like `Nat.shrink` but instead operates on `Fin`. -/
partial def Fin.shrink {n : Nat} (m : Fin n.succ) : List (Fin n.succ) :=
  if 0 < m then
    let m := m / 2
    let rest := shrink m
    m :: rest
  else
    []

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink := Fin.shrink

local instance Int_sizeOfAbs : SizeOf Int := ⟨Int.natAbs⟩

/-- `Int.shrinkable` operates like `Nat.shrinkable` but also includes the negative variants. -/
instance Int.shrinkable : Shrinkable Int where
  shrink n :=
    Nat.shrink n.natAbs |>.map fun x => - Int.ofNat x

instance Bool.shrinkable : Shrinkable Bool := {}
instance Char.shrinkable : Shrinkable Char := {}

instance Prod.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] : Shrinkable (Prod α β) where
  shrink := fun (fst,snd) =>
    let shrink1 := shrA.shrink fst |>.map fun x => (x, snd)
    let shrink2 := shrB.shrink snd |>.map fun x => (fst, x)
    shrink1 ++ shrink2

end Shrinkers

section Samplers

open Gen SampleableExt

instance Nat.sampleableExt : SampleableExt Nat :=
  mkSelfContained (do choose Nat 0 (← getSize))

instance Fin.sampleableExt {n : Nat} : SampleableExt (Fin (n.succ)) :=
  mkSelfContained (do choose (Fin n.succ) (Fin.ofNat' _ 0) (Fin.ofNat' _ (← getSize)))

instance Int.sampleableExt : SampleableExt Int :=
  mkSelfContained (do choose Int (-(← getSize)) (← getSize))

instance Bool.sampleableExt : SampleableExt Bool :=
  mkSelfContained $ chooseAny Bool

/-- This can be specialized into customized `SampleableExt Char` instances.
The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `chars` with uniform probabilities.  -/
def Char.sampleable (length : Nat) (chars : Array Char) : SampleableExt Char :=
  mkSelfContained do
    let x ← choose Nat 0 length
    if x == 0 then
      let n ← interpSample Nat
      pure $ Char.ofNat n
    else
      elements chars

instance Char.sampleableDefault : SampleableExt Char :=
  Char.sampleable 3
    #[' ', '0', '1', '2', '3', 'a', 'b', 'c', 'A', 'B', 'C', ':', ',', ';', '`', '\\', '/']

instance Prod.sampleableExt {α β : Type u} [SampleableExt α] [SampleableExt β] :
    SampleableExt (α × β) where
  proxy := Prod (proxy α) (proxy β)
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := prodOf sample sample
  interp := Prod.map interp interp

instance Prop.sampleableExt : SampleableExt Prop where
  proxy := Bool
  proxyRepr := inferInstance
  sample := interpSample Bool
  shrink := inferInstance
  interp := Coe.coe

end Samplers

/-- An annotation for values that should never get shrinked. -/
def NoShrink (α : Type u) := α

namespace NoShrink

def mk (x : α) : NoShrink α := x
def get (x : NoShrink α) : α := x

instance inhabited [inst : Inhabited α] : Inhabited (NoShrink α) := inst
instance repr [inst : Repr α] : Repr (NoShrink α) := inst

instance shrinkable : Shrinkable (NoShrink α) where
  shrink := fun _ => []

instance sampleableExt [SampleableExt α] [Repr α] : SampleableExt (NoShrink α) :=
  SampleableExt.mkSelfContained $ (NoShrink.mk ∘ SampleableExt.interp) <$> SampleableExt.sample

end NoShrink

end SlimCheck
