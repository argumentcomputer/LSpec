/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/

/-!
# Bounded and DefaultRange classes

This module encapsulates the notion of a range of elements. 

## Main definitions
  * `Bounded` class for objects which are naturally bounded 
    by two `lo` and `hi` elements;
  * `DefaultRange` class for objects which are unbounded, 
    but nevertheless need a convenient range of values which to operate within.

Note that we go against Lean's principles by NOT providing any 
mathematical guarantees for the `Bounded` and `DefaultRange` classes. 
It is perfectly possible to define `Bounded Nat` with `lo := 37` and `hi := 37`;
we leave these to the judgement of the programmer. *gasp of horror*
This more follows the design of `Bounded` in Haskell, and allows us to 
forgo carrying proofs around when we start defining `Random` instances.

Lean developers, please forgive us.

## References
  * Haskell
-/

namespace SlimCheck

class Bounded (α : Type u) where 
  lo : α
  hi : α

class DefaultRange (α : Type u) where 
  lo : α
  hi : α

instance [Bounded α] : DefaultRange α where 
  lo := Bounded.lo 
  hi := Bounded.hi

instance : Bounded Bool where 
  lo := true 
  hi := false

instance : DefaultRange Nat where 
  lo := 0 
  hi := USize.size

instance {n : Nat} : Bounded (Fin n.succ) where 
  lo := ⟨0, n.succ_pos⟩
  hi := ⟨n, n.lt_succ_self⟩

instance : DefaultRange Int where 
  lo :=  - Int.ofNat (USize.size / 2)
  hi := Int.ofNat (USize.size / 2 - 1)

end SlimCheck
