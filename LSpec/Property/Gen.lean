module

/-!
# Pure Random Generator (`Gen`)

A deterministic, pure generator monad for property-based testing.
Unlike `IO.runRand`, `Gen` never touches global `IO.stdGenRef`, making it
100% thread-safe and reproducible under parallel test execution.
-/

namespace LSpec.Prop
public section

/-- Deterministic SplitMix64 PRNG state. Fast, splittable, and completely thread-safe. -/
structure Rng where
  state : UInt64
  deriving BEq, Repr, Inhabited

namespace Rng

def ofSeed (seed : UInt64) : Rng := ⟨seed⟩

/-- Advance state and return a uniformly distributed `UInt64`. -/
@[inline] def nextUInt64 (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Split into two independent PRNG streams. -/
@[inline] def split (r : Rng) : Rng × Rng :=
  let (a, r1) := r.nextUInt64
  let (b, r2) := r1.nextUInt64
  (⟨a⟩, ⟨b ^^^ r2.state⟩)

/-- Uniform `Nat` in `[lo, hi]` (inclusive). If `lo > hi`, swaps bounds. -/
def nextNatBound (r : Rng) (lo hi : Nat) : Nat × Rng :=
  let (lo, hi) := if lo ≤ hi then (lo, hi) else (hi, lo)
  let span := hi - lo + 1
  if span ≤ 1 then
    (lo, r)
  else if span ≤ UInt64.size then
    let (v, r') := r.nextUInt64
    (lo + v.toNat % span, r')
  else
    -- Combine two UInt64 draws for very large spans.
    let (v1, r1) := r.nextUInt64
    let (v2, r2) := r1.nextUInt64
    let combined := v1.toNat * UInt64.size + v2.toNat
    (lo + combined % span, r2)

end Rng

/-- Pure generator monad parameterized by a size hint (`Nat`) and pure `Rng` state. -/
abbrev Gen (α : Type u) := ReaderT (ULift Nat) (StateM (ULift Rng)) α

namespace Gen

/-- Execute a generator with a given size and PRNG state. -/
def runWith (g : Gen α) (size : Nat) (rng : Rng) : α × Rng :=
  let (a, st) := (g.run ⟨size⟩).run ⟨rng⟩
  (a, st.down)

/-- Execute a generator with a given size and `UInt64` seed. -/
def evalSeed (g : Gen α) (size : Nat) (seed : UInt64) : α :=
  (g.runWith size (Rng.ofSeed seed)).1

/-- Read the current size parameter. -/
def getSize : Gen Nat :=
  return (← read).down

/-- Run a generator with a transformed size parameter. -/
def resize (f : Nat → Nat) (g : Gen α) : Gen α :=
  withReader (fun s => ⟨f s.down⟩) g

/-- Run a generator with the size parameter passed explicitly. -/
def sized (f : Nat → Gen α) : Gen α := do
  f (← getSize)

/-- Scale the size parameter by `f`. Alias for `resize`. -/
def scale (f : Nat → Nat) (g : Gen α) : Gen α :=
  resize f g

/-- Draw a raw `UInt64`. -/
def nextUInt64 : Gen UInt64 := do
  let r := (← get).down
  let (v, r') := r.nextUInt64
  set (ULift.up r')
  return v

/-- Generate a `Nat` uniformly in `[lo, hi]` (inclusive). -/
def chooseNat (lo hi : Nat) : Gen Nat := do
  let r := (← get).down
  let (v, r') := r.nextNatBound lo hi
  set (ULift.up r')
  return v

/-- Generate an `Int` uniformly in `[lo, hi]` (inclusive). -/
def chooseInt (lo hi : Int) : Gen Int := do
  let (lo, hi) := if lo ≤ hi then (lo, hi) else (hi, lo)
  let span := (hi - lo).toNat
  let offset ← chooseNat 0 span
  return lo + Int.ofNat offset

/-- Generate a `Bool` with equal probability. -/
def bool : Gen Bool := do
  return ((← nextUInt64) &&& 1) == 1

/-- Generate a `UInt8` in `[lo, hi]`. -/
def chooseUInt8 (lo : UInt8 := 0) (hi : UInt8 := UInt8.ofNat (UInt8.size - 1)) : Gen UInt8 :=
  Nat.toUInt8 <$> chooseNat lo.toNat hi.toNat

/-- Generate a `UInt16` in `[lo, hi]`. -/
def chooseUInt16 (lo : UInt16 := 0) (hi : UInt16 := UInt16.ofNat (UInt16.size - 1)) : Gen UInt16 :=
  Nat.toUInt16 <$> chooseNat lo.toNat hi.toNat

/-- Generate a `UInt32` in `[lo, hi]`. -/
def chooseUInt32 (lo : UInt32 := 0) (hi : UInt32 := UInt32.ofNat (UInt32.size - 1)) : Gen UInt32 :=
  Nat.toUInt32 <$> chooseNat lo.toNat hi.toNat

/-- Generate a `UInt64` in `[lo, hi]`. -/
def chooseUInt64 (lo : UInt64 := 0) (hi : UInt64 := UInt64.ofNat (UInt64.size - 1)) : Gen UInt64 :=
  Nat.toUInt64 <$> chooseNat lo.toNat hi.toNat

/-- Generate a `Fin n` uniformly. -/
def chooseFin (n : Nat) [NeZero n] : Gen (Fin n) := do
  let k ← chooseNat 0 (n - 1)
  return Fin.ofNat n k

/-- Choose uniformly among an array of generators, using `fallback` if empty. -/
def oneOf (gens : Array (Gen α)) (fallback : Gen α) : Gen α := do
  if h : gens.size > 0 then
    let i ← chooseNat 0 (gens.size - 1)
    if hi : i < gens.size then gens[i] else fallback
  else
    fallback

/-- Choose uniformly among an array of generators (requires `Inhabited α`). -/
def oneOf! [Inhabited α] (gens : Array (Gen α)) : Gen α :=
  oneOf gens (pure default)

/-- Choose uniformly among an array of values, returning `fallback` if empty. -/
def elements (xs : Array α) (fallback : α) : Gen α := do
  if h : xs.size > 0 then
    let i ← chooseNat 0 (xs.size - 1)
    if hi : i < xs.size then return xs[i] else return fallback
  else
    return fallback

/-- Choose uniformly among an array of values (requires `Inhabited α`). -/
def elements! [Inhabited α] (xs : Array α) : Gen α :=
  elements xs default

/-- Weighted choice among `(weight, generator)` pairs. -/
def frequency (weighted : Array (Nat × Gen α)) (fallback : Gen α) : Gen α := do
  let totalWeight := weighted.foldl (fun acc (w, _) => acc + w) 0
  if totalWeight == 0 then
    fallback
  else
    let choice ← chooseNat 0 (totalWeight - 1)
    let mut cumulative := 0
    for (w, g) in weighted do
      cumulative := cumulative + w
      if choice < cumulative then
        return ← g
    fallback

/-- Generate an `Array α` of length in `[0, size]`. -/
def arrayOf (g : Gen α) : Gen (Array α) := do
  let len ← chooseNat 0 (← getSize)
  let mut out := Array.mkEmpty len
  for _ in [:len] do
    out := out.push (← g)
  return out

/-- Generate a non-empty `Array α` of length in `[1, max 1 size]`. -/
def arrayOf1 (g : Gen α) : Gen (Array α) := do
  let sz := max 1 (← getSize)
  let len ← chooseNat 1 sz
  let mut out := Array.mkEmpty len
  for _ in [:len] do
    out := out.push (← g)
  return out

/-- Generate a `List α` of length in `[0, size]`. -/
def listOf (g : Gen α) : Gen (List α) :=
  Array.toList <$> arrayOf g

/-- Generate a non-empty `List α`. -/
def listOf1 (g : Gen α) : Gen (List α) :=
  Array.toList <$> arrayOf1 g

/-- Generate an `Option α` (`none` ~20% of the time, `some` ~80%). -/
def optionOf (g : Gen α) : Gen (Option α) :=
  frequency #[(1, pure none), (4, some <$> g)] (pure none)

/-- Generate a `Prod α β`. -/
def prodOf {α β : Type u} (ga : Gen α) (gb : Gen β) : Gen (α × β) :=
  return (← ga, ← gb)

/-- Generate a `ByteArray` of length in `[0, size]`. -/
def byteArray : Gen ByteArray := do
  let len ← chooseNat 0 (← getSize)
  let mut out := ByteArray.emptyWithCapacity len
  for _ in [:len] do
    out := out.push (← chooseUInt8)
  return out

/-- Generate a random permutation of `xs`. -/
def permutationOf : List α → Gen (List α)
  | [] => pure []
  | x :: xs => do
    let ys ← permutationOf xs
    let i ← chooseNat 0 ys.length
    return ys.take i ++ [x] ++ ys.drop i

/-- Try up to `maxTries` times to generate a value satisfying `p`. -/
def suchThat? (g : Gen α) (p : α → Bool) (maxTries : Nat := 100) : Gen (Option α) := do
  for _ in [:maxTries] do
    let x ← g
    if p x then return some x
  return none

end Gen

end
end LSpec.Prop
