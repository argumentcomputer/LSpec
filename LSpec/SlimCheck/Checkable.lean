/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/

import LSpec.SlimCheck.Sampleable
import Lean

/-!
# `Checkable` Class
Checkable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.
This is a port of the Haskell QuickCheck library.
## Creating Customized Instances
The type classes `Checkable`, `SampleableExt` and `Shrinkable` are the
means by which `SlimCheck` creates samples and tests them. For instance,
the proposition `∀ i j : ℕ, i ≤ j` has a `Checkable` instance because `ℕ`
is sampleable and `i ≤ j` is decidable. Once `SlimCheck` finds the `Checkable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. Once it has found a
counter-example it will then use a `Shrinkable` instance to reduce the
example. This allows the user to create new instances and apply
`SlimCheck` to new situations.
### What do I do if I'm testing a property about my newly defined type?
Let us consider a type made for a new formalization:
```lean
structure MyType where
  x : ℕ
  y : ℕ
  h : x ≤ y
  deriving Repr
```
How do we test a property about `MyType`? For instance, let us consider
`Checkable.check $ ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `Shrinkable MyType` and `SampleableExt MyType`. We can define one as follows:
```lean
instance : Shrinkable MyType where
  shrink := fun ⟨x,y,h⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (fun ⟨⟨fst, snd⟩, ha⟩ => ⟨⟨fst, fst + snd, sorry⟩, sorry⟩)
instance : SampleableExt MyType :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    pure $ ⟨x, x + xyDiff, sorry⟩
```
Again, we take advantage of the fact that other types have useful
`Shrinkable` implementations, in this case `Prod`. Note that the second
proof is heavily based on `WellFoundedRelation` since its used for termination so
the first step you want to take is almost always to `simp_wf` in order to
get through the `WellFoundedRelation`.
## Main definitions
  * `Checkable` class
  * `Checkable.check`: a way to test a proposition using random examples
## Tags
random testing
## References
  * https://hackage.haskell.org/package/QuickCheck
-/

namespace SlimCheck

/-- Result of trying to disprove `p`
The constructors are:
  *  `success : (PSum Unit p) → TestResult p`
     succeed when we find another example satisfying `p`
     In `success h`, `h` is an optional proof of the proposition.
     Without the proof, all we know is that we found one example
     where `p` holds. With a proof, the one test was sufficient to
     prove that `p` holds and we do not need to keep finding examples.
   * `gaveUp : ℕ → TestResult p`
     give up when a well-formed example cannot be generated.
     `gaveUp n` tells us that `n` invalid examples were tried.
     Above 100, we give up on the proposition and report that we
     did not find a way to properly test it.
   * `failure : ¬ p → (List String) → ℕ → TestResult p`
     a counter-example to `p`; the strings specify values for the relevant variables.
     `failure h vs n` also carries a proof that `p` does not hold. This way, we can
     guarantee that there will be no false positive. The last component, `n`,
     is the number of times that the counter-example was shrunk.
-/
inductive TestResult (p : Prop) where
  | success : PSum Unit p → TestResult p
  | gaveUp : Nat → TestResult p
  | failure : ¬ p → List String → Nat → TestResult p
  deriving Inhabited

/-- Configuration for testing a property. -/
structure Configuration where
  numInst : Nat := 100
  maxSize : Nat := 100
  numRetries : Nat := 10
  traceDiscarded : Bool := false
  traceSuccesses : Bool := false
  traceShrink : Bool := false
  traceShrinkCandidates : Bool := false
  randomSeed : Option Nat := none
  quiet : Bool := false

namespace Configuration

/-- A configuration with all the trace options enabled, useful for debugging. -/
def verbose : Configuration where
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true

end Configuration

/--
`PrintableProp p` allows one to print a proposition so that
`SlimCheck` can indicate how values relate to each other.
It's basically a poor man's delaborator.
-/
class PrintableProp (p : Prop) where
  printProp : String

export PrintableProp (printProp)

instance (priority := low) : PrintableProp p where
  printProp := "⋯"

/-- `Checkable p` uses random examples to try to disprove `p`. -/
class Checkable (p : Prop) where
  run (cfg : Configuration) (minimize : Bool) : Gen (TestResult p)

def NamedBinder (_n : String) (p : Prop) : Prop := p

namespace TestResult

def toString : TestResult p → String
| success (PSum.inl _) => "success (no proof)"
| success (PSum.inr _) => "success (proof)"
| gaveUp n => s!"gave {n} times"
| failure _ counters _ => s!"failed {counters}"

instance : ToString (TestResult p) := ⟨toString⟩

/-- Applicative combinator proof carrying test results. -/
def combine {p q : Prop} : PSum Unit (p → q) → PSum Unit p → PSum Unit q
| PSum.inr f, PSum.inr proof => PSum.inr $ f proof
| _, _ => PSum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and : TestResult p → TestResult q → TestResult (p ∧ q)
| failure h xs n, _ => failure (fun h2 => h h2.left) xs n
| _, failure h xs n => failure (fun h2 => h h2.right) xs n
| success h1, success h2 => success $ combine (combine (PSum.inr And.intro) h1) h2
| gaveUp n, gaveUp m => gaveUp $ n + m
| gaveUp n, _ => gaveUp n
| _, gaveUp n => gaveUp n

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction. -/
def or : TestResult p → TestResult q → TestResult (p ∨ q)
| failure h1 xs n, failure h2 ys m =>
  let h3 := fun h =>
    match h with
    | Or.inl h3 => h1 h3
    | Or.inr h3 => h2 h3
  failure h3 (xs ++ ys) (n + m)
| success h, _ => success $ combine (PSum.inr Or.inl) h
| _, success h => success $ combine (PSum.inr Or.inr) h
| gaveUp n, gaveUp m => gaveUp $ n + m
| gaveUp n, _ => gaveUp n
| _, gaveUp n => gaveUp n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def imp (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q :=
  match r with
  | failure h2 xs n => failure (mt h h2) xs n
  | success h2 => success $ combine p h2
  | gaveUp n => gaveUp n

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def iff (h : q ↔ p) (r : TestResult p) : TestResult q :=
  imp h.mp r (PSum.inr h.mpr)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addInfo (x : String) (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q :=
  if let failure h2 xs n := r then
    failure (mt h h2) (x :: xs) n
  else
    imp h r p

/-- Add some formatting to the information recorded by `addInfo`. -/
def addVarInfo [Repr γ] (var : String) (x : γ) (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q  :=
  addInfo s!"{var} := {repr x}" h r p

def isFailure : TestResult p → Bool
  | failure .. => true
  | _ => false

end TestResult

namespace Checkable

open TestResult

def runProp (p : Prop) [Checkable p] : Configuration → Bool → Gen (TestResult p) := Checkable.run

/-- A `dbgTrace` with special formatting -/
def slimTrace [Pure m] (s : String) : m Unit :=
  dbgTrace s!"[SlimCheck: {s}]" fun _ => pure ()

instance andCheckable [Checkable p] [Checkable q] : Checkable (p ∧ q) where
  run := fun cfg min => do
    let xp ← runProp p cfg min
    let xq ← runProp q cfg min
    pure $ and xp xq

instance orCheckable [Checkable p] [Checkable q] : Checkable (p ∨ q) where
  run := fun cfg min => do
    let xp ← runProp p cfg min
    -- As a little performance optimization we can just not run the second
    -- test if the first succeeds
    match xp with
    | success (PSum.inl h) => pure $ success (PSum.inl h)
    | success (PSum.inr h) => pure $ success (PSum.inr $ Or.inl h)
    | _ =>
      let xq ← runProp q cfg min
      pure $ or xp xq

instance iffCheckable [Checkable ((p ∧ q) ∨ (¬ p ∧ ¬ q))] : Checkable (p ↔ q) where
  run := fun cfg min => do
    let h ← runProp ((p ∧ q) ∨ (¬ p ∧ ¬ q)) cfg min
    have key {a b} : (a ↔ b) ↔ (a ∧ b) ∨ (¬ a ∧ ¬ b) := by
      constructor
      · intro h; rw [h]
        by_cases h : b
        · exact .inl $ .intro h h
        · exact .inr $ .intro h h
      · intro h
        match h with
        | .inl h => exact Iff.intro (fun _ => h.2) (fun _ => h.1)
        | .inr h => exact Iff.intro (fun a => False.elim $ h.1 a) (fun b => False.elim $ h.2 b)
    pure $ iff key h

instance decGuardCheckable [PrintableProp p] [Decidable p] {β : p → Prop} [∀ h, Checkable (β h)] : Checkable (NamedBinder var $ ∀ h, β h) where
  run := fun cfg min => do
    if h : p then
      let res := (runProp (β h) cfg min)
      let s := printProp p
      (fun r => addInfo s!"guard: {s}" (· $ h) r (PSum.inr $ fun q _ => q)) <$> res
    else if cfg.traceDiscarded || cfg.traceSuccesses then
      let res := (fun _ => pure $ gaveUp 1)
      let s := printProp p
      slimTrace s!"discard: Guard {s} does not hold"; res
    else
      pure $ gaveUp 1

instance forallTypesCheckable {f : Type → Prop} [Checkable (f Int)] : Checkable (NamedBinder var $ ∀ x, f x) where
  run := fun cfg min => do
    let r ← runProp (f Int) cfg min
    pure $ addVarInfo var "ℤ" (· $ Int) r

/-- Format the counter-examples found in a test failure. -/
def formatFailure (s : String) (xs : List String) (n : Nat) : String :=
  let counter := "\n".intercalate xs
  let parts := [
    "\n===================",
    s,
    counter,
    s!"({n} shrinks)",
    "-------------------"
  ]
  "\n".intercalate parts

/-- Increase the number of shrinking steps in a test result. -/
def addShrinks (n : Nat) : TestResult p → TestResult p
| TestResult.failure p xs m => TestResult.failure p xs (m + n)
| p => p

/-- Shrink a counter-example `x` by using `Shrinkable.shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.
The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `SizeOf`)
than `x`. -/
def minimizeAux [SampleableExt α] {β : α → Prop} [∀ x, Checkable (β x)]
  (cfg : Configuration) (var : String) (x : SampleableExt.proxy α) (n : Nat) :
    OptionT Gen (Σ x, TestResult (β (SampleableExt.interp x))) := do
  let candidates := SampleableExt.shrink.shrink x
  if cfg.traceShrinkCandidates then
    slimTrace s!"Candidates for {var} := {repr x}:\n  {repr candidates}"
  for candidate in candidates do
    if cfg.traceShrinkCandidates then
      slimTrace s!"Trying {var} := {repr candidate}"
    let res ← OptionT.lift $ Checkable.runProp (β (SampleableExt.interp candidate)) cfg true
    if res.isFailure then
      if cfg.traceShrink then
        slimTrace s!"{var} shrunk to {repr candidate} from {repr x}"
      let currentStep := OptionT.lift $ pure $ Sigma.mk candidate (addShrinks (n + 1) res)
      -- todo: `nextStep` is unused. Why is it here?
      -- let nextStep := @minimizeAux α _ β _ cfg var candidate (n + 1)
      return ← (currentStep)
  if cfg.traceShrink then
    slimTrace s!"No shrinking possible for {var} := {repr x}"
  failure

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [SampleableExt α] {β : α → Prop} [∀ x, Checkable (β x)] (cfg : Configuration) (var : String)
    (x : SampleableExt.proxy α) (r : TestResult (β $ SampleableExt.interp x)) : Gen (Σ x, TestResult (β $ SampleableExt.interp x)) := do
  if cfg.traceShrink then
     slimTrace "Shrink"
     slimTrace s!"Attempting to shrink {var} := {repr x}"
  let res ← OptionT.run $ minimizeAux cfg var x 0
  pure $ res.getD ⟨x, r⟩

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it. -/
instance varCheckable [SampleableExt α] {β : α → Prop} [∀ x, Checkable (β x)] : Checkable (NamedBinder var $ ∀ x : α, β x) where
  run := fun cfg min => do
    let x ← SampleableExt.sample
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"{var} := {repr x}"
    let r ← Checkable.runProp (β $ SampleableExt.interp x) cfg false
    let ⟨finalX, finalR⟩ ←
      if isFailure r then
        if cfg.traceSuccesses then
          slimTrace s!"{var} := {repr x} is a failure"
        if min then
          minimize cfg var x r
        else
          pure $ ⟨x, r⟩
      else
        pure $ ⟨x, r⟩
    pure $ addVarInfo var finalX (· $ SampleableExt.interp finalX) finalR

/-- Test a universal property about propositions -/
instance propVarCheckable {β : Prop → Prop} [∀ b : Bool, Checkable (β b)] :
  Checkable (NamedBinder var $ ∀ p : Prop, β p)
where
  run := fun cfg min =>
    imp (fun h (b : Bool) => h b) <$> Checkable.runProp (NamedBinder var $ ∀ b : Bool, β b) cfg min

instance (priority := high) unusedVarCheckable [Nonempty α] [Checkable β] :
  Checkable (NamedBinder var $ ∀ _x : α, β)
where
  run := fun cfg min => do
    if cfg.traceDiscarded || cfg.traceSuccesses then
      slimTrace s!"{var} is unused"
    let r ← Checkable.runProp β cfg min
    let finalR := addInfo s!"{var} is irrelevant (unused)" id r
    pure $ imp (· $ Classical.ofNonempty) finalR (PSum.inr $ fun x _ => x)

instance (priority := low) decidableCheckable {p : Prop} [PrintableProp p] [Decidable p] : Checkable p where
  run := fun _ _ =>
    if h : p then
      pure $ success (PSum.inr h)
    else
      let s := printProp p
      pure $ failure h [s!"issue: {s} does not hold"] 0

end Checkable

section PrintableProp

instance Eq.printableProp [Repr α] {x y : α} : PrintableProp (x = y) where
  printProp := s!"{repr x} = {repr y}"

instance Ne.printableProp [Repr α] {x y : α} : PrintableProp (x ≠ y) where
  printProp := s!"{repr x} ≠ {repr y}"

instance LE.printableProp [Repr α] [LE α] {x y : α} : PrintableProp (x ≤ y) where
  printProp := s!"{repr x} ≤ {repr y}"

instance LT.printableProp [Repr α] [LT α] {x y : α} : PrintableProp (x < y) where
  printProp := s!"{repr x} < {repr y}"

instance And.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x ∧ y) where
  printProp := s!"{printProp x} ∧ {printProp y}"

instance Or.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x ∨ y) where
  printProp := s!"{printProp x} ∨ {printProp y}"

instance Iff.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x ↔ y) where
  printProp := s!"{printProp x} ↔ {printProp y}"

instance Imp.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x → y) where
  printProp := s!"{printProp x} → {printProp y}"

instance Not.printableProp [PrintableProp x] : PrintableProp (¬x) where
  printProp := s!"¬{printProp x}"

instance True.printableProp : PrintableProp True where
  printProp := "True"

instance False.printableProp : PrintableProp False where
  printProp := "False"

instance Bool.printableProp {b : Bool} : PrintableProp b where
  printProp := if b then "true" else "false"

end PrintableProp

section IO
open TestResult

/-- Execute `cmd` and repeat every time the result is `gave_up` (at most `n` times). -/
def retry (cmd : Rand (TestResult p)) : Nat → Rand (TestResult p)
  | 0 => pure $ TestResult.gaveUp 1
  | n + 1 => do match ← cmd with
    | success hp => pure $ success hp
    | TestResult.failure h xs n => pure $ failure h xs n
    | gaveUp _ => retry cmd n

/-- Count the number of times the test procedure gave up. -/
def giveUp (x : Nat) : TestResult p → TestResult p
  | success (PSum.inl ()) => gaveUp x
  | success (PSum.inr p) => success $ (PSum.inr p)
  | gaveUp n => gaveUp $ n + x
  | TestResult.failure h xs n => failure h xs n

/-- Try `n` times to find a counter-example for `p`. -/
def Checkable.runSuiteAux (p : Prop) [Checkable p] (cfg : Configuration) (r : TestResult p) :
    Nat → Rand (TestResult p)
  | 0 => pure r
  | n + 1 => do
    let size := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    if cfg.traceSuccesses then
      slimTrace s!"New sample"
      slimTrace s!"Retrying up to {cfg.numRetries} times until guards hold"
    let x ← retry (ReaderT.run (Checkable.runProp p cfg true) ⟨size⟩) cfg.numRetries
    match x with
    | (success (PSum.inl ())) => runSuiteAux p cfg r n
    | (gaveUp g) => runSuiteAux p cfg (giveUp g r) n
    | _ => pure $ x

/-- Try to find a counter-example of `p`. -/
def Checkable.runSuite (p : Prop) [Checkable p] (cfg : Configuration := {}) : Rand (TestResult p) :=
  Checkable.runSuiteAux p cfg (success $ PSum.inl ()) cfg.numInst

/-- Run a test suite for `p` in `BaseIO` using the global RNG in `stdGenRef`. -/
def Checkable.checkIO (p : Prop) [Checkable p] (cfg : Configuration := {}) : BaseIO (TestResult p) :=
  match cfg.randomSeed with
  | none => IO.runRand (Checkable.runSuite p cfg)
  | some seed => IO.runRandWith seed (Checkable.runSuite p cfg)

end IO

namespace Decorations

open Lean

/-- Traverse the syntax of a proposition to find universal quantifiers
quantifiers and add `NamedBinder` annotations next to them. -/
partial def addDecorations (e : Expr) : Expr :=
  e.replace fun expr => match expr with
    | Expr.forallE name type body data =>
      let n := name.toString
      let newType := addDecorations type
      let newBody := addDecorations body
      let rest := Expr.forallE name newType newBody data
      some $ mkApp2 (mkConst `SlimCheck.NamedBinder) (mkStrLit n) rest
    | _ => none

/-- `DecorationsOf p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
abbrev DecorationsOf (_p : Prop) := Prop

open Elab.Tactic in
/-- In a goal of the shape `⊢ DecorationsOf p`, `mk_decoration` examines
the syntax of `p` and adds `NamedBinder` around universal quantifications
to improve error messages. This tool can be used in the declaration of a
function as follows:
```lean
def foo (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations) [Checkable p'] : ...
```
`p` is the parameter given by the user, `p'` is a definitionally equivalent
proposition where the quantifiers are annotated with `NamedBinder`.
-/
scoped elab "mk_decorations" : tactic => do
  let goalType ← (← getMainGoal).getType
  if let Expr.app (.const ``Decorations.DecorationsOf ..) body := goalType then
    closeMainGoal `SlimCheck.mk_decorations (addDecorations body)

end Decorations

open Decorations in
/-- Run a test suite for `p` and throw an exception if `p` does not not hold.-/
def Checkable.check (p : Prop) (cfg : Configuration := {})
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : IO Unit := do
  match ← Checkable.checkIO p' cfg with
  | TestResult.success _ => if !cfg.quiet then IO.println "Success" else pure ()
  | TestResult.gaveUp n => if !cfg.quiet then IO.println s!"Gave up {n} times"
  | TestResult.failure _ xs n => throw (IO.userError $ formatFailure "Found problems!" xs n)

-- #eval Checkable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x) Configuration.verbose
-- #eval Checkable.check (∀ x : Nat, ∀ y : Nat, x + y = y + x) Configuration.verbose
-- #eval Checkable.check (∀ (x : (Nat × Nat)), x.fst - x.snd - 10 = x.snd - x.fst - 10) Configuration.verbose
-- #eval Checkable.check (∀ (x : Nat) (h : 10 < x), 5 < x) Configuration.verbose

end SlimCheck
