module
public import LSpec.Core
public import LSpec.Assert
public import LSpec.Property.Gen
public import LSpec.Property.Sampleable

/-!
# Bool-based Property Testing (`Property`, `PropTestable`, `PropTest`)

Purely `Bool`- and `AssertM`-based property testing inspired by QuickCheck and
`nest-slimcheck`:
- No `Prop` / `Decidable` / `mk_decorations` tactic overhead.
- Works for arbitrary arity functions `fun (a : A) (b : B) => ...` returning
  `Bool`, `AssertM Unit`, `Except String Unit`, or nested `forAll` / `==>` combinators.
- Thread-safe deterministic per-test PRNG (`Rng`) with seed always recorded and
  reported for 100% reproducible failures under parallel execution.
-/

namespace LSpec.Prop
public section

/-- Configuration for a property-based test. -/
structure PropertyConfig where
  /-- Number of passing test cases required. -/
  numTests : Nat := 100
  /-- Maximum generator size parameter (grows linearly from 0 to `maxSize`). -/
  maxSize : Nat := 100
  /-- Maximum ratio of discarded inputs per requested test before giving up. -/
  maxDiscardRatio : Nat := 10
  /-- Maximum shrinking steps per failing argument. -/
  maxShrinks : Nat := 100
  /-- Optional fixed seed; if `none`, uses the deterministic per-test seed from `TestContext`. -/
  seed : Option UInt64 := none
  deriving BEq, Repr

namespace PropertyConfig

/-- Read overrides from `TestOptions` keys (`prop.numTests`, `prop.maxSize`,
    `prop.maxDiscardRatio`, `prop.maxShrinks`, `prop.seed`). -/
def fromOptions (opts : TestOptions) (base : PropertyConfig := {}) : PropertyConfig :=
  {
    numTests := opts.getNat "prop.numTests" base.numTests
    maxSize := opts.getNat "prop.maxSize" base.maxSize
    maxDiscardRatio := opts.getNat "prop.maxDiscardRatio" base.maxDiscardRatio
    maxShrinks := opts.getNat "prop.maxShrinks" base.maxShrinks
    seed := opts.getUInt64? "prop.seed" |>.orElse fun () => base.seed
  }

end PropertyConfig

/-- Outcome of a single generated property trial (after any shrinking). -/
inductive PropOutcome where
  | passed
  | discarded
  | failed (args : List String) (message : String) (pos : Option SourcePos := none)
  deriving BEq, Repr

/-- A single-trial property runner returning `(outcome, numShrinks, nextRng)`. -/
structure Property where
  runOnce : PropertyConfig → Nat → Rng → IO (PropOutcome × Nat × Rng)

/-- Any type that can be checked as a property (`Bool`, `AssertM Unit`,
    `Except String Unit`, `Implies`, `Property`, and functions `α → β`). -/
class PropTestable (α : Type u) where
  toProperty : α → Property

instance : PropTestable Property where
  toProperty p := p

instance : PropTestable Bool where
  toProperty b := {
    runOnce := fun _ _ rng =>
      if b then pure (.passed, 0, rng)
      else pure (.failed [] "property evaluated to false" none, 0, rng)
  }

instance : PropTestable (AssertM Unit) where
  toProperty act := {
    runOnce := fun _ _ rng => do
      match ← act.run with
      | .ok () => pure (.passed, 0, rng)
      | .error (.skipped _) => pure (.discarded, 0, rng)
      | .error (.failed err) =>
        let msg := if err.details.isEmpty then err.message
          else s!"{err.message}\n{err.details}"
        pure (.failed [] msg err.pos, 0, rng)
  }

instance : PropTestable (Except String Unit) where
  toProperty res := {
    runOnce := fun _ _ rng =>
      match res with
      | .ok () => pure (.passed, 0, rng)
      | .error msg => pure (.failed [] msg none, 0, rng)
  }

/-- Precondition guard for properties: `(n != 0) ==> Nat.blt (n - 1) n`.
    If `cond` is `false`, the generated input is discarded without evaluating `body`. -/
def implies [PropTestable β] (cond : Bool) (body : Unit → β) : Property where
  runOnce cfg size rng :=
    if cond then
      (PropTestable.toProperty (body ())).runOnce cfg size rng
    else
      pure (.discarded, 0, rng)

/-- Precondition guard syntax for properties: `(n != 0) ==> Nat.blt (n - 1) n`. -/
syntax:25 term:26 " ==> " term:25 : term
macro_rules
  | `($c ==> $b) => `(LSpec.Prop.implies $c (fun () => $b))

/-- Greedy shrinking loop bounded by `maxShrinks`. -/
private partial def shrinkLoop [PropTestable β] (cfg : PropertyConfig) (size : Nat)
    (innerRng : Rng) (shrink : α → List α) (f : α → β)
    (curX : α) (curArgs : List String) (curMsg : String) (curPos : Option SourcePos)
    (stepsLeft : Nat) (totalShrinks : Nat) : IO (α × List String × String × Option SourcePos × Nat) := do
  if stepsLeft == 0 then
    return (curX, curArgs, curMsg, curPos, totalShrinks)
  let candidates := shrink curX
  for cand in candidates do
    let (res, innerShrinks, _) ← (PropTestable.toProperty (f cand)).runOnce cfg size innerRng
    match res with
    | .failed candArgs candMsg candPos =>
      return ← shrinkLoop cfg size innerRng shrink f cand candArgs candMsg candPos
        (stepsLeft - 1) (totalShrinks + 1 + innerShrinks)
    | _ => pure ()
  return (curX, curArgs, curMsg, curPos, totalShrinks)

/-- Format a generated argument for counterexample display.
    Provides built-in support for `Repr`, `ToString`, and `ByteArray` without orphan instances. -/
class FormatValue (α : Type u) where
  formatValue : α → String

instance (priority := high) [Repr α] : FormatValue α where
  formatValue x := reprStr x

instance (priority := low) [ToString α] : FormatValue α where
  formatValue x := toString x

instance : FormatValue ByteArray where
  formatValue bs := s!"ByteArray({bs.data.toList})"

/-- Quantify over a custom generator and shrinker with an optional argument label. -/
def forAllShrink [FormatValue α] [PropTestable β] (gen : Gen α) (shrink : α → List α)
    (f : α → β) (label : Option String := none) : Property where
  runOnce cfg size rng := do
    let (x, rngAfterSample) := gen.runWith size rng
    let (res, innerShrinks, rngAfterBody) ← (PropTestable.toProperty (f x)).runOnce cfg size rngAfterSample
    match res with
    | .passed => return (.passed, 0, rngAfterBody)
    | .discarded => return (.discarded, 0, rngAfterBody)
    | .failed args msg pos =>
      let (minX, minArgs, minMsg, minPos, totalShrinks) ←
        shrinkLoop cfg size rngAfterSample shrink f x args msg pos cfg.maxShrinks innerShrinks
      let rendered := FormatValue.formatValue minX
      let formatted := match label with
        | some name => s!"{name} := {rendered}"
        | none => rendered
      return (.failed (formatted :: minArgs) minMsg minPos, totalShrinks, rngAfterBody)

/-- Quantify over a custom generator using `Shrinkable α`. -/
def forAll [FormatValue α] [Shrinkable α] [PropTestable β] (gen : Gen α)
    (f : α → β) (label : Option String := none) : Property :=
  forAllShrink gen Shrinkable.shrink f label

/-- Quantify over a custom generator with shrinking disabled. -/
def forAllNoShrink [FormatValue α] [PropTestable β] (gen : Gen α)
    (f : α → β) (label : Option String := none) : Property :=
  forAllShrink gen (fun _ => []) f label

/-- Quantify over `Sampleable α` with an explicit variable name shown in counterexamples. -/
def forAllNamed [Sampleable α] [Shrinkable α] [FormatValue α] [PropTestable β]
    (name : String) (f : α → β) : Property :=
  forAllShrink Sampleable.sample Shrinkable.shrink f (some name)

/-- Automatic property checking for arbitrary-arity functions `α → β`. -/
instance (priority := low) [Sampleable α] [Shrinkable α] [FormatValue α] [PropTestable β] :
    PropTestable (α → β) where
  toProperty f := forAllShrink Sampleable.sample Shrinkable.shrink f none

/-- Overall result of running a property test suite. -/
inductive PropertyResult where
  | passed (numTests : Nat) (seed : UInt64)
  | failed (args : List String) (message : String) (pos : Option SourcePos)
      (numTests : Nat) (numShrinks : Nat) (seed : UInt64)
  | gaveUp (discarded : Nat) (passed : Nat) (seed : UInt64)
  deriving BEq, Repr

/-- Execute a `Property` with `cfg` and explicit `seed`. -/
def runProperty (prop : Property) (cfg : PropertyConfig) (seed : UInt64) : IO PropertyResult := do
  let maxDiscards := cfg.numTests * cfg.maxDiscardRatio
  let mut passed := 0
  let mut discarded := 0
  let mut rng := Rng.ofSeed seed
  while passed < cfg.numTests do
    let attempt := passed + discarded
    let size :=
      if cfg.numTests ≤ 1 then cfg.maxSize
      else min cfg.maxSize ((attempt * cfg.maxSize) / (cfg.numTests - 1))
    let (outcome, shrinks, rng') ← prop.runOnce cfg size rng
    rng := rng'
    match outcome with
    | .passed =>
      passed := passed + 1
    | .discarded =>
      discarded := discarded + 1
      if discarded > maxDiscards then
        return .gaveUp discarded passed seed
    | .failed args msg pos =>
      return .failed args msg pos (passed + 1) shrinks seed
  return .passed passed seed

/-- Format counterexample arguments for failure output. -/
def formatCounterexample (args : List String) (msg : String)
    (pos : Option SourcePos) (failedAt : Nat) (totalTests : Nat)
    (numShrinks : Nat) (seed : UInt64) : String :=
  let argLines := args.zipIdx.map fun (a, i) =>
    if (a.splitOn " := ").length > 1 then s!"  {a}"
    else s!"  arg {i} := {a}"
  let locLine := match pos with
    | some p => [s!"  at {p}"]
    | none => []
  let header := s!"Falsified after {failedAt}/{totalTests} tests ({numShrinks} shrinks, seed {seed}):"
  let body := argLines ++ locLine ++ [s!"  reason: {msg}"]
  "\n".intercalate (header :: body)

/-- A packaged property test implementing `LSpec.IsTest`.
    Defers construction of the `Property` via `Unit → Property` so nothing runs on import. -/
structure PropTest where
  mkProperty : Unit → Property
  config : PropertyConfig := {}

namespace PropTest

def of [PropTestable α] (p : Unit → α) (config : PropertyConfig := {}) : PropTest :=
  { mkProperty := fun () => PropTestable.toProperty (p ()), config }

end PropTest

instance : IsTest PropTest where
  run ctx pt := do
    let cfg := PropertyConfig.fromOptions ctx.options pt.config
    let seed := cfg.seed.getD ctx.seed
    let prop ← IO.lazyPure pt.mkProperty
    match ← runProperty prop cfg seed with
    | .passed n s =>
      return .pass s!"({n} tests, seed {s})"
    | .gaveUp d p s =>
      return .fail
        s!"gave up after {d} discarded inputs ({p}/{cfg.numTests} passed, seed {s})"
        ""
        (.gaveUp s d p)
    | .failed args msg pos failedAt shrinks s =>
      let details := formatCounterexample args msg pos failedAt cfg.numTests shrinks s
      return .fail
        s!"falsified after {failedAt}/{cfg.numTests} tests ({shrinks} shrinks, seed {s})"
        details
        (.property s failedAt shrinks)

end
end LSpec.Prop
