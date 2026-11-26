module
public import LSpec.Core
public import LSpec.Assert
public import LSpec.Property.Check

/-!
# Hspec-style Specification DSL (`SpecM`, `Spec`)

Provides a clean `do`-block DSL (`describe`, `context`, `it`, `prop`, `xit`,
`parallel`, `sequential`, `withTag`, `withOptions`, `withResource`,
`beforeAll`, `beforeEach`, `afterEach`, `aroundEach`) backed by the `TestTree` IR.

Because `Spec := SpecM Unit` is `StateT (Array TestTree) BaseIO Unit`, defining
a suite (`def mySuite : Spec := do ...`) does **zero** test-tree construction or
execution at module import time. For suites containing large closed pure
expressions inside `it` blocks (expressions that do not depend on any runtime
variable or parameter), set `set_option compiler.extract_closed false` on the
declaration or test library so Lean does not hoist them into module initializers.
-/

namespace LSpec
public section

/-- Specification builder monad accumulating `TestTree` nodes.
    Lives in `BaseIO` so suites are deferred until run time and `withResource`
    can allocate typed scope slots without acquiring resources during `--list`. -/
abbrev SpecM (α : Type) := StateT (Array TestTree) BaseIO α

/-- A test specification (Hspec-style `do` block). -/
abbrev Spec := SpecM Unit

/-- Run a `Spec` and collect its top-level `TestTree` children. -/
def Spec.collect (s : Spec) : BaseIO (Array TestTree) := do
  let (_, trees) ← s.run #[]
  return trees

/-- Run a `Spec` and wrap its children in a single named root `TestTree.group`. -/
def Spec.toTestTree (rootName : String := "") (s : Spec) : BaseIO TestTree := do
  let children ← s.collect
  if rootName.isEmpty && children.size == 1 then
    return children[0]!
  else
    return .group rootName children

/-- Push a raw `TestTree` node into the current `SpecM` scope. -/
def addTree (tree : TestTree) : SpecM Unit :=
  modify (·.push tree)

/-- Include another `Spec` inline in the current scope. -/
def includeSpec (s : Spec) : SpecM Unit := s

/-! ## Grouping -/

/-- Group related tests under a component/module description (Hspec `describe`). -/
def describe (name : String) (body : Spec) : SpecM Unit := do
  let children ← body.collect
  addTree (.group name children)

/-- Group related tests under a scenario/circumstance description (Hspec `context`). -/
def context (name : String) (body : Spec) : SpecM Unit :=
  describe name body

/-- Alias for `describe`. -/
def group (name : String) (body : Spec) : SpecM Unit :=
  describe name body

/-! ## Leaf Tests -/

/-- Define a deferred unit test whose body `Unit → AssertM Unit` is only evaluated
    when the test actually executes (never at module import, `--list`, or filtering). -/
def itThunk (name : String) (mkBody : Unit → AssertM Unit) : SpecM Unit :=
  addTree (.leaf name #[] fun ctx => do
    let action ← IO.lazyPure mkBody
    IsTest.run ctx action)

/-- Define a unit test whose body runs in `AssertM Unit` (Bool assertions + IO).
    Expands to `itThunk` so even pure `let` bindings at the top of a `do` block
    are deferred under a `Unit →` lambda and never execute during tree construction.
    Uses a non-reserved symbol so downstream code can still use `it` as an identifier. -/
syntax &"it " term:arg term : term
syntax &"it " term:arg " <| " term : term

macro_rules
  | `(it $name $body) => `(LSpec.itThunk $name (fun () => $body))
  | `(it $name <| $body) => `(LSpec.itThunk $name (fun () => $body))

/-- Define a unit test from any `IsTest` instance. -/
def test [IsTest t] (name : String) (tVal : t) : SpecM Unit :=
  addTree (.single name tVal)

/-- Define a deferred pure `Bool` unit test (`Unit → Bool`). -/
def itCheck (name : String) (cond : Unit → Bool) (pos : SourcePos := by exact pos%) : SpecM Unit :=
  itThunk name fun () => do
    let ok ← liftM (m := IO) (IO.lazyPure cond)
    expect ok "expected true, got false" pos

/-- Convenience macro for deferred pure `Bool` unit tests:
    `itBool "addition works" (2 + 2 == 4)`. -/
syntax &"itBool " term:arg term : term
macro_rules
  | `(itBool $name $cond) => `(LSpec.itCheck $name (fun () => $cond))

/-- Define a skipped / pending test (Hspec `xit`). The body is never executed. -/
def xitThunk (name : String) (_body : Unit → AssertM Unit := fun () => pure ())
    (reason : Option String := some "skipped (xit)") : SpecM Unit :=
  addTree (.leaf name #[] (fun _ => pure (.skip reason)))

syntax &"xit " term:arg term : term
macro_rules
  | `(xit $name $body) => `(LSpec.xitThunk $name (fun () => $body))

/-- Define a deferred Bool-based property test (`Unit → α`). -/
def propThunk [Prop.PropTestable α] (name : String) (mkBody : Unit → α)
    (config : Prop.PropertyConfig := {}) : SpecM Unit :=
  addTree (.single name (Prop.PropTest.of mkBody config))

/-- Define a Bool-based property test (`fun (a : A) (b : B) => ...`).
    Accepts any `Prop.PropTestable` body (`Bool`, `AssertM Unit`, `Except String Unit`,
    `==>`, `forAll`, or arbitrary-arity functions) and defers it under `fun () => ...`.
    Uses non-reserved symbols so downstream code can still use `prop` as an identifier. -/
syntax &"prop " term:arg term : term
syntax &"prop " term:arg " <| " term : term
syntax &"propWith " term:arg term:arg term : term
syntax &"propWith " term:arg term:arg " <| " term : term

macro_rules
  | `(prop $name $body) => `(LSpec.propThunk $name (fun () => $body))
  | `(prop $name <| $body) => `(LSpec.propThunk $name (fun () => $body))
  | `(propWith $name $cfg $body) => `(LSpec.propThunk $name (fun () => $body) $cfg)
  | `(propWith $name $cfg <| $body) => `(LSpec.propThunk $name (fun () => $body) $cfg)

/-- Define a skipped property test. -/
def xpropThunk (name : String) (_body : Unit → α)
    (reason : Option String := some "skipped (xprop)") : SpecM Unit :=
  addTree (.leaf name #[] (fun _ => pure (.skip reason)))

syntax &"xprop " term:arg term : term
macro_rules
  | `(xprop $name $body) => `(LSpec.xpropThunk $name (fun () => $body))

/-! ## Concurrency, Tags, and Options Modifiers -/

private def wrapChildren (wrap : TestTree → TestTree) (body : Spec) : SpecM Unit := do
  let children ← body.collect
  if children.size == 1 then
    addTree (wrap children[0]!)
  else if children.size > 1 then
    addTree (wrap (.group "" children))

/-- Allow tests in `body` to run concurrently (up to the runner's `--threads` limit). -/
def parallel (body : Spec) : SpecM Unit :=
  wrapChildren (.withMode .parallel) body

/-- Force tests in `body` to run sequentially in declaration order. -/
def sequential (body : Spec) : SpecM Unit :=
  wrapChildren (.withMode .sequential) body

/-- Attach a single tag to all tests in `body` (filterable via `--tag` / `--exclude-tag`). -/
def withTag (tag : String) (body : Spec) : SpecM Unit :=
  wrapChildren (.withTags #[tag]) body

/-- Attach multiple tags to all tests in `body`. -/
def withTags (tags : Array String) (body : Spec) : SpecM Unit :=
  wrapChildren (.withTags tags) body

/-- Override `TestOptions` for all tests in `body`. -/
def withOptions (f : TestOptions → TestOptions) (body : Spec) : SpecM Unit :=
  wrapChildren (.withOptions f) body

/-- Override property-testing defaults (`numTests`, `maxSize`, `seed`, etc.) for `body`. -/
def withPropConfig (cfg : Prop.PropertyConfig) (body : Spec) : SpecM Unit :=
  withOptions (fun opts =>
    let opts := opts
      |>.setNat "prop.numTests" cfg.numTests
      |>.setNat "prop.maxSize" cfg.maxSize
      |>.setNat "prop.maxDiscardRatio" cfg.maxDiscardRatio
      |>.setNat "prop.maxShrinks" cfg.maxShrinks
    match cfg.seed with
    | some s => opts.setUInt64 "prop.seed" s
    | none => opts) body

/-! ## Scoped Resources & Lifecycle Hooks -/

/-- Acquire a shared resource once before running `body`, pass a getter `IO α`
    to tests inside `body`, and release the resource in a `finally` block once
    all tests in `body` complete.

    Listing (`--list`) or filtering out `body` never calls `spec.acquire`. -/
def withResource (spec : ResourceSpec α) (body : IO α → Spec) : SpecM Unit := do
  let ref ← IO.mkRef (none : Option α)
  let getRes : IO α := do
    match ← ref.get with
    | some a => pure a
    | none => throw (IO.userError s!"Resource '{spec.description}' accessed outside its active scope")
  let children ← (body getRes).collect
  let acquire : IO (IO Unit) := do
    let a ← spec.acquire
    ref.set (some a)
    return do
      try
        spec.release a
      finally
        ref.set none
  let inner :=
    if children.size == 1 then children[0]!
    else .group "" children
  addTree (.withResource spec.description acquire inner)

/-- Hspec-style `beforeAll`: acquire a resource once for `body` (optional `release` hook). -/
def beforeAll (acquire : IO α) (release : α → IO Unit := fun _ => pure ())
    (description : String := "shared resource") (body : IO α → Spec) : SpecM Unit :=
  withResource { description, acquire, release } body

/-- Run a `setup` action before every leaf test in `body`. -/
def beforeEach (setup : IO Unit) (body : Spec) : SpecM Unit :=
  wrapChildren (.aroundEach fun run ctx => do setup; run ctx) body

/-- Run a `teardown` action after every leaf test in `body` (even on failure/exception). -/
def afterEach (teardown : IO Unit) (body : Spec) : SpecM Unit :=
  wrapChildren (.aroundEach fun run ctx => do
    try run ctx finally teardown) body

/-- Wrap every leaf test execution in `body` (Hspec `around`). -/
def aroundEach (wrap : IO TestResult → IO TestResult) (body : Spec) : SpecM Unit :=
  wrapChildren (.aroundEach fun run ctx => wrap (run ctx)) body

end
end LSpec
