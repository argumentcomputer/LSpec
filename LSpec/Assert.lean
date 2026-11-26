module
public import LSpec.Core
public meta import Lean.Elab.Term

/-!
# Bool-based Assertions & Expectations (`AssertM`)

Combines `nest-unit` (source-location tracking via `pos%` and `ExceptT`
assertions) with `Hspec` expectations (`shouldBe`, `shouldNotBe`,
`shouldSatisfy`, `shouldThrow`, `pending`) and `LSpec` unpacking helpers
(`expectSome`, `expectOk`, `expectErr`).

All assertions are `Bool`-based (no `Prop`/`Decidable` overhead), and `pos%`
imports `Lean.Elab.Term` only at `meta` stage so runtime test binaries have
zero dependency on the `Lean` compiler library.
-/

namespace LSpec
public section

open Lean Elab Term in
/-- Compile-time macro expanding to the current `LSpec.SourcePos` literal. -/
elab "pos%" : term => do
  let file ← getFileName
  let fileMap ← getFileMap
  let pos := match (← getRef).getPos? with
    | some p => fileMap.toPosition p
    | none => { line := 0, column := 0 }
  let stx ← `(LSpec.SourcePos.mk $(quote file) $(quote pos.line) $(quote pos.column))
  elabTerm stx (some (mkConst ``LSpec.SourcePos))

/-- Details of a failed assertion. -/
structure AssertionError where
  message : String
  details : String := ""
  pos : Option SourcePos := none
  deriving BEq, Repr

/-- Early termination of an `AssertM` test body: either failure or pending/skipped. -/
inductive AssertStop where
  | failed (err : AssertionError)
  | skipped (reason : Option String := none)
  deriving BEq, Repr

/-- Monad for unit tests with assertions and IO effects.
    Defined as a nominal single-field `structure` (erased to `IO (Except AssertStop α)`
    at runtime) so `do`-notation never unfolds `AssertM α` to `IO (Except AssertStop α)`
    and always inserts `MonadLift IO AssertM` cleanly for polymorphic `IO` actions such
    as `IO.ofExcept` or `withResource` getters. -/
structure AssertM (α : Type) where
  /-- Execute an `AssertM` action in `IO`. -/
  run : IO (Except AssertStop α)

namespace AssertM

instance : Monad AssertM where
  pure a := ⟨pure (.ok a)⟩
  bind m f := ⟨do
    match ← m.run with
    | .ok a => (f a).run
    | .error e => pure (.error e)⟩

instance : MonadExceptOf AssertStop AssertM where
  throw e := ⟨pure (.error e)⟩
  tryCatch m h := ⟨do
    match ← m.run with
    | .ok a => pure (.ok a)
    | .error e => (h e).run⟩

instance : MonadLift IO AssertM where
  monadLift m := ⟨.ok <$> m⟩

instance : MonadLift BaseIO AssertM where
  monadLift m := ⟨.ok <$> m⟩

instance : MonadFinally AssertM where
  tryFinally' x h := ⟨do
    let r ← tryFinally' x.run fun res => do
      let a? := match res with
        | some (.ok a) => some a
        | _ => none
      (h a?).run
    match r with
    | (.ok a, .ok b) => pure (.ok (a, b))
    | (.error e, _) => pure (.error e)
    | (_, .error e) => pure (.error e)⟩

end AssertM

/-- Type alias for a unit test action. -/
abbrev UnitTest := AssertM Unit

instance : IsTest UnitTest where
  run _ action := do
    match ← action.run with
    | .ok () => return .pass
    | .error (.skipped reason) => return .skip reason
    | .error (.failed err) =>
      let loc := match err.pos with
        | some p => s!"at {p}"
        | none => ""
      let details :=
        if loc.isEmpty then err.details
        else if err.details.isEmpty then loc
        else s!"{loc}\n{err.details}"
      return .fail err.message details (.assertion err.pos)

/-- Deferred pure `Bool` test (`Unit → Bool`). Eager `Bool` is intentionally not
an `IsTest` instance so pure test expressions are never evaluated eagerly. -/
instance : IsTest (Unit → Bool) where
  run _ f := do
    let ok ← IO.lazyPure f
    if ok then return .pass
    else return .fail "assertion failed" "evaluated to false" (.assertion none)

/-- Deferred `IO Bool` test. -/
instance : IsTest (IO Bool) where
  run _ action := do
    if ← action then return .pass
    else return .fail "assertion failed" "evaluated to false" (.assertion none)

/-! ## Core Assertion Primitives -/

/-- Unconditionally fail the current test with a message and optional details. -/
def fail (message : String) (details : String := "")
    (pos : SourcePos := by exact pos%) : AssertM α :=
  throw (.failed { message, details, pos := some pos })

/-- Mark the current test as pending / skipped. -/
def pending (reason : Option String := none) : AssertM α :=
  throw (.skipped reason)

/-- Mark the current test as pending / skipped with an explanation. -/
def pendingWith (reason : String) : AssertM α :=
  throw (.skipped (some reason))

/-- Assert that a `Bool` condition is `true`.
    (Named `expect` / `assertTrue` because `assert` is a reserved `do`-block keyword in Lean 4.) -/
def expect (cond : Bool) (message : String := "expected true, got false")
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  unless cond do
    throw (.failed { message, pos := some pos })

/-- Alias for `expect`. -/
abbrev assertTrue (cond : Bool) (message : String := "expected true, got false")
    (pos : SourcePos := by exact pos%) : AssertM Unit :=
  expect cond message pos

/-- Assert that a `Bool` condition is `false`. -/
def expectFalse (cond : Bool) (message : String := "expected false, got true")
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  if cond then
    throw (.failed { message, pos := some pos })

/-- Alias for `expectFalse`. -/
abbrev assertFalse (cond : Bool) (message : String := "expected false, got true")
    (pos : SourcePos := by exact pos%) : AssertM Unit :=
  expectFalse cond message pos

/-- Assert that every boolean in an `Array Bool` is `true`, reporting the first failing index. -/
def expectAll (conds : Array Bool) (message : String := "assertion failed")
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  for h : i in [:conds.size] do
    unless conds[i] do
      throw (.failed {
        message := s!"{message} (at index {i})"
        pos := some pos
      })

/-- Alias for `expectAll`. -/
abbrev assertAll (conds : Array Bool) (message : String := "assertion failed")
    (pos : SourcePos := by exact pos%) : AssertM Unit :=
  expectAll conds message pos

/-! ## Hspec-style Expectations -/

/-- Assert that `actual == expected` using `BEq`. -/
def shouldBe [BEq α] [Repr α] (actual expected : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  unless actual == expected do
    throw (.failed {
      message := "values not equal"
      details := s!"expected: {reprStr expected}\n but got: {reprStr actual}"
      pos := some pos
    })

/-- Assert that `actual != unexpected` using `BEq`. -/
def shouldNotBe [BEq α] [Repr α] (actual unexpected : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  if actual == unexpected then
    throw (.failed {
      message := "values unexpectedly equal"
      details := s!"did not expect: {reprStr unexpected}"
      pos := some pos
    })

/-- Assert that `actual` satisfies a boolean predicate `pred`. -/
def shouldSatisfy [Repr α] (actual : α) (pred : α → Bool)
    (label : String := "predicate") (pos : SourcePos := by exact pos%) : AssertM Unit := do
  unless pred actual do
    throw (.failed {
      message := s!"value failed to satisfy {label}"
      details := s!"value: {reprStr actual}"
      pos := some pos
    })

/-- Assert that `actual < bound` using `Ord`. -/
def shouldBeLt [Ord α] [Repr α] (actual bound : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  unless compare actual bound == .lt do
    throw (.failed {
      message := "expected strictly less than"
      details := s!"got: {reprStr actual}\nnot < {reprStr bound}"
      pos := some pos
    })

/-- Assert that `actual ≤ bound` using `Ord`. -/
def shouldBeLe [Ord α] [Repr α] (actual bound : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  let cmp := compare actual bound
  unless cmp == .lt || cmp == .eq do
    throw (.failed {
      message := "expected less than or equal"
      details := s!"got: {reprStr actual}\nnot ≤ {reprStr bound}"
      pos := some pos
    })

/-- Assert that `actual > bound` using `Ord`. -/
def shouldBeGt [Ord α] [Repr α] (actual bound : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  unless compare actual bound == .gt do
    throw (.failed {
      message := "expected strictly greater than"
      details := s!"got: {reprStr actual}\nnot > {reprStr bound}"
      pos := some pos
    })

/-- Assert that `actual ≥ bound` using `Ord`. -/
def shouldBeGe [Ord α] [Repr α] (actual bound : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  let cmp := compare actual bound
  unless cmp == .gt || cmp == .eq do
    throw (.failed {
      message := "expected greater than or equal"
      details := s!"got: {reprStr actual}\nnot ≥ {reprStr bound}"
      pos := some pos
    })

/-- Assert that a string contains `substr`. -/
def shouldContainSubstr (haystack substr : String)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  unless (haystack.splitOn substr).length > 1 || substr.isEmpty do
    throw (.failed {
      message := s!"expected string to contain {reprStr substr}"
      details := s!"actual: {reprStr haystack}"
      pos := some pos
    })

/-- Assert that a list contains `elem`. -/
def shouldContain [BEq α] [Repr α] (xs : List α) (elem : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  unless xs.contains elem do
    throw (.failed {
      message := s!"expected list to contain {reprStr elem}"
      details := s!"list: {reprStr xs}"
      pos := some pos
    })

/-- Assert that an `IO` action returns a value equal to `expected`. -/
def shouldReturn [BEq α] [Repr α] (action : IO α) (expected : α)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  let actual ← action
  shouldBe actual expected pos

/-- Assert that an `IO` action throws an `IO.Error`, optionally matching a substring. -/
def shouldThrow (action : IO α) (expectedSubstr : Option String := none)
    (pos : SourcePos := by exact pos%) : AssertM Unit := do
  let threw : Option String ← liftM (m := IO) do
    try
      let _ ← action
      pure none
    catch e =>
      pure (some e.toString)
  match threw with
  | none =>
    throw (.failed {
      message := "expected IO action to throw an exception, but it succeeded"
      pos := some pos
    })
  | some msg =>
    if let some sub := expectedSubstr then
      unless (msg.splitOn sub).length > 1 || sub.isEmpty do
        throw (.failed {
          message := s!"exception message did not contain {reprStr sub}"
          details := s!"got exception: {msg}"
          pos := some pos
        })

/-! ## Option & Except Unpacking Combinators -/

/-- Unwrap `Option.some a`, failing the test on `none`. -/
def expectSome (opt : Option α) (message : String := "expected 'some _', got 'none'")
    (pos : SourcePos := by exact pos%) : AssertM α :=
  match opt with
  | some a => pure a
  | none => throw (.failed { message, pos := some pos })

/-- Assert that an `Option` is `none`. -/
def expectNone [Repr α] (opt : Option α) (pos : SourcePos := by exact pos%) : AssertM Unit :=
  match opt with
  | none => pure ()
  | some a => throw (.failed {
      message := "expected 'none'"
      details := s!"got: some ({reprStr a})"
      pos := some pos
    })

/-- Unwrap `Except.ok a`, failing the test with the stringified error on `Except.error e`. -/
def expectOk [ToString ε] (res : Except ε α) (pos : SourcePos := by exact pos%) : AssertM α :=
  match res with
  | .ok a => pure a
  | .error e => throw (.failed {
      message := "expected 'Except.ok _', got 'Except.error'"
      details := s!"error: {e}"
      pos := some pos
    })

/-- Unwrap `Except.ok a`, formatting errors with `Repr`. -/
def expectOkRepr [Repr ε] (res : Except ε α) (pos : SourcePos := by exact pos%) : AssertM α :=
  match res with
  | .ok a => pure a
  | .error e => throw (.failed {
      message := "expected 'Except.ok _', got 'Except.error'"
      details := s!"error: {reprStr e}"
      pos := some pos
    })

/-- Unwrap `Except.error e`, failing the test on `Except.ok a`. -/
def expectErr [Repr α] (res : Except ε α) (pos : SourcePos := by exact pos%) : AssertM ε :=
  match res with
  | .error e => pure e
  | .ok a => throw (.failed {
      message := "expected 'Except.error _', got 'Except.ok'"
      details := s!"got: ok ({reprStr a})"
      pos := some pos
    })

end
end LSpec
