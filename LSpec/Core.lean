module
public import Std.Data.HashMap

/-!
# LSpec Core

Core test tree IR, outcomes, options, and processor abstractions.
Inspired by `nest-core` (`TestTree`, `IsTest`, `TestProcessor`) and `Hspec`
(`parallel`/`sequential` execution modes, tags, scoped resources).

This module has no runtime dependency on the `Lean` compiler library so test
binaries stay lightweight and fast to compile and import.
-/

namespace LSpec
public section

/-- Source location captured at compile time for assertion failure reporting. -/
structure SourcePos where
  file : String
  line : Nat
  col : Nat
  deriving BEq, Repr, Inhabited

instance : ToString SourcePos where
  toString p := s!"{p.file}:{p.line}:{p.col}"

/-- Dynamically-typed option value stored in `TestOptions`. -/
inductive OptionValue where
  | bool (val : Bool)
  | nat (val : Nat)
  | uint64 (val : UInt64)
  | string (val : String)
  deriving BEq, Repr

/-- Key-value options passed through the `TestTree` and to `TestProcessor`s. -/
structure TestOptions where
  entries : Std.HashMap String OptionValue := {}

namespace TestOptions

def empty : TestOptions := {}

def setBool (o : TestOptions) (key : String) (v : Bool) : TestOptions :=
  { entries := o.entries.insert key (.bool v) }

def setNat (o : TestOptions) (key : String) (v : Nat) : TestOptions :=
  { entries := o.entries.insert key (.nat v) }

def setUInt64 (o : TestOptions) (key : String) (v : UInt64) : TestOptions :=
  { entries := o.entries.insert key (.uint64 v) }

def setString (o : TestOptions) (key : String) (v : String) : TestOptions :=
  { entries := o.entries.insert key (.string v) }

def getBool? (o : TestOptions) (key : String) : Option Bool :=
  match o.entries[key]? with
  | some (.bool v) => some v
  | _ => none

def getBool (o : TestOptions) (key : String) (default : Bool := false) : Bool :=
  (o.getBool? key).getD default

def getNat? (o : TestOptions) (key : String) : Option Nat :=
  match o.entries[key]? with
  | some (.nat v) => some v
  | _ => none

def getNat (o : TestOptions) (key : String) (default : Nat := 0) : Nat :=
  (o.getNat? key).getD default

def getUInt64? (o : TestOptions) (key : String) : Option UInt64 :=
  match o.entries[key]? with
  | some (.uint64 v) => some v
  | some (.nat v) => some v.toUInt64
  | _ => none

def getUInt64 (o : TestOptions) (key : String) (default : UInt64 := 0) : UInt64 :=
  (o.getUInt64? key).getD default

def getString? (o : TestOptions) (key : String) : Option String :=
  match o.entries[key]? with
  | some (.string v) => some v
  | _ => none

def getString (o : TestOptions) (key : String) (default : String := "") : String :=
  (o.getString? key).getD default

def contains (o : TestOptions) (key : String) : Bool :=
  o.entries.contains key

/-- Merge two option maps, with `override` taking precedence over `base`. -/
def merge (base override : TestOptions) : TestOptions :=
  override.entries.fold (init := base) fun acc k v =>
    { entries := acc.entries.insert k v }

end TestOptions

/-- Execution concurrency mode for a subtree of tests. -/
inductive ExecutionMode where
  /-- Tests in this subtree may run concurrently up to the configured thread limit. -/
  | parallel
  /-- Tests in this subtree run one at a time in declaration order. -/
  | sequential
  deriving BEq, Repr, Inhabited

/-- Combine an enclosing execution mode with an inner `.withMode` modifier.
    Once inside a `.sequential` scope, nested `.parallel` stays `.sequential`
    so sequential ordering invariants cannot be violated by inner subtrees. -/
@[expose] def ExecutionMode.combine (outer inner : ExecutionMode) : ExecutionMode :=
  match outer with
  | .sequential => .sequential
  | .parallel => inner

/-- Why a test failed. -/
inductive FailureReason where
  /-- A unit test assertion or boolean expectation failed. -/
  | assertion (pos : Option SourcePos := none)
  /-- A property test found a counterexample. -/
  | property (seed : UInt64) (numTests : Nat) (numShrinks : Nat)
  /-- A property test discarded too many generated inputs. -/
  | gaveUp (seed : UInt64) (discarded : Nat) (passed : Nat)
  /-- An uncaught `IO.Error` was thrown while running the test. -/
  | exception (error : String)
  deriving BEq, Repr

/-- The outcome of running a single test. -/
inductive Outcome where
  | passed
  | skipped (reason : Option String := none)
  | failed (reason : FailureReason)
  deriving BEq, Repr, Inhabited

/-- Full result returned by executing a single test. -/
structure TestResult where
  outcome : Outcome
  summary : String := ""
  details : String := ""
  deriving BEq, Repr, Inhabited

namespace TestResult

@[expose] def pass (summary : String := "") (details : String := "") : TestResult :=
  { outcome := .passed, summary, details }

@[expose] def skip (reason : Option String := none) : TestResult :=
  { outcome := .skipped reason, summary := reason.getD "pending" }

@[expose] def fail (summary : String) (details : String := "")
    (reason : FailureReason := .assertion none) : TestResult :=
  { outcome := .failed reason, summary, details }

@[expose] def isPassed (r : TestResult) : Bool :=
  match r.outcome with
  | .passed => true
  | _ => false

@[expose] def isSkipped (r : TestResult) : Bool :=
  match r.outcome with
  | .skipped _ => true
  | _ => false

@[expose] def isFailed (r : TestResult) : Bool :=
  match r.outcome with
  | .failed _ => true
  | _ => false

end TestResult

/-- Runtime context passed to every test execution. -/
structure TestContext where
  options : TestOptions := {}
  /-- Full hierarchical path of enclosing group names and the leaf test name. -/
  path : Array String := #[]
  /-- Deterministic per-test seed derived from the runner's master seed and `path`. -/
  seed : UInt64 := 0

namespace TestContext

/-- Dot-free slash-separated display path (e.g. `"Math/Addition/commutativity"`). -/
def pathString (ctx : TestContext) : String :=
  "/".intercalate ctx.path.toList

end TestContext

/-- Core extensibility class describing any type that can be executed as a test. -/
class IsTest (t : Type) where
  run : TestContext → t → IO TestResult

/-- Specification for a shared resource acquired once for a subtree and released
after all tests in that subtree finish. -/
structure ResourceSpec (α : Type) where
  description : String
  acquire : IO α
  release : α → IO Unit := fun _ => pure ()

/-- The core `TestTree` intermediate representation (living in `Type 0`).

Every leaf test is deferred as a closure `TestContext → IO TestResult`, so
building or inspecting a `TestTree` (e.g. for `--list` or filtering) never
executes test code or acquires resources. -/
inductive TestTree : Type where
  /-- A single deferred test leaf. -/
  | leaf (name : String) (tags : Array String) (exec : TestContext → IO TestResult)
  /-- A named group of child test trees. -/
  | group (name : String) (children : Array TestTree)
  /-- Override the concurrency mode (`parallel` or `sequential`) for a subtree. -/
  | withMode (mode : ExecutionMode) (child : TestTree)
  /-- Attach tags to every test in a subtree. -/
  | withTags (tags : Array String) (child : TestTree)
  /-- Transform `TestOptions` for a subtree. -/
  | withOptions (f : TestOptions → TestOptions) (child : TestTree)
  /-- Wrap every leaf execution in a subtree (used for `beforeEach`/`afterEach`/`aroundEach`). -/
  | aroundEach (wrap : (TestContext → IO TestResult) → TestContext → IO TestResult) (child : TestTree)
  /-- Acquire a shared resource before running `child`, and run the returned
      release action in a `finally` block once `child` completes. -/
  | withResource (description : String) (acquire : IO (IO Unit)) (child : TestTree)

instance : Inhabited TestTree := ⟨.group "" #[]⟩

namespace TestTree

/-- Build a single leaf node from any `IsTest` instance. -/
def single [inst : IsTest t] (name : String) (test : t) (tags : Array String := #[]) : TestTree :=
  .leaf name tags (fun ctx => inst.run ctx test)

/-- Combine multiple trees under a named group. -/
def ofArray (name : String) (children : Array TestTree) : TestTree :=
  .group name children

/-- Combine multiple trees under a named group. -/
def ofList (name : String) (children : List TestTree) : TestTree :=
  .group name children.toArray

end TestTree

/-- A pluggable processor that consumes a `TestTree` and `TestOptions`
(e.g. running tests in parallel, listing test paths, formatting reports). -/
structure TestProcessor where
  name : String
  shouldRun : TestOptions → Bool
  exec : TestOptions → TestTree → IO UInt32

namespace TestProcessor

/-- Run the first processor whose `shouldRun` predicate matches `opts`. -/
def runFirst? (procs : List TestProcessor) (opts : TestOptions) (tree : TestTree) :
    Option (IO UInt32) :=
  match procs.find? (·.shouldRun opts) with
  | some p => some (p.exec opts tree)
  | none => none

end TestProcessor

/-- Mix a `UInt64` using SplitMix64 finalizer for deterministic per-test seed derivation. -/
@[expose] def mixSeed (x : UInt64) : UInt64 :=
  let z := (x + 0x9E3779B97F4A7C15)
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- Derive a deterministic per-test seed from a master seed and the test path. -/
@[expose] def deriveTestSeed (masterSeed : UInt64) (path : Array String) : UInt64 :=
  let h := path.foldl (init := masterSeed) fun acc seg =>
    mixSeed (acc ^^^ seg.hash)
  mixSeed h

end
end LSpec
