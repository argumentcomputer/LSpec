# LSpec

A lightweight, **Bool-based**, **parallel-first**, **formally verified** testing framework for Lean 4 with zero external dependencies.

LSpec combines ideas from:
- **[Hspec](https://hspec.github.io/)**: ergonomic `SpecM` `do`-block DSL (`describe`, `context`, `it`, `prop`, `shouldBe`, `beforeAll`, `parallel`, `sequential`, `xit`/`pending`)
- **[nest-core](https://github.com/hargoniX/nest-core)**: `TestTree` IR, extensible `IsTest` typeclass, pluggable `TestProcessor`s, and scoped resources
- **[nest-unit](https://github.com/hargoniX/nest-unit)**: `AssertM` monad with compile-time source locations (`file:line:col`) via `pos%`
- **[nest-slimcheck](https://github.com/hargoniX/nest-slimcheck)**: per-test deterministic seeds always printed for reproducible property-test failures

## Key Design Goals

1. **Zero import-time overhead**:
   - All tests are `Bool`- and `AssertM`-based (no `Prop`/`Decidable` synthesis, proof-erasure overhead, or runtime `Lean` compiler dependency).
   - Every leaf test (`it`, `itBool`, `prop`, `propWith`) is deferred under a `Unit →` thunk inside `Spec` (`StateT (Array TestTree) BaseIO Unit`). For test libraries or declarations containing heavy closed pure expressions inside `it` blocks, setting `compiler.extract_closed false` (e.g. `moreLeanArgs = ["-Dcompiler.extract_closed=false"]` on your test library) prevents Lean from hoisting them into module initializers. Importing test modules does zero test work.
2. **Bounded-thread parallel execution (`-j N` / `--threads N`)**:
   - A fixed-size worker pool runs at most `N` tests concurrently while releasing each completed test closure immediately so peak RSS stays proportional to `N` rather than total suite size.
   - Per-test stdout/stderr isolation (`IO.FS.withIsolatedStreams`) keeps output deterministic and readable.
   - `sequential` subtrees and scoped `withResource`/`beforeAll` fixtures compose cleanly with parallelism.
3. **Deterministic, thread-safe Bool property testing**:
   - Pure SplitMix64 `Gen` monad (never mutates global `IO.stdGenRef`), with fuel-bounded shrinking and deterministic per-test seeds derived from `(masterSeed, testPath)`.
4. **Formally verified runner (`LSpecProofs`)**:
   - Core filtering, reporting, and plan-compilation logic is total and verified directly in Lean with zero `sorry`s, alongside a small-step operational semantics proof of bounded concurrency, sequential exclusion, resource bracket safety, deadlock freedom, and sequential–parallel equivalence—enforced in CI with zero overhead for consumers.

## Installation & Quick Start

Add LSpec as a dependency and register a test driver executable in `lakefile.toml`:

```toml
testDriver = "tests"

[[require]]
name = "LSpec"
git = "https://github.com/argumentcomputer/LSpec"
rev = "main"

[[lean_exe]]
name = "tests"
root = "Tests.Main"
```

Write your test suite in `Tests/Main.lean` (see also [Examples/Examples.lean](Examples/Examples.lean)):

```lean
import LSpec

open LSpec LSpec.Prop

def mySuite : Spec := do
  describe "Arithmetic" do
    it "adds numbers" do
      shouldBe (2 + 2) 4
      shouldBeLt (3 : Nat) 5

    itBool "multiplies numbers" (3 * 4 == 12)

    prop "addition is commutative" fun (a b : Nat) =>
      a + b == b + a

    prop "subtraction with guard" fun (a b : Nat) =>
      (Nat.ble b a) ==> (a - b + b == a)

def main (args : List String) : IO UInt32 :=
  lspecMain mySuite args
```

Run via `lake test` or invoke the compiled binary directly:

```bash
# Run sequentially (default)
lake test

# Run with 4 worker threads (bounded concurrency for CI speed vs. RSS tuning)
lake test -- -j 4

# List all tests without running tests or acquiring resources
lake test -- --list

# Filter by path, exact path, exclusion, or tags
lake test -- Arithmetic --exclude slow --tag fast

# Reproduce a property-test failure with its reported seed
lake test -- --seed 123456789 --num-tests 200
```

## Assertions & Expectations (`AssertM`)

Inside `it "description" do ...`, assertions run in `AssertM Unit` (`ExceptT AssertStop IO Unit`) and capture the exact `file:line:col` of any failure:

| Function | Purpose |
|---|---|
| `expect cond` / `assertTrue cond` | Fail if `cond == false` *(note: `assert` is a Lean 4 `do`-keyword)* |
| `expectFalse cond` / `assertFalse cond` | Fail if `cond == true` |
| `expectAll conds` / `assertAll conds` | Fail with index on first `false` in `Array Bool` |
| `shouldBe actual expected` | `BEq` equality with `Repr` diff |
| `shouldNotBe actual unexpected` | `BEq` inequality |
| `shouldSatisfy actual pred label` | Boolean predicate check |
| `shouldBeLt` / `shouldBeLe` / `shouldBeGt` / `shouldBeGe` | `Ord`-based comparisons |
| `shouldContain` / `shouldContainSubstr` | List / String containment |
| `shouldReturn action expected` | Assert `IO` return value |
| `shouldThrow action expectedSubstr?` | Assert `IO` throws an error |
| `expectSome` / `expectNone` | Unwrap `Option` in `do`-notation |
| `expectOk` / `expectOkRepr` / `expectErr` | Unwrap `Except` in `do`-notation |
| `fail msg` / `pending` / `pendingWith reason` | Explicit failure or pending skip |

## Property-Based Testing (`LSpec.Prop`)

Properties accept arbitrary-arity functions returning `Bool`, `AssertM Unit`, `Except String Unit`, precondition guards (`==>`), or explicit generators (`forAll`, `forAllShrink`, `forAllNoShrink`, `forAllNamed`). Use `propWith` or `withPropConfig` to override sample counts, size, or seeds per test/subtree:

```lean
def propSuite : Spec := do
  describe "Lists" do
    prop "reverse involution" fun (xs : List Nat) =>
      xs.reverse.reverse == xs

    prop "append length (using AssertM)" fun (xs ys : List Nat) =>
      shouldBe (xs ++ ys).length (xs.length + ys.length)

    propWith "custom generator" { numTests := 200 } <|
      forAll (Gen.chooseNat 10 20) fun n =>
        Nat.ble 10 n && Nat.ble n 20
```

Custom types only need `Sampleable`, `Shrinkable` (no `WellFoundedRelation` proof required), and `Repr` (or `ToString` / `FormatValue`):

```lean
structure Pair where
  left : Nat
  right : Nat
  deriving BEq, Repr

instance : Shrinkable Pair where
  shrink p :=
    (Shrinkable.shrink p.left).map (fun l => { p with left := l }) ++
    (Shrinkable.shrink p.right).map (fun r => { p with right := r })

instance : Sampleable Pair where
  sample := return { left := ← Gen.chooseNat 0 (← Gen.getSize),
                     right := ← Gen.chooseNat 0 (← Gen.getSize) }
```

## Parallelism, Resources, and Hooks

- **`--threads N` / `-j N`**: caps concurrent test execution to `N` worker threads. Completed test closures are dropped immediately upon finishing to keep peak RSS bounded.
- **Preventing closed-term hoisting**: plain `def mySuite : Spec := do ...` works for both top-level and parameterized suites. If a test module contains expensive closed pure expressions inside `it`/`itBool` bodies, add `set_option compiler.extract_closed false` (or `moreLeanArgs = ["-Dcompiler.extract_closed=false"]` on your test library) so Lean never hoists them into module initializers.
- **`sequential do ...` / `parallel do ...`**: override concurrency per subtree. A `sequential` subtree runs its tests strictly in order as one pool job, while sibling `sequential` subtrees may still run concurrently if their parent is `parallel`.
- **`withResource` / `beforeAll`**: acquire a shared resource once for a subtree and release it in `finally` after all tests in that subtree complete. Never acquired during `--list` or when filtered out.
- **`beforeEach` / `afterEach` / `aroundEach`**: per-leaf lifecycle hooks.
- **`withTag` / `withTags`**: tag subtrees for `--tag` and `--exclude-tag` selection.
- **`withOptions` / `withPropConfig`**: scope configuration overrides to a subtree.

## CLI Options (`lspecMain` / `defaultMain`)

Any test executable whose `main` delegates to `lspecMain` (or `defaultMain` / `defaultMainTree`) automatically parses the flags below via `LSpec.parseCliArgs`. Pass them via `lake test -- <flags>`, `lake exe <target> <flags>`, or directly to the compiled binary (projects with custom drivers calling `runSpec` / `runTree` programmatically can reuse `parseCliArgs` or define their own CLI):

```
  -j, --threads <N>       Run up to N tests concurrently (default: 1)
  --sequential            Run all tests sequentially (alias for --threads 1)
  --list                  List matching test paths and exit without running
  <pattern>               Run only tests whose path contains <pattern>
  --filter <pattern>      Same as positional <pattern> (repeatable)
  --exact <path>          Run only tests matching <path> exactly (repeatable)
  --exclude <pattern>     Exclude tests whose path contains <pattern>
  --tag <tag>             Run only tests carrying <tag> (repeatable)
  --exclude-tag <tag>     Skip tests carrying <tag> (repeatable)
  --seed <u64>            Master seed for deterministic property tests
  --num-tests <N>         Override property-test sample count
  --max-size <N>          Override property-test maximum generator size
  --fail-fast             Stop starting new tests after the first failure
  --color / --no-color    Force or disable ANSI color output
  -v, --verbose           Show extra details and captured output on passes
  -h, --help              Show this help message
```

`--exclude=a,b`, `--tag=a,b`, and `--exclude-tag=a,b` also accept comma-separated lists, and `NO_COLOR` disables ANSI colors when neither `--color` nor `--no-color` is passed.

## Formal Verification (`LSpecProofs`)

The core pure functions in `LSpec.Runner` (`filterTree`, `listTests`, `ReportTree.summarize`, `ReportTree.failures`, `compilePlan`, `computeWorkerCount`) are total and formally verified in the optional `LSpecProofs` library (zero `sorry`s, zero external dependencies, zero runtime overhead for consumers):

- **[LSpecProofs/Filter.lean](LSpecProofs/Filter.lean)**: filter soundness & completeness (`listTests_filterTree_eq`), idempotence (`filterTree_idempotent`), empty-filter identity, exclusion dominance, and non-empty surviving `withResource` scopes (filtered-out resources are never acquired).
- **[LSpecProofs/Report.lean](LSpecProofs/Report.lean)**: exact report accounting (`passed + failed + skipped = leafCount`, `failed = failures.size`, `allPassed ↔ failures.isEmpty`), permutation invariance of summary counts across parallel completion orders, `compilePlan` equivalence with `listTests`, deterministic per-test seed assignment, and `computeWorkerCount` bounds.
- **[LSpecProofs/Concurrency.lean](LSpecProofs/Concurrency.lean)**: small-step operational semantics of the bounded `WorkerPool` + `ExecPlan` scheduler proving bounded concurrency (`activeWorkers ≤ cap`), sequential exclusion & strict left-to-right ordering, `withResource` acquire/release bracketing (no child before acquire, no release before children finish, exact-once release on termination), deadlock freedom & strong normalization, and sequential–parallel confluence (`parallel_eq_sequential`).
- **[LSpecProofs/Axioms.lean](LSpecProofs/Axioms.lean)**: compile-time `#guard_msgs in #print axioms` gate ensuring all 31 headline theorems rely exclusively on Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero `sorryAx` or custom axioms, built with `-DwarningAsError=true` in CI.

Build and verify all proofs with:

```sh
lake build LSpecProofs --wfail
```
