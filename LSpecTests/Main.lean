import LSpec
import LSpecTests.ImportCheck

open LSpec LSpec.Prop

/-! # LSpec Self-Test Suite

Dogfoods LSpec's own `SpecM` DSL, `AssertM` expectations, Bool-based property
testing, bounded-thread parallel runner, scoped resources, filtering, and CLI.

Run all primary tests:
  `lake test`
  `lake exe tests -j 4`

Run the opt-in memory stress suite (50 × 100MB allocations):
  `lake exe tests --tag memory -j 4`
-/

/-- Helper to run a small inner `Spec` programmatically and inspect its result. -/
private def runInner (s : Spec) (cfg : RunConfig := {}) : IO (ReportTree × RunSummary) :=
  runSpec s cfg

/-! ## Assertions & Expectations -/

def assertionSuite : Spec := do
  describe "Assertions & Expectations" do
    it "expect and expectFalse pass on expected booleans" do
      expect true
      assertTrue true
      expectFalse false
      assertFalse false
      expectAll #[true, true, true]
      assertAll #[true, true, true]

    it "expect fails with source location on false" do
      let (rep, sum) ← runInner do
        it "failing expect" do
          expect false "custom failure"
      shouldBe sum.failed 1
      shouldBe sum.passed 0
      let fails := rep.failures
      shouldBe fails.size 1
      shouldContainSubstr fails[0]!.result.summary "custom failure"
      shouldContainSubstr fails[0]!.result.details "LSpecTests/Main.lean:"

    it "assertAll reports the failing index" do
      let (rep, sum) ← runInner do
        it "index 2 fails" do
          assertAll #[true, true, false, true] "check"
      shouldBe sum.failed 1
      shouldContainSubstr rep.failures[0]!.result.summary "index 2"

    it "shouldBe and shouldNotBe compare via BEq and format Repr on failure" do
      shouldBe (2 + 2) 4
      shouldNotBe "hello" "world"
      let (rep, sum) ← runInner do
        it "mismatch" do
          shouldBe (1 + 1) 3
      shouldBe sum.failed 1
      shouldContainSubstr rep.failures[0]!.result.details "expected: 3"
      shouldContainSubstr rep.failures[0]!.result.details "but got: 2"

    it "shouldSatisfy and ordering expectations work via Ord" do
      shouldSatisfy (42 : Nat) (· % 2 == 0) "even"
      shouldBeLt (1 : Nat) 2
      shouldBeLe (2 : Nat) 2
      shouldBeGt (5 : Nat) 3
      shouldBeGe (5 : Nat) 5
      shouldContain [1, 2, 3] 2
      shouldContainSubstr "hello world" "world"

    it "shouldReturn and shouldThrow test IO actions" do
      shouldReturn (pure 7 : IO Nat) 7
      shouldThrow (throw (IO.userError "boom: disk full") : IO Unit) (some "disk full")
      let (_, sum) ← runInner do
        it "did not throw" do
          shouldThrow (pure () : IO Unit)
      shouldBe sum.failed 1

    it "expectSome / expectNone / expectOk / expectErr unwrap cleanly" do
      let v ← expectSome (some 42)
      shouldBe v 42
      expectNone (none : Option Nat)
      let okVal ← expectOk (Except.ok 10 : Except String Nat)
      shouldBe okVal 10
      let errVal ← expectErr (Except.error "oops" : Except String Nat)
      shouldBe errVal "oops"

      let (_, sum) ← runInner do
        it "none fails" do
          let _ ← expectSome (none : Option Nat)
        it "error fails" do
          let _ ← expectOk (Except.error "bad" : Except String Nat)
      shouldBe sum.failed 2

    it "pending, pendingWith, and xit record skipped tests" do
      let (_, sum) ← runInner do
        it "p1" do pending
        it "p2" do pendingWith "waiting on upstream"
        xit "p3" do fail "must not run"
      shouldBe sum.skipped 3
      shouldBe sum.failed 0
      shouldBe sum.allPassed true

    itBool "itBool runs deferred pure Bool checks" (List.range 5 == [0, 1, 2, 3, 4])

    it "uncaught IO exceptions are caught per test without crashing the runner" do
      let (rep, sum) ← runInner do
        it "throws" do
          let _ ← (throw (IO.userError "unexpected crash") : IO Unit)
        it "still runs" do
          expect true
      shouldBe sum.failed 1
      shouldBe sum.passed 1
      shouldContainSubstr rep.failures[0]!.result.details "unexpected crash"

    it "IO.ofExcept lifts cleanly into AssertM and DSL keywords stay non-reserved" do
      let v ← IO.ofExcept (Except.ok 42 : Except String Nat)
      let prop := v
      let it := prop + 1
      shouldBe it 43

/-! ## Scoped Resources & Lifecycle Hooks -/

def resourceSuite : Spec := do
  describe "Scoped Resources & Hooks" do
    it "withResource acquires once, shares across tests, and releases in finally" do
      let log ← IO.mkRef (#[] : Array String)
      let resSpec : ResourceSpec String := {
        description := "test-db"
        acquire := do
          log.modify (·.push "acquire")
          return "conn-42"
        release := fun c => do
          log.modify (·.push s!"release:{c}")
      }
      let (_, sum) ← runInner (cfg := { threads := 2 }) do
        withResource resSpec fun getConn => do
          it "t1" do
            let c ← getConn
            shouldBe c "conn-42"
          it "t2 fails" do
            let c ← getConn
            shouldBe c "wrong"
      shouldBe sum.passed 1
      shouldBe sum.failed 1
      let events ← log.get
      shouldBe events #["acquire", "release:conn-42"]

    it "filtered-out or listed withResource never calls acquire" do
      let acquired ← IO.mkRef false
      let resSpec : ResourceSpec Unit := {
        description := "expensive"
        acquire := acquired.set true
      }
      let s : Spec := do
        describe "GroupA" do
          withResource resSpec fun _ => do
            it "heavy" do expect true
        describe "GroupB" do
          it "light" do expect true
      let tree ← s.toTestTree ""
      -- Listing must not acquire
      let listed := listTests tree
      shouldBe listed.size 2
      expectFalse (← acquired.get)
      -- Filtering out GroupA must not acquire
      let (_, sum) ← runTree tree { filter := { includes := #["GroupB"] } }
      shouldBe sum.passed 1
      expectFalse (← acquired.get)

    it "beforeEach, afterEach, and aroundEach wrap every leaf test" do
      let count ← IO.mkRef 0
      let (_, sum) ← runInner (cfg := { threads := 1 }) do
        beforeEach (count.modify (· + 1)) do
          afterEach (count.modify (· + 10)) do
            it "a" do expect true
            it "b" do expect false
      shouldBe sum.passed 1
      shouldBe sum.failed 1
      -- Each of 2 tests adds 1 before + 10 after = 22
      shouldBe (← count.get) 22

/-! ## Bool-based Property Testing -/

def propertySuite : Spec := do
  describe "Bool-based Property Testing" do
    prop "Nat addition is commutative" fun (a b : Nat) =>
      a + b == b + a

    prop "List reverse is an involution" fun (xs : List Nat) =>
      xs.reverse.reverse == xs

    prop "Array toList/toArray roundtrip" fun (xs : Array Int) =>
      xs.toList.toArray == xs

    prop "ByteArray append size" fun (a b : ByteArray) =>
      (a ++ b).size == a.size + b.size

    prop "precondition guard ==> filters inputs" fun (n : Nat) =>
      (n != 0) ==> Nat.blt (n - 1) n

    prop "AssertM body works inside prop" fun (xs ys : List Nat) =>
      shouldBe (xs ++ ys).length (xs.length + ys.length)

    prop "custom generator with forAll" <|
      forAll (Gen.chooseNat 10 20) fun n =>
        Nat.ble 10 n && Nat.ble n 20

    it "shrinks failing Nat counterexample to minimal value" do
      let (rep, sum) ← runInner (cfg := { seed := some 12345 }) do
        propWith "lt 10" { numTests := 100, maxSize := 50 } fun (n : Nat) => Nat.blt n 10
      shouldBe sum.failed 1
      let details := rep.failures[0]!.result.details
      shouldContainSubstr details "arg 0 := 10"
      shouldContainSubstr details "seed "

    it "shrinks failing List counterexample to minimal length and elements" do
      let (rep, sum) ← runInner (cfg := { seed := some 999 }) do
        propWith "len < 2" { numTests := 100, maxSize := 20 } fun (xs : List Nat) => Nat.blt xs.length 2
      shouldBe sum.failed 1
      shouldContainSubstr rep.failures[0]!.result.details "[0, 0]"

    it "reports gaveUp when precondition is unsatisfiable" do
      let (rep, sum) ← runInner (cfg := { seed := some 42 }) do
        propWith "impossible guard" { numTests := 10, maxDiscardRatio := 2 } fun (n : Nat) =>
          (Nat.blt n 0) ==> true
      shouldBe sum.failed 1
      shouldContainSubstr rep.failures[0]!.result.summary "gave up"

    it "is 100% deterministic across sequential and parallel runs with the same seed" do
      let mkSpec : Spec := do
        describe "Det" do
          prop "p1" (fun (n : Nat) => shouldBeLt n 7)
          prop "p2" (fun (a b : Nat) => shouldBeLt (a + b) 12)
          prop "p3" (fun (xs : List Nat) => shouldBeLt xs.length 3)
      let (r1, _) ← runInner mkSpec { threads := 1, seed := some 77777 }
      let (r2, _) ← runInner mkSpec { threads := 4, seed := some 77777 }
      let d1 := r1.failures.map (·.result.details)
      let d2 := r2.failures.map (·.result.details)
      shouldBe d1 d2
      shouldBe d1.size 3

/-! ## Bounded-Thread Parallel Runner -/

def parallelSuite : Spec := do
  describe "Bounded-Thread Parallel Runner" do
    it "strictly enforces --threads N concurrency bound while achieving real parallelism" do
      let active ← Std.Mutex.new (0 : Nat)
      let peak ← Std.Mutex.new (0 : Nat)
      let makeWorkers : Spec := do
        describe "Workers" do
          for i in [:12] do
            it s!"worker-{i}" do
              active.atomically do
                let cur := (← get) + 1
                set cur
                peak.atomically do
                  if cur > (← get) then set cur
              IO.sleep 30
              active.atomically do
                set ((← get) - 1)
      let (_, sum) ← runInner makeWorkers { threads := 3 }
      shouldBe sum.passed 12
      shouldBe sum.threads 3
      let maxObserved ← peak.atomically get
      shouldBeLe maxObserved 3
      shouldBeGe maxObserved 2

    it "runs strictly sequentially when threads := 1" do
      let active ← Std.Mutex.new (0 : Nat)
      let peak ← Std.Mutex.new (0 : Nat)
      let s : Spec := do
        for i in [:5] do
          it s!"seq-{i}" do
            active.atomically do
              let cur := (← get) + 1
              set cur
              peak.atomically do
                if cur > (← get) then set cur
            IO.sleep 10
            active.atomically do
              set ((← get) - 1)
      let (_, sum) ← runInner s { threads := 1 }
      shouldBe sum.passed 5
      shouldBe (← peak.atomically get) 1

    it "respects sequential modifier even when threads > 1" do
      let order ← Std.Mutex.new (#[] : Array Nat)
      let active ← Std.Mutex.new (0 : Nat)
      let peak ← Std.Mutex.new (0 : Nat)
      let s : Spec := do
        sequential do
          for i in [:5] do
            it s!"ordered-{i}" do
              active.atomically do
                let cur := (← get) + 1
                set cur
                peak.atomically do
                  if cur > (← get) then set cur
              IO.sleep 10
              order.atomically (modify (·.push i))
              active.atomically (modify (· - 1))
      let (_, sum) ← runInner s { threads := 4 }
      shouldBe sum.passed 5
      shouldBe (← peak.atomically get) 1
      shouldBe (← order.atomically get) #[0, 1, 2, 3, 4]

    it "isolates stdout per test under concurrent execution" do
      let s : Spec := do
        for i in [:8] do
          it s!"io-{i}" do
            IO.println s!"marker-start-{i}"
            IO.sleep 15
            IO.println s!"marker-end-{i}"
      let (rep, sum) ← runInner s { threads := 4 }
      shouldBe sum.passed 8
      match rep with
      | .group _ children =>
        shouldBe children.size 8
        for h : i in [:children.size] do
          match children[i] with
          | .leaf lr =>
            shouldBe lr.capturedOutput s!"marker-start-{i}\nmarker-end-{i}\n"
          | _ => fail "expected leaf report"
      | _ => fail "expected group report"

    it "supports --fail-fast skipping remaining queued tests" do
      let (_, sum) ← runInner (cfg := { threads := 1, failFast := true }) do
        it "t1 fails" do expect false
        it "t2 skipped" do expect true
        it "t3 skipped" do expect true
      shouldBe sum.failed 1
      shouldBe sum.skipped 2
      shouldBe sum.passed 0

    it "does not acquire withResource after --fail-fast triggers" do
      let acquired ← IO.mkRef false
      let (_, sum) ← runInner (cfg := { threads := 1, failFast := true }) do
        it "t1 fails" do expect false
        beforeAll (do acquired.set true; pure 1) (fun _ => pure ()) "should-skip" fun getR => do
          it "t2 skipped" do
            let _ ← getR
            expect true
          it "t3 skipped" do
            let _ ← getR
            expect true
      shouldBe (← acquired.get) false
      shouldBe sum.failed 1
      shouldBe sum.skipped 2
      shouldBe sum.passed 0

    it "keeps nested parallel inside sequential strictly sequential in listTests and execution" do
      let s : Spec := do
        sequential do
          parallel do
            it "a" do expect true
            it "b" do expect true
      let tree ← s.toTestTree ""
      let listed := listTests tree .parallel
      shouldBe listed.size 2
      shouldBe (listed.all (·.mode == .sequential)) true

/-! ## Filtering, Listing & CLI -/

def cliSuite : Spec := do
  describe "Filtering, Listing & CLI" do
    it "filters by substring, exact path, exclude, and tags" do
      let s : Spec := do
        describe "Math" do
          withTag "fast" do
            it "add" do expect true
          withTag "slow" do
            it "mul" do expect true
        describe "String" do
          withTag "fast" do
            it "concat" do expect true
      let tree ← s.toTestTree ""
      shouldBe (listTests tree).size 3

      let (_, s1) ← runTree tree { filter := { includes := #["Math"] } }
      shouldBe s1.passed 2

      let (_, s2) ← runTree tree { filter := { exact := #["Math/add"] } }
      shouldBe s2.passed 1

      let (_, s3) ← runTree tree { filter := { excludes := #["mul"] } }
      shouldBe s3.passed 2

      let (_, s4) ← runTree tree { filter := { includeTags := #["fast"] } }
      shouldBe s4.passed 2

      let (_, s5) ← runTree tree { filter := { excludeTags := #["slow"] } }
      shouldBe s5.passed 2

    it "parses CLI flags cleanly and rejects invalid options" do
      let cli ← expectOk (parseCliArgs [
        "-j", "8", "--seed", "42", "--num-tests=250", "--max-size", "64",
        "--tag", "fast", "--exclude-tag=slow,nightly", "--exclude=flaky",
        "--exact", "Math/add", "--fail-fast", "--no-color", "-v", "Math"
      ])
      shouldBe cli.threads (some 8)
      shouldBe cli.seed (some 42)
      shouldBe cli.numTests (some 250)
      shouldBe cli.maxSize (some 64)
      shouldBe cli.includeTags #["fast"]
      shouldBe cli.excludeTags #["slow", "nightly"]
      shouldBe cli.excludes #["flaky"]
      shouldBe cli.exact #["Math/add"]
      shouldBe cli.includes #["Math"]
      shouldBe cli.failFast true
      shouldBe cli.color (some false)
      shouldBe cli.verbose true

      let _ ← expectErr (parseCliArgs ["--threads", "0"])
      let errMissing ← expectErr (parseCliArgs ["--threads"])
      shouldContainSubstr errMissing "missing value"
      let _ ← expectErr (parseCliArgs ["--bogus-flag"])

    it "import-time guard suite can run its safe test without triggering boom tests" do
      let (_, sum) ← runInner LSpecTests.ImportCheck.importGuardSuite {
        filter := { includes := #["passing lazy check"] }
      }
      shouldBe sum.passed 1
      shouldBe sum.failed 0

/-! ## Opt-in Memory Stress Suite (`--tag memory`)

Each of 50 tests allocates a 100 MB `ByteArray`. With bounded concurrency (`-j N`),
completed test closures are released immediately so peak RSS stays proportional
to `N × 100 MB` rather than growing to `5 GB`.
-/

set_option compiler.extract_closed false in
def memoryStressSuite : Spec := do
  withTag "memory" do
    describe "Memory stress (50 × 100MB)" do
      for i in [:50] do
        it s!"alloc 100MB #{i + 1}" do
          let arr := ByteArray.mk (.replicate (100 * 1024 * 1024) 0xFF)
          expect (arr.size == 100 * 1024 * 1024)

def allTests : Spec := do
  assertionSuite
  resourceSuite
  propertySuite
  parallelSuite
  cliSuite
  LSpecTests.ImportCheck.importGuardSuite
  memoryStressSuite

def main (args : List String) : IO UInt32 := do
  -- Exclude opt-in suites (`memory`, `import-guard`) unless explicitly requested via `--tag`.
  let defaults : RunConfig :=
    if args.any (fun a => a == "--tag" || a.startsWith "--tag=") then {}
    else { filter := { excludeTags := #["memory", "import-guard"] } }
  lspecMain allTests args defaults
