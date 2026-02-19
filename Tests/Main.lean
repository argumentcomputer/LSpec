import LSpec

open LSpec

/-! # LSpec test suite

Dogfoods `lspecIO` as the outer runner. Primary suites always run;
the memory stress suite is opt-in via `./tests memory`.
-/

private def String.containsSub (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- Helper: run an IO action with stdout and stderr redirected to /dev/null.
def quietly (action : IO α) : IO α := do
  let devNull ← IO.FS.Handle.mk "/dev/null" .write
  let nullStream := IO.FS.Stream.ofHandle devNull
  let oldStdout ← (IO.setStdout nullStream : BaseIO _)
  let oldStderr ← (IO.setStderr nullStream : BaseIO _)
  try
    let result ← action
    let _ ← (IO.setStdout oldStdout : BaseIO _)
    let _ ← (IO.setStderr oldStderr : BaseIO _)
    pure result
  catch e =>
    let _ ← (IO.setStdout oldStdout : BaseIO _)
    let _ ← (IO.setStderr oldStderr : BaseIO _)
    throw e

-- Helper: run a TestSeq via runIO (no printing), then assert on the bool and
-- check that the output contains a given substring.
def assertRunIO (tSeq : TestSeq) (expectPass : Bool) (expectSubstr : String := "") :
    IO (Bool × Nat × Nat × Option String) := do
  let (pass, output) ← tSeq.runIO
  let boolOk := pass == expectPass
  let substrOk := expectSubstr.isEmpty || output.containsSub expectSubstr
  if boolOk && substrOk then
    pure (true, 0, 0, none)
  else
    let mut msg := ""
    unless boolOk do
      msg := msg ++ s!"expected pass={expectPass} but got pass={pass}"
    unless substrOk do
      if !msg.isEmpty then msg := msg ++ "; "
      msg := msg ++ s!"expected output to contain \"{expectSubstr}\" but got:\n{output}"
    pure (false, 0, 0, some msg)

section PrimarySuites

/-! ## TestSeq.runIO basics -/

def runIOBasics : TestSeq :=
  group "TestSeq.runIO basics" (
    .individualIO "passing test returns (true, _)" none
      (assertRunIO (test "t" (1 = 1)) true) .done ++
    .individualIO "failing test returns (false, _)" none
      (assertRunIO (test "t" (1 = 2)) false) .done ++
    .individualIO "multiple passing tests" none
      (assertRunIO (test "a" (1 = 1) ++ test "b" (2 = 2)) true) .done ++
    .individualIO "mixed pass/fail returns false" none
      (assertRunIO (test "a" (1 = 1) ++ test "b" (1 = 2)) false) .done ++
    .individualIO ".done is identity" none
      (assertRunIO .done true) .done
  )

/-! ## Grouping -/

def groupingTests : TestSeq :=
  group "Grouping" (
    .individualIO "group produces labeled output" none
      (assertRunIO (group "myGroup" (test "t" true)) true "myGroup") .done ++
    .individualIO "describe produces labeled output" none
      (assertRunIO (describe "myDescribe" (test "t" true)) true "myDescribe") .done ++
    .individualIO "context produces labeled output" none
      (assertRunIO (context "myContext" (test "t" true)) true "myContext") .done ++
    .individualIO "nested groups work" none
      (assertRunIO (group "outer" (group "inner" (test "t" true))) true "inner") .done
  )

/-! ## IO tests -/

def ioTests : TestSeq :=
  group "IO tests" (
    .individualIO "individualIO success" none (do
      let (pass, _) ← (TestSeq.individualIO "t" none (pure (true, 0, 0, none)) .done).runIO
      if pass then pure (true, 0, 0, none)
      else pure (false, 0, 0, some "expected pass=true")
    ) .done ++
    .individualIO "individualIO failure" none (do
      let (pass, _) ← (TestSeq.individualIO "t" none (pure (false, 0, 100, some "boom")) .done).runIO
      if !pass then pure (true, 0, 0, none)
      else pure (false, 0, 0, some "expected failure but got success")
    ) .done ++
    .individualIO "individualIO error message propagates" none
      (assertRunIO
        (TestSeq.individualIO "t" none (pure (false, 0, 100, some "specific error msg")) .done)
        false "specific error msg") .done
  )

/-! ## Combinators -/

def combinatorTests : TestSeq :=
  group "Combinators" (
    withOptionSome "withOptionSome on some" (some 42) (fun n =>
      test "value is 42" (n = 42)) ++
    withOptionNone "withOptionNone on none" (none : Option Nat)
      (test "reached" true) ++
    .individualIO "withOptionSome on none fails" none
      (assertRunIO
        (withOptionSome "got none" (none : Option Nat) (fun _ => test "unreachable" true))
        false) .done ++
    .individualIO "withOptionNone on some fails" none
      (assertRunIO
        (withOptionNone "got some" (some 42) (test "unreachable" true))
        false) .done ++
    withExceptOk "withExceptOk on ok" (Except.ok 10 : Except String Nat) (fun n =>
      test "value is 10" (n = 10)) ++
    withExceptError "withExceptError on error" (Except.error "oops" : Except String Nat) (fun e =>
      test "error is oops" (e = "oops"))
  )

/-! ## Append -/

def appendTests : TestSeq :=
  group "Append" (
    .individualIO "++ chains tests" none
      (assertRunIO (test "a" (1 = 1) ++ test "b" (2 = 2)) true) .done ++
    .individualIO "++ preserves order" none (do
      let (_, output) ← (test "first" (1 = 1) ++ test "second" (2 = 2)).runIO
      -- "first" should appear before "second" in the output
      let hasBoth := output.containsSub "first" && output.containsSub "second"
      -- Check ordering via splitOn: if we split on "first", "second" should be in the tail
      let afterFirst := (output.splitOn "first").getD 1 ""
      let ordered := afterFirst.containsSub "second"
      if hasBoth && ordered then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected 'first' before 'second' in:\n{output}")
    ) .done
  )

/-! ## Property tests -/

def propertyTests : TestSeq :=
  group "Property tests" (
    .individualIO "checkIO passing property" none
      (assertRunIO (checkIO "add_zero" (∀ n : Nat, n + 0 = n)) true) .done ++
    .individualIO "checkIO failing property" none
      (assertRunIO (checkIO "bad" (∀ n : Nat, n = n + 1)) false) .done
  )

/-! ## lspecIO integration -/

def lspecIOIntegration : TestSeq :=
  group "lspecIO integration" (
    .individualIO "returns 0 on all-pass" none (quietly do
      let map := Std.HashMap.ofList [("s", [test "t" (1 = 1)])]
      let rc ← lspecIO map []
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "returns 1 on any failure" none (quietly do
      let map := Std.HashMap.ofList [("s", [test "t" (1 = 2)])]
      let rc ← lspecIO map []
      if rc == 1 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=1, got rc={rc}")
    ) .done ++
    .individualIO "empty map returns 0" none (quietly do
      let rc ← lspecIO (.ofList []) []
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "suite filtering by name prefix" none (quietly do
      let map := Std.HashMap.ofList [
        ("math.add", [test "t" (1 + 1 = 2)]),
        ("string.concat", [test "t" ("a" ++ "b" = "ab")])
      ]
      let rc ← lspecIO map ["math"]
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0 with filter, got rc={rc}")
    ) .done ++
    .individualIO "non-matching filter runs nothing (returns 0)" none (quietly do
      let map := Std.HashMap.ofList [("suite", [test "t" (1 = 2)])]
      let rc ← lspecIO map ["nonexistent"]
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0 with no matches, got rc={rc}")
    ) .done
  )

/-! ## lspecEachIO -/

def lspecEachIOTests : TestSeq :=
  group "lspecEachIO" (
    .individualIO "returns 0 on all-pass" none (quietly do
      let rc ← lspecEachIO [1, 2, 3] fun n => pure (test s!"{n}" (n > 0))
      if rc == 0 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=0, got rc={rc}")
    ) .done ++
    .individualIO "returns 1 on any failure" none (quietly do
      let rc ← lspecEachIO [1, 0, 3] fun n =>
        pure (test s!"{n}>0" (decide (n > 0)))
      if rc == 1 then pure (true, 0, 0, none)
      else pure (false, 0, 0, some s!"expected rc=1, got rc={rc}")
    ) .done
  )

end PrimarySuites

/-! ## Memory stress suite (opt-in: `./tests memory`)

Each of 50 tests allocates a 100 MB `ByteArray`. With the tail-recursive fix,
RSS should stay bounded rather than climbing to 5 GB+.
Run and watch in htop to verify.
-/

def memoryStressTests : TestSeq :=
  go 50
where
  go : Nat → TestSeq
    | 0 => .done
    | n + 1 =>
      .individualIO s!"alloc 100MB #{50 - n}" none (do
        -- Allocate 100 MB and touch it so it's not optimised away
        let arr := ByteArray.mk (.replicate (100 * 1024 * 1024) 0xFF)
        let ok := arr.size > 0
        pure (ok, 0, 0, none)
      ) (go n)

def main (args : List String) : IO UInt32 := do
  let runMemory := args.contains "memory"
  let primarySuites : Std.HashMap String (List TestSeq) := .ofList [
    ("TestSeq.runIO basics", [runIOBasics]),
    ("Grouping", [groupingTests]),
    ("IO tests", [ioTests]),
    ("Combinators", [combinatorTests]),
    ("Append", [appendTests]),
    ("Property tests", [propertyTests]),
    ("lspecIO integration", [lspecIOIntegration]),
    ("lspecEachIO", [lspecEachIOTests])
  ]
  let filterArgs := args.filter (· != "memory")
  let rc ← lspecIO primarySuites filterArgs
  if runMemory then
    IO.println "\n=== Memory stress test (watch RSS in htop) ==="
    let memMap : Std.HashMap String (List TestSeq) := .ofList [
      ("memory stress (50 × 100MB)", [memoryStressTests])
    ]
    let rc2 ← lspecIO memMap []
    return max rc rc2
  return rc
