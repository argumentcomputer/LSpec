module
public import LSpec.Core
public import LSpec.Spec
public import LSpec.Runner
public import LSpec.Processors

/-!
# CLI Argument Parsing & Main Entry Points (`LSpec.Cli`)

Provides `lspecMain`, `defaultMain`, `defaultMainTree`, `defaultMainWithProcessors`,
and `runSpec` with full command-line support for:
- `-j N` / `--threads N` / `--threads=N` (bounded parallel worker pool)
- `--sequential` (alias for `--threads 1`)
- `--list` (list matching tests without executing or acquiring resources)
- `<pattern>` / `--filter <pattern>` (substring filter, repeatable)
- `--exact <path>` (exact path match, repeatable)
- `--exclude <pattern>` / `--exclude=a,b` (exclude matching paths)
- `--tag <tag>` / `--exclude-tag <tag>` (tag filtering)
- `--seed <u64>` (deterministic property-test master seed)
- `--num-tests <n>` / `--max-size <n>` (global property-test overrides)
- `--fail-fast` (stop after first failure)
- `--color` / `--no-color` (respects `NO_COLOR`)
- `-v` / `--verbose` (show details & captured output on passing tests)
- `-h` / `--help`
-/

namespace LSpec
public section

/-- Parsed CLI options. -/
structure CliOptions where
  threads : Option Nat := none
  sequential : Bool := false
  listOnly : Bool := false
  includes : Array String := #[]
  exact : Array String := #[]
  excludes : Array String := #[]
  includeTags : Array String := #[]
  excludeTags : Array String := #[]
  seed : Option UInt64 := none
  numTests : Option Nat := none
  maxSize : Option Nat := none
  failFast : Bool := false
  color : Option Bool := none
  verbose : Bool := false
  showHelp : Bool := false
  deriving BEq, Repr

private def parseNatArg (flag val : String) : Except String Nat :=
  match val.toNat? with
  | some n => .ok n
  | none => .error s!"expected natural number for {flag}, got '{val}'"

private def parseUInt64Arg (flag val : String) : Except String UInt64 :=
  match val.toNat? with
  | some n => .ok n.toUInt64
  | none => .error s!"expected unsigned integer for {flag}, got '{val}'"

private def splitPrefix? (arg pfx : String) : Option String :=
  if arg.startsWith pfx then some ((arg.drop pfx.length).toString) else none

/-- Parse CLI arguments into `CliOptions`. -/
def parseCliArgs (args : List String) : Except String CliOptions :=
  go args {}
where
  go : List String → CliOptions → Except String CliOptions
    | [], o => .ok o
    | "-h" :: rest, o | "--help" :: rest, o =>
      go rest { o with showHelp := true }
    | "--list" :: rest, o =>
      go rest { o with listOnly := true }
    | "--sequential" :: rest, o =>
      go rest { o with sequential := true, threads := some 1 }
    | "--fail-fast" :: rest, o =>
      go rest { o with failFast := true }
    | "--color" :: rest, o =>
      go rest { o with color := some true }
    | "--no-color" :: rest, o =>
      go rest { o with color := some false }
    | "-v" :: rest, o | "--verbose" :: rest, o =>
      go rest { o with verbose := true }
    | "-j" :: val :: rest, o | "--threads" :: val :: rest, o => do
      let n ← parseNatArg "--threads" val
      if n == 0 then throw "--threads must be at least 1"
      go rest { o with threads := some n }
    | "--filter" :: pat :: rest, o =>
      go rest { o with includes := o.includes.push pat }
    | "--exact" :: pat :: rest, o =>
      go rest { o with exact := o.exact.push pat }
    | "--exclude" :: pat :: rest, o =>
      go rest { o with excludes := o.excludes.push pat }
    | "--tag" :: tag :: rest, o =>
      go rest { o with includeTags := o.includeTags.push tag }
    | "--exclude-tag" :: tag :: rest, o =>
      go rest { o with excludeTags := o.excludeTags.push tag }
    | "--seed" :: val :: rest, o => do
      let s ← parseUInt64Arg "--seed" val
      go rest { o with seed := some s }
    | "--num-tests" :: val :: rest, o => do
      let n ← parseNatArg "--num-tests" val
      go rest { o with numTests := some n }
    | "--max-size" :: val :: rest, o => do
      let n ← parseNatArg "--max-size" val
      go rest { o with maxSize := some n }
    | arg :: rest, o =>
      if rest.isEmpty &&
          ["-j", "--threads", "--filter", "--exact", "--exclude", "--tag",
           "--exclude-tag", "--seed", "--num-tests", "--max-size"].contains arg then
        .error s!"missing value for '{arg}' (use --help for usage)"
      else if let some val := splitPrefix? arg "--threads=" then do
        let n ← parseNatArg "--threads" val
        if n == 0 then throw "--threads must be at least 1"
        go rest { o with threads := some n }
      else if let some val := splitPrefix? arg "-j" then do
        let n ← parseNatArg "-j" val
        if n == 0 then throw "-j must be at least 1"
        go rest { o with threads := some n }
      else if let some val := splitPrefix? arg "--filter=" then
        go rest { o with includes := o.includes.push val }
      else if let some val := splitPrefix? arg "--exact=" then
        go rest { o with exact := o.exact.push val }
      else if let some val := splitPrefix? arg "--exclude=" then
        let xs := (val.splitOn ",").filter (!·.isEmpty)
        go rest { o with excludes := o.excludes ++ xs.toArray }
      else if let some val := splitPrefix? arg "--tag=" then
        let xs := (val.splitOn ",").filter (!·.isEmpty)
        go rest { o with includeTags := o.includeTags ++ xs.toArray }
      else if let some val := splitPrefix? arg "--exclude-tag=" then
        let xs := (val.splitOn ",").filter (!·.isEmpty)
        go rest { o with excludeTags := o.excludeTags ++ xs.toArray }
      else if let some val := splitPrefix? arg "--seed=" then do
        let s ← parseUInt64Arg "--seed" val
        go rest { o with seed := some s }
      else if let some val := splitPrefix? arg "--num-tests=" then do
        let n ← parseNatArg "--num-tests" val
        go rest { o with numTests := some n }
      else if let some val := splitPrefix? arg "--max-size=" then do
        let n ← parseNatArg "--max-size" val
        go rest { o with maxSize := some n }
      else if arg.startsWith "-" then
        .error s!"unknown option '{arg}' (use --help for usage)"
      else
        go rest { o with includes := o.includes.push arg }

def cliHelpText : String :=
  String.intercalate "\n" [
    "LSpec test runner options:",
    "  -j, --threads <N>       Run up to N tests concurrently (default: 1)",
    "  --sequential            Run all tests sequentially (alias for --threads 1)",
    "  --list                  List matching test paths and exit without running",
    "  <pattern>               Run only tests whose path contains <pattern>",
    "  --filter <pattern>      Same as positional <pattern> (repeatable)",
    "  --exact <path>          Run only tests matching <path> exactly (repeatable)",
    "  --exclude <pattern>     Exclude tests whose path contains <pattern>",
    "  --tag <tag>             Run only tests carrying <tag> (repeatable)",
    "  --exclude-tag <tag>     Skip tests carrying <tag> (repeatable)",
    "  --seed <u64>            Master seed for deterministic property tests",
    "  --num-tests <N>         Override property-test sample count",
    "  --max-size <N>          Override property-test maximum generator size",
    "  --fail-fast             Stop starting new tests after the first failure",
    "  --color / --no-color    Force or disable ANSI color output",
    "  -v, --verbose           Show extra details and captured output on passes",
    "  -h, --help              Show this help message"
  ]

/-- Convert `CliOptions` + defaults into `TestOptions` for `TestProcessor`s. -/
def CliOptions.toTestOptions (cli : CliOptions) (defaults : RunConfig := {})
    (noColorEnv : Bool := false) : TestOptions := Id.run do
  let mut opts := defaults.options
  let threads := cli.threads.getD defaults.threads
  opts := opts.setNat "runner.threads" (max 1 threads)
  opts := opts.setBool "runner.sequential" (cli.sequential || defaults.defaultMode == .sequential)
  opts := opts.setBool "runner.list" cli.listOnly
  opts := opts.setBool "runner.failFast" (cli.failFast || defaults.failFast)
  opts := opts.setBool "runner.isolateStreams" defaults.isolateStreams
  let useColor := match cli.color with
    | some c => c
    | none => !noColorEnv
  opts := opts.setBool "console.color" useColor
  opts := opts.setBool "console.verbose" cli.verbose
  if let some s := cli.seed.orElse (fun () => defaults.seed) then
    opts := opts.setUInt64 "runner.seed" s
  if let some n := cli.numTests then
    opts := opts.setNat "prop.numTests" n
  if let some sz := cli.maxSize then
    opts := opts.setNat "prop.maxSize" sz
  let enc (xs : Array String) : String := "\x00".intercalate xs.toList
  let incs := defaults.filter.includes ++ cli.includes
  let exts := defaults.filter.exact ++ cli.exact
  let excs := defaults.filter.excludes ++ cli.excludes
  let itags := defaults.filter.includeTags ++ cli.includeTags
  let etags := defaults.filter.excludeTags ++ cli.excludeTags
  unless incs.isEmpty do opts := opts.setString "filter.includes" (enc incs)
  unless exts.isEmpty do opts := opts.setString "filter.exact" (enc exts)
  unless excs.isEmpty do opts := opts.setString "filter.excludes" (enc excs)
  unless itags.isEmpty do opts := opts.setString "filter.includeTags" (enc itags)
  unless etags.isEmpty do opts := opts.setString "filter.excludeTags" (enc etags)
  return opts

/-- Execute a `TestTree` using a custom list of `TestProcessor`s and CLI arguments. -/
def defaultMainWithProcessors (procs : List TestProcessor) (tree : TestTree)
    (args : List String) (defaults : RunConfig := {}) : IO UInt32 := do
  let cli ← match parseCliArgs args with
    | .ok c => pure c
    | .error msg =>
      IO.eprintln s!"error: {msg}"
      return 2
  if cli.showHelp then
    IO.println cliHelpText
    return 0
  let noColorEnv := (← IO.getEnv "NO_COLOR").isSome
  let opts := cli.toTestOptions defaults noColorEnv
  match TestProcessor.runFirst? procs opts tree with
  | none =>
    IO.eprintln "error: no test processor matched the given options"
    return 2
  | some act => act

/-- Execute a `TestTree` with the default processors (`list`, `console`). -/
def defaultMainTree (tree : TestTree) (args : List String)
    (defaults : RunConfig := {}) : IO UInt32 :=
  defaultMainWithProcessors Processors.defaultProcessors tree args defaults

/-- Execute a `Spec` with CLI argument parsing and the default processors.
    This is the primary entry point for test executables:
    ```lean
    def main (args : List String) : IO UInt32 :=
      LSpec.lspecMain mySuite args
    ``` -/
def lspecMain (spec : Spec) (args : List String)
    (defaults : RunConfig := {}) : IO UInt32 := do
  let tree ← spec.toTestTree ""
  defaultMainTree tree args defaults

/-- Alias for `lspecMain` matching `nest-core`'s naming. -/
def defaultMain (spec : Spec) (args : List String := [])
    (defaults : RunConfig := {}) : IO UInt32 :=
  lspecMain spec args defaults

/-- Programmatically run a `Spec` with an explicit `RunConfig` (no CLI parsing,
    no stdout printing), returning `(ReportTree, RunSummary)`. -/
def runSpec (spec : Spec) (cfg : RunConfig := {}) : IO (ReportTree × RunSummary) := do
  let tree ← spec.toTestTree ""
  runTree tree cfg

end
end LSpec
