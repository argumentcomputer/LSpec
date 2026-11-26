module
public import LSpec.Core
public import LSpec.Runner

/-!
# Built-in `TestProcessor`s (`LSpec.Processors`)

Inspired by `nest-core`'s pluggable `TestProcessor` architecture and `LSpec`'s
readable hierarchical console output with bottom failure recaps:
- `Processors.list`: prints all matching test paths (with tags & mode) without
  running any tests or acquiring any resources.
- `Processors.console`: executes the `TestTree` with bounded parallelism and
  renders hierarchical pass/fail/skip output, per-test timings, captured stdout
  on failure (or `--verbose`), summary counts, and a bottom recap of failures.
-/

namespace LSpec.Processors
public section

private def ansiReset := "\x1b[0m"
private def ansiGreen := "\x1b[32m"
private def ansiBoldGreen := "\x1b[1;32m"
private def ansiRed := "\x1b[31m"
private def ansiBoldRed := "\x1b[1;31m"
private def ansiYellow := "\x1b[33m"
private def ansiDim := "\x1b[2m"
private def ansiBold := "\x1b[1m"

private def colorize (useColor : Bool) (code : String) (s : String) : String :=
  if useColor then code ++ s ++ ansiReset else s

private def pad (indent : Nat) : String :=
  String.ofList (List.replicate indent ' ')

private def indentBlock (indent : Nat) (s : String) : String :=
  let prefixStr := pad indent
  let lines := s.splitOn "\n"
  "\n".intercalate (lines.map (prefixStr ++ ·))

/-- Build a `TestFilter` from standard `TestOptions` keys. -/
def filterFromOptions (opts : TestOptions) : TestFilter :=
  let splitNonEmpty (key : String) : Array String :=
    let raw := opts.getString key ""
    if raw.isEmpty then #[]
    else (raw.splitOn "\x00").filter (!·.isEmpty) |>.toArray
  {
    includes := splitNonEmpty "filter.includes"
    exact := splitNonEmpty "filter.exact"
    excludes := splitNonEmpty "filter.excludes"
    includeTags := splitNonEmpty "filter.includeTags"
    excludeTags := splitNonEmpty "filter.excludeTags"
  }

/-- Build a `RunConfig` from standard `TestOptions` keys. -/
def runConfigFromOptions (opts : TestOptions) : RunConfig :=
  {
    threads := opts.getNat "runner.threads" 1
    defaultMode :=
      if opts.getBool "runner.sequential" false then .sequential else .parallel
    seed := opts.getUInt64? "runner.seed"
    filter := filterFromOptions opts
    options := opts
    failFast := opts.getBool "runner.failFast" false
    isolateStreams := opts.getBool "runner.isolateStreams" true
  }

/-- Format a `ReportTree` as a human-readable string (useful for both console
    output and programmatic inspection in tests). -/
partial def formatReport (report : ReportTree) (useColor : Bool := false)
    (verbose : Bool := false) : String :=
  let lines := (go 0 report).run #[] |>.2
  "\n".intercalate lines.toList
where
  push (s : String) : StateM (Array String) Unit := modify (·.push s)

  go (indent : Nat) : ReportTree → StateM (Array String) Unit
    | .group name children => do
      let nextIndent :=
        if name.isEmpty then indent
        else indent + 2
      unless name.isEmpty do
        push s!"{pad indent}{colorize useColor ansiBold name}"
      for c in children do
        go nextIndent c
    | .leaf rep => do
      let timing := colorize useColor ansiDim s!"({rep.durationMs} ms)"
      match rep.result.outcome with
      | .passed =>
        let glyph := colorize useColor ansiGreen "✓"
        let extra := if rep.result.summary.isEmpty then "" else s!" {colorize useColor ansiDim rep.result.summary}"
        push s!"{pad indent}{glyph} {rep.name}{extra} {timing}"
        if verbose && !rep.result.details.isEmpty then
          push (indentBlock (indent + 2) rep.result.details)
        if verbose && !rep.capturedOutput.isEmpty then
          push (indentBlock (indent + 2) s!"[output]\n{rep.capturedOutput.trimAsciiEnd}")
      | .skipped reason =>
        let glyph := colorize useColor ansiYellow "○"
        let msg := match reason with
          | some r => s!" ({r})"
          | none => " (pending)"
        push s!"{pad indent}{glyph} {rep.name}{colorize useColor ansiYellow msg}"
      | .failed _ =>
        let glyph := colorize useColor ansiRed "×"
        let msg := if rep.result.summary.isEmpty then "" else s!": {rep.result.summary}"
        push s!"{pad indent}{glyph} {colorize useColor ansiRed (rep.name ++ msg)} {timing}"
        unless rep.result.details.isEmpty do
          push (indentBlock (indent + 4) rep.result.details)
        unless rep.capturedOutput.isEmpty do
          push (indentBlock (indent + 4) s!"[captured output]\n{rep.capturedOutput.trimAsciiEnd}")

/-- Format the bottom failure recap and run summary. -/
def formatSummary (report : ReportTree) (summary : RunSummary)
    (useColor : Bool := false) : String := Id.run do
  let mut lines : Array String := #[]
  let fails := report.failures
  unless fails.isEmpty do
    lines := lines.push ""
    lines := lines.push (colorize useColor ansiBoldRed
      "-------------------------------- Failing tests ---------------------------------")
    for rep in fails do
      let fullPath := "/".intercalate rep.path.toList
      lines := lines.push (colorize useColor ansiRed s!"× {fullPath}")
      unless rep.result.summary.isEmpty do
        lines := lines.push (indentBlock 2 rep.result.summary)
      unless rep.result.details.isEmpty do
        lines := lines.push (indentBlock 2 rep.result.details)
  lines := lines.push ""
  let statusStr :=
    if summary.allPassed then
      colorize useColor ansiBoldGreen
        s!"{summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
    else
      colorize useColor ansiBoldRed
        s!"{summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
  let metaInfo := colorize useColor ansiDim
    s!"({summary.total} total, {summary.totalDurationMs} ms, threads={summary.threads}, seed={summary.seed})"
  lines := lines.push s!"{statusStr} {metaInfo}"
  return "\n".intercalate lines.toList

/-- Processor that lists all matching tests without executing them or acquiring resources.
    Enabled when `TestOptions` has `"runner.list" = true`. -/
def list : TestProcessor where
  name := "list"
  shouldRun opts := opts.getBool "runner.list" false
  exec opts tree := do
    let filter := filterFromOptions opts
    let mode := if opts.getBool "runner.sequential" false then .sequential else .parallel
    let filtered := filterTree filter tree
    match filtered with
    | none => return 0
    | some t =>
      let entries := listTests t mode
      for entry in entries do
        let tagSuffix :=
          if entry.tags.isEmpty then ""
          else s!"  [{", ".intercalate entry.tags.toList}]"
        let modeSuffix := match entry.mode with
          | .sequential => "  (sequential)"
          | .parallel => ""
        IO.println s!"{entry.pathString}{tagSuffix}{modeSuffix}"
      return 0

/-- Default console processor that runs tests with bounded parallelism and prints
    hierarchical results plus a summary. -/
def console : TestProcessor where
  name := "console"
  shouldRun _ := true
  exec opts tree := do
    let cfg := runConfigFromOptions opts
    let useColor := opts.getBool "console.color" true
    let verbose := opts.getBool "console.verbose" false
    let (report, summary) ← runTree tree cfg
    let body := formatReport report useColor verbose
    unless body.isEmpty do
      IO.println body
    IO.println (formatSummary report summary useColor)
    return if summary.allPassed then 0 else 1

/-- Default processor pipeline: `list` first (if `--list`), otherwise `console`. -/
def defaultProcessors : List TestProcessor := [list, console]

end
end LSpec.Processors
