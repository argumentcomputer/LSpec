open System

def runCmd (cmd : String) (args : Array String) (testing : Bool) :
    IO $ Option String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if testing then IO.println out.stdout
  if out.exitCode == 0 then return none
  else return some out.stderr

def getTestPathsFromLake : IO $ List FilePath := do
  let source ← IO.FS.readFile ⟨"lakefile.lean"⟩
  let lines := source.splitOn "\n" |>.filter fun line =>
    !(line.trimLeft |>.startsWith "--")
  return ("\n".intercalate lines).splitOn "lean_exe"
    |>.map (·.trimLeft)
    |>.filter (·.startsWith "Tests.")
    |>.map fun str =>
      let str := str.append "\n" |>.replace "\n" " " |>.replace "\t" " "
      let module := str.splitOn " " |>.head!
      mkFilePath (module.splitOn ".") |>.withExtension "lean"

def System.FilePath.noExtensionWithSep (p : FilePath) (sep : String) : String :=
  p.withExtension "" |>.toString.replace FilePath.pathSeparator.toString sep

def main (args : List String) : IO UInt32 := do
  let leanPaths :=
    if args.isEmpty then ← getTestPathsFromLake else args.map FilePath.mk
  if leanPaths.isEmpty then
    IO.println "No tests to run"
    return 0
  for path in leanPaths do
    let lib := path.noExtensionWithSep "."
    IO.println s!"Building {lib}"
    match ← runCmd "lake" #["build", lib] false with
    | some msg => IO.eprintln s!"{msg}\nFailed to build {lib}"; return 1
    | none => pure ()
  let mut failures := #[]
  for path in leanPaths do
    let exe := path.noExtensionWithSep "-"
    let path : FilePath := "." / ".lake" / "build" / "bin" / exe
    IO.println s!"Running {path}"
    match ← runCmd path.toString #[] true with
    | some msg => failures := failures.push msg
    | none => pure ()
  if failures.isEmpty then
    IO.println "All tests passed!"
    return 0
  IO.eprint s!"Failed tests:\n{String.join failures.data}"
  return 1
