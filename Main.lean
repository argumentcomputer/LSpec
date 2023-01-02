open System

partial def getLeanPaths (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getLeanPaths dir.path acc) acc
  else return if fp.extension == some "lean" then acc.push fp else acc

def runCmd (cmd : String) (args : Array String) (testing : Bool) :
    IO $ Option String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if testing then IO.println out.stdout
  if out.exitCode == 0 then return none
  else return some out.stderr

def getDefaultLeanPaths : IO $ Array (String × String) :=
  return (← getLeanPaths ⟨"Tests"⟩).map fun path =>
    let path := path.withExtension "" |>.toString
    let sep := System.FilePath.pathSeparator.toString
    (path.replace sep ".", path.replace sep "-")

def getUserLeanPaths (args : List String) : Array (String × String) :=
  .mk $ args.map fun path =>
    let lib := s!"Tests.{path}"
    (lib, lib.replace "." "-")

def main (args : List String) : IO UInt32 := do
  let mut exeFiles := #[]
  let leanPaths :=
    if args.isEmpty then ← getDefaultLeanPaths
    else getUserLeanPaths args
  for (lib, exe) in leanPaths do
    IO.println s!"Building {exe}"
    match ← runCmd "lake" #["build", lib] false with
    | some msg =>
      IO.eprintln s!"{msg}\nFailed to build {exe}"
      return 1
    | none => exeFiles := exeFiles.push exe
  let mut failures := #[]
  for exe in exeFiles do
    IO.println s!"\nRunning {exe}"
    match ← runCmd s!"./build/bin/{exe}" #[] true with
    | some msg => failures := failures.push msg
    | none => pure ()
  if failures.isEmpty then
    IO.println "\nAll tests passed!"
    return 0
  IO.eprintln s!"\nFailed tests:\n{"\n".intercalate failures.data}"
  return 1
