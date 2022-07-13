open System

partial def getFilePaths (fp : FilePath) (acc : List FilePath := []) :
    IO (List FilePath) := do
  if ← fp.isDir then
    let mut extra : List FilePath := []
    for dirEntry in (← fp.readDir) do
      for innerFp in ← getFilePaths dirEntry.path do
        extra := extra.concat innerFp
    return acc ++ extra
  else
    if (fp.extension.getD "") == "lean" then
      return acc.concat fp
    else
      return acc

def runCmd (descr cmd : String) (args : Array String := #[]) : IO Bool := do
  IO.println descr
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode == 0 then
    IO.println out.stdout
    return false
  else
    IO.eprintln out.stderr
    return true

def main : IO UInt32 := do
  let mut exeFiles : List String := []
  for testCase in (← getFilePaths ⟨"Tests"⟩).map
      fun fp => (fp.toString.splitOn ".").head! do
    let exe := testCase.replace "/" "-"
    let pkg := testCase.replace "/" "."
    if ← runCmd s!"Building {exe}" "lake" #["build", pkg] then
      return (1 : UInt32)
    exeFiles := exe :: exeFiles
  let mut hasFailure : Bool := false
  for exe in exeFiles.reverse do
    hasFailure := hasFailure ||
      (← runCmd s!"Running {exe}" s!"./build/bin/{exe}")
  if !hasFailure then
    IO.println "All tests passed!"
    return 0
  IO.println "Some test failed!"
  return 1
