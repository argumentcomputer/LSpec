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

def runCmd (descr cmd : String) (args : Array String := #[])
    (building : Bool) : IO Bool := do
  IO.println descr
  if building then
    let out ← IO.Process.output { cmd := cmd, args := args }
    if out.exitCode == 0 then return false
    else IO.eprintln out.stderr; return true
  else
    let out ← IO.Process.spawn { cmd := cmd, args := args }
    return (← out.wait) != 0

def main : IO UInt32 := do
  let mut exeFiles : List String := []
  for testCase in (← getFilePaths ⟨"Tests"⟩).map
      fun fp => (fp.toString.splitOn ".").head! do
    let exe := testCase.replace "/" "-"
    let pkg := testCase.replace "/" "."
    if ← runCmd s!"Building {exe}" "lake" #["build", pkg] true then
      IO.eprintln s!"Failed to build {exe}."
      return 1
    exeFiles := exe :: exeFiles
  let mut hasFailure : Bool := false
  for exe in exeFiles.reverse do
    hasFailure := hasFailure ||
      (← runCmd s!"\nRunning {exe}" s!"./build/bin/{exe}" #[] false)
  if !hasFailure then
    IO.println "\nAll tests passed!"
    return 0
  IO.eprintln "\nSome test failed!"
  return 1
