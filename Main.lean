import LSpec -- forcing oleans generation

open System in
partial def getFilePaths
  (fp : FilePath) (ext : String) (acc : List FilePath := []) :
    IO (List FilePath) := do
  if ← fp.isDir then
    let mut extra : List FilePath := []
    for dirEntry in (← fp.readDir) do
      for innerFp in ← getFilePaths dirEntry.path ext do
        extra := extra.concat innerFp
    return acc ++ extra
  else
    if (fp.extension.getD "") == ext then
      return acc.concat fp
    else
      return acc

def runCmd (descr cmd : String)
  (args : Array String := #[]) (env: Array (String × Option String) := #[]) :
    IO Bool := do
  IO.println descr
  let out ← IO.Process.output { cmd := cmd, args := args, env := env }
  if out.exitCode != 0 then
    IO.println  out.stdout
    IO.eprintln out.stderr
    return true
  return false

def main : IO UInt32 := do
  if ← runCmd "Building main package" "lake" #["build"] then return 1

  let mut testCases : List String := []

  for testFilePath in ← getFilePaths ⟨"Tests"⟩ "lean" do
    let testCase := testFilePath.fileName.get!
    testCases := testCases.concat testCase

  if testCases.isEmpty then
    IO.println "\nNo more tests to run"
    return 0

  let mut allPassed : Bool := true

  for testCase in testCases do
    IO.println s!"\nRunning tests for {testCase}"
    let out ← IO.Process.output {
      cmd := "lake"
      args := #["env", "lean", "--run", s!"Tests/{testCase}"]
    }
    IO.print out.stdout
    if out.exitCode != 0 then
      IO.eprint out.stderr
      allPassed := false
  
  if allPassed then
    IO.println "\nAll tests passed!"
    return 0
  return 1
