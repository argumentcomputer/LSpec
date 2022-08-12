open System

partial def getLeanFilePathsList (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    let mut extra : Array FilePath := #[]
    for dirEntry in ← fp.readDir do
      for innerFp in ← getLeanFilePathsList dirEntry.path do
        extra := extra.push innerFp
    return acc.append extra
  else
    if (fp.extension.getD "") == "lean" then
      return acc.push fp
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

def getDefaultLeanPaths : IO $ List (String × String) :=
  return (← getLeanFilePathsList ⟨"Tests"⟩).data.map fun fp =>
    let path := (fp.toString.splitOn ".").head!
    let sep := System.FilePath.pathSeparator.toString
    (path.replace sep ".", path.replace sep "-")

def getUserLeanPaths (args : List String) : List (String × String) :=
  args.map fun path =>
    let lib := s!"Tests.{path}"
    (lib, lib.replace "." "-")

def main (args : List String) : IO UInt32 := do
  let mut exeFiles : List String := []
  let leanPaths :=
    if args.isEmpty then ← getDefaultLeanPaths
    else getUserLeanPaths args
  for (lib, exe) in leanPaths do
    if ← runCmd s!"Building {exe}" "lake" #["build", lib] true then
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
