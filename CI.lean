open System

def ciConfig (branches : String) : String := s!"name: \"LSpec CI\"
on:
  pull_request:
  push:
    branches:{branches}
jobs:
  build:
    name: Build
    runs-on: ubuntu-latest
    steps:
      - name: install elan
        run: |
          set -o pipefail
          curl -sSfL https://github.com/leanprover/elan/releases/download/v4.0.0/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
          ./elan-init -y --default-toolchain none
          echo \"$HOME/.elan/bin\" >> $GITHUB_PATH
      - uses: actions/checkout@v4
      - name: run LSpec binary
        run: lake exe lspec
"

def main (branches : List String) : IO Unit := do
  let branches := if branches.isEmpty then ["main"] else branches
  let branches := .join $ branches.map (s!"\n      - {·}")
  let wfPath : FilePath := ".github" / "workflows"
  let ciPath : FilePath := wfPath / "lspec.yml"
  if ← ciPath.pathExists then
    IO.println s!"{ciPath} already exists"
  else
    if !(← wfPath.pathExists) then IO.FS.createDirAll wfPath
    IO.FS.writeFile ciPath (ciConfig branches)
