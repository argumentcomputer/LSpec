# LSpec

A testing framework for Lean 4, inspired by Haskell's [Hspec](https://hspec.github.io/) package.

## Usage

### Composing tests

Sequences of tests are represented by the `TestSeq` datatype.
In order to instantiate terms of `TestSeq`, use the `test` helper function:

```lean
#check
  test "Nat equality" (4 = 4) $
  test "Nat inequality" (4 ≠ 5)
-- test "Nat equality" (4 = 4) (test "Nat inequality" (4 ≠ 5)) : TestSeq
```

`test` consumes a description a proposition and a next test
The proposition, however, must have its own instance of `TDecidable`.

### The `TDecidable` class

`TDecidable` is how Lean is instructed to decide whether certain propositions are resolved as `true` or `false`.

This is an example of a simple instance for decidability of equalities:

```lean
instance (x y : α) [DecidableEq α] [Repr α] : TDecidable (x = y) :=
  if h : x = y then
    .isTrue h
  else
    .isFalse h s!"Not equal: {repr x} and {repr y}"
```

The custom failure message is optional.

There are more examples of `TDecidable` instances in [LSpec/Instances.lean](LSpec/Instances.lean).
Such instances are automatically imported via `import LSpec`.

The user is, of course, free to provide their own instances.

### Actually running the tests

#### The `#lspec` command

The `#lspec` command allows you to test interactively in a file.

Examples:

```lean
#lspec
  test "four equals four" (4 = 4) $
  test "five equals five" (5 = 5)
-- ✓ four equals four
-- ✓ five equals five

#lspec do
  test "four equals four" (4 = 4)
  test "five equals five" (5 = 5)
-- ✓ four equals four
-- ✓ five equals five
```

An important note is that a failing test will raise an error, interrupting the building process.

The fact that test execution happens in the `LSpec` monad allows the use of `do` notation, as seen above.
So one can (ab)use the `do` notation run multiple tests without dollar signs.
In such case, every call to `test` creates a `TestSeq` with a single test.

#### The `lspec` function

The `lspec` function can be used for generic purposes inside other functions.
It returns a term of type `Except String String`, representing success or failure, with a message for each case.

```lean
def tests :=
  test "four equals four" (4 = 4) $
  test "five equals five" (5 = 5)

def foo : IO Unit := do
  match lspec tests with
  | .ok    msg => IO.println msg
  | .error msg => IO.eprintln msg
```

#### The `lspecIO` function

`lspecIO` is meant to be used in files to be compiled and integrated in a testing infrastructure, as shown soon.

```lean
def fourIO : IO Nat :=
  return 4

def fiveIO : IO Nat :=
  return 5

def main : IO UInt32 := do
  let four ← fourIO
  let five ← fiveIO
  lspec do
    test "fourIO equals 4" (four = 4)
    test "fiveIO equals 5" (five = 5)
```

## Setting up a testing infra

The LSpec package also provides a binary that runs test files automatically.
The binary becomes available by running `lake build LSpec`, which will generate the file `./lean_packages/LSpec/build/bin/lspec`.

The `lspec` binary recursively searches for Lean files inside a `Tests` directory.
For each Lean file present `Tests`, there must exist a corresponding `lean_exe` in your `lakefile.lean`.

For instance, suppose that the directory `Tests` contains the files `Tests/F1.lean` and `Tests/Some/Dir/F2.lean`.
In this case, you need to add the following lines to your `lakefile.lean`:

```lean
lean_exe Tests.F1
lean_exe Tests.Some.Dir.F2
```

### Using LSpec on CI

To integrate LSpec to GitHub workflows, create the file `.github/workflows/lspec.yml` with the content:

```yml
name: "LSpec CI"
on:
  pull_request:
  push:
    branches:
      - main
jobs:
  build:
    name: Build
    runs-on: ubuntu-latest
    steps:
      - name: install elan
        run: |
          set -o pipefail
          curl -sSfL https://github.com/leanprover/elan/releases/download/v1.3.1/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
          ./elan-init -y --default-toolchain none
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
      - uses: actions/checkout@v2
      - name: build LSpec
        run: lake build LSpec
      - name: run LSpec
        run: ./lean_packages/LSpec/build/bin/lspec
```
