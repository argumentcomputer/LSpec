# LSpec

A testing framework for Lean 4, inspired by Haskell's [Hspec](https://hspec.github.io/) package.

## Usage

There are two ways to use LSpec: via the `#lspec` command and the `lspec` function.
Both become available once you `import LSpec`.

Use the former when you want to test a function in the same file it is defined.
If you use `LSpec` as a dependency, a test failure shall interrupt the execution of the `lake build` command and throw an error visible in the editor.

The latter is for writing tests in a separate test file.
Test files can be run independently with the `lspec` binary, as shown later.

### The `TestSeq` type

`TestSeq` is used to represent sequences of tests.
In order to instantiate terms of `TestSeq`, use one of the two following helper functions:

* `test`: consumes a description and a proposition;
* `test'`: consumes a description, a proposition and an (optional) extra `TestSeq`.
Use it if you don't want to use `do` notation.

The propositions above, however, must have their own instances of `TDecidable`.

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

### The `#lspec` command

The `#lspec` command allows you to test interactively in a file.
It requires one argument `t : TestSeq`.

Examples:

```lean
import LSpec

#lspec do
  test "four equals four" (4 = 4)
  test "five equals five" (5 = 5)

#lspec
  test' "four equals four" (4 = 4) $
  test' "five equals five" (5 = 5)
```

### The `lspec` function

The `lspec` function is for writing tests in a separate file and represents the result of one `LSpec` test suite.
Similarly to the `#lspec` command, it requires an argument of type `TestSeq`.

For example, we can create a standalone `Tests.lean` file:
```lean
import LSpec

def main := lspec $
  test "four equals four" (4 = 4)
```

If you run `Tests.lean`, the expected output should be:
```lean
✓ four equals four
```

### The `lspec` binary

Suppose you want to create multiple test files, each with a separate test suite.
Create a folder called `Tests` in the root directory of your project and then:

1. Add Lean files similar to the `Tests.lean` example above.
2. Compile the LSpec binary with `lake build LSpec`.
3. Run the binary with `./lean_packages/LSpec/build/bin/lspec`.

The `lspec` binary triggers a `lake build` automatically, which takes care of interactive tests created with the `#lspec` command.

After building your package, the `lspec` binary searches for and recursively runs Lean files inside the `Tests` directory.
It allows adding folders inside `Tests` to create a custom file structure.

For this to work, all of your Lean files used in the tests must be built when `lake build` is called.

## Using LSpec on CI

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
