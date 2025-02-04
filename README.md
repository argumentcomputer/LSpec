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
The proposition, however, must have its own instance of `Testable`.

You can also collect `TestSeq` into conceptual test groups by using the
helper function `group`:

```lean
#check
  test "Nat equality" (42 = 42) $
  group "manual group" $
    test "Nat equality inside group" (4 = 4)
```

### The `Testable` class

`Testable` is how Lean is instructed to decide whether certain propositions are resolved as `true` or `false`.

This is an example of a simple instance for decidability of equalities:

```lean
instance (x y : α) [DecidableEq α] [Repr α] : Testable (x = y) :=
  if h : x = y then
    .isTrue h
  else
    .isFalse h s!"Not equal: {repr x} and {repr y}"
```

The custom failure message is optional.

There are more examples of `Testable` instances in [LSpec/Instances.lean](LSpec/Instances.lean).

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
```

An important note is that a failing test will raise an error, interrupting the building process.

#### The `lspecIO` function

`lspecIO` is meant to be used in files to be compiled and integrated in a testing infrastructure, as shown soon.

```lean
def fourIO : IO Nat :=
  return 4

def fiveIO : IO Nat :=
  return 5

def main := do
  let four ← fourIO
  let five ← fiveIO
  lspecIO $
    test "fourIO equals 4" (four = 4) $
    test "fiveIO equals 5" (five = 5)
```

## Integration with `SlimCheck`

There are 3 main typeclasses associated with any  `SlimCheck` test:

* `Shrinkable` : The typeclass that takes a type `a : α` and returns a `List α` of elements which
  should be thought of as being "smaller" than `a` (in some sense dependent on the type `α` being 
  considered).
* `SampleableExt` : The typeclass of a . 
  This is roughly equivalent to `QuickCheck`'s `Arbitrary` typeclass. 
* `Checkable` : The property to be checked by `SlimCheck` must have a `Checkable` instance.

In order to use `SlimCheck` tests for custom data types, the user will need to implement 
instances of the typeclasses `Shrinkable` and `SampleableExt` for the custom types appearing
in the properties being tested.

The module [LSpec.SlimCheck.Checkable](LSpec/SlimCheck/Checkable.lean) contains may of 
the useful definitions and instances that can be used to derive a Checkable instance 
for a wide variety of properties given just the instances above. If all else fails, the user can 
also define the Checkable instance by hand. 

Once this is done a `Slimcheck` test is evaluated in a similar way to 
`LSpec` tests: 

```lean
#lspec check "add_comm" $ ∀ n m : Nat, n + m = m + n

#lspec check "add_comm" $ ∀ n m : Nat, n + m = m + m
-- × add_comm

-- ===================
-- Found problems!
-- n := 1
-- m := 0
-- issue: 1 = 0 does not hold
-- (0 shrinks)
-- -------------------
```

## Setting up a testing infra

The LSpec package also provides a binary that runs test files automatically.
Run `lake exe lspec` to build it (if it hasn't been built yet) and execute it.

The `lspec` binary searches for binary executables defined in `lakefile.lean` whose module name starts with "Tests".
Then it builds and runs each of them.

For instance, suppose you want to run the test suites defined in `Tests/F1.lean` and `Tests/Some/Dir/F2.lean`.
In this case, you need to add the following lines to your `lakefile.lean`:

```lean
lean_exe Tests.F1
lean_exe Tests.Some.Dir.F2
```

## Running specific test suites

The `lspec` binary also accepts specific test suites as input.
For example, you can call `lake exe lspec Tests/Foo.lean Tests/Some/Bar.lean` and it will build and run those.

This is particularly useful for running test suites locally.

### Using LSpec on CI

To integrate LSpec to GitHub workflows, run `lake exe lspec-ci branch1 branch2`.
The singleton containing `main` is the default branch list.
`lspec-ci` will create a file `.github/workflows/lspec.yml` with the content:

```yml
name: "LSpec CI"
on:
  pull_request:
  push:
    branches:
      - <branch1>
      - <branch2>
      - ...
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
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
      - uses: actions/checkout@v4
      - name: run LSpec binary
        run: lake exe lspec
```
