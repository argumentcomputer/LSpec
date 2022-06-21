# LSpec

A Testing Framework for Lean

## Usage

There are two ways to use LSpec: via the `#lspec` command and via the `lspec` function. Both become available once you `import LSpec`.

Use the former when you want to test a function in the same file it is defined. If you use `LSpec` as a dependency, a test failure shall interrupt the execution of `lake build` command and throw an error visible in the editor.

The latter is for writing tests in a separate test file. Test files can be ran
independently with the `lspec` binary, as shown later.

## The `LSpec` and `Rel` types

`LSpec` is the basic structure used to encode tests. We can create a term with type `LSpec` by using the `it` function described below.

`Rel` represents an assertion of some kind. This is very general; here are some examples:

```lean
def shouldBe [BEq α] (a' : α) : Rel α :=
  fun a => a == a'
```

This simple predicate asserts that the input `a'` should be some value `a`.

We also define:
```lean
def shouldNotBe [BEq α] (a' : α) : Rel α :=
  fun a => not $ a == a'

def shouldBeEmpty : Rel (List α) :=
  fun l => l.isEmpty

def shouldNotBeEmpty : Rel (List α) :=
  fun l => not l.isEmpty
```

These are just some of the most trivial assertions. For the time being, we do not provide many more, although it can change. That said, one can easily define some custom assertion type for their own needs.

## The `it` helper function

`it` creates an instance of an `LSpec` and represents a single test. `it`
requires four arguments:

1. `descr : String`: a discription of the test
2. `val : α`: the value tested
3. `rel : Rel α`: an assertion that `a` is tested on
4. `next : LSpec`: the next test (also defined by an `it`);
the default option `done` represents no further tests.

For example, we could define two simple tests:
```lean
def twoTests : LSpec := 
  it "knows equality" 42 (shouldBe 42) $
  it "knows lists" [42].length (shouldBe 1)
```

## The `#lspec` command

The `#lspec` command allows you to test interactively in a file. It requires one argument `foo : LSpec`.

The command will throw an error if the type of the argument is not `LSpec` or if the test fails.

For example:

```lean
#lspec it "knows equality" 4 (shouldBe 4)
```

Will output `✓ it knows equality` and succeed.

## The `lspec` function

The `lspec` function is for writing tests in a separate file, and represents the result of one `LSpec` test suite. As discussed earlier, one can chain `LSpec` tests by providing the next test as the last argument of `it` function. `lspec` funciton requires two arguments, a description of the tests and the `LSpec` to run.

For example, take `twoTests` we defined above. Then we can create a standalone `Tests.lean` file:
```lean
import LSpec

def twoTests : LSpec := 
  it "knows equality" 42 (shouldBe 42) $
  it "knows lists" [42].length (shouldBe 1)

def main :=
  lspec "some description" twoTests
```

If you run `Tests.lean`, the expected output should be:
```lean
Testing that: some description
✓ it knows equality
✓ it knows lists
```

## The `lspec` binary

Suppose you want to create multiple test files, each with their own test suite. Create a folder called `Tests` in the root directory of your project and then:

1. Add Lean files similar to the `Tests.lean` example above
2. Compile the LSpec binary with `lake compile LSpec`
3. Run the binary with `./lean_packages/LSpec/build/bin/lspec`

The `lspec` binary triggers a `lake build` automatically, which takes care of interactive tests created with the `#lspec` command.

After building your package, the `lspec` binary searches for and recursively runs Lean files inside `Tests` directory. It allows to add folders inside `Tests` to create your own file structure.

For this to work, all of your Lean files used in the tests must be built when
`lake build` is called.

## Using LSpec on CI

To integrate LSpec to GitHub workflows, create the file
`.github/workflows/lspec.yml` with the content:

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
