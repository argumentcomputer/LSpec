# LSpec

A Testing Framework for Lean

## Usage

There are two ways to use LSpec: via the `#lspec` command and via the `lspec`
function. Both become available once you `import LSpec`.

The former is used when you want to test a function in the same file you define
it. If the test fails, an error is thrown, which can interrupt the `lake build`
command in your lib that uses LSpec as a dependency.

The latter is meant for writing tests on a separate file, which can then be run
independently with the `lspec` binary. We'll see more about it later.

## The `LSpec` and `Rel` types

`LSpec` is the basic structure used to encode tests. We can create an term with
type `LSpec` by using the `it` function, which is described below.

`Rel` represents an assertion of some kind. This is very general; here are some
examples:

```lean
def shouldBe [BEq α] (a' : α) : Rel α :=
  fun a => a == a'
```

This predicate simply asserts that the input `a'` should be some value `a`.

We also define:
```lean
def shouldNotBe [BEq α] (a' : α) : Rel α :=
  fun a => not $ a == a'

def shouldBeEmpty : Rel (List α) :=
  fun l => l.isEmpty

def shouldNotBeEmpty : Rel (List α) :=
  fun l => not l.isEmpty
```

These are just some of the most basic assertions that are provided.
One can easily define some custom assertion type for their own needs.

## The `it` helper function

`it` creates an instance of an `LSpec` and represents a single test. `it`
requires four arguments:

1. `descr : String`: a discription of the test
2. `val : α`: the value being tested
3. `rel : Rel α`: an assertion that `a` is being tested on
4. `next : LSpec`: the next test (also defined by an `it`);
the default option `done` represents no further tests.

For example, we could define two simple tests:
```lean
def twoTests : LSpec := 
  it "knows equality" 42 (shouldBe 42) $
  it "knows lists" [42].length (shouldBe 1)
```

## The `#lspec` command

The `#lspec` command allows you to test interactively in a file.
It requires one argument `foo : LSpec`.

The command will throw an error if the type of the argument is not `LSpec` or
if the test fails.

For example:

```lean
#lspec it "knows equality" 4 (shouldBe 4)
```

Will output `✓ it knows equality` and succeed.

## The `lspec` function

The `lspec` function is for writing tests on a separate file, and represents the
result of one `LSpec` test. It requires two arguments, a description of the
tests and the `LSpec` test being run.

For example, take `twoTests` we defined above. Then we can create a standalone
`Tests.lean` file:

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

Now suppose you want to create multiple test files, each with their own test
suite. You just need to create a folder called `Tests` in the root directory of
your project and then:

1. Add Lean files similar to the `Tests.lean` example above
2. Compile the LSpec binary with `lake compile LSpec`
3. Run the binary with `./lean_packages/LSpec/build/bin/lspec`, which searches
for and runs Lean files inside `Tests` recursively (yes, you can add folders
inside `Tests` and create your own file structure)

Note: this flow can be automated with CI flows.
