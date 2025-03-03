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

`lspecIO` is meant to be used in files to be compiled and integrated in a testing infrastructure, as shown below.

```lean
def aaSuite := [
    test "four equals four" (4 = 4)
  ]

def bbSuite := [
    test "five equals five" (5 = 5)
  ]

def main := lspecIO $ .ofList [
    ("aa", aaSuite),
    ("bb", bbSuite)
  ]
```

Once such `main` function is defined, its respective executable can be tagged as the `@[test_driver]` in the lakefile.
For further information, inspect the docstring of `lspecIO`.

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
