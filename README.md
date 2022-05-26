# LSpec
A Testing Framework for Lean

## Usage

In the file where you want to run the tests: `import LSpec`, define the specification using the
`mkspec` syntax, and run the test using `#spec Tests <specname> with <input_param>`

```lean
def foo (n : Nat) : Nat := n

mkspec fooSpec : foo := alwaysEquals foo 4

#spec Test fooSpec with 4 => "Always equals four"

#spec Tests fooSpec with [2,3,4,5,6,6]
```

See `Tests/test.lean` for more examples.

## Generic specs

So far the following generic specs are defined: 

* `equals`
* `alwaysEquals`
* `doesntContain`
* `depDoesntContain`
* `neverContains`

But more can be defined by following the examples provided in `Spec.Lean`. The `reducible` attribute
is important in defining the generic specification, so make sure to include it when you write your
own specifications by hand.