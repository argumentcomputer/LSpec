/--
Specification tests will result in either a `success` or `failure`, with some associated string 
outputs.
-/
inductive Result
  | success
  | failure

def Result.toString : Result → String
  | .success => "✓ Success!"
  | .failure => "× Failure!"

/--
For now `Result` is not much more than `Bool`, so the distinction is arbitrary. The infrastructure
is in place to support more robust test results closer to what is offered by Hspec. 
-/
def ofBool : Bool → Result
  | true  => .success
  | false => .failure

def Result.toBool : Result → Bool
  | .success => true
  | _        => false

/--
The basic structure used to encode specifications. In this case `SpecOn obj` represents a
specification for `obj`.
-/
structure SpecOn {α : Type} (obj : α) where
  -- The parameters `testParam` that the spec is to be tested against
  testParam : Type
  -- The property `prop` that the spec is 
  prop : testParam → Result

/-
This section contains a list of generic specifications that the user can plug in to generate 
instances of `SpecOn obj`. 

For example a specification for `foo : Nat → Nat` can be defined using

`@[reducible] def SpecOn foo := alwaysEquals foo 4`

Some syntactic sugar is provided in `Meta.lean` to make this process less painful.

The aim is for this list to expand, but the API of creating specifications with `SpecOn` should
always be available in edge cases not captured by those provided in the library.
-/
section SectionSpecs

variable {α β : Type} [BEq α] [BEq β]

/--
`equals` tests for boolean equality of two terms
-/
@[reducible] def equals (a b : α) : SpecOn () :=
  ⟨Unit, fun _ => ofBool $ a == b⟩

/--
`alwaysEquals` tests whether the function `f` is constant equal to `b`
-/
@[reducible] def alwaysEquals (f : α → β) (b : β) : SpecOn f :=
  ⟨α, fun a => ofBool $ f a == b⟩

/--
`doesntContain` tests whether a list does not contain the `testParam`
-/
@[reducible] def doesntContain (bs : List β) : SpecOn bs :=
  ⟨β, fun b => ofBool $ not $ bs.contains b⟩

/--
`depDoesntContain` is a dependent version of `doesntContain`, where the output of a list-valued
function `f` does not contain a parametrized 
-/
@[reducible] def depDoesntContain (f : α → List β) : SpecOn f :=
  ⟨α × β, fun (a, b) => ofBool $ not $ (f a).contains b⟩

/--
`neverContains` test whether a list-valued function `f` never evaluates to a list containing a fixed
`b : β`. 
-/
@[reducible] def neverContains (f : α → List β) (b : β) : SpecOn f :=
  ⟨α, fun a => ofBool $ not $ (f a).contains b⟩

end SectionSpecs

/-
Examples are tests for specifications that can be run with `.check` to yield a result, or evaluated
with `#spec` defined in `Meta.lean`. 
-/
section SectionExample

variable {α : Type} {a : α}

/--
A structure wrapping an example `testParam` for a Spec. This has room to grow to make specification
testing more robust. For example, it may eventually include randomized tests.
-/
structure ExampleOf (spec : SpecOn a) where
  -- An optional string description for the example being tested, this is part of the output when run
  descr : Option String
  -- An example `testParam` to run the specification on.
  exam  : spec.testParam

-- Plural of the above
structure ExamplesOf (spec : SpecOn a) where
  descr : Option String
  exams : List spec.testParam

namespace ExampleOf

/--
Helper functions to build examples of specifications from input parameters and optional descriptions.
If/when examples become more complicated, more of these helper functions can be written to write more
complicated examples.
-/
def fromParam {spec : SpecOn a} (input : spec.testParam) : ExampleOf spec :=
  ⟨none, input⟩

def fromDescrParam {spec : SpecOn a} (descr : String) (input : spec.testParam) : ExampleOf spec :=
  ⟨descr, input⟩

/--
`check` an example, and yield a `Result`
-/
def check {α : Type} {a : α} {spec : SpecOn a} (exmp : ExampleOf spec) : Result :=
  spec.prop exmp.exam

/--
Extract the relevant pieces of a `Result` for pretty-priting and analysis. This is:
* The example description
* Whether or not the test failed 
* The string encoding the result.
-/
def run {α : Type} {a : α} {spec : SpecOn a} (exmp : ExampleOf spec) :
    Option String × Bool × String :=
  let res := exmp.check
  (exmp.descr, res.toBool, res.toString)

end ExampleOf

/-
Plural of the above
-/
namespace ExamplesOf

def fromParams {α : Type} {a : α} {spec : SpecOn a}
    (input : List spec.testParam) : ExamplesOf spec :=
  ⟨none, input⟩

def fromDescrParams {α : Type} {a : α} {spec : SpecOn a}
    (descr : String) (input : List spec.testParam) : ExamplesOf spec :=
  ⟨descr, input⟩

def check {α : Type} {a : α} {spec : SpecOn a} (exmps : ExamplesOf spec) :
    List Result :=
  exmps.exams.map spec.prop

def run {α : Type} {a : α} {spec : SpecOn a} (exmps : ExamplesOf spec) :
    Option String × List (Bool × String) :=
  let res := exmps.check
  (exmps.descr, (res.map Result.toBool).zip $ res.map Result.toString)

end ExamplesOf

end SectionExample
