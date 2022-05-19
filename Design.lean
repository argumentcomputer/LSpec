-- Eventually make this more interesting
abbrev Result := Bool 

-- I went back and forth on this for a while, and arrived at this tentative definition of a Spec.
structure SpecOn {α : Type} (obj : α) where
  testParam : Type -- Specs can contain parameters to allow for an eventual way of writing specs 
  prop : testParam → Result -- The actual property that's being tested
                            -- I wanted this to be a literal `Prop`, but dealing with the `DecidablePred` 
                            -- instance was annoying
  result (test : testParam) : Result → String -- Pretty print the result for test runs

-- The idea is to write generic specs in the library like this one
@[reducible]def alwaysEquals {α β : Type} [BEq β] (f : α → β) (b : β) : SpecOn f := {
  testParam := α
  prop      := fun a => f a == b
  result    := fun a b => match b with
    | true  => "yes"
    | false => "no"
}

-- Specs can also not contain parameters if they're specs about things that don't fit neatly into
-- a function type
@[reducible]def doesntContain {α β : Type} [BEq β] (bx : List β) (b : β) : SpecOn bx := {
  testParam := Unit
  prop      := fun _ => not <| bx.contains b
  result    := fun a b => match b with
    | true  => "yes"
    | false => "no"
}

-- Basic Example type, as functionality is added it will probably get more complicated (custom messages
-- and configurations per example)
structure Example {α : Type} {a : α} (spec : SpecOn a) where
  ex : spec.testParam

abbrev Examples {α : Type} {a : α} (spec : SpecOn a) := List <| Example spec

namespace Example

-- Tool to construct "default" examples from a given 
def fromParam {α : Type} {a : α} (spec : SpecOn a) (input : spec.testParam) : Example spec := { ex := input }

-- Check the example, now `Result` is `Bool` but this has room to grow
partial def check {α : Type} {a : α} {spec : SpecOn a} (exmp : Example spec) : Result := 
  spec.prop exmp.ex

-- Expand this out 
partial def run {α : Type} {a : α} {spec : SpecOn a} (exmp : Example spec) : String :=
  spec.result exmp.ex <| check exmp

end Example

-- Ditto from above
namespace Examples

def fromParams {α : Type} {a : α} (spec : SpecOn a) (input : List spec.testParam) : Examples spec := 
  input.map <| Example.fromParam spec

partial def check {α : Type} {a : α} {spec : SpecOn a} (exmp : Examples spec) : List Result := 
  exmp.map Example.check

partial def run {α : Type} {a : α} {spec : SpecOn a} (exmps : Examples spec) : List String :=
  exmps.map Example.run 

end Examples

namespace test1

def foo (n : Nat) : Nat := 4

-- Once we have generic specs above, we can easily construct specs for particular examples
-- The idea is to hook this into a version of the syntax Arthur implemented in `YatimaSpec.lean`
@[reducible]def fooSpec : SpecOn foo := alwaysEquals foo 4

-- Can create examples for the specs also using .fromParam
def fooExample  : Example  fooSpec := Example.fromParam fooSpec 3
def fooExamples : Examples fooSpec := Examples.fromParams fooSpec [2,3,4,5,6,6]

-- Running is as easy as `.run`
#eval fooExample.run
#eval fooExamples.run

end test1

namespace test2

def onlyEven (xs : List Nat) : List Nat := xs.filter (· % 2 == 0)

@[reducible]def noOddSpec : SpecOn onlyEven := {
  testParam := List Nat × Nat
  prop      := fun (xs, x) => not <| (onlyEven xs).contains x
  result    := fun (xs, x) b => match b with
    | true => "yes"
    | false => "no"
}

def evenExample : Example noOddSpec := Example.fromParam noOddSpec ([1,2,3],3)
def evenExamples : Examples noOddSpec := Examples.fromParams noOddSpec [([1,2,3],3), ([6,27,19,20],7), ([45,7,45,672,34,231,42,3],3)]

#eval evenExample.run
#eval evenExamples.run

end test2