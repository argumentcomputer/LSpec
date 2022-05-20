-- Pretty much lifted from Hspec
inductive FailureReason
  | noReason
  | reason (descr : String := "")
  | expectedButGot (descr : String := "") (exp got : String)
  | error {ε α : Type} (descr : String := "") (ex : Except ε α) 

open FailureReason in
instance : ToString FailureReason :=
{
  toString := fun res => match res with
    | noReason                     => ""
    | reason         descr         => descr 
    | expectedButGot descr exp got => let ebg := s!"expected {exp} but got {got}"
      if descr == "" then ebg else s!"descr: ebg"
    | error          descr except  => if descr == "" then "Exception thrown" else s!"{descr}"
}

open FailureReason

inductive Result
  | ok
  | fail (reason : FailureReason := noReason) -- (Maybe Location) 
  | pend                                      -- (Maybe Location)

open Result

instance : ToString Result := 
{
  toString := fun res => match res with
  | ok       => "Test Ok!"
  | fail res => s!"{res}"
  | pend     => "Still pending"
}
open Result

-- helper function for now, but can very easily add more robust descriptions in the generic specs
-- below
def fromBool : Bool → Result
  | true  => ok
  | false => fail

-- I went back and forth on this for a while, and arrived at this tentative definition of a Spec.
structure SpecOn {α : Type} (obj : α) where
  testParam : Type -- Specs can contain parameters to allow for an eventual way of writing specs 
  prop : testParam → Result -- The actual property that's being tested
                            -- I wanted this to be a literal `Prop`, but dealing with the `DecidablePred` 
                            -- instance was annoying

-- The idea is to write generic specs in the library like this one
@[reducible]def alwaysEquals {α β : Type} [BEq β] (f : α → β) (b : β) : SpecOn f := {
  testParam := α
  prop      := fun a => fromBool $ f a == b
}

-- Specs can also not contain parameters if they're specs about things that don't fit neatly into
-- a function type
@[reducible]def doesntContain {β : Type} [BEq β] (bx : List β) : SpecOn bx := {
  testParam := β
  prop      := fun b => fromBool $ not $ bx.contains b
}

@[reducible]def depDoesntContain {α β : Type} [BEq β] (f : α → List β) : SpecOn f := {
  testParam := α × β
  prop      := fun (a, b) => fromBool $ not $ (f a).contains b
}

@[reducible]def neverContains {α β : Type} [BEq β] (f : α → List β) (b : β) : SpecOn f := {
  testParam := α
  prop      := fun a => fromBool $ not $ (f a).contains b
}

section exampleSection

variable {α : Type} {a : α}

-- Basic Example type, as functionality is added it will probably get more complicated (custom messages
-- and configurations per example)
structure Example (spec : SpecOn a) where
  descr : Option String
  exam : spec.testParam

abbrev Examples (spec : SpecOn a) := List $ Example spec

namespace Example

-- Tool to construct "default" examples from a given parameter, this will be helpful eventually when
-- examples become more complicated
def fromParam (spec : SpecOn a) (input : spec.testParam) : Example spec := { 
  descr := none
  exam  := input 
}

def fromDescrParam (spec : SpecOn a) (descr : String) (input : spec.testParam) : Example spec := {
    descr := pure descr
    exam  := input
}

-- Check the example, and get a `Result`
def check {α : Type} {a : α} {spec : SpecOn a} (exmp : Example spec) : Result := 
  spec.prop exmp.exam

-- This can eventually be expanded so a run does more than just IO
def run {α : Type} {a : α} {spec : SpecOn a} (exmp : Example spec) : String :=
  match exmp.descr with
    | none   => s!"{exmp.check}"
    | some d => s!"it {d}: {exmp.check}"

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

end exampleSection

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

@[reducible]def noOddSpec : SpecOn onlyEven := depDoesntContain onlyEven 

def evenExample : Example noOddSpec := Example.fromDescrParam noOddSpec "doesn't have odds" ([1,2,3],3)
def evenExamples : Examples noOddSpec := Examples.fromParams noOddSpec [([1,2,3],3), ([6,27,19,20],7), ([45,7,45,672,34,231,42,3],3)]

#eval evenExample.run
#eval evenExamples.run

end test2