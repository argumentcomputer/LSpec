-- TODO: Fix documentation

inductive Result
  | success
  | failure

def Result.toString : Result → String
  | .success => "✓ Success!"
  | .failure => "× Failure!"

-- helper function for now, but can very easily add more robust descriptions in the generic specs
-- below
def ofBool : Bool → Result
  | true  => .success
  | false => .failure

def Result.toBool : Result → Bool
  | .success => true
  | _        => false

-- I went back and forth on this for a while, and arrived at this tentative definition of a Spec.
structure SpecOn {α : Type} (obj : α) where
  -- Specs can contain parameters to allow for an eventual way of writing specs
  testParam : Type
  -- The actual property that's being tested
  -- I wanted this to be a literal `Prop`, but dealing with the `DecidablePred`
  -- instance was annoying
  prop : testParam → Result

@[reducible] def equals {α : Type} [BEq α] (a b : α) : SpecOn () :=
  ⟨Unit, fun _ => ofBool $ a == b⟩

-- The idea is to write generic specs in the library like this one
@[reducible] def alwaysEquals {α β : Type} [BEq β] (f : α → β) (b : β) : SpecOn f :=
  ⟨α, fun a => ofBool $ f a == b⟩

-- Specs can also not contain parameters if they're specs about things that don't fit neatly into
-- a function type
@[reducible] def doesntContain {β : Type} [BEq β] (bx : List β) : SpecOn bx :=
  ⟨β, fun b => ofBool $ not $ bx.contains b⟩

@[reducible] def depDoesntContain {α β : Type} [BEq β] (f : α → List β) : SpecOn f :=
  ⟨α × β, fun (a, b) => ofBool $ not $ (f a).contains b⟩

@[reducible] def neverContains {α β : Type} [BEq β] (f : α → List β) (b : β) : SpecOn f :=
  ⟨α, fun a => ofBool $ not $ (f a).contains b⟩

section SectionExample

variable {α : Type} {a : α}

-- Basic Example type, as functionality is added it will probably get more complicated (custom messages
-- and configurations per example)
structure ExampleOf (spec : SpecOn a) where
  descr : Option String
  exam  : spec.testParam

structure ExamplesOf (spec : SpecOn a) where
  descr : Option String
  exams : List spec.testParam

-- abbrev ExamplesOf (spec : SpecOn a) := List $ ExampleOf spec

namespace ExampleOf

-- Tool to construct "default" examples from a given parameter, this will be helpful eventually when
-- examples become more complicated
def fromParam {spec : SpecOn a} (input : spec.testParam) : ExampleOf spec :=
  ⟨none, input⟩

def fromDescrParam {spec : SpecOn a} (descr : String) (input : spec.testParam) : ExampleOf spec :=
  ⟨descr, input⟩

-- Check the example, and get a `Result`
def check {α : Type} {a : α} {spec : SpecOn a} (exmp : ExampleOf spec) : Result :=
  spec.prop exmp.exam

-- This can eventually be expanded so a run does more than just IO
def run {α : Type} {a : α} {spec : SpecOn a} (exmp : ExampleOf spec) :
    Option String × Bool × String :=
  let res := exmp.check
  (exmp.descr, res.toBool, res.toString)

end ExampleOf

-- Ditto from above
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
