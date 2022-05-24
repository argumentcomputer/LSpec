import LSpec.Spec


namespace test1

def foo (n : Nat) : Nat := n

-- Once we have generic specs above, we can easily construct specs for particular examples
-- The idea is to hook this into a version of the syntax Arthur implemented in `YatimaSpec.lean`
@[reducible] def fooSpec : SpecOn foo := alwaysEquals foo 4

-- Can create examples for the specs also using .fromParam
def fooExample  : ExampleOf fooSpec := .fromParam 4
def fooExamples : ExamplesOf fooSpec := .fromParams [2,3,4,5,6,6]

#spec 0
 -- Invalid term to run '#spec' with

#spec fooExample
-- ✓ Success!

#spec fooExamples
-- × Failure!
-- × Failure!
-- ✓ Success!
-- × Failure!
-- × Failure!
-- × Failure!

end test1

namespace test2

def onlyEven (xs : List Nat) : List Nat := xs.filter (· % 2 == 0)

@[reducible] def noOddSpec : SpecOn onlyEven := depDoesntContain onlyEven 

def evenExample : ExampleOf noOddSpec :=
  .fromDescrParam "doesn't have odds" ([1,2,3],3)

def evenExamples : ExamplesOf noOddSpec :=
  .fromParams [([1,2,3],3), ([6,27,19,20],7), ([45,7,45,672,34,231,42,3],3)]

#spec evenExample
-- doesn't have odds:
-- ✓ Success!

#spec evenExamples
-- ✓ Success!
-- ✓ Success!
-- ✓ Success!

end test2
