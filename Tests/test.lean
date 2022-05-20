import LSpec.Spec


namespace test1

def foo (n : Nat) : Nat := 4

-- Once we have generic specs above, we can easily construct specs for particular examples
-- The idea is to hook this into a version of the syntax Arthur implemented in `YatimaSpec.lean`
@[reducible]def fooSpec : SpecOn foo := alwaysEquals foo 4

-- Can create examples for the specs also using .fromParam
def fooExample  : ExampleOf fooSpec := ExampleOf.fromParam fooSpec 3
def fooExamples : Examples fooSpec := Examples.fromParams fooSpec [2,3,4,5,6,6]

-- Running is as easy as `.run`
#eval fooExample.run
#eval fooExamples.run

end test1

namespace test2

def onlyEven (xs : List Nat) : List Nat := xs.filter (· % 2 == 0)

@[reducible]def noOddSpec : SpecOn onlyEven := depDoesntContain onlyEven 

def evenExample : ExampleOf noOddSpec := ExampleOf.fromDescrParam noOddSpec "doesn't have odds" ([1,2,3],3)
def evenExamples : Examples noOddSpec := Examples.fromParams noOddSpec [([1,2,3],3), ([6,27,19,20],7), ([45,7,45,672,34,231,42,3],3)]

#eval evenExample.run
#eval evenExamples.run

end test2