import LSpec.Meta
import LSpec.Runner

namespace test1

def foo (n : Nat) : Nat := n

-- Once we some generic spec is defined, one can easily construct specs to test particular properties
@[reducible] def fooSpec : SpecOn foo := alwaysEquals foo 4

-- Can create examples for the specs also using .fromParam
def fooExample  : ExampleOf fooSpec := .fromParam 4
def fooExamples : ExamplesOf fooSpec := .fromParams [2,3,4,5,6,6]


-- Examples are tested using `#spec`:

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


/-
Some more spec examples. 
-/
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

/-
The above test examples, but with a metaprogramming layer to make the process more seamless.
-/
namespace test3

def foo (n : Nat) : Nat := n

mkspec fooSpec : foo := alwaysEquals foo 4

#spec Test fooSpec with 4
#spec Tests fooSpec with [2,3,4,5,6,6]


def onlyEven (xs : List Nat) : List Nat := xs.filter (· % 2 == 0)

mkspec noOddSpec : onlyEven := depDoesntContain onlyEven

#spec Test noOddSpec with ([1,2,3],3) => "doesn't have odds"

#spec Tests noOddSpec with [([1,2,3],3), ([6,27,19,20],7), ([45,7,45,672,34,231,42,3],3)]

end test3

namespace test4

-- Tests using raw functions
def testTree : Spec :=
  describe "test" do
    it (doesntContain [1,2,3]) $ ExampleOf.fromDescrParam "[1,2,3] doesn't contain 4" 4
    it (doesntContain [1,2,3]) $ ExampleOf.fromDescrParam "[1,2,3] doesn't contain 5" 5
    describe "testing failures" $ do
      it (doesntContain [1,2,3]) $ ExampleOf.fromDescrParam "[1,2,3] doesn't contain 1" 1
      it (doesntContain [1,2,3]) $ ExampleOf.fromDescrParam "[1,2,3] doesn't contain 2" 2
    it (equals 1 2) $ ExampleOf.fromDescrParam "1 equals 2" ()
    it (equals 1 1) $ ExampleOf.fromDescrParam "1 equals 1" ()

-- Tests that use the Meta.lean syntax
def testTree2 : Spec :=
  describe "test2" do
     it' $ Test doesntContain [1,2,3] with 4 => "Hello"
     it' $ Test doesntContain [1,2,3] with 3 => "World"
     it' $ Test doesntContain [1,2,3] with 1

-- testTree1 and testTree2 combined into a single tree
def combined : Spec := do
  describe "combined" do
    testTree
    testTree2

#eval combined.run
/-
combined
  test
    [1,2,3] doesn't contain 4: ✓ Success!
    [1,2,3] doesn't contain 5: ✓ Success!
    testing failures
      [1,2,3] doesn't contain 1: × Failure!
      [1,2,3] doesn't contain 2: × Failure!
    1 equals 2: × Failure!
    1 equals 1: ✓ Success!
  test2
    Hello: ✓ Success!
    World: × Failure!
    × Failure!
-/
end test4