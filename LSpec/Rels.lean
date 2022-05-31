import LSpec.LSpec

/-- Tests for boolean equality of two terms -/
def shouldBe [BEq α] (a' : α) : Rel α :=
  fun a => a == a'

/-- Tests for boolean inequality of two terms -/
def shouldNotBe [BEq α] (a' : α) : Rel α :=
  fun a => not $ a == a'

/-- Tests if a list is empty -/
def shouldBeEmpty : Rel (List α) :=
  fun l => l.isEmpty

/-- Tests if a list is nonempty -/
def shouldNotBeEmpty : Rel (List α) :=
  fun l => not l.isEmpty

/-- Tests membership of a term and a list -/
def shouldContain [BEq α] (a : α) : Rel (List α) :=
  fun l => l.contains a

/-- Tests if a term is not contained in a list -/
def shouldNotContain [BEq α] (a : α) : Rel (List α) :=
  fun l => not $ l.contains a
