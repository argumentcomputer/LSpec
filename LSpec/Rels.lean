import LSpec.LSpec

def shouldBe [BEq α] (a' : α) : Rel α :=
  fun a => a == a'

def shouldNotBe [BEq α] (a' : α) : Rel α :=
  fun a => not $ a == a'

def shouldBeEmpty : Rel (List α) :=
  fun l => l.isEmpty

def shouldNotBeEmpty : Rel (List α) :=
  fun l => not l.isEmpty

def shouldContain [BEq α] (a : α) : Rel (List α) :=
  fun l => l.contains a

def shouldNotContain [BEq α] (a : α) : Rel (List α) :=
  fun l => not $ l.contains a
