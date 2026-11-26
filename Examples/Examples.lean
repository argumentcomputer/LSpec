import LSpec

open LSpec LSpec.Prop

/-!
# LSpec Examples

Demonstrates:
- Hspec-style `describe` / `context` / `it` / `itBool` / `xit`
- Bool-based expectations (`shouldBe`, `shouldContainSubstr`, `expect`)
- Bool-based property testing (`prop`, `==>`, `forAll`, custom `Sampleable`/`Shrinkable`)
- Scoped resources (`withResource`), tags (`withTag`), and `sequential` execution
- Bounded-thread CLI runner (`lspecMain`)
-/

/-! ## Custom type with `Sampleable` & `Shrinkable` -/

structure Pair where
  left : Nat
  right : Nat
  deriving BEq, Repr

instance : Shrinkable Pair where
  shrink p :=
    (Shrinkable.shrink p.left).map (fun l => { p with left := l }) ++
    (Shrinkable.shrink p.right).map (fun r => { p with right := r })

instance : Sampleable Pair where
  sample := return { left := ← Gen.chooseNat 0 (← Gen.getSize),
                     right := ← Gen.chooseNat 0 (← Gen.getSize) }

/-! ## Defining Suites -/

def mathSuite : Spec := do
  describe "Math" do
    context "addition" do
      it "adds two numbers" do
        shouldBe (2 + 2) 4
        shouldBe (0 + 5) 5

      itBool "is associative on small values" ((1 + 2) + 3 == 1 + (2 + 3))

      prop "is commutative" fun (a b : Nat) =>
        a + b == b + a

      prop "with precondition guard" fun (a b : Nat) =>
        (Nat.ble b a) ==> (a - b + b == a)

    context "custom Pair generator" do
      prop "sum is at least each component" fun (p : Pair) =>
        Nat.ble p.left (p.left + p.right) && Nat.ble p.right (p.left + p.right)

      prop "with explicit weighted generator" <|
        let biasedGen : Gen Nat :=
          Gen.frequency #[
            (5, Gen.chooseNat 0 10),
            (3, Gen.chooseNat 11 100),
            (2, Gen.chooseNat 101 1000)
          ] (pure 0)
        forAll biasedGen fun n => Nat.ble n 1000

def resourceExample : Spec := do
  describe "Resources & Execution Modes" do
    let tempResource : ResourceSpec String := {
      description := "shared greeting"
      acquire := pure "hello from fixture"
      release := fun _ => pure ()
    }
    withResource tempResource fun getGreeting => do
      it "reads shared resource" do
        let msg ← getGreeting
        shouldContainSubstr msg "fixture"

    sequential do
      it "runs first" do expect true
      it "runs second" do expect true

    withTag "slow" do
      xit "pending integration check" do
        pendingWith "not yet implemented"

def main (args : List String) : IO UInt32 :=
  lspecMain (do mathSuite; resourceExample) args { threads := 4 }
