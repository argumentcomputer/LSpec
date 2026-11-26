module
public import LSpec

/-!
# Import-Time Execution Guard Fixture

Imported unconditionally by `LSpecTests.Main`. Every suite here contains a sentinel
that would fail or panic if Lean evaluated test bodies during module
initialization (either eagerly or via `compiler.extract_closed` hoisting).
-/

namespace LSpecTests.ImportCheck
public section

open LSpec

/-- Pure computation that panics if ever evaluated. With `compiler.extract_closed`
    disabled on the suite, importing this module must not hoist or evaluate this
    before `main` runs. -/
@[noinline] def boomIfEvaluatedAtImport (n : Nat) : Bool :=
  if n == 999999 then panic! "BUG: pure test body was evaluated at import time!"
  else true

set_option compiler.extract_closed false in
/-- Suite that is imported by `LSpecTests.Main` and registered under the
    `import-guard` tag so it is filtered out by default; if any body ran at
    import time, the process would crash immediately on startup. -/
public def importGuardSuite : Spec := do
  withTag "import-guard" do
    describe "Import-time laziness guard" do
      itBool "closed pure panic is never evaluated at import" (boomIfEvaluatedAtImport 999999)
      it "closed pure let inside AssertM is never evaluated at import" do
        let ok := boomIfEvaluatedAtImport 999999
        expect ok
      prop "closed pure let inside prop is never evaluated at import" <|
        let ok := boomIfEvaluatedAtImport 999999
        fun (_ : Nat) => ok
      it "passing lazy check runs normally when selected" do
        expect (boomIfEvaluatedAtImport 1)

end
end LSpecTests.ImportCheck
