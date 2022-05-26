import Lean
import LSpec.Spec

open Lean

private def getBool! : Expr → Bool
  | .const ``Bool.true  .. => true
  | .const ``Bool.false .. => false
  | _                      => unreachable!

private def getStr! : Expr → String
  | .lit (.strVal s) _ => s
  | _                  => unreachable!

private def getOptionStr! (e : Expr) : Option String :=
  if e.isAppOf ``Option.some then some (getStr! $ e.getArg! 2)
  else
    if e.isAppOf ``Option.none then none
    else unreachable!

private def recoverTestResult! (res : Expr) : Bool × String :=
  (getBool! $ res.getArg! 2, getStr! $ res.getArg! 3)

open Meta Elab Command Term in
/--
* `#spec someExample : ExampleOf someSpec` calls `someExample.run`
* `#spec someExamples : ExamplesOf someSpec` calls `someExamples.run`

In either case, `#spec` also prints the outcomes of the tests. If a test fails,
an error is thrown, which can interrupt the build process.
-/
elab "#spec " term:term : command =>
  liftTermElabM `assert do
    let term ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let type ← inferType term
    if type.isAppOf ``ExampleOf then
      -- `Option String × Bool × String`
      let res ← reduce (← mkAppM ``ExampleOf.run #[term])
      let descr := getOptionStr! (res.getArg! 2)
      match recoverTestResult! (res.getArg! 3) with
      | (true,  msg) => logInfo $
        if descr.isSome then s!"{descr.get!}:\n{msg}" else msg
      | (false, msg) => throwError
        if descr.isSome then s!"{descr.get!}:\n{msg}" else msg
    else if type.isAppOf ``ExamplesOf then
       -- `Option String × List (Bool × String)`
      let res ← reduce (← mkAppM ``ExamplesOf.run #[term])
      let descr := getOptionStr! (res.getArg! 2)
      match (res.getArg! 3).listLit? with
      | none => unreachable!
      | some (_, res) =>
        let res := res.map recoverTestResult!
        let success? := res.foldl (init := true) fun acc (b, _) => acc && b
        let msg' : String := match descr with
          | none => "\n".intercalate $ res.map fun (_, msg) => msg
          | some d =>
            s!"{d}\n" ++ ("\n".intercalate $ res.map fun (_, msg) => msg)
        if success? then logInfo msg' else throwError msg'
    else throwError "Invalid term to run '#spec' with"

syntax (name := spec) "mkspec " ident " : " term " := " term : command

/--
Helper macro to build specifications out of the generic specifications. So if
you have `def foo (n : Nat) : Nat := n` in your environment, then

`mkspec fooSpec : foo := alwaysEquals foo 4`

Expands to

`@[reducible] def fooSpec : SpecOn foo := alwaysEquals foo 4`
-/
macro_rules
  | `(mkspec $id:ident : $f := $t) => `(@[reducible] def $id : SpecOn $f := $t)

syntax "Test " term " with " term (" => " str)? : term
syntax "Tests " term " with " term (" => " str)? : term

/--
Helper macros to build terms of `ExampleOf` or `ExamplesOf` respectively as:

* `Test <spec_name> with <input_param> => <description>`
* `Tests <spec_name> with <input_param> => <description>`

These macros are expanded to their respective `fromParam/fromDescrParam` and
`fromParam/fromDescrParams` functions.
-/
macro_rules
  | `(Test $t with $x $[=> $s]?) => match s with
    | some s => `((.fromDescrParam $s $x : ExampleOf $t))
    | none   => `((.fromParam $x : ExampleOf $t))
  | `(Tests $t with $x $[=> $s]?) => match s with
    | some s => `((.fromDescrParams $s $x : ExamplesOf $t))
    | none   => `((.fromParams $x : ExamplesOf $t))
