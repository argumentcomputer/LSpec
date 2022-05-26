import Lean
import LSpec.Spec

open Lean

def getBool! : Expr → Bool
  | .const ``Bool.true  .. => true
  | .const ``Bool.false .. => false
  | _                      => unreachable!

def getStr! : Expr → String
  | .lit (.strVal s) _ => s
  | _                  => unreachable!

def getOptionStr! (e : Expr) : Option String :=
  if e.isAppOf ``Option.some then some (getStr! $ e.getArg! 2)
  else
    if e.isAppOf ``Option.none then none
    else unreachable!

def recoverTestResult (res : Expr) : Bool × String :=
  (getBool! $ res.getArg! 2, getStr! $ res.getArg! 3)

open Meta Elab Command Term in
elab "#spec " term:term : command =>
  liftTermElabM `assert do
    let term ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let type ← inferType term
    if type.isAppOf ``ExampleOf then
      -- `Option String × Bool × String`
      let res ← reduce (← mkAppM ``ExampleOf.run #[term])
      let descr := getOptionStr! (res.getArg! 2)
      match recoverTestResult (res.getArg! 3) with
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
        let res := res.map recoverTestResult
        let success? := res.foldl (init := true) fun acc (b, _) => acc && b
        let msg' : String := match descr with
          | none => "\n".intercalate $ res.map fun (_, msg) => msg
          | some d =>
            s!"{d}\n" ++ ("\n".intercalate $ res.map fun (_, msg) => msg)
        if success? then logInfo msg' else throwError msg'
    else throwError "Invalid term to run '#spec' with"

/-
Some macros to support making specifications out of the generic specifications. Use this as

`mkspec fooSpec : foo := alwaysEquals foo 4`

to serve a synonym for

`@[reducible] def fooSpec : SpecOn foo := alwaysEquals foo 4`

Check out `../Tests/test.lean` for more examples.
-/
syntax (name := spec) "mkspec " ident " : " term " := " term : command

macro_rules
  | `(mkspec $id:ident : $f := $t) => `(@[reducible] def $id : SpecOn $f := $t)

/-
Some macros to support building examples. Use this as

`#spec Test <spec_name> with <input_param> => <description>`

Check out `../Tests/test.lean` for examples.
-/
syntax "Test " term " with " term (" => " str)? : term
syntax "Tests " term " with " term (" => " str)? : term

macro_rules
  | `(Test $t with $x $[=> $s]?) => match s with
    | some s => `((.fromDescrParam $s $x : ExampleOf $t))
    | none   => `((.fromParam $x : ExampleOf $t))
  | `(Tests $t with $x $[=> $s]?) => match s with
    | some s => `((.fromDescrParams $s $x : ExamplesOf $t))
    | none   => `((.fromParams $x : ExamplesOf $t))
