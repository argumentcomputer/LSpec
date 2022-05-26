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

-- Syntax to help build examples
syntax "Test " term " with " term (" => " str)? : term
syntax "Tests " term " with " term (" => " str)? : term

macro_rules
  | `(Test $t with $x) => `((.fromParam $x : ExampleOf $t))
  | `(Test $t with $x => $s) => `((.fromDescrParam $s $x : ExampleOf $t))
  | `(Tests $t with $x) => `((.fromParams $x : ExamplesOf $t))
  | `(Tests $t with $x => $s) => `((.fromDescrParams $s $x : ExamplesOf $t))

-- Syntax to help build specs
syntax (name := spec) "mkspec " ident " : " term " := " term : command

open Syntax Elab Command in
@[commandElab spec]
def elabSpec : CommandElab
  | `(mkspec $id:ident : $f := $t) => do 
      elabCommand <|
      ← `(@[reducible] def $id : SpecOn $f := $t)
  | _ => throwUnsupportedSyntax