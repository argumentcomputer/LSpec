import Lean
import LSpec.LSpec

syntax (name := lspecStx) "#lspec " term : command

open Lean Meta Elab Command Term in
/--
Custom elaborator for the `#lspec` command. 
Basically it runs the normal `lspec` function and outputs to the Infoview.
-/
@[commandElab lspecStx] unsafe def elabLSpec : CommandElab := fun stx => do
  let term := stx[1]
  liftTermElabM `lspec do
    let term ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let type ← inferType term
    if type.isAppOf ``LSpec then
      let res ← reduce $ ← mkAppM ``compileLSpecResult #[term]
      let success? : Bool ← evalExpr Bool ``Bool (res.getArg! 2)
      let msg : String ← evalExpr String ``String (res.getArg! 3)
      if success?
        then logInfo msg
        else throwError msg
    else throwError "Invalid term to run '#lspec' with"
