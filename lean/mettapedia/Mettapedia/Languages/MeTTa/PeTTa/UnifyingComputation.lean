import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec
import Lean.Elab.Tactic
import Lean.Meta.Reduce

/-!
# Kernel-checked finite computations of the unifying source machine

Normalize one configuration and one transition at a time, then compose the
existing `run_succ_of_step` equations. This avoids repeatedly reducing an
entire stateful prefix when checking closed controls. The metaprogram only
proposes reflexivity and equality-composition terms; the kernel checks them.
It adds no evaluator, native decision axiom or completion assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingComputation

open Lean Meta Elab Tactic
open Unifying

elab "unifying_run" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_,left,_) := target.eq? | throwError "expected an equality observation"
  let observer := left.getAppFn
  unless observer.isConstOf ``observed || observer.isConstOf ``shown do
    throwError "expected observed or shown around a source run"
  let arguments := left.getAppArgs
  unless arguments.size == 1 do throwError "expected one source run"
  let computation := arguments[0]!
  unless computation.isAppOfArity ``Unifying.run 3 do throwError "unfold the source-run wrapper first"
  let inputs := computation.getAppArgs
  let registry := inputs[0]!
  let some fuel := (← whnf inputs[1]!).rawNatLit? | throwError "expected a concrete scheduler allowance"
  let mut remaining := fuel
  let mut current ← withTransparency .all <| reduce inputs[2]!
  let mut agreement ← mkEqRefl (mkApp3 (mkConst ``Unifying.run) registry (mkNatLit fuel) current)
  let mut terminal := false
  while !terminal do
    let stopped ← withTransparency .all <|
      reduce (mkApp3 (mkConst ``Unifying.run) registry (mkNatLit 0) current)
    if remaining == 0 || !(stopped.isAppOf ``Outcome.exhausted) then
      terminal := true
    else
      let advanced ← withTransparency .all <| reduce (mkApp2 (mkConst ``step) registry current)
      if advanced.isAppOf ``Option.some then
        let next := advanced.getAppArgs.back!
        let reflexive ← mkEqRefl advanced
        let equation ← withTransparency .all <| mkAppM ``run_succ_of_step
          #[registry,mkNatLit (remaining - 1),current,next,reflexive]
        agreement ← mkEqTrans agreement equation
        current := next
        remaining := remaining - 1
      else
        terminal := true
  let final ← withTransparency .all <|
    reduce (mkApp3 (mkConst ``Unifying.run) registry (mkNatLit remaining) current)
  agreement ← mkEqTrans agreement (← mkEqRefl final)
  let proof ← mkCongrArg observer agreement
  unless ← withTransparency .all <| isDefEq (← inferType proof) target do
    throwError "the checked source computation does not match the requested observation"
  goal.assign proof
  replaceMainGoal []

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingComputation
