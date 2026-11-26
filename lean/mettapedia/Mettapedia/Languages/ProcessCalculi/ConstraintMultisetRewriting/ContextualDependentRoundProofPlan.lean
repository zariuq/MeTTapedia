import Lean
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklist

/-! A proof plan for preserving an already decided solver round. The
scrutinee comes from the type of the supplied non-stuck witness. -/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklist

open Lean Meta Elab Tactic

elab "keep_round_result " witness:term : tactic => withMainContext do
  let accepted ← elabTerm witness none
  let some (_, result, rejected) ← matchNe? (← inferType accepted) |
    throwErrorAt witness "expected a proof that a round is not stuck"
  unless rejected.getAppFn.isConstOf ``Round.stuck do
    throwErrorAt witness "expected a proof that a round is not stuck"
  let resultName ← mkFreshUserName `roundResult
  let equalityName ← mkFreshUserName `roundEquality
  let goal ← getMainGoal
  let (_, generalized) ← goal.generalize
    #[{ expr := result, xName? := some resultName, hName? := some equalityName }]
  replaceMainGoal [generalized]
  let resultIdent := mkIdent resultName
  let equalityIdent := mkIdent equalityName
  evalTactic (← `(tactic|
    cases $resultIdent:ident with
    | stuck => exact False.elim ($witness $equalityIdent:ident)
    | progress update decreases => rfl
    | refuted absent => rfl))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklist
