import Mettapedia.OSLF.Syntax.GSOSNativeHistory
import Mettapedia.OSLF.Syntax.DeterministicGSOSEdgeControls

/-!
# Event histories retain more than an action-tree readout

Two actual prefix executions have the same action word and exact endpoint
but different supplied occurrence origins. The entire coloured unfolding
therefore cannot select between their receipts. A positive path with an
empty origin carrier has no such receipt, although the underlying
operational transition is enabled.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeHistory.Controls

open Mettapedia.OSLF.DeterministicGSOS.Controls EdgeControls

noncomputable def firstHistory :
    History law worlds variableSteps (Fin 2) () world firstEvent.source firstEvent.target :=
  .cons firstEvent (.nil firstEvent.target)

noncomputable def secondHistory :
    History law worlds variableSteps (Fin 2) () world firstEvent.source firstEvent.target :=
  .cons secondEvent (.nil secondEvent.target)

theorem same_action_word : firstHistory.actions = [7] ∧ secondHistory.actions = [7] :=
  ⟨rfl, rfl⟩

theorem histories_differ : firstHistory ≠ secondHistory := by
  intro same
  have origins := congrArg History.origins same
  change [(0 : Fin 2)] = [1] at origins
  exact Fin.zero_ne_one (List.cons.inj origins).1

theorem first_complete_readout :
    (unfolding law worlds variableSteps () world firstEvent.source).read firstHistory.actions =
      some firstEvent.target :=
  history_unfolding_readout firstHistory

theorem second_complete_readout :
    (unfolding law worlds variableSteps () world firstEvent.source).read secondHistory.actions =
      some firstEvent.target :=
  history_unfolding_readout secondHistory

/-- Even the complete unfolding does not reconstruct the supplied occurrence receipt. -/
theorem no_unfolding_origin_recovery :
    ¬ ∃ recover : Mettapedia.CategoryTheory.PartialActionTree Nat (signature.Term naturals ()) →
        History law worlds variableSteps (Fin 2) () world firstEvent.source firstEvent.target,
      recover (unfolding law worlds variableSteps () world firstEvent.source) = firstHistory ∧
        recover (unfolding law worlds variableSteps () world firstEvent.source) = secondHistory := by
  rintro ⟨recover, first, second⟩
  exact histories_differ (first.symm.trans second)

/-- Enabled transitions do not manufacture an element of an empty origin carrier. -/
theorem empty_origin_history_word :
    ∀ {source endpoint : signature.Term naturals ()}
      (history : History law worlds variableSteps Empty () world source endpoint),
      history.actions = []
  | _, _, .nil _ => rfl
  | _, _, .cons event _ => event.origin.elim

theorem no_empty_origin_history :
    ¬ ∃ history : History law worlds variableSteps Empty () world firstEvent.source firstEvent.target,
      history.actions = [7] := by
  rintro ⟨history, word⟩
  have empty := empty_origin_history_word history
  rw [word] at empty
  cases empty

theorem enabled_but_empty_receipt :
    Operational.coalgebra law (variableSteps.app world) PUnit.unit () firstEvent.source 7 =
        some firstEvent.target ∧
      ¬ ∃ history : History law worlds variableSteps Empty () world firstEvent.source firstEvent.target,
        history.actions = [7] :=
  ⟨firstEvent.valid, no_empty_origin_history⟩

end Mettapedia.OSLF.DeterministicGSOS.NativeHistory.Controls
