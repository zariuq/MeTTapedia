import Mettapedia.Tools.CbvPositiveUnification

/-! Checked projections and refusal controls for the optional unifier evaluator. -/

set_option autoImplicit false

namespace Mettapedia.Tools.CbvPositiveUnification.Controls

open Mettapedia.Logic.LP
open PositiveUnificationEvaluation.Controls

attribute [local cbv_simproc cbv_eval] successfulUnification

section

attribute [local cbv_opaque] unifyTotal

theorem two_link_alias_projection :
    (unifyTotal aliases).map (fun substitution => substitution 0) =
      some (.const "answer") := by cbv

theorem an_unassigned_variable_is_not_invented :
    (unifyTotal aliases).map (fun substitution => substitution 7) =
      some (.var 7) := by cbv

end

theorem a_constant_conflict_is_not_success :
    (unifyTotal (σ := signature) [(.const "first", .const "second")]).isSome = false := by cbv

theorem an_occurs_cycle_is_not_success :
    (unifyTotal (σ := signature)
      [(.var 0, .app 1 fun _ => .var 0)]).isSome = false := by cbv

theorem a_too_small_budget_is_not_a_rejection_certificate :
    (unifyFuel 0 aliases).isSome = false ∧
      (unifyTotal aliases).isSome = true := by cbv

end Mettapedia.Tools.CbvPositiveUnification.Controls
