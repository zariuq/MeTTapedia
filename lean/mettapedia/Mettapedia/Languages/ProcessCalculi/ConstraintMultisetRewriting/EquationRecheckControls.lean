import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationRecheck
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeupControls

/-!
# Actual tell-only wake detection and the equal-length branch boundary
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationRecheckControls

open EquationWakeupControls

theorem tell_only_wake_is_detected : EquationRecheck.changed before after = true :=
  EquationRecheck.detects_selected_readiness A label tell_step pendingSelection
    pending_cannot_fire_before pending_can_fire_after

theorem equal_length_branch_is_not_a_store_identity :
    EquationRecheck.changed zeroBranch oneBranch = false ∧
      ¬ A.Equivalent zeroBranch.equations oneBranch.equations :=
  ⟨by decide, equal_counts_do_not_identify_branches.2.2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationRecheckControls
