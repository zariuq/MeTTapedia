import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformationQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveControls

/-! # Actual shared-query refutation supplies information; a new joined witness invalidates it -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformationQueryControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveControls
open ContextualInformationQueries

local instance : DecidableEq ContextualSelectionViews.Controls.base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : ContextualSelectionViews.Controls.base.Srt) :
    DecidableEq (ContextualSelectionViews.Controls.base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

theorem the_actual_refuter_constructs_the_joined_information :
    Admitted queries locals [] rows world [] [patterns] := by
  apply of_certified_refutations queries locals 2 [] rows world [] [patterns]
  · exact ⟨ContextualFrameUnifier.solvable_of_consistent ⟨generator captures, SubstitutionAction.models_nil _ _⟩, by simp⟩
  · intro chosen member
    obtain rfl := List.mem_singleton.mp member
    exact the_shared_variable_conjunction_is_certifiably_absent

theorem the_information_profile_retains_the_shared_query :
    ContextualConjunctiveAbsence.Ask queries locals captures [] patterns rows world :=
  the_actual_refuter_constructs_the_joined_information.absent patterns (List.mem_singleton_self _)

theorem the_added_joint_witness_refuses_the_same_information :
    ¬ Admitted queries locals [] rows enlarged [] [patterns] := by
  intro admitted
  exact adding_that_row_invalidates_the_guard
    (admitted.absent patterns (List.mem_singleton_self _))

theorem stopping_the_query_solver_is_not_a_joined_certificate :
    ContextualConjunctiveAbsence.certifies queries locals captures 0 [] patterns rows world = false :=
  zero_fuel_does_not_refute_any_of_the_nonempty_candidate_set

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformationQueryControls
