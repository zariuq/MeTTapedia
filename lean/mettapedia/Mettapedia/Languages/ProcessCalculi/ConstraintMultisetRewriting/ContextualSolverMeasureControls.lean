import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidWeightControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfActiveControls

/-!
# The three-coordinate order applies to actual normalization and pruning

Decomposition leaves the first two coordinates fixed and lowers tree weight.
The explicit binder model of same-hole pruning leaves image size fixed and
lowers parameter cost. A larger primary coordinate cannot be compensated by
smaller later coordinates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasureControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverMeasure

abbrev base := ContextualRigidWeightControls.base
abbrev source := ContextualRigidWeightControls.source
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def candidate : Assignment source source
  | false => ContextualBindingWorklist.Controls.constant
  | true => ContextualBindingWorklist.Controls.constant

theorem the_actual_source_measure_is_two_two_ten :
    measure (S := base) candidate ContextualRigidWeightControls.problem = (2, 2, 10) := by
  decide +kernel

theorem the_actual_normalized_measure_is_two_two_eight :
    (ContextualRigidSolver.normalize ContextualRigidWeightControls.problem).map
      (measure (S := base) candidate) = some (2, 2, 8) := by
  decide +kernel

theorem actual_same_hole_pruning_makes_lexicographic_progress :
    letI := ContextualSelfActiveControls.update.equality
    Smaller
      (measure (S := ScopePullback.Controls.base) (source := ContextualSelfActiveControls.update.declaration)
        (next := ContextualSelfPair.Controls.others) ContextualSelfActiveControls.residual
        ContextualSelfActiveControls.update.remaining)
      (measure (S := ScopePullback.Controls.base) (source := ContextualSelfPair.Controls.old)
        (next := ContextualSelfPair.Controls.others) ContextualSelfPair.Controls.locallyBound
        ContextualSelfActiveControls.equations) := by
  apply of_interface_lt
  · dsimp only [ContextualSolverMeasure.measure]
    rw [ContextualSelfActiveControls.the_actual_residual_still_has_five_active_image_nodes,
      ContextualSelfActiveControls.the_source_model_has_five_active_image_nodes]
  · dsimp only [ContextualSolverMeasure.measure]
    rw [ContextualSelfActiveControls.the_actual_pruned_interfaces_cost_two,
      ContextualSelfActiveControls.the_original_active_interfaces_cost_four]
    decide

theorem a_primary_decrease_allows_larger_later_coordinates : Smaller (1, 1000003, 987654321) (2, 0, 0) := by
  apply of_image_lt
  decide

theorem shrinking_later_coordinates_cannot_hide_a_larger_image : ¬ Smaller (3, 0, 0) (2, 1000003, 987654321) := by
  simp only [Smaller, Prod.lex_iff]
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasureControls
