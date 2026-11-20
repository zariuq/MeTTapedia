import Mettapedia.GSLT.Core.OperationalColimitStageFactorization
import Mettapedia.GSLT.Core.OperationalColimitStageEqualityControls

/-!
# Controls for finite support with a retained original stage

The growing diagram has no initial reduction, but its initial image
reduces later. Factorization returns an actual route out of the original
stage. A single-step witness necessarily uses a positive stage here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits.Controls

open CategoryTheory

theorem later_reduction_has_route_from_zero :
    ∃ future, ∃ route : (0 : ℕ) ⟶ future,
      ∃ after : (growing.obj future).theory.Term,
        (growing.obj future).theory.Step ((growing.map route).mapTerm false) after ∧
          inject growing future after = inject growing 1 true :=
  (reduction_from_stage_iff growing false (inject growing 1 true)).mp initial_image_has_step

theorem later_path_has_route_from_zero :
    ∃ future, ∃ route : (0 : ℕ) ⟶ future,
      ∃ after : (growing.obj future).theory.Term,
        (growing.obj future).theory.MultiStep ((growing.map route).mapTerm false) after ∧
          inject growing future after = inject growing 1 true :=
  (multiStep_from_stage_iff growing false (inject growing 1 true)).mp
    (.step initial_image_has_step (.refl _))

theorem witnessed_step_stage_is_positive {future : ℕ} (route : (0 : ℕ) ⟶ future)
    {after : (growing.obj future).theory.Term}
    (step : (growing.obj future).theory.Step ((growing.map route).mapTerm false) after) :
    0 < future := step.1

theorem no_initial_stage_step_witness :
    ¬ ∃ after : (growing.obj 0).theory.Term,
      (growing.obj 0).theory.Step false after := no_initial_step

#print axioms later_reduction_has_route_from_zero
#print axioms later_path_has_route_from_zero
#print axioms witnessed_step_stage_is_positive
#print axioms no_initial_stage_step_witness

end Mettapedia.GSLT.IndexedOperational.OperationalColimits.Controls
