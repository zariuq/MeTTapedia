import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameFlexPairControls

/-!
# Both repeated-spine models survive a strict named-pair decrease

The two formal projections give different original images but the same
repeated occurrence. Both factor through the actual fresh-helper update
with smaller active work. Recoverable binding still refuses disjoint
dependencies that require the fresh common interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexActiveControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

abbrev base := ContextualFrameFlexPairControls.base
abbrev source := ContextualFrameFlexPairControls.declaration
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def firstMap : Ren base [(), ()] [()] := fun _ position => match position with
  | .zero => .zero
  | .succ .zero => .zero
  | .succ (.succ impossible) => nomatch impossible
def secondMap : Ren base [()] [()] := fun _ position => position
def problem : Problem source := ContextualFrameFlexPairControls.repeated ++ ContextualFrameFlexPairControls.repeated
def update := ContextualNamedFlexPair.apply source false true Bool.false_ne_true rfl firstMap secondMap
  ContextualFrameFlexPairControls.repeated

theorem the_two_source_models_each_have_two_active_image_nodes :
    potential ContextualFrameFlexPairControls.firstSolution (active problem) = 2 ∧
      potential ContextualFrameFlexPairControls.secondSolution (active problem) = 2 := by
  constructor <;> decide +kernel

theorem only_the_selected_equation_is_discharged :
    update.remaining.length = 1 := by
  decide +kernel

theorem both_distinct_models_factor_through_the_actual_update_with_strict_progress :
    letI := update.equality
    (∃ first : Assignment update.declaration source, Models first update.remaining ∧
      (∀ identity, ContextualFrameFlexPairControls.firstSolution identity = instantiate first (update.answer identity)) ∧
      potential first (active update.remaining) <
        potential ContextualFrameFlexPairControls.firstSolution (active problem)) ∧
    (∃ second : Assignment update.declaration source, Models second update.remaining ∧
      (∀ identity, ContextualFrameFlexPairControls.secondSolution identity = instantiate second (update.answer identity)) ∧
      potential second (active update.remaining) <
        potential ContextualFrameFlexPairControls.secondSolution (active problem)) := by
  have firstModel : Models ContextualFrameFlexPairControls.firstSolution problem :=
    (models_append _ _ _).mpr ⟨ContextualFrameFlexPairControls.repeated_arguments_have_a_first_actual_solution,
      ContextualFrameFlexPairControls.repeated_arguments_have_a_first_actual_solution⟩
  have secondModel : Models ContextualFrameFlexPairControls.secondSolution problem :=
    (models_append _ _ _).mpr ⟨ContextualFrameFlexPairControls.repeated_arguments_have_a_different_actual_solution,
      ContextualFrameFlexPairControls.repeated_arguments_have_a_different_actual_solution⟩
  constructor
  · exact ContextualNamedFlexProgress.model_progress (S := base) (source := source) false true Bool.false_ne_true rfl
      firstMap secondMap ContextualFrameFlexPairControls.repeated ContextualFrameFlexPairControls.firstSolution firstModel
  · exact ContextualNamedFlexProgress.model_progress (S := base) (source := source) false true Bool.false_ne_true rfl
      firstMap secondMap ContextualFrameFlexPairControls.repeated ContextualFrameFlexPairControls.secondSolution secondModel

theorem strict_progress_does_not_identify_the_original_images :
    ContextualFrameFlexPairControls.firstSolution false ≠ ContextualFrameFlexPairControls.secondSolution false := by
  intro same
  cases same

theorem a_disjoint_scope_still_needs_the_fresh_interface :
    (ContextualBindingWorklist.tryEquation
      (observe ContextualFrameFlexPairControls.disjointLeft,
        observe ContextualFrameFlexPairControls.disjointRight)).isSome = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexActiveControls
