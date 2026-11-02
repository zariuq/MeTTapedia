import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationRepeatedControls

/-!
# Progress controls for binding fields and repeated occurrence arguments

The lambda's field contains its own bound variable. Its one-node residual
replaces a two-node source image. Repeating an occurrence argument still
permits two different contextual images; both exhibit the same strict
imitation progress. A forward assignment alone does not decrease syntactic
size: its fresh helper application has its own node.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationProgress.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualBinding.Controls (base)

namespace Lambda

open ContextualImitation.Controls

theorem the_closed_lambda_has_two_nodes : termSize (combined original) = 2 := by
  rw [synthesis_returns_the_closed_identity_lambda]
  rfl

theorem its_open_field_has_one_node : termSize (second helper) = 1 := by
  with_unfolding_all rfl

theorem actual_lambda_imitation_strictly_decreases_the_model :
    ∃ remaining : Assignment target target,
      ContextualResidual.Models remaining (ContextualResidual.mapProblem first problem) ∧
      (∀ identity, combined identity = instantiate remaining (first identity)) ∧
      targetPotential [] ContextualFrame.Controls.Operator.lam others remaining ∅ <
        sourcePotential [] () others combined ∅ := by
  exact model_progress [] ContextualFrame.Controls.Operator.lam others
    (fun _ position => nomatch position) (.cons (.var .zero) .nil) problem
    (by with_unfolding_all exact List.mem_singleton_self _)
    combined the_synthesized_answer_solves_the_original_problem ∅

theorem the_fresh_answer_is_not_itself_a_syntactic_size_decrease :
    termSize (first original) = termSize (generator source original) + 2 := by
  with_unfolding_all rfl

end Lambda

namespace Repeated

open ContextualImitation.RepeatedControls
open ContextualImitation.Controls (others original)

theorem the_first_image_removes_exactly_one_constructor_node :
    targetPotential [(), ()] ContextualFrame.Controls.Operator.pair others projectFirst ∅ + 1 =
      sourcePotential [(), ()] () others (Assignment.compose projectFirst first) ∅ := by
  with_unfolding_all decide

theorem the_second_image_removes_exactly_one_constructor_node :
    targetPotential [(), ()] ContextualFrame.Controls.Operator.pair others projectSecond ∅ + 1 =
      sourcePotential [(), ()] () others (Assignment.compose projectSecond first) ∅ := by
  with_unfolding_all decide

theorem progress_does_not_identify_the_two_contextual_answers :
    Assignment.compose projectFirst first original ≠ Assignment.compose projectSecond first original :=
  the_original_images_are_distinct

end Repeated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationProgress.Controls
