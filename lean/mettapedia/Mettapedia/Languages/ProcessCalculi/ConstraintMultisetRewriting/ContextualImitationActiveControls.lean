import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitationProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameImitationControls

/-!
# Fresh helpers may increase active names while decreasing model work

A binary imitation replaces one active hole by two field helpers. Its actual
queue has more active names, so the binding phase's name-count bound cannot
be reused for this case. The model-image potential still decreases. A second
case retains a lambda helper's local bound variable without importing the
caller's ambient variable into the closed declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationActiveControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

abbrev base := ContextualFrameImitationControls.base
abbrev source := ContextualFrameImitationControls.declaration
abbrev extended := signature base source
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def emptyRenaming : Ren base [] [()] := fun _ position => nomatch position
def pairFields : Args extended (base.arity (s := ()) .pair) [()] :=
  .cons (ContextualFrameImitationControls.call (.var .zero))
    (.cons ContextualFrameImitationControls.constant .nil)
def pairUpdate := ContextualNamedImitation.apply source false emptyRenaming .pair pairFields []

def pairCandidate : Assignment source source
  | false => ContextualFrameImitationControls.pair ContextualFrameImitationControls.constant
      ContextualFrameImitationControls.constant
  | true => ContextualFrameImitationControls.constant

theorem the_pair_problem_has_an_independent_model :
    Models pairCandidate ContextualFrameImitationControls.problem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem there_are_two_original_active_names : (active ContextualFrameImitationControls.problem).card = 2 := by
  decide +kernel

theorem the_actual_helper_queue_has_three_active_names :
    letI := pairUpdate.equality
    (active pairUpdate.remaining).card = 3 := by
  decide +kernel

theorem counting_names_alone_does_not_decrease_for_imitation :
    letI := pairUpdate.equality
    ¬ (active pairUpdate.remaining).card < (active ContextualFrameImitationControls.problem).card := by
  rw [the_actual_helper_queue_has_three_active_names, there_are_two_original_active_names]
  omega

theorem the_original_pair_model_cost_is_four :
    potential pairCandidate (active ContextualFrameImitationControls.problem) = 4 := by
  decide +kernel

theorem the_actual_named_pair_update_strictly_decreases_model_work :
    letI := pairUpdate.equality
    ∃ remaining : Assignment pairUpdate.declaration source, Models remaining pairUpdate.remaining ∧
      (∀ identity, pairCandidate identity = instantiate remaining (pairUpdate.answer identity)) ∧
      potential remaining (active pairUpdate.remaining) <
        potential pairCandidate (active ContextualFrameImitationControls.problem) := by
  exact ContextualNamedImitationProgress.model_progress (S := base) (source := source) false emptyRenaming .pair pairFields []
    pairCandidate the_pair_problem_has_an_independent_model

def lambdaFields : Args extended (base.arity (s := ()) .lam) [()] :=
  .cons (ContextualFrameImitationControls.pair (.var .zero)
    (ContextualFrameImitationControls.call (.var (.succ .zero)))) .nil
def lambdaUpdate := ContextualNamedImitation.apply source false emptyRenaming .lam lambdaFields []

def lambdaCandidate : Assignment source source
  | false => .op (.inl .lam) (.cons (ContextualFrameImitationControls.pair (.var .zero)
      ContextualFrameImitationControls.constant) .nil)
  | true => ContextualFrameImitationControls.constant

theorem the_binding_field_has_an_independent_capture_free_model :
    Models lambdaCandidate ContextualFrameImitationControls.binderProblem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem the_actual_binding_field_update_strictly_decreases_model_work :
    letI := lambdaUpdate.equality
    ∃ remaining : Assignment lambdaUpdate.declaration source, Models remaining lambdaUpdate.remaining ∧
      (∀ identity, lambdaCandidate identity = instantiate remaining (lambdaUpdate.answer identity)) ∧
      potential remaining (active lambdaUpdate.remaining) <
        potential lambdaCandidate (active ContextualFrameImitationControls.binderProblem) := by
  exact ContextualNamedImitationProgress.model_progress (S := base) (source := source) false emptyRenaming .lam lambdaFields []
    lambdaCandidate the_binding_field_has_an_independent_capture_free_model

theorem direct_recovery_still_refuses_the_unavailable_ambient_argument :
    (ContextualBindingWorklist.tryEquation
      (observe (ContextualFrameImitationControls.hole (Γ := [()])),
        observe ContextualFrameImitationControls.body)).isSome = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationActiveControls
