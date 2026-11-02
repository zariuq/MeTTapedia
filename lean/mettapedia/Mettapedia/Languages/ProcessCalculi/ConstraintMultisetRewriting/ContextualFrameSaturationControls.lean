import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSaturation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupportControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklistControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklistControls

/-!
# Saturation over infinite declaration families and general residuals

The executable worklist finishes a modelled problem whose Nat-indexed
declarations include widely separated identities. A repeated application
and a compound application can instead form a nonempty saturated residual,
even with a concrete model. The fresh-helper control finishes its later
ground equation and returns an actual solution of the original problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSaturationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualFrameUpdate

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def pendingCount {V : Type} {source : V → MetaArity base} {problem : Problem source} :
    ContextualFrameWorklist.Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem the_infinite_source_family_finishes_at_widely_separated_names :
    pendingCount (ContextualFrameWorklist.run 4 ContextualActiveSupportControls.declaration
      ContextualActiveSupportControls.problem) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 4 ContextualActiveSupportControls.problem
    ContextualActiveSupportControls.declaration ContextualActiveSupportControls.image
    ContextualActiveSupportControls.the_original_equations_have_an_actual_model]
  decide +kernel

theorem an_infinite_source_family_has_a_saturated_factored_run :
    ∃ (fuel : Nat) (update : Update ContextualActiveSupportControls.problem),
      ContextualFrameWorklist.run fuel ContextualActiveSupportControls.declaration
        ContextualActiveSupportControls.problem = .residual update ∧
        (letI := update.equality
         ContextualFrameWorklist.choose (S := base) (source := update.declaration) update.remaining = none) ∧
        ∃ residual : Assignment update.declaration ContextualActiveSupportControls.declaration,
          Models residual update.remaining ∧
          ∀ identity, ContextualActiveSupportControls.image identity = instantiate residual (update.answer identity) :=
  ContextualFrameSaturation.saturates_preserving_every_solution _ _ _
    ContextualActiveSupportControls.the_original_equations_have_an_actual_model

abbrev generalSource := ContextualBindingWorklist.Controls.declaration
def generalProblem : Problem generalSource :=
  ContextualBindingWorklist.Controls.repeatedProblem ++ ContextualBindingWorklist.Controls.compoundProblem

def generalModel : Assignment generalSource generalSource
  | false => .var .zero
  | true => ContextualBindingWorklist.Controls.constant

theorem the_repeated_and_compound_equations_have_a_model : Models generalModel generalProblem := by
  intro equation member
  simp only [generalProblem, ContextualBindingWorklist.Controls.repeatedProblem,
    ContextualBindingWorklist.Controls.compoundProblem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem the_actual_run_retains_both_general_equations :
    ContextualFrameWorklist.run 1 generalSource generalProblem =
      .residual (ContextualFrameWorklist.identity generalProblem) := by
  have normalized : ContextualRigidSolver.normalize generalProblem = some generalProblem := by
    with_unfolding_all rfl
  have noRefutation : ContextualFrameRefutation.choose generalProblem = none := by
    with_unfolding_all rfl
  have noChoice : ContextualFrameWorklist.choose generalProblem = none := by rfl
  simp only [ContextualFrameWorklist.run, ContextualFrameWorklist.runWithRefuter,
    ContextualFrameWorklist.normalizationUpdate]
  split
  · rename_i computed
    cases normalized.symm.trans computed
  · rename_i remaining computed
    have same : remaining = generalProblem := Option.some.inj (computed.symm.trans normalized)
    subst remaining
    split
    · rename_i impossible computed
      cases noRefutation.symm.trans computed
    · split
      · rfl
      · rename_i update computed
        cases noChoice.symm.trans computed

theorem the_nonempty_general_residual_is_saturated :
    ∃ update : Update generalProblem,
      ContextualFrameWorklist.run 1 generalSource generalProblem = .residual update ∧
        update.remaining.length = 2 ∧
        (letI := update.equality
         ContextualFrameWorklist.choose (S := base) (source := update.declaration) update.remaining = none) ∧
        Models generalModel generalProblem := by
  refine ⟨ContextualFrameWorklist.identity generalProblem,
    the_actual_run_retains_both_general_equations, rfl, ?_, the_repeated_and_compound_equations_have_a_model⟩
  rfl

theorem the_ordinary_fresh_helper_run_finishes_and_saturates :
    ∃ update : Update ContextualFrameWorklist.Controls.constrained,
      ContextualFrameWorklist.run 3 ContextualFrameWorklist.Controls.declaration
        ContextualFrameWorklist.Controls.constrained = .residual update ∧
        update.remaining = [] ∧
        (letI := update.equality
         ContextualFrameWorklist.choose (S := base) (source := update.declaration) update.remaining = none) ∧
        Models update.answer ContextualFrameWorklist.Controls.constrained := by
  obtain ⟨update, computed, empty, solved⟩ :=
    ContextualFrameWorklist.Controls.the_computed_fresh_frame_answer_solves_the_whole_original_queue
  refine ⟨update, computed, empty, ?_, solved⟩
  rw [empty]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSaturationControls
