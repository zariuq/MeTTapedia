import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls

/-!
# A bounded joint solve cannot repair a refused original guard

The negative body has consistent terminal equations and valid resources,
but its earlier nonbinding guard has a countermodel. Every actual bounded
return retains that failure. The positive body computes a key through
stored code and checks the returned answer before its second publication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSourceSchedules

namespace EarlierGuard

open ContextualPrefixPublicationControls (DataOperator base none initial firstLocals)
open ContextualScheduleControls.EarlierSchema

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)
local instance : DecidableEq (ContextualAnswerFamilies.Names guardedBody.native.guardVariables) := ContextualNativeBodies.Body.guardEquality guardedBody.native

def firstCut : guardedBody.native.CutIndex := ⟨0, by decide +kernel⟩

theorem terminal_consistent : ContextualConditionalExecution.Solvable guardedResult.equations := by
  rw [guardedBody.final_equations]
  exact the_guard_refusal_is_not_a_terminal_conflict.2

theorem the_first_guard_is_false : ¬ (guardedBody.cuts.get firstCut).Holds := by
  intro firstHeld
  apply a_later_binding_does_not_repair_the_compiled_earlier_check
  refine ⟨?_, the_guard_refusal_is_not_a_terminal_conflict.1,
    the_guard_refusal_is_not_a_terminal_conflict.2, ?_⟩
  · with_unfolding_all exact compiled_accepts.1
  · intro cut member
    change cut ∈ [_, _] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · with_unfolding_all exact firstHeld
    · intro check member
      cases member

theorem the_joint_problem_is_consistent_despite_the_refusal :
    ContextualConditionalExecution.Solvable guardedBody.native.guardProblem :=
  guardedBody.native.guard_problem_solvable_iff.mpr terminal_consistent

theorem every_bounded_return_keeps_the_earlier_failure (fuel : Nat) :
    ∃ update : ContextualFrameUpdate.Update guardedBody.native.guardProblem,
      ContextualFrameWorklist.run fuel guardedBody.native.guardFamily guardedBody.native.guardProblem = .residual update ∧
        ¬ (guardedBody.native.reducedGuardView update firstCut).Holds := by
  obtain ⟨update, computed, same⟩ := guardedBody.native.actual_guard_update terminal_consistent fuel
  exact ⟨update, computed, fun accepted => the_first_guard_is_false ((same firstCut).mp accepted)⟩

end EarlierGuard

namespace ComputedJoin

open ContextualClausePublication.BinderControls (DataOperator dataSignature base)
open ContextualScheduleControls.ComputedBody (body admitted)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) sort)
  infer_instance
local instance : DecidableEq (ContextualAnswerFamilies.Names body.native.guardVariables) := ContextualNativeBodies.Body.guardEquality body.native

theorem every_bounded_return_preserves_the_computed_guard (fuel : Nat) :
    ∃ update : ContextualFrameUpdate.Update body.native.guardProblem,
      ContextualFrameWorklist.run fuel body.native.guardFamily body.native.guardProblem = .residual update ∧
        ∀ index : body.native.CutIndex, (body.native.reducedGuardView update index).Holds := by
  obtain ⟨update, computed, same⟩ := body.native.actual_guard_update (body.admitted_final_solvable admitted) fuel
  refine ⟨update, computed, ?_⟩
  intro index
  exact (same index).mpr ((body.compile_exact.mpr admitted).2.2.2 _ (List.get_mem _ _))

end ComputedJoin

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleControls
