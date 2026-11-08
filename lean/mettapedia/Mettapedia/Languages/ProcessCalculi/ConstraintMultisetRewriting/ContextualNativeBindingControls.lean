import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls

/-!
# Native binding preserves a computed answer and rejects incompatible reuse

The source body opens a stored lambda, computes a key, takes a permit and
reuses its answer twice. Its native binding models retain answer 7. A
demand for 9 has no model. An unused inconsistent schema does not poison
the binding problem.

The last control separates binding consistency from guard admission: a
body with a false earlier guard still has a binding model. Its guard must
therefore be checked at its own cut before publication is admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualSourceSchedules
open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries origin symbol located)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace Computed

open ContextualScheduleControls.ComputedBody (body result admitted conflictingBody conflictingResult)

def sourceValue : Term (signature base result.declarations) [] () :=
  queryView captures ContextualClauseSequencingControls.rowLocals origin
    (located 10 ContextualClauseSequencingControls.retainedAnswer)

def produced : List (Term (signature base (queryFamily body.native.bindingLocals body.native.guardFamily)) [] ()) :=
  [located 9 (symbol 7),
    instantiate (ContextualSelectionViews.capturedSource body.native.bindingLocals body.native.guardFamily)
      (instantiate body.native.bindingCurrent sourceValue)]

theorem the_computed_body_has_a_native_binding_model (occupied : Finset Nat) :
    ContextualConditionalExecution.Solvable (body.native.nativeBindingInformation occupied produced []) := by
  have parts := body.admitted_characterization.mp admitted
  exact (body.native.native_binding_solvable_iff parts.1 parts.2.1 occupied produced []).mpr parts.2.2.1

theorem every_native_binding_model_retains_seven {Future : Type} (future : Future → MetaArity base)
    (occupied : Finset Nat)
    (candidate : Assignment (ContextualClauseFrames.nativeActive body.native.bindingLocals body.native.bindingLocals body.native.guardFamily) future)
    (model : ContextualResidual.Models candidate (body.native.nativeBindingInformation occupied produced [])) :
    instantiate candidate
      (instantiate (ContextualSelectionViews.capturedTarget
        (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals) body.native.guardFamily)
        (instantiate body.native.bindingCurrent sourceValue)) = located 10 (symbol 7) := by
  have source := body.native.binding_current_model _ (body.native.native_binding_model_reflects occupied produced [] candidate model)
  erw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
  exact ContextualClauseSequencingControls.source_next_preserves_the_returned_answer future _ source

private theorem conflicting_information_has_no_model :
    ¬ ContextualConditionalExecution.Solvable conflictingResult.equations := by
  intro consistent
  have good := ContextualClauseSequencingControls.source_next_admitted
  apply ContextualClauseSequencingControls.a_conflicting_second_read_cannot_fire
  refine ⟨good.take_distinct, good.output_distinct, rfl, rfl, rfl,
    good.taken_present, good.read_present, good.apart, good.fresh, consistent, ?_⟩
  intro check member
  cases member

theorem incompatible_reuse_has_no_native_binding_model (occupied : Finset Nat) :
    ¬ ContextualConditionalExecution.Solvable (conflictingBody.native.nativeBindingInformation occupied [] []) := by
  have good := body.admitted_characterization.mp admitted
  exact fun consistent => conflicting_information_has_no_model
    ((conflictingBody.native.native_binding_solvable_iff good.1 good.2.1 occupied [] []).mp consistent)

end Computed

namespace Dormant

open ContextualComputedJoinControls (world plan picked store)
open ContextualClauseSequencingControls (rowLocals nextPlan selection)

local instance : DecidableEq world.Names := world.equality

def impossibleRow : Row locals captures [] () :=
  ⟨.schema (ContextualStoredRows.asTemplate locals captures (store 2).value),
    [(observe (symbol (Γ := []) 1), observe (symbol (Γ := []) 2))]⟩

def entry : ContextualClauseSourceState.World locals Nat [] () :=
  { world with rows := fun occurrence => if occurrence = 2 then impossibleRow else store occurrence }

local instance : DecidableEq entry.Names := entry.equality

abbrev middle := ContextualClauseSourceState.target queries locals entry plan picked
local instance : DecidableEq middle.Names := middle.equality
abbrev result := ContextualClauseSourceState.target captures rowLocals middle nextPlan selection

def body : Schedule base Nat [] () entry result :=
  .snoc (.snoc (.nil entry) queries plan picked) captures nextPlan selection

theorem unused_schema_has_no_instance {Future : Type} (future : Future → MetaArity base)
    (candidate : Assignment captures future) (pattern : Term (signature base future) [] ()) :
    ¬ Matches locals captures candidate pattern (entry.rows 2) := by
  change ¬ Matches locals captures candidate pattern impossibleRow
  rintro ⟨extension, images, conditions, _value⟩
  have clash := conditions (observe (symbol (Γ := []) 1), observe (symbol (Γ := []) 2)) (List.mem_singleton_self _)
  change observe (symbol (decl := extension.declarations) (Γ := []) 1) =
    observe (symbol (Γ := []) 2) at clash
  have values := observe_injective clash
  have impossible : (1 : Nat) = 2 := DataOperator.symbol.inj
    (Sum.inl.inj (Sum.inl.inj (Term.op.inj values).1))
  omega

set_option maxHeartbeats 800000 in
theorem selected_information_ignores_the_unused_condition :
    result.equations = ContextualScheduleControls.ComputedBody.result.equations := by
  with_unfolding_all rfl

theorem the_native_binding_is_still_consistent (occupied : Finset Nat) :
    ContextualConditionalExecution.Solvable (body.native.nativeBindingInformation occupied [] []) := by
  have good := ContextualScheduleControls.ComputedBody.body.admitted_characterization.mp
    ContextualScheduleControls.ComputedBody.admitted
  apply (body.native.native_binding_solvable_iff good.1 good.2.1 occupied [] []).mpr
  rw [selected_information_ignores_the_unused_condition]
  exact good.2.2.1

end Dormant

namespace EarlierGuard

open ContextualPrefixPublicationControls (initial)
open ContextualScheduleControls.EarlierSchema (body admitted guardedBody)

/-- Binding compilation cannot discharge an earlier guard merely because
later equations make the final joint problem consistent. -/
theorem a_binding_model_is_not_guard_admission (occupied : Finset Nat) :
    ContextualConditionalExecution.Solvable (guardedBody.native.nativeBindingInformation occupied [] []) ∧
      ¬ guardedBody.Admitted := by
  have good := body.admitted_characterization.mp admitted
  have final : ContextualConditionalExecution.Solvable ContextualScheduleControls.EarlierSchema.guardedResult.equations := by
    have consistent := ContextualScheduleControls.EarlierSchema.the_guard_refusal_is_not_a_terminal_conflict.2
    change ContextualConditionalExecution.Solvable
      (ContextualResidual.mapProblem guardedBody.frame.assignment initial.equations ++ guardedBody.deltas) at consistent
    rw [← guardedBody.final_equations] at consistent
    exact consistent
  refine ⟨(guardedBody.native.native_binding_solvable_iff good.1 good.2.1 occupied [] []).mpr final, ?_⟩
  intro accepted
  exact ContextualScheduleControls.EarlierSchema.a_later_binding_does_not_repair_the_compiled_earlier_check
    (guardedBody.compile_exact.mpr accepted)

end EarlierGuard

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingControls
