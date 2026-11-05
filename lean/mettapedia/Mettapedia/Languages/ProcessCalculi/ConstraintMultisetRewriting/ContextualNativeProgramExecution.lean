import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramGuards

/-!
# Selected-body admission is exactly one constructed native firing

The compiler constructs the rule, physical selection, output syntax,
publication flags and resource/guard queries from the authored schedule.
The comparison assumes neither successful source admission nor source
shape/resource validity. Those obligations are checked by the compiled
queries. The native firing includes an actual worklist return at the
declared finite budget.

This is admission equivalence for the current ordinary/shared production
grammar and the constructed entry/control context. Result observations,
selectively captured templates and arbitrary program contexts have their
separate obligations; the control occurrence is explicit program data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualPredicateQueryAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

noncomputable def producerQueries (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :=
  schedule.producerResourceQueries ++ schedule.producerGuardQueries occupied

theorem source_iff_native_body_admission (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    schedule.Admitted ↔
      ∃ observed : WithQueries schedule.guardNativeBank (schedule.nativeBindingState occupied),
        observed.firing.rule = schedule.producerRule ∧ observed.firing.selection = schedule.bindingSelection ∧
          observed.firing.outputs = schedule.producerOutputs occupied ∧ observed.firing.reusable = schedule.producerReusable ∧
          observed.firing.fuel = fuel ∧ observed.queries = schedule.producerQueries occupied := by
  constructor
  · intro source
    obtain ⟨shapes, resources, consistent, guards⟩ := schedule.admitted_characterization.mp source
    obtain ⟨firing, rule, selection, outputs, reusable, budget⟩ :=
      schedule.realize_native_producer shapes resources consistent occupied fuel
    have nativeConsistent :=
      (schedule.native_binding_solvable_iff shapes resources occupied schedule.producerValues []).mpr consistent
    have structural := (schedule.producer_resource_queries_iff occupied nativeConsistent).mpr ⟨shapes, resources⟩
    have checked := (schedule.producer_guard_queries_iff shapes resources consistent occupied).mp guards
    have observations : ∀ query ∈ schedule.producerQueries occupied,
        AskData (ContextualConditionalExecution.information schedule.guardNativeBank schedule.guardFamily occupied
          firing.selection firing.rule (schedule.nativeBindingState occupied).rows (schedule.nativeBindingState occupied).equations)
          query (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present := by
      intro query member
      rw [rule, selection]
      rcases List.mem_append.mp member with resource | guard
      · exact structural query resource
      · exact checked query guard
    let observed : WithQueries schedule.guardNativeBank (schedule.nativeBindingState occupied) :=
      ⟨firing, schedule.producerQueries occupied, observations⟩
    exact ⟨observed, rule, selection, outputs, reusable, budget, rfl⟩
  · rintro ⟨observed, rule, selection, _outputs, _reusable, _budget, queries⟩
    have nativeConsistent : ContextualConditionalExecution.Solvable
        (schedule.nativeBindingInformation occupied schedule.producerValues []) := by
      have original := observed.firing.admitted.solvable
      rw [rule, selection] at original
      exact original
    have observations : ∀ query ∈ schedule.producerQueries occupied,
        AskData (schedule.nativeBindingInformation occupied schedule.producerValues []) query
          (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied))
          (schedule.nativeBindingState occupied).present := by
      intro query member
      have original := observed.observations query (by rw [queries]; exact member)
      rw [rule, selection] at original
      exact original
    have structural := (schedule.producer_resource_queries_iff occupied nativeConsistent).mp
      (fun query member => observations query (List.mem_append_left _ member))
    obtain ⟨shapes, resources⟩ := structural
    have consistent :=
      (schedule.native_binding_solvable_iff shapes resources occupied schedule.producerValues []).mp nativeConsistent
    have guards := (schedule.producer_guard_queries_iff shapes resources consistent occupied).mpr
      (fun query member => observations query (List.mem_append_right _ member))
    exact schedule.admitted_characterization.mpr ⟨shapes, resources, consistent, guards⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
