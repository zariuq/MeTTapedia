import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationAdequacy

/-!
# Name reflection and process Drop remain different declarations

The source quotient satisfies quote-after-drop at the name sort. Process
drop-after-quote is an admitted operational source event only in the extended
profile. These statements hold at every ambient context, and their occurrence
realizations use the same contextual source compiler.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationReflection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres RhoScopedParallelEvents
open ContextualCommunicationProfiles ContextualCommunicationAdequacy
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

theorem root_has_declared_source_step {admitted : SourceRule → Prop} {context : Ctx sig}
    (root : ContextualCommunicationProfiles.Root admitted context) :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := admitted) root.source root.target := by
  simpa only [RhoScopedParallelEvents.Step, join_zero_right] using factorization_occurrence root (zero context)

def reflectionRoot {context : Ctx sig} (process : Term sig context Srt.pr) :
    ContextualCommunicationProfiles.Root withReflection context :=
  ⟨⟨.reflection, trivial⟩,
    { body := ContextualAssignment.ofClosed contDiscard context
      close := fun _ position => match position with | .zero => process }⟩

theorem reflectionRoot_source {context : Ctx sig} (process : Term sig context Srt.pr) :
    (reflectionRoot process).source = drop (quote (RhoEquationConstructorControls.project process)) := rfl

theorem reflectionRoot_target {context : Ctx sig} (process : Term sig context Srt.pr) :
    (reflectionRoot process).target = RhoEquationConstructorControls.project process := rfl

theorem process_drop_source_step {context : Ctx sig} (process : Process context) :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
      (drop (quote process)) process := by
  induction process using Quotient.inductionOn with
  | _ process => exact root_has_declared_source_step (reflectionRoot process)

theorem process_drop_has_occurrence_execution {context : Ctx sig} (process : Process context) :
    ∃ before after : Configuration (Process context) (Occurrence context),
      before.equations = [] ∧ labels ContextualCommunicationProfiles.label before.present =
        normalized (drop (quote process)) ∧
      InterpretedStep withReflection (ContextualCommunicationProfiles.action context).identity before after ∧
      labels ContextualCommunicationProfiles.label after.present = normalized process :=
  every_source_step_has_occurrence_execution _ _ (process_drop_source_step process)

theorem name_quote_drop_is_equation {context : Ctx sig} (name : Name context) :
    quote (drop name) = name := quote_drop name

theorem count_join {context : Ctx sig} (first second : Process context) :
    RhoSourceOutputPredicate.count (join first second) =
      RhoSourceOutputPredicate.count first + RhoSourceOutputPredicate.count second := by
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
          change outputCount (RhoEquationConstructorControls.parallel first second) =
            outputCount first + outputCount second
          simp [RhoEquationConstructorControls.parallel, outputCount, outputCountArgs, outputHeadCount]

theorem core_root_has_output {context : Ctx sig}
    (root : ContextualCommunicationProfiles.Root core context) :
    0 < RhoSourceOutputPredicate.count root.source := by
  rcases root with ⟨⟨selected, permitted⟩, firing⟩
  cases selected with
  | communication => exact RhoScopedEquationEventControls.root_source_has_output firing
  | reflection => exact False.elim permitted

theorem core_event_has_output {context : Ctx sig} {source target : Process context}
    (event : RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core) source target) :
    0 < RhoSourceOutputPredicate.count source := by
  obtain ⟨root, surrounding, sourceShape, _targetShape⟩ :=
    (step_iff_root_surrounding source target).mp event
  rw [sourceShape, count_join]
  exact (core_root_has_output root).trans_le (Nat.le_add_right _ _)

theorem dropped_null_has_no_core_event {context : Ctx sig} (target : Process context) :
    ¬ RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core)
      (drop (quote (zero context))) target := by
  intro event
  have positive := core_event_has_output event
  change 0 < (0 : Nat) at positive
  omega

theorem dropped_null_has_no_core_occurrence_execution {context : Ctx sig}
    (before after : Configuration (Process context) (Occurrence context))
    (sourceRead : labels ContextualCommunicationProfiles.label before.present =
      normalized (drop (quote (zero context)))) :
    ¬ InterpretedStep core (ContextualCommunicationProfiles.action context).identity before after := by
  intro executed
  have event := executed.no_invention
  rw [observe_identity_of_normalized before.present _ sourceRead] at event
  exact dropped_null_has_no_core_event _ event

theorem operational_drop_need_not_be_conversion :
    ∃ process : Process [], drop (quote process) ≠ process ∧
      RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
        (drop (quote process)) process :=
  ⟨visible, suspended_not_visible, process_drop_source_step visible⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationReflection
