import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationPlugging
import Mettapedia.OSLF.Syntax.RhoContextScopeComparison

/-!
# Intrinsic communication, quotation and declared reaction-context controls

The positive cases retain an actual ambient process variable, substitute it
later, and bind a received name below quotation. The negative cases separate
source name equality from process reduction, reject unequal channel classes,
and retain the source's explicit boundary on reaction contexts.
The intrinsic quotation-crossing example is explicitly separated from the
canonical rho carrier, whose quotations seal their bodies.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationProfileControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoIntrinsicReadback RhoScopedInstanceReadout RhoScopedParallelEvents RhoCanonicalNamePairs
open ContextualCommunicationProfiles ContextualCommunicationAdequacy
open ContextualCommunicationReflection ContextualCommunicationPlugging
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

def ambientBody : Term sig [Srt.nm, Srt.pr] Srt.pr := .var (.succ .zero)
def ambientChannel : Term sig [Srt.pr] Srt.nm := weaken chan
def ambientPayload : Term sig [Srt.pr] Srt.pr := weaken nilP
def ambientRoot : ContextualCommunicationProfiles.Root core [Srt.pr] :=
  communicationRoot ambientChannel ambientPayload ambientBody

theorem ambient_target_is_the_callers_process :
    ambientRoot.target = project (.var .zero : Term sig [Srt.pr] Srt.pr) := by
  rw [show ambientRoot = communicationRoot ambientChannel ambientPayload ambientBody from rfl,
    communication_target_is_capture_avoiding]
  rfl

theorem ambient_communication_uses_two_physical_inputs :
    (instanceRule ambientRoot).take.length = 2 :=
  communication_takes_two_occurrences ambientChannel ambientPayload ambientBody

theorem open_communication_has_actual_occurrence_execution :
    ∃ before after : Configuration (Process [Srt.pr])
        (ContextualCommunicationProfiles.Occurrence [Srt.pr]),
      before.equations = [] ∧ labels ContextualCommunicationProfiles.label before.present =
        normalized ambientRoot.source ∧
      InterpretedStep core (ContextualCommunicationProfiles.action [Srt.pr]).identity before after ∧
      labels ContextualCommunicationProfiles.label after.present =
        normalized (project (.var .zero : Term sig [Srt.pr] Srt.pr)) := by
  have event := root_has_declared_source_step ambientRoot
  rw [ambient_target_is_the_callers_process] at event
  exact every_source_step_has_occurrence_execution _ _ event

theorem later_supplied_process_is_the_actual_result (process : Term sig [] Srt.pr) :
    bindQ (extend process) ambientRoot.target = project process := by
  rw [ambient_target_is_the_callers_process]
  rfl

theorem later_plugging_has_actual_occurrence_execution (process : Term sig [] Srt.pr) :
    ∃ before after : Configuration (Process []) (ContextualCommunicationProfiles.Occurrence []),
      before.equations = [] ∧ labels ContextualCommunicationProfiles.label before.present =
        normalized (bindQ (extend process) ambientRoot.source) ∧
      InterpretedStep core (ContextualCommunicationProfiles.action []).identity before after ∧
      labels ContextualCommunicationProfiles.label after.present = normalized (project process) := by
  have result := substitution_plugging (extend process) ambientRoot.source ambientRoot.target
    (root_has_declared_source_step ambientRoot)
  rw [later_supplied_process_is_the_actual_result] at result
  exact result

def quotedBody : Term sig [Srt.nm] Srt.pr :=
  dropRaw (quoteRaw (outputRaw (.var .zero) null))

theorem received_name_is_substituted_below_quotation :
    (communicationRoot chan nilP quotedBody).target =
      project (dropRaw (quoteRaw (outputRaw chan null))) := by
  rw [communication_target_is_capture_avoiding]
  rfl

theorem quoted_continuation_has_actual_occurrence_execution :
    ∃ before after : Configuration (Process []) (ContextualCommunicationProfiles.Occurrence []),
      before.equations = [] ∧ labels ContextualCommunicationProfiles.label before.present =
        normalized (communicationRoot chan nilP quotedBody).source ∧
      InterpretedStep core (ContextualCommunicationProfiles.action []).identity before after ∧
      labels ContextualCommunicationProfiles.label after.present =
        normalized (project (dropRaw (quoteRaw (outputRaw chan null)))) := by
  have event := root_has_declared_source_step (communicationRoot chan nilP quotedBody)
  rw [received_name_is_substituted_below_quotation] at event
  exact every_source_step_has_occurrence_execution _ _ event

def quietName : Name [] := quote (zero [])
def loudName : Name [] := quote visible

theorem unequal_channel_classes : quietName ≠ loudName := by
  intro same
  have counts := congrArg RhoSourceOutputPredicate.count same
  change (0 : Nat) = 1 at counts
  cases counts

theorem unequal_channels_have_no_occurrence_execution
    (before after : Configuration (Process []) (ContextualCommunicationProfiles.Occurrence []))
    (sourceRead : labels ContextualCommunicationProfiles.label before.present =
      normalized (join (outputClass quietName (zero []))
        (inputClass loudName (project (null : Term sig [Srt.nm] Srt.pr))))) :
    ¬ InterpretedStep core (ContextualCommunicationProfiles.action []).identity before after := by
  intro executed
  exact unequal_channel_classes (interpreted_communication_requires_channel_agreement
    (ContextualCommunicationProfiles.action []).identity before after quietName loudName
    (zero []) (project null) (observe_identity_of_normalized _ _ sourceRead) executed)

theorem source_equation_and_operational_drop_are_separate :
    quote (drop quietName) = quietName ∧
      (∀ target : Process [],
        ¬ RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core)
          (drop (quote (zero []))) target) ∧
      RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
        (drop (quote (zero []))) (zero []) :=
  ⟨name_quote_drop_is_equation quietName, dropped_null_has_no_core_event,
    process_drop_source_step (zero [])⟩

theorem process_reduction_does_not_become_equality :
    drop (quote visible) ≠ visible ∧
      RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
        (drop (quote visible)) visible :=
  ⟨suspended_not_visible, process_drop_source_step visible⟩

theorem output_payload_reaction_permission_is_absent :
    ¬ RhoScopedEquationEventControls.parallelPermission Srt.pr Op.out 1 := by
  intro impossible
  exact impossible

theorem input_body_reaction_permission_is_absent :
    ¬ RhoScopedEquationEventControls.parallelPermission Srt.pr Op.inp 1 := by
  intro impossible
  exact impossible

theorem broad_intrinsic_descent_cannot_be_used_as_source_permission :
    ¬ ∀ {source target : Term sig [] Srt.pr},
      rhoSourceWithDrop.Step source target →
        Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
          rhoRuleInterpretation rhoBasePremises RhoSchema.Authored.rhoCalcWithDrop
          (RhoSchema.IntrinsicEncoding.encodeTerm source) (RhoSchema.IntrinsicEncoding.encodeTerm target) :=
  RhoContextScopeComparison.unrestricted_step_translation_fails

def quoteCrossingReceiver : Term sig [] Srt.pr := inputRaw chan quotedBody

theorem intrinsic_quote_crossing_fails_the_canonical_scope_check :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" 0
      (RhoSchema.IntrinsicEncoding.encodeTerm quoteCrossingReceiver) = false := by
  decide +kernel

theorem intrinsic_quote_crossing_is_not_a_canonical_closed_process :
    ¬ Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (RhoSchema.IntrinsicEncoding.encodeTerm quoteCrossingReceiver) := by
  intro typed
  have safe :=
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff _).mp typed |>.2
  rw [intrinsic_quote_crossing_fails_the_canonical_scope_check] at safe
  cases safe

def stagedCommunication : ContextualCommunicationProfiles.Root withReflection [] :=
  ⟨⟨.communication, trivial⟩,
    communication chan RhoSourceOutputPredicate.output (dropRaw (.var .zero))⟩

theorem staged_communication_publishes_the_suspended_process :
    stagedCommunication.target = suspended := rfl

theorem communication_then_explicit_activation :
    Relation.ReflTransGen
      (RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection))
      stagedCommunication.source visible := by
  have first := root_has_declared_source_step stagedCommunication
  rw [staged_communication_publishes_the_suspended_process] at first
  exact (Relation.ReflTransGen.single first).tail (process_drop_source_step visible)

theorem staged_communication_has_two_retained_occurrence_steps :
    ∃ before middle after : Configuration (Process []) (ContextualCommunicationProfiles.Occurrence []),
      before.equations = [] ∧
      Represents before stagedCommunication.source ∧
      InterpretedStep withReflection (ContextualCommunicationProfiles.action []).identity before middle ∧
      Represents middle suspended ∧
      InterpretedStep withReflection (ContextualCommunicationProfiles.action []).identity middle after ∧
      Represents after visible := by
  obtain ⟨before, middle, initial, sourceRead, first, middleRead⟩ :=
    every_source_step_has_occurrence_execution _ _ (root_has_declared_source_step stagedCommunication)
  rw [staged_communication_publishes_the_suspended_process] at middleRead
  obtain ⟨after, second, targetRead⟩ := source_step_has_firing suspended visible middle
    first.retains_model middleRead (process_drop_source_step visible)
  exact ⟨before, middle, after, initial,
    ⟨by rw [initial]; exact (ContextualCommunicationProfiles.action []).models_nil _, sourceRead⟩,
    first, ⟨first.retains_model, middleRead⟩, second, second.retains_model, targetRead⟩

theorem suspended_normalizes_to_one_occurrence : normalized suspended = {suspended} := by
  apply normalized_singleton_of_card_one
  rw [normalized_card, RhoIntrinsicCanonicalBag.components_bagContents, suspended, RhoCanonicalNamePairs.encode_drop]
  rfl

theorem visible_normalizes_to_one_occurrence : normalized visible = {visible} := by
  apply normalized_singleton_of_card_one
  rw [normalized_card]
  change (RhoIntrinsicCanonicalBag.components (outputClass (project chan) (project nilP))).card = 1
  rw [RhoScopedConstructorInventory.output_components]
  rfl

/-- A public absence observer distinguishes the two stages. A comparison
that hides this intermediate state must state that restriction or arrange
private preparation/atomic publication; endpoint agreement is insufficient. -/
theorem public_absence_distinguishes_staging
    (middle after : Configuration (Process []) (ContextualCommunicationProfiles.Occurrence []))
    (middleRep : Represents middle suspended) (afterRep : Represents after visible) :
    Check.Holds (ContextualCommunicationProfiles.action []) (ContextualCommunicationProfiles.action []).identity
      ContextualCommunicationProfiles.label middle.present (.absent visible) ∧
    ¬ Check.Holds (ContextualCommunicationProfiles.action []) (ContextualCommunicationProfiles.action []).identity
      ContextualCommunicationProfiles.label after.present (.absent visible) := by
  have mid := middleRep.2
  have final := afterRep.2
  rw [suspended_normalizes_to_one_occurrence] at mid
  rw [visible_normalizes_to_one_occurrence] at final
  constructor
  · intro occurrence present
    have member : ContextualCommunicationProfiles.label occurrence ∈
        labels ContextualCommunicationProfiles.label middle.present :=
      Multiset.mem_map.mpr ⟨occurrence, present, rfl⟩
    rw [mid, Multiset.mem_singleton] at member
    simp only [SubstitutionAction.apply_identity, member]
    exact Ne.symm suspended_not_visible
  · intro absent
    have member : visible ∈ labels ContextualCommunicationProfiles.label after.present := by
      rw [final]
      exact Multiset.mem_singleton_self _
    obtain ⟨occurrence, present, same⟩ := Multiset.mem_map.mp member
    have refused := absent occurrence present
    simp only [SubstitutionAction.apply_identity, same] at refused
    exact refused rfl

/-- At the closed source context, the separating observation is also the
actual universal guard entailment required by the CMR step. -/
theorem public_absence_entailment_distinguishes_staging
    (middle after : Configuration (Process []) (ContextualCommunicationProfiles.Occurrence []))
    (middleRep : Represents middle suspended) (afterRep : Represents after visible) :
    (ContextualCommunicationProfiles.action []).Entails middle.equations
      (fun assignment => Check.Holds (ContextualCommunicationProfiles.action []) assignment
        ContextualCommunicationProfiles.label middle.present (.absent visible)) ∧
    ¬ (ContextualCommunicationProfiles.action []).Entails after.equations
      (fun assignment => Check.Holds (ContextualCommunicationProfiles.action []) assignment
        ContextualCommunicationProfiles.label after.present (.absent visible)) := by
  obtain ⟨beforeCheck, afterCheck⟩ := public_absence_distinguishes_staging middle after middleRep afterRep
  constructor
  · intro assignment _
    have identity : assignment = (ContextualCommunicationProfiles.action []).identity := by
      funext sort position
      cases position
    rw [identity]
    exact beforeCheck
  · intro entailed
    exact afterCheck (entailed _ afterRep.1)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationProfileControls
