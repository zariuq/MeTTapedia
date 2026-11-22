import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationPlugging
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationGround
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
      ContextualCommunicationProfiles.label middle.present (.predicate .none visible) ∧
    ¬ Check.Holds (ContextualCommunicationProfiles.action []) (ContextualCommunicationProfiles.action []).identity
      ContextualCommunicationProfiles.label after.present (.predicate .none visible) := by
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
        ContextualCommunicationProfiles.label middle.present (.predicate .none visible)) ∧
    ¬ (ContextualCommunicationProfiles.action []).Entails after.equations
      (fun assignment => Check.Holds (ContextualCommunicationProfiles.action []) assignment
        ContextualCommunicationProfiles.label after.present (.predicate .none visible)) := by
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

namespace Payload

open RhoPayloadPresentation
open ContextualFamily

abbrev base := ContextualCommunication.Payload.base
abbrev locals := ContextualCommunication.Payload.locals

def channel : Term base [] .nm := freeT "receive"
def code {Γ : Ctx base} : Term base Γ .pr := outT (freeT "answer") nilT
def runReceived : Term base [.pr] .pr := .var .zero
def nameReceived : Term base [.pr] .pr := outT received nilT
def nestedReceived : Term base [.pr] .pr := inpT (freeT "nested") (.var (.succ .zero))
def literalDrop : Term base [.pr] .pr := drpT (quoT code)

section CanonicalSurface

open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (FreeSortContext)
open Mettapedia.OSLF.MeTTaIL.Syntax (rhoReflectivePresentation)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Canonical (canonicalize)
open RhoPayloadParameterizedRuntime (mapClass mapClass_eq_iff)
open ContextualCommunicationAdequacy.Payload (Store InterpretedStep
  every_source_has_store canonical_surface_step_iff_firing canonical_surface_firing_reflects_paper)

private theorem emptyHasNoFreeProcesses (name : String) :
    FreeSortContext.empty name ≠ some rhoReflectivePresentation.processSort := by
  simp [FreeSortContext.empty]

/-- The wrapped name is compiled before communicating. The physical
commit and the paper reduction of the original spelling read back to
the same supplied process, not to the raw dangling-index residual. -/
theorem wrapped_surface_communicates_on_the_step :
    ∃ (safe : canonicalWholeNameSafe RawBoundary.surfaceSpelling = true)
      (before after : Store []) (residual : ParameterizedRewriteSystem.Process FreeSortContext.empty),
      ContextualCommunicationAdequacy.Payload.Represents before
        (mapClass emptyHasNoFreeProcesses
          (canonicalProcess RawBoundary.surfaceSpelling RawBoundary.surfaceSpelling_typed safe)) ∧
      InterpretedStep before after ∧
      ContextualCommunicationAdequacy.Payload.Represents after
        (mapClass emptyHasNoFreeProcesses residual) ∧
      Nonempty (Reduction.Reduces RawBoundary.surfaceSpelling residual.1) ∧
      canonicalize residual.1 =
        canonicalize (.apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]) := by
  obtain ⟨safe, reached, reacts, expected⟩ := RawBoundary.canonical_surface_communicates
  let entry := canonicalProcess RawBoundary.surfaceSpelling RawBoundary.surfaceSpelling_typed safe
  let intended := ParameterizedRewriteSystem.stepTarget entry ⟨1, reacts⟩
  obtain ⟨before, represented⟩ := every_source_has_store (mapClass emptyHasNoFreeProcesses entry)
  obtain ⟨after, fired, final⟩ :=
    (canonical_surface_step_iff_firing emptyHasNoFreeProcesses
      RawBoundary.surfaceSpelling_typed safe (target := intended) represented).mp ⟨reached, reacts, rfl⟩
  obtain ⟨residual, _, paper, readback⟩ :=
    canonical_surface_firing_reflects_paper emptyHasNoFreeProcesses
      RawBoundary.surfaceSpelling_typed safe represented fired
  have same := (mapClass_eq_iff emptyHasNoFreeProcesses residual intended).mp
    (readback.readback.symm.trans final.readback)
  exact ⟨safe, before, after, residual, represented, fired, readback, paper, same.trans expected⟩

end CanonicalSurface

section ScopedRelay

open RhoPayloadParameterizedRuntime (classStep classStep_cls)
open ContextualCommunicationAdequacy.Payload (Store InterpretedStep source_step_has_firing
  target_step_reads_back reindexed_step_has_firing)

attribute [local instance] Classical.propDecidable

private def ambientProcess : Term base [.pr] .pr := .var .zero
private def relayChannel : Term base [.pr] .nm := freeT "relay"

/-- The next channel comes from the received process. The payload of that
next send is the caller's process, not the received one. -/
private def relayBody : Term base [.pr, .pr] .pr :=
  outT (quoT (.var .zero)) (.var (.succ .zero))

private def receiveTwice : Term base [.pr, .pr] .pr :=
  parT (.var .zero) (.var .zero)

private def listener : Term base [.pr] .pr := inpT (quoT (drpT (quoT code))) receiveTwice

/-- Even an executable COMM inside the quoted packet is suspended here. -/
private def sealed : Term base [.pr] .pr :=
  drpT (quoT (parT code (inpT (freeT "answer") (.var .zero))))

private def relayStart : Term base [.pr] .pr :=
  parT (parT (outT (quoT (drpT relayChannel)) code) (inpT relayChannel relayBody))
    (parT listener sealed)

private def relayMiddle : Term base [.pr] .pr :=
  parT (parT (outT (quoT code) ambientProcess) listener) sealed

private def relayEnd : Term base [.pr] .pr :=
  parT (parT ambientProcess ambientProcess) sealed

private theorem relay_step :
    Steps strictRules relayStart relayMiddle := by
  apply steps_of_equiv
    (equiv_parT (equiv_parT (equiv_outT (quoteDrop_equiv relayChannel) (.refl _)) (.refl _)) (.refl _))
    (parT_assoc (outT (quoT code) ambientProcess) listener sealed).symm
  exact steps_parCong [] (parT listener sealed) (steps_comm [] relayChannel code relayBody)

private theorem relay_second_step :
    Steps strictRules relayMiddle relayEnd := by
  apply steps_of_equiv
    (equiv_parT (equiv_parT (.refl _)
      (equiv_inpT (quoteDrop_equiv (quoT code)) (.refl _))) (.refl _)) (.refl _)
  exact steps_parCong [] sealed (steps_comm [] (quoT code) ambientProcess receiveTwice)

private theorem relay_end_has_no_step (target : Cls [.pr] .pr) :
    ¬ classStep (cls relayEnd) target := by
  intro reaction
  have represented : classStep (cls relayEnd) (cls (Quotient.out target)) :=
    (RhoPayloadPresentation.cls_out target).symm ▸ reaction
  exact no_strict_step_of_no_output (source := relayEnd) rfl
    ((classStep_cls _ _).mp represented)

local notation "Rep" => ContextualCommunicationAdequacy.Payload.Represents

/-- A relay at open scope runs twice, retains the untouched packet, and
publishes two occurrences of the exact caller process. The suspended
packet alone cannot provide a third reaction. -/
theorem scoped_relay_has_two_commits :
    ∃ (before middle after : Store [.pr]),
      Rep before (cls relayStart) ∧ InterpretedStep before middle ∧
      Rep middle (cls relayMiddle) ∧ InterpretedStep middle after ∧
      Rep after (cls relayEnd) ∧ (∀ next, ¬ InterpretedStep after next) := by
  obtain ⟨world, labels⟩ := IndexedOccurrences.realize (atoms relayStart)
  let before : Store [.pr] := ⟨[], world⟩
  have starts : Rep before (cls relayStart) := ⟨(ContextualCommunicationAdequacy.Payload.action _).models_nil _, labels⟩
  obtain ⟨middle, first, atMiddle⟩ := source_step_has_firing starts ((classStep_cls _ _).mpr relay_step)
  obtain ⟨after, second, atEnd⟩ := source_step_has_firing atMiddle ((classStep_cls _ _).mpr relay_second_step)
  refine ⟨before, middle, after, starts, first, atMiddle, second, atEnd, ?_⟩
  intro next extra
  obtain ⟨target, invented, _⟩ := target_step_reads_back atEnd extra
  exact relay_end_has_no_step target invented

private def supplyCaller : Sub base [.pr] []
  | _, .zero => parT code code

/-- Supplying a parallel caller repacks each of the two result variables
into two code occurrences. The quoted packet is unchanged. -/
theorem supplying_the_caller_repackages_the_same_relay :
    ∃ (before after : Store []),
      Rep before (bindQ supplyCaller (cls relayMiddle)) ∧ InterpretedStep before after ∧
      labels ContextualCommunicationAdequacy.Payload.label after.present =
        Multiset.replicate 4 (cls (code (Γ := []))) + {cls (bind supplyCaller sealed)} := by
  obtain ⟨_, middle, finish, _, _, original, second, atEnd, _⟩ := scoped_relay_has_two_commits
  obtain ⟨world, values⟩ := IndexedOccurrences.realize (atoms (bind supplyCaller relayMiddle))
  let before : Store [] := ⟨[], world⟩
  have repacked : Rep before (bindQ supplyCaller (cls relayMiddle)) :=
    ⟨(ContextualCommunicationAdequacy.Payload.action _).models_nil _, values⟩
  obtain ⟨_, after, _, fired, _, observed⟩ :=
    reindexed_step_has_firing supplyCaller original second repacked
  rw [atEnd.2, ← atomsQ_bindQ] at observed
  exact ⟨before, after, repacked, fired, observed⟩

/-- An ambient variable can be assigned a name to solve an input equation
without that equation holding in the current scope. This is why source
reaction admission uses the fixed interpretation, not satisfiability alone. -/
theorem mere_channel_unifiability_is_not_fixed_matching :
    let a := ContextualCommunicationAdequacy.Payload.action [.nm]
    let unknown : Term base [.nm] .nm := .var .zero
    let fixed : Term base [.nm] .nm := freeT "fixed"
    let problem := [(cls (inpT unknown nilT), cls (inpT fixed nilT))]
    a.Consistent problem ∧ ¬ a.Models a.identity problem := by
  dsimp only
  let a := ContextualCommunicationAdequacy.Payload.action [.nm]
  let unknown : Term base [.nm] .nm := .var .zero
  let fixed : Term base [.nm] .nm := freeT "fixed"
  let fill : Sub base [.nm] [.nm] := fun _ position =>
    match position with
    | .zero => fixed
  have different : cls unknown ≠ cls fixed := by
    intro equal
    have core := qcore_invariant (cls_eq_iff.mp equal)
    change QKey.var .zero = QKey.free "fixed" at core
    cases core
  refine ⟨⟨fill, (a.models_cons _ _ _).mpr ⟨rfl, a.models_nil _⟩⟩, ?_⟩
  intro atCurrent
  have solved := (a.models_cons a.identity (cls (inpT unknown nilT), cls (inpT fixed nilT)) []).mp atCurrent
  have same := solved.1
  change a.apply a.identity (cls (inpT unknown nilT)) =
    a.apply a.identity (cls (inpT fixed nilT)) at same
  rw [a.apply_identity, a.apply_identity] at same
  have parts := inpParts_invariant (cls_eq_iff.mp same)
  change ({(cls unknown, cls nilT)} : Multiset _) = {(cls fixed, cls nilT)} at parts
  exact different (congrArg Prod.fst (Multiset.singleton_inj.mp parts))

end ScopedRelay

variable {V W : Type} (captures : V → MetaArity base) (next : W → MetaArity base)
  (occupied : Finset Nat)

theorem actual_communication_is_admitted :
    ContextualActivatedStep.Valid locals captures occupied ContextualCommunicationGround.Payload.selection
      (ContextualCommunication.Payload.rule captures)
      (ContextualCommunicationGround.Payload.rows captures channel code runReceived)
      (ContextualCommunicationGround.Payload.before captures)
      (ContextualCommunicationGround.Payload.outputs captures occupied) :=
  ContextualCommunicationGround.Payload.activation_valid captures channel code runReceived occupied

theorem received_process_is_the_result
    (assignment : Assignment (ContextualCommunicationGround.Payload.active captures) next)
    (solved : ContextualFrameUnifier.Models assignment
      (ContextualCommunicationGround.Payload.problem captures channel code runReceived occupied)) :
    ContextualFamily.instantiate assignment (ContextualCommunicationGround.Payload.outputs captures occupied 2) =
      ContextualFamily.Rigid.includeTerm next (code (Γ := [])) :=
  ContextualCommunicationGround.Payload.result_in_every_solution captures channel code runReceived occupied next assignment solved

theorem received_name_is_quoted
    (assignment : Assignment (ContextualCommunicationGround.Payload.active captures) next)
    (solved : ContextualFrameUnifier.Models assignment
      (ContextualCommunicationGround.Payload.problem captures channel code nameReceived occupied)) :
    ContextualFamily.instantiate assignment (ContextualCommunicationGround.Payload.outputs captures occupied 2) =
      ContextualFamily.Rigid.includeTerm next (outT (quoT code) nilT : Term base [] .pr) :=
  ContextualCommunicationGround.Payload.result_in_every_solution captures channel code nameReceived occupied next assignment solved

theorem nested_receiver_does_not_capture_payload
    (assignment : Assignment (ContextualCommunicationGround.Payload.active captures) next)
    (solved : ContextualFrameUnifier.Models assignment
      (ContextualCommunicationGround.Payload.problem captures channel code nestedReceived occupied)) :
    ContextualFamily.instantiate assignment (ContextualCommunicationGround.Payload.outputs captures occupied 2) =
      ContextualFamily.Rigid.includeTerm next (inpT (freeT "nested") code : Term base [] .pr) :=
  ContextualCommunicationGround.Payload.result_in_every_solution captures channel code nestedReceived occupied next assignment solved

theorem receiving_does_not_execute_a_literal_drop
    (assignment : Assignment (ContextualCommunicationGround.Payload.active captures) next)
    (solved : ContextualFrameUnifier.Models assignment
      (ContextualCommunicationGround.Payload.problem captures channel code literalDrop occupied)) :
    ContextualFamily.instantiate assignment (ContextualCommunicationGround.Payload.outputs captures occupied 2) =
        ContextualFamily.Rigid.includeTerm next (drpT (quoT code) : Term base [] .pr) ∧
      ∀ target : Term base [] .pr, ¬ Steps strictRules (drpT (quoT code)) target :=
  ⟨ContextualCommunicationGround.Payload.result_in_every_solution captures channel code literalDrop occupied next assignment solved,
    fun _ => drop_inert_strict _ _⟩

theorem one_occurrence_cannot_supply_both_consumed_premises :
    ¬ ContextualActivatedStep.Valid locals captures occupied
      (⟨[0, 0], [], [2]⟩ : Selection Nat)
      (ContextualCommunication.Payload.rule captures)
      (ContextualCommunicationGround.Payload.rows captures channel code runReceived)
      (ContextualCommunicationGround.Payload.before captures)
      (fun _ => ContextualCommunicationGround.Payload.outputs captures occupied 2) := by
  intro valid
  exact (by decide : ¬ ([0, 0] : List Nat).Nodup) valid.take_distinct

theorem distinct_free_channels_cannot_solve_the_rule
    (assignment : Assignment (ContextualCommunication.Payload.source captures) next) :
    ¬ (ContextualFamily.instantiate assignment
          ((ContextualCommunication.Payload.rule captures).take[0]'(by change 0 < 2; decide)) =
        Rigid.includeTerm next (inpT (freeT "left") runReceived) ∧
      ContextualFamily.instantiate assignment
          ((ContextualCommunication.Payload.rule captures).take[1]'(by change 1 < 2; decide)) =
        Rigid.includeTerm next (outT (freeT "right") code)) := by
  rintro ⟨receiver, sender⟩
  change ContextualCommunication.Payload.input
    (ContextualFamily.instantiate assignment
      (generator (ContextualCommunication.Payload.source captures) (.inl .channel)))
    (ContextualFamily.instantiate assignment
      (generator (ContextualCommunication.Payload.source captures) (.inl .continuation))) = _ at receiver
  change ContextualCommunication.Payload.output
    (ContextualFamily.instantiate assignment
      (generator (ContextualCommunication.Payload.source captures) (.inl .channel)))
    (ContextualFamily.instantiate assignment
      (generator (ContextualCommunication.Payload.source captures) (.inl .payload))) = _ at sender
  erw [instantiate_generator, instantiate_generator] at receiver sender
  have channels := (ContextualCommunication.Payload.input_fields receiver).1.symm.trans
    (ContextualCommunication.Payload.output_fields sender).1
  simp [Rigid.includeTerm, freeT] at channels

end Payload

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationProfileControls
