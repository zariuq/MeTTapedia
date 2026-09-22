import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceRegistry
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentProofEvidence

/-!
# Service adapters driven by the actual assembly producers

The matching adapter decides admission of a submitted receipt. Its target is
the existing decoded, proof-relevant occurrence/index judgment, independently
of the assembly callback. This is not a decision procedure for arbitrary
matching search or the full native reconstruction operation. Separate laws
retain the callback's actual native proof and exact selected proposition;
the proof need not be the reference J syntax.

The HOL adapter submits the actual output of `Assembly.produceHOL` to the
existing intrinsic native-proof service, at the original requested claim.
It neither rebuilds the kernel nor changes the general source-derivability
target. Replay qualification is separate from kernel claim binding.

These are two precisely classified adapter instances of the existing
four-face interface, not a choice of Prime's service faces or a model of four
assembly callbacks. Native formation, interpreted meaning, proof provenance
and revision freshness remain distinct. Intrinsic proofs are not unchecked
external bytes, and a represented HOL proposition is not its native proof.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentAssemblyServices

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef NIKMetalogic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation
open SharedJudgmentFragment SharedJudgmentServiceInterpretation

universe u v w w'

variable {assembly : Assembly}

/-! ## Decision of submitted receipt admission -/

/-- The requested occurrence and element index are checked by the existing
evidence type. No callback output or acceptance bit occurs in this meaning. -/
def submittedReceiptTarget : AdmissionObject where
  Carrier := PolarizedNeedMatchedIndex.Request × NativeWireData.Wire
  Meaning input := ∃ receipt,
    MatchedIndexDependentTransport.decodeAdmitted input.2 = some receipt ∧
      Nonempty (PolarizedNeedMatchedIndex.Evidence input.1 receipt)

theorem receipt_meaning_iff_consume (expected : PolarizedNeedMatchedIndex.Request)
    (input : NativeWireData.Wire) :
    submittedReceiptTarget.Meaning (expected, input) ↔
      ∃ transport, MatchedIndexDependentTransport.consume? expected input = some transport := by
  constructor
  · rintro ⟨receipt, decoded, evidence⟩
    have checked := (PolarizedNeedMatchedIndex.validate_evidence_iff expected receipt).mpr evidence
    have canonical := MatchedIndexDependentTransport.consume_checked_receipt expected receipt checked
    have selected := (MatchedIndexDependentTransport.consume_iff _ _ _).mp canonical |>.2.2
    exact ⟨⟨receipt, receipt.output⟩,
      (MatchedIndexDependentTransport.consume_iff _ _ _).mpr ⟨decoded, checked, selected⟩⟩
  · rintro ⟨transport, consumed⟩
    exact ⟨transport.receipt,
      ((MatchedIndexDependentTransport.consume_iff _ _ _).mp consumed).1,
      (MatchedIndexDependentTransport.consume_selection consumed).1⟩

theorem receipt_callback_iff (admission : MatchAdmission assembly)
    (coverage : MatchCoverage assembly) (expected : PolarizedNeedMatchedIndex.Request)
    (input : NativeWireData.Wire) :
    (assembly.reconstructMatch expected input).isSome = true ↔
      submittedReceiptTarget.Meaning (expected, input) := by
  constructor
  · intro present
    cases returned : assembly.reconstructMatch expected input with
    | none => simp only [returned, Option.isSome_none, Bool.false_eq_true] at present
    | some result =>
        obtain ⟨transport, consumed, _, _⟩ := admission _ _ _ _ returned
        exact (receipt_meaning_iff_consume expected input).mpr ⟨transport, consumed⟩
  · intro meaningful
    obtain ⟨transport, consumed⟩ := (receipt_meaning_iff_consume expected input).mp meaningful
    obtain ⟨source, returned⟩ := coverage expected input transport consumed
    simp only [returned, Option.isSome_some]

/-- Only the presence of this assembly's actual reconstruction is observed.
Its decision meaning still has to be justified independently. -/
def receiptDecisionRaw (assembly : Assembly) : RawService.{0, 0} submittedReceiptTarget :=
  .directDecision fun input => (assembly.reconstructMatch input.1 input.2).isSome

theorem receipt_decision_qualified (admission : MatchAdmission assembly)
    (coverage : MatchCoverage assembly) : (receiptDecisionRaw assembly).Qualified :=
  fun input => receipt_callback_iff admission coverage input.1 input.2

theorem receipt_interface_matches (assembly : Assembly) :
    SharedJudgmentServiceRegistry.InterfaceMatches (receiptDecisionRaw assembly) .directDecision :=
  .directDecision _

def receiptService (assembly : Assembly) (admission : MatchAdmission assembly)
    (coverage : MatchCoverage assembly) : NIK.Service.{0, 0} submittedReceiptTarget :=
  (receiptDecisionRaw assembly).toService (receipt_decision_qualified admission coverage)

def receiptRequest (assembly : Assembly) (admission : MatchAdmission assembly)
    (coverage : MatchCoverage assembly) (expected : PolarizedNeedMatchedIndex.Request)
    (input : NativeWireData.Wire) :
    NIKServiceInvocation.Request (receiptService assembly admission coverage) :=
  .directDecision (expected, input)

theorem receipt_service_accepts_iff (admission : MatchAdmission assembly)
    (coverage : MatchCoverage assembly) (expected : PolarizedNeedMatchedIndex.Request)
    (input : NativeWireData.Wire) :
    (NIKServiceInvocation.invoke (receiptRequest assembly admission coverage expected input)).acceptedValue =
        some (expected, input) ↔ submittedReceiptTarget.Meaning (expected, input) := by
  change (if (assembly.reconstructMatch expected input).isSome then some (expected, input) else none) =
    some (expected, input) ↔ _
  cases present : (assembly.reconstructMatch expected input).isSome <;>
    simpa [present] using (receipt_callback_iff admission coverage expected input)

/-- The NIK decision licenses the submitted receipt. The separate actual
response retains whichever native proof the callback really returned. -/
theorem receipt_accepted_actual_response (admission : MatchAdmission assembly)
    (coverage : MatchCoverage assembly) (expected : PolarizedNeedMatchedIndex.Request)
    (input : NativeWireData.Wire)
    (accepted :
      (NIKServiceInvocation.invoke (receiptRequest assembly admission coverage expected input)).acceptedValue =
        some (expected, input)) :
    ∃ source proposition transport,
      assembly.reconstructMatch expected input = some (source, proposition) ∧
      SharedJudgmentServices.Invocation assembly
        (SharedJudgmentServices.Request.matching (n := 0) expected input)
        (.matched source proposition) ∧
      MatchedIndexDependentTransport.consume? expected input = some transport ∧
      proposition = transport.proposition ∧
      getElem? transport.receipt.values expected.index = some transport.selected ∧
      transport.selected = transport.receipt.output ∧
      FormationSensitive.Judgment assembly.rules .nil source proposition := by
  have meaningful := (receipt_service_accepts_iff admission coverage expected input).mp accepted
  obtain ⟨transport, consumed⟩ := (receipt_meaning_iff_consume expected input).mp meaningful
  obtain ⟨source, returned⟩ := coverage expected input transport consumed
  obtain ⟨other, otherConsumed, proposition, admitted⟩ := admission _ _ _ _ returned
  have same : other = transport := Option.some.inj (otherConsumed.symm.trans consumed)
  subst other
  exact ⟨source, transport.proposition, transport, returned, .matchingSuccess returned,
    consumed, rfl, (MatchedIndexDependentTransport.consume_selection consumed).2.1,
    (MatchedIndexDependentTransport.consume_selection consumed).2.2, admitted⟩

/-! ## Actual HOL production followed by the unchanged native-proof interface -/

variable {Γ : HOL.Ctx HOL.UniformListInduction.BaseSort}

theorem hol_interface_matches (Γ : HOL.Ctx HOL.UniformListInduction.BaseSort) :
    SharedJudgmentServiceRegistry.InterfaceMatches (HOLControls.raw Γ)
      (.nativeProof (UniformListChartNIKService.intrinsicProofSystem Γ)) :=
  .nativeProof _ _

/-- The raw callback determines which intrinsic proof is submitted. An
absent producer result is not replaced by a reference proof. -/
def holRequest? (assembly : Assembly) (replay : UniformListChartNIKService.ReplayRequest Γ) :
    Option (NIKServiceInvocation.Request (UniformListChartNIKService.nativeProofService Γ)) :=
  (assembly.produceHOL Γ replay).map fun proof => .nativeProof replay.claim proof

def holRun? (assembly : Assembly) (replay : UniformListChartNIKService.ReplayRequest Γ) :
    Option (UniformListChartNIKService.SourceClaim Γ) :=
  (holRequest? assembly replay).bind fun request =>
    (NIKServiceInvocation.invoke request).acceptedValue

/-- Before assembly qualification, acceptance means that an actual returned
proof passed the existing kernel at this exact submitted claim. -/
theorem holRun_some_iff (assembly : Assembly)
    (replay : UniformListChartNIKService.ReplayRequest Γ)
    (claim : UniformListChartNIKService.SourceClaim Γ) :
    holRun? assembly replay = some claim ↔
      ∃ proof, assembly.produceHOL Γ replay = some proof ∧
        (UniformListChartNIKService.intrinsicKernel Γ).decide replay.claim proof = true ∧
        claim = replay.claim := by
  constructor
  · intro returned
    obtain ⟨request, selected, accepted⟩ := Option.bind_eq_some_iff.mp returned
    obtain ⟨proof, produced, same⟩ := Option.map_eq_some_iff.mp selected
    cases same
    exact ⟨proof, produced,
      (NIKServiceInvocation.native_proof_value_iff _ _ _ _ _ _).mp accepted⟩
  · rintro ⟨proof, produced, checked, bound⟩
    unfold holRun? holRequest?
    rw [produced]
    exact (NIKServiceInvocation.native_proof_value_iff
      (target := UniformListChartNIKService.sourceTarget Γ)
      (UniformListChartNIKService.intrinsicProofSystem Γ)
      (UniformListChartNIKService.intrinsicKernel Γ)
      (UniformListChartNIKService.intrinsic_meaning_exact Γ) replay.claim proof claim).mpr
        ⟨checked, bound⟩

/-- Replay qualification, not intrinsic claim binding alone, connects this
actual producer/service pipeline to the submitted equational certificates. -/
theorem holRun_iff (qualified : HOLReplayQualified assembly)
    (replay : UniformListChartNIKService.ReplayRequest Γ)
    (claim : UniformListChartNIKService.SourceClaim Γ) :
    holRun? assembly replay = some claim ↔
      UniformListChartNIKService.replayAccepted Γ replay = true ∧ claim = replay.claim := by
  constructor
  · intro accepted
    obtain ⟨proof, produced, _, bound⟩ := (holRun_some_iff assembly replay claim).mp accepted
    exact ⟨(qualified.1 Γ replay).mp (by simp only [produced, Option.isSome_some]), bound⟩
  · rintro ⟨accepted, bound⟩
    have present := (qualified.1 Γ replay).mpr accepted
    cases produced : assembly.produceHOL Γ replay with
    | none => simp only [produced, Option.isSome_none, Bool.false_eq_true] at present
    | some proof =>
        exact (holRun_some_iff assembly replay claim).mpr
          ⟨proof, produced, (produced_hol_admission qualified produced).1, bound⟩

theorem faithful_hol_service (qualified : HOLReplayQualified assembly)
    {evidence : SharedJudgmentProofEvidence.Evidence Γ}
    (faithful : evidence.Produced) :
    holRequest? assembly evidence.request = some evidence.nativeRequest ∧
      holRun? assembly evidence.request = some evidence.request.claim := by
  refine ⟨?_, (holRun_iff qualified _ _).mpr
    ⟨SharedJudgmentProofEvidence.Evidence.accepted faithful, rfl⟩⟩
  rw [holRequest?, SharedJudgmentProofEvidence.faithful_production qualified faithful]
  rfl

variable {C : Cwf.{u, v, w, w'}}
variable {interpretation : SharedJudgmentInterpretation.Data assembly C}

/-- The actual callback-driven NIK request, shared native response and
independently related semantic value all concern the same retained claim.
This preserves the explicit formation and meaning premises of the attachment. -/
theorem faithful_hol_service_attached (qualified : HOLReplayQualified assembly)
    {evidence : SharedJudgmentProofEvidence.Evidence Γ} (faithful : evidence.Produced)
    (attachment : NativeAttachment (UniformListChartNIKService.sourceTarget Γ) interpretation)
    (environment : Sub Tower.Head Γ.length (attachment.scope evidence.request.claim))
    (bound : SharedJudgmentProofEvidence.ResponseBound attachment evidence environment)
    (formed : FormationSensitive.ContextFormation assembly.rules
      (attachment.context evidence.request.claim))
    (typed : FormationSensitive.CtxMor assembly.rules
      (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types Γ)
      (attachment.context evidence.request.claim) environment)
    (meaning : attachment.MeaningCompatible) :
    holRequest? assembly evidence.request = some evidence.nativeRequest ∧
      holRun? assembly evidence.request = some evidence.request.claim ∧
      (SharedJudgmentServices.invoke assembly (.hol Γ evidence.request environment)).nativePayload? =
        some (attachment.payload evidence.request.claim, attachment.nativeType evidence.request.claim) ∧
      FormationSensitive.Judgment assembly.rules (attachment.context evidence.request.claim)
        (attachment.payload evidence.request.claim) (attachment.nativeType evidence.request.claim) ∧
      interpretation.ty ⟨attachment.context evidence.request.claim, formed⟩
        (attachment.nativeType evidence.request.claim) (attachment.semanticType evidence.request.claim formed) ∧
      interpretation.term ⟨attachment.context evidence.request.claim, formed⟩
        (attachment.payload evidence.request.claim) (attachment.nativeType evidence.request.claim)
        (attachment.semanticType evidence.request.claim formed) (attachment.value evidence.request.claim formed) :=
  ⟨(faithful_hol_service qualified faithful).1, (faithful_hol_service qualified faithful).2,
    SharedJudgmentProofEvidence.produced_attached_response qualified faithful attachment environment
      bound formed typed meaning⟩

/-! ## Actual alternate proofs and changed callbacks -/

namespace ReceiptControls

open PolarizedNeedMatchedIndex PolarizedNeedMatchedIndex.Examples
open SharedJudgmentServices.Examples

/-- An actual alternate callback returns the admitted reflexivity result of
the checked J step. It does not return the reference J source term. -/
def reflexivityAssembly : Assembly :=
  { common with reconstructMatch := fun expected input =>
      (MatchedIndexDependentTransport.consume? expected input).map fun transport =>
        (transport.proof, transport.proposition) }

theorem reflexivity_admission : MatchAdmission reflexivityAssembly := by
  intro expected input source proposition returned
  obtain ⟨transport, consumed, same⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨transport, consumed, rfl,
    HOLNativeRelatorCompatibility.wire_relator_judgment
      (MatchedIndexDependentTransport.consume_proof_admitted consumed)⟩

theorem reflexivity_coverage : MatchCoverage reflexivityAssembly := by
  intro expected input transport consumed
  refine ⟨transport.proof, ?_⟩
  change (MatchedIndexDependentTransport.consume? expected input).map _ = _
  rw [consumed]
  rfl

theorem reflexivity_decision_qualified : (receiptDecisionRaw reflexivityAssembly).Qualified :=
  receipt_decision_qualified reflexivity_admission reflexivity_coverage

/-- Receipt decisions agree, while the actual reconstruction syntax differs.
Therefore this normalized decision is not the full reconstruction service. -/
theorem same_receipt_decision : receiptDecisionRaw reflexivityAssembly = receiptDecisionRaw common := by
  unfold receiptDecisionRaw
  congr 1
  funext input
  change ((MatchedIndexDependentTransport.consume? input.1 input.2).map _).isSome =
    ((MatchedIndexDependentTransport.consume? input.1 input.2).map _).isSome
  cases MatchedIndexDependentTransport.consume? input.1 input.2 <;> rfl

theorem canonical_distinct_returned_proofs :
    common.reconstructMatch canonical.request (admittedWire canonical) =
        some (canonicalTransport.source, canonicalTransport.proposition) ∧
      reflexivityAssembly.reconstructMatch canonical.request (admittedWire canonical) =
        some (canonicalTransport.proof, canonicalTransport.proposition) ∧
      canonicalTransport.source ≠ canonicalTransport.proof := by
  refine ⟨?_, ?_, ?_⟩
  · change (MatchedIndexDependentTransport.consume? canonical.request (admittedWire canonical)).map _ = _
    rw [MatchedIndexDependentTransport.Examples.canonical_reconstruction]
    rfl
  · change (MatchedIndexDependentTransport.consume? canonical.request (admittedWire canonical)).map _ = _
    rw [MatchedIndexDependentTransport.Examples.canonical_reconstruction]
    rfl
  · intro impossible
    cases impossible

theorem canonical_reflexivity_service_accepted :
    (NIKServiceInvocation.invoke (receiptRequest reflexivityAssembly reflexivity_admission
      reflexivity_coverage canonical.request (admittedWire canonical))).acceptedValue =
        some (canonical.request, admittedWire canonical) :=
  (receipt_service_accepts_iff reflexivity_admission reflexivity_coverage _ _).mpr
    ((receipt_meaning_iff_consume _ _).mpr
      ⟨_, MatchedIndexDependentTransport.Examples.canonical_reconstruction⟩)

def droppedMatching : Assembly := { common with reconstructMatch := fun _ _ => none }

theorem dropped_matching_not_covered : ¬ MatchCoverage droppedMatching := by
  intro coverage
  obtain ⟨source, returned⟩ := coverage _ _ _
    MatchedIndexDependentTransport.Examples.canonical_reconstruction
  cases returned

/-- Replaying an admitted native proof cannot validate an altered receipt. -/
def replayedMatching : Assembly :=
  { common with reconstructMatch := fun _ _ => some (canonicalTransport.source, canonicalTransport.proposition) }

theorem replayed_matching_not_admitted : ¬ MatchAdmission replayedMatching := by
  intro admission
  obtain ⟨transport, consumed, _, _⟩ := admission canonical.request (admittedWire changedOutput)
    canonicalTransport.source canonicalTransport.proposition rfl
  rw [MatchedIndexDependentTransport.Examples.changed_output_rejected] at consumed
  cases consumed

theorem replayed_receipt_decision_not_qualified : ¬ (receiptDecisionRaw replayedMatching).Qualified := by
  intro qualified
  have meaningful := (qualified (canonical.request, admittedWire changedOutput)).mp rfl
  obtain ⟨transport, consumed⟩ := (receipt_meaning_iff_consume _ _).mp meaningful
  rw [MatchedIndexDependentTransport.Examples.changed_output_rejected] at consumed
  cases consumed

end ReceiptControls

namespace HOLCallbackControls

open HOL HOL.UniformListInduction

def changedPremises (Γ : HOL.Ctx BaseSort) : UniformListChartNIKService.ReplayRequest Γ :=
  { UniformListChartNIKService.actualRequest Γ with
      stepPremises := HOL.UniformListInductionChart.alteredStepAssumptions Γ }

/-- This deliberately incorrect callback ignores the supplied certificates.
Its returned intrinsic proof is valid, but it is not a qualified replay. -/
def replayedHOL : Assembly :=
  { common with produceHOL := fun Γ _ => some (UniformListChartNIKService.actualNativeProof Γ) }

theorem common_actual (Γ : HOL.Ctx BaseSort) :
    holRequest? common (UniformListChartNIKService.actualRequest Γ) =
        some (SharedJudgmentProofEvidence.Controls.actual Γ).nativeRequest ∧
      holRun? common (UniformListChartNIKService.actualRequest Γ) =
        some (UniformListChartNIKService.mapLengthClaim Γ) :=
  faithful_hol_service common_hol_replay (SharedJudgmentProofEvidence.Controls.actual_faithful Γ)

theorem common_detoured (Γ : HOL.Ctx BaseSort) :
    holRequest? common (UniformListChartProofSyntax.detouredRequest Γ) =
        some (SharedJudgmentProofEvidence.Controls.detoured Γ).nativeRequest ∧
      holRun? common (UniformListChartProofSyntax.detouredRequest Γ) =
        some (UniformListChartNIKService.mapLengthClaim Γ) :=
  faithful_hol_service common_hol_replay (SharedJudgmentProofEvidence.Controls.detoured_faithful Γ)

theorem common_refuses_changed_premises : holRun? common (changedPremises []) = none := rfl

/-- The unchanged intrinsic kernel binds the claim, not certificate history.
Thus the callback's independent replay qualification is indispensable. -/
theorem replayed_accepts_changed_premises :
    holRun? replayedHOL (changedPremises []) =
      some (UniformListChartNIKService.mapLengthClaim []) := rfl

theorem replayed_not_qualified : ¬ HOLReplayQualified replayedHOL := by
  intro qualified
  have accepted := (qualified.1 [] (changedPremises [])).mp rfl
  change false = true at accepted
  cases accepted

theorem replayed_changed_claim_rejected : holRun? replayedHOL
    { UniformListChartNIKService.actualRequest [] with claim := (theory, lengthNil) } = none := rfl

theorem missing_induction_rejected : holRun? common
    { UniformListChartNIKService.actualRequest [] with claim := (equations, mapLength) } = none := rfl

end HOLCallbackControls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentAssemblyServices
