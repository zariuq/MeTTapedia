import Mettapedia.Languages.Metamath.CompressedByteClassifierMM2Adapter

/-!
# Compact compressed-byte classifier to the existing MM2 scanner GSLT

The compact byte classifier and the existing MM2 scanner were authored
independently.  This module makes their common byte-stage boundary explicit as
a composable path-valued GSLT realization:

```text
compact authored byte GSLT
          -> existing MM2 scanner source GSLT
          -> existing MM2 scanner target GSLT
```

One source byte remains one source transition, then exactly two target
transitions (classify and dispatch).  The classified state retains the actual
public MM2 row selected by the existing scanner vocabulary.

The compact core also contains an end-of-input-only fault constructor.  That
constructor cannot be produced by the byte source operation; its full
semantics belongs to the separate finalizer stage.  The total carrier map has
an explicitly marked fallback only for that unreachable byte-stage endpoint;
all source transitions use the exact outcome theorem below.

This is a semantic GSLT-to-GSLT bridge.  It does not claim that the resulting
row has fired in an assembled flat MM2 program; owner/cursor/scheduler
execution is a later realization boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2GSLTBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.ClassifierLowering
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

abbrev ScannerByteOccurrence :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ByteOccurrence

abbrev ScannerFault :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerFault

abbrev ScannerOutcome :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerOutcome

abbrev ScannerSourceTerm :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.SourceTerm

abbrev ScannerSourceStep :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.SourceStep

abbrev ScannerTargetClassification :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.TargetClassification

abbrev scannerSourceGSLT :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.sourceGSLT

abbrev scannerTargetGSLT :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.targetGSLT

abbrev scannerRealization :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.scannerRealization

abbrev scannerReachabilityNTT :=
  Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.scannerReachabilityNTT

abbrev phaseToMM2 :=
  Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.phaseToMM2

abbrev targetRowToMM2 :=
  Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.targetRowToMM2

/-- Preserve byte ownership and occurrence position before entering the MM2
scanner's source-owned request vocabulary. -/
def occurrenceToMM2 (occurrence : ByteOccurrence Atom) : ScannerByteOccurrence where
  owner := occurrence.owner
  position := occurrence.position
  byte := occurrence.byte

theorem occurrenceToMM2_injective : Function.Injective occurrenceToMM2 := by
  intro left right equal
  cases left with
  | mk leftOwner leftPosition leftByte =>
      cases right with
      | mk rightOwner rightPosition rightByte =>
          simp only [occurrenceToMM2] at equal
          injection equal with ownerEqual positionEqual byteEqual
          subst rightOwner
          subst rightPosition
          subst rightByte
          rfl

/-- The compact action vocabulary is the authored compressed action vocabulary
used by the existing MM2 scanner. -/
def actionToMM2 : Action -> CompressedAction
  | .step index => .step index
  | .save => .save
  | .unknown => .unknown

/-- The compact prefix representation has the same denotation as the compact
MM2 scanner representation. -/
theorem prefixValue_eq_compressedPrefixValue (reversePrefix : List Nat) :
    prefixValue reversePrefix =
      Mettapedia.Languages.Metamath.MM2CompressedProofExecution.compressedPrefixValue
        reversePrefix := by
  induction reversePrefix with
  | nil => rfl
  | cons digit remaining inductionHypothesis =>
      simp [prefixValue,
        Mettapedia.Languages.Metamath.MM2CompressedProofExecution.compressedPrefixValue,
        inductionHypothesis]

/-- The byte-stage faults have direct scanner counterparts.  The final branch
is deliberately a carrier-totalization fallback: `incompleteOpenIndex` is
created only by the separate end-of-input finalizer, never by
`authoredOutcome`. -/
def faultToMM2 : Fault -> ScannerFault
  | .invalidByte byte => .invalidByte byte
  | .saveOutsideCompleted phase =>
      .saveOutsideCompleted (phaseToMM2 phase)
  | .questionInsideOpenIndex reversePrefix =>
      .questionInsideOpenIndex reversePrefix
  | .incompleteOpenIndex _ => .invalidByte (UInt8.ofNat 0)

/-- Total map on source-term carriers.  Exactness for actual byte transitions
is stated separately by `authoredOutcome_maps_exact`; the end-of-input-only
fallback above is never used by that theorem. -/
def outcomeToMM2 : Outcome -> ScannerOutcome
  | .decoded actions next =>
      .decoded (actions.map actionToMM2) (phaseToMM2 next)
  | .fault reason => .fault (faultToMM2 reason)

/-- The phase map preserves the retained compact prefix exactly. -/
theorem phaseToMM2_reversePrefix (phase : Phase) :
    Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerPhase.reversePrefix
      (phaseToMM2 phase) =
      Phase.reversePrefix phase :=
  Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.phaseToMM2_reversePrefix
    phase

/-- The compact index has the same value after moving the retained prefix into
the existing MM2 scanner phase. -/
theorem indexValue_maps_exact (phase : Phase) (terminalDigit : Nat) :
    indexValue (Phase.reversePrefix phase) terminalDigit =
      Mettapedia.Languages.Metamath.MM2CompressedProofExecution.compressedIndexValue
        (Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerPhase.reversePrefix
          (phaseToMM2 phase)) terminalDigit := by
  unfold indexValue
  rw [phaseToMM2_reversePrefix, prefixValue_eq_compressedPrefixValue]
  rfl

/-- Dispatch commutes with the independently authored MM2 scanner classifier.
This is the byte-stage semantic comparison; it is separate from actual MM2
scheduler execution. -/
theorem dispatch_maps_exact
    (phase : Phase) (byte : UInt8) (byteClass : ByteClass) :
    outcomeToMM2 (dispatch phase byte byteClass) =
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.dispatchByte
        (phaseToMM2 phase) byte
          (Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.classToMM2
            byteClass) := by
  cases phase <;> cases byteClass <;>
    simp [dispatch, outcomeToMM2, faultToMM2, phaseToMM2,
      Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.phaseToMM2,
      actionToMM2,
      Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.classToMM2,
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.dispatchByte,
      Phase.reversePrefix,
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.ScannerPhase.reversePrefix,
      indexValue, prefixValue_eq_compressedPrefixValue,
      Mettapedia.Languages.Metamath.MM2CompressedProofExecution.compressedIndexValue,
      Mettapedia.Languages.Metamath.MM2CompressedProofExecution.compressedPrefixValue]

/-- The independent compact byte operation has exactly the existing scanner's
outcome at the corresponding phase and byte. -/
theorem authoredOutcome_maps_exact (phase : Phase) (byte : UInt8) :
    outcomeToMM2 (authoredOutcome phase byte) =
      Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.authoredOutcome
        (phaseToMM2 phase) byte := by
  rw [authoredOutcome_eq_targetDispatch, dispatch_maps_exact,
    Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.classToMM2_classify]
  exact
    (Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.authoredOutcome_eq_dispatch
      (phaseToMM2 phase) byte).symm

/-- Map the compact classifier's actual source GSLT carrier to the already
authored MM2 scanner source carrier. -/
def mapSourceTerm :
    SourceTerm Atom -> ScannerSourceTerm
  | .request request =>
      .request (occurrenceToMM2 request.occurrence)
        (phaseToMM2 request.phase)
  | .outcome request outcome =>
      .outcome (occurrenceToMM2 request.occurrence) (outcomeToMM2 outcome)

/-- Each actual compact source byte step maps to the existing scanner's one
semantic source step.  The target classifier/dispatch expansion is composed
separately below. -/
theorem mapSourceStep
    {source target : SourceTerm Atom}
    (step : SourceStep (scannerStage Atom) source target) :
    ScannerSourceStep (mapSourceTerm source) (mapSourceTerm target) := by
  cases step with
  | run request =>
      change ScannerSourceStep
        (.request (occurrenceToMM2 request.occurrence)
          (phaseToMM2 request.phase))
        (.outcome (occurrenceToMM2 request.occurrence)
          (outcomeToMM2 (authoredOutcome request.phase request.occurrence.byte)))
      rw [authoredOutcome_maps_exact]
      exact Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.SourceStep.run _ _

/-- The compact byte GSLT is a strict semantic source-stage realization of the
existing MM2 scanner source GSLT. -/
def sourceRealization :
    OperationalRealization (sourceGSLT Atom) scannerSourceGSLT where
  mapTerm := mapSourceTerm
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := fun step =>
    .cons ⟨mapSourceStep step⟩ (.refl _)

/-- The first bridge retains one semantic source transition rather than
silently bypassing the independently authored scanner source operation. -/
theorem sourceRealization_step_length (request : Request Atom) :
    (sourceRealization.mapStep
      (SourceStep.run (stage := scannerStage Atom) request)).length = 1 := by
  rfl

/-- Compose the semantic source bridge with the existing two-step MM2 scanner
lowering.  This is the reusable GSLT-to-GSLT transformation chain for one
compact compressed byte. -/
def realizationToMM2 :
    OperationalRealization (sourceGSLT Atom) scannerTargetGSLT :=
  sourceRealization.comp scannerRealization

/-- One actual compact byte becomes the existing classifier/dispatch path;
the source-to-source bridge adds no administrative target step. -/
theorem realizationToMM2_step_length (request : Request Atom) :
    (realizationToMM2.mapStep
      (SourceStep.run (stage := scannerStage Atom) request)).length = 2 := by
  rfl

/-- The exact target classification witnessed for an actual compact source
byte.  Its endpoint has not been supplied by a caller: it comes from the
independently authored compact source operation. -/
def sourceRunClassification (request : Request Atom) :
    ScannerTargetClassification
      (.request (occurrenceToMM2 request.occurrence)
        (phaseToMM2 request.phase))
      (.outcome (occurrenceToMM2 request.occurrence)
        (outcomeToMM2 (authoredOutcome request.phase request.occurrence.byte))) := by
  rw [authoredOutcome_maps_exact]
  rw [Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.authoredOutcome_eq_dispatch]
  exact Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.TargetClassification.classify _ _

/-- The classified intermediate state of the composed route retains precisely
the concrete MM2 row selected by the compact classifier. -/
theorem sourceRun_classification_row_exact (request : Request Atom) :
    Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classificationRow
      (.request (occurrenceToMM2 request.occurrence)
        (phaseToMM2 request.phase))
      (.outcome (occurrenceToMM2 request.occurrence)
        (outcomeToMM2 (authoredOutcome request.phase request.occurrence.byte))) =
      targetRowToMM2
        (ByteClass.row (classify request.phase request.occurrence.byte)) := by
  rw [authoredOutcome_maps_exact]
  rw [Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.authoredOutcome_eq_dispatch]
  simpa [Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classificationRow,
    Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.targetClassificationRow,
    occurrenceToMM2] using
    (Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.targetRowToMM2_classify_row
      request.phase request.occurrence.byte).symm

/-- OSLF observes the complete composite at finite macro-step scale.  Its
contravariant direction is inherited from predicate pullback, while the
realization itself remains in source-to-target execution order. -/
def realizationToMM2ReachabilityNTT :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject scannerTargetGSLT.closure)
      (oslfForwardModalObject (sourceGSLT Atom).closure) :=
  realizationToMM2.closureOSLFPullback

/-- Closure OSLF sees the same staged composition as the path-valued
realization, rather than a separate ad-hoc modal bridge. -/
theorem realizationToMM2ReachabilityNTT_comp :
    realizationToMM2ReachabilityNTT =
      scannerReachabilityNTT.comp sourceRealization.closureOSLFPullback := by
  exact OperationalRealization.closureOSLFPullback_comp
    sourceRealization scannerRealization

private def terminalARequest : Request Atom where
  occurrence :=
    { owner := .symbol "mm-compressed-bridge-unit"
      position := 0
      byte := UInt8.ofNat 65 }
  phase := .between

private def invalidRequest : Request Atom where
  occurrence :=
    { owner := .symbol "mm-compressed-bridge-unit"
      position := 1
      byte := UInt8.ofNat 48 }
  phase := .between

/-- Positive control: the first terminal byte takes the composed two-step
MM2 scanner route. -/
theorem terminal_A_composed_route_has_two_steps :
    (realizationToMM2.mapStep
      (SourceStep.run (stage := scannerStage Atom) terminalARequest)).length = 2 := by
  exact realizationToMM2_step_length terminalARequest

/-- Negative control: a malformed byte remains an explicit static MM2
invalid-byte row through the composed semantic bridge. -/
theorem invalid_byte_composed_row_is_static :
    Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classificationRow
      (.request (occurrenceToMM2 invalidRequest.occurrence)
        (phaseToMM2 invalidRequest.phase))
      (.outcome (occurrenceToMM2 invalidRequest.occurrence)
        (outcomeToMM2
          (authoredOutcome invalidRequest.phase invalidRequest.occurrence.byte))) ∈
      Mettapedia.Languages.Metamath.MM2CompressedProofExecution.compressedVerifierStaticRows := by
  rw [sourceRun_classification_row_exact]
  simpa [invalidRequest] using
    Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter.invalid_byte_mm2_row_is_static

#print axioms occurrenceToMM2_injective
#print axioms prefixValue_eq_compressedPrefixValue
#print axioms phaseToMM2_reversePrefix
#print axioms indexValue_maps_exact
#print axioms dispatch_maps_exact
#print axioms authoredOutcome_maps_exact
#print axioms mapSourceStep
#print axioms sourceRealization
#print axioms sourceRealization_step_length
#print axioms realizationToMM2
#print axioms realizationToMM2_step_length
#print axioms sourceRunClassification
#print axioms sourceRun_classification_row_exact
#print axioms realizationToMM2ReachabilityNTT
#print axioms realizationToMM2ReachabilityNTT_comp
#print axioms terminal_A_composed_route_has_two_steps
#print axioms invalid_byte_composed_row_is_static

end Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2GSLTBridge
