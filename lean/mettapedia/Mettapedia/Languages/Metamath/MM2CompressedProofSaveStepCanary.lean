import Mettapedia.Languages.Metamath.MM2CompressedProofHeapProtocolCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# One scheduled MM2 save step

This file qualifies only the concrete `Z` save transition.  The preceding heap
lookup is covered by its own bounded modules, while their semantic composition
is provided by the occurrence-heap protocol.  Keeping these checks separate
avoids normalizing the combined compressed program.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSaveStepCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapProtocolCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def saveScanBefore : Atom :=
  .expression
    [.symbol "mm-compressed-scan", canaryScope, canaryProof, natAtom 0,
      compressedWordAtom [90], .symbol "mm-compressed-just-completed-step",
      listAtom natAtom []]

def saveMachineBefore : Atom :=
  .expression
    [.symbol "mm-compressed-machine", canaryScope, canaryProof,
      compressedIndexCodeAtom [] 1, compressedIndexCodeAtom [] 1,
      compressedIndexCodeAtom [] 1]

def saveStackTopCell : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", canaryProof,
      compressedIndexCodeAtom [] 0, canaryNode]

def saveProgram : List Atom :=
  [compressedSaveRule, saveScanBefore, saveMachineBefore,
    canaryStackSuccessor, saveStackTopCell, canaryNodeZero,
    canaryHeapSuccessor] ++ compressedAZCaptureRows

def saveAfter : List Atom :=
  cFireReflectiveSourceExecFact saveProgram compressedSaveDirective

def saveMachineAfter : Atom :=
  .expression
    [.symbol "mm-compressed-machine", canaryScope, canaryProof,
      compressedIndexCodeAtom [] 2, compressedIndexCodeAtom [] 1,
      compressedIndexCodeAtom [] 1]

def saveScanAfter : Atom :=
  .expression
    [.symbol "mm-compressed-scan", canaryScope, canaryProof, natAtom 0,
      listAtom natAtom [], .symbol "mm-compressed-between-steps",
      listAtom natAtom []]

def semanticSaveBefore :
    State Atom Atom ProofNodeValue Unit :=
  ⟨canaryProof, canarySemanticHeap,
    .save canaryProof canaryProofOccurrence⟩

def semanticSaveAfter :
    State Atom Atom ProofNodeValue Unit :=
  ⟨canaryProof,
    canarySemanticHeap ++ [.occurrence canaryProofOccurrence],
    .saved canaryProof canarySemanticHeap.length canaryProofOccurrence⟩

/-- The ordinary scheduled MM2 step selects the authored save directive and
emits the exact semantic heap row and occurrence-sensitive receipt. -/
theorem scheduled_save_step_matches_occurrence_protocol :
    cReflectiveSourceWorkQueueStep .leaveInert saveProgram = some saveAfter ∧
      canarySavedHeapOne ∈ saveAfter ∧
      canarySaveReceiptOne ∈ saveAfter ∧
      saveMachineAfter ∈ saveAfter ∧
      saveScanAfter ∈ saveAfter ∧
      canaryUnexpectedNodeOne ∉ saveAfter := by
  decide +kernel

/-- The scheduled list-machine transition is the exact executable target
step recognized by OSLF, rather than a separately reconstructed phase-local
firing. -/
theorem scheduled_save_step_inhabits_exact_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT .leaveInert)).satisfies saveProgram
        (reflectiveNativeListExactTargetNativeType .leaveInert saveAfter).pred := by
  apply
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert saveProgram saveAfter).2
  exact scheduled_save_step_matches_occurrence_protocol.1

/-- First concrete save commuting square.  The semantic heap appends the
selected occurrence, the actual scheduler executes the emitted MM2 rule, the
exact encoded heap pointer and receipt appear, and no fresh proof node is
invented. -/
structure ScheduledSaveCommutingSquare : Prop where
  semanticStep : Step semanticSaveBefore semanticSaveAfter
  concreteStep :
    cReflectiveSourceWorkQueueStep .leaveInert saveProgram = some saveAfter
  nativeStep :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT .leaveInert)).satisfies saveProgram
        (reflectiveNativeListExactTargetNativeType .leaveInert saveAfter).pred
  heapRowExact :
    heapProofRow canaryProof canarySemanticHeap.length canaryProofOccurrence ∈
      saveAfter
  receiptExact :
    saveReceiptRow canaryProof canarySemanticHeap.length
        canaryProofOccurrence ∈ saveAfter
  machineExact : saveMachineAfter ∈ saveAfter
  scannerExact : saveScanAfter ∈ saveAfter
  noFreshNode : canaryUnexpectedNodeOne ∉ saveAfter

theorem scheduled_save_commuting_square : ScheduledSaveCommutingSquare := by
  obtain ⟨concreteStep, heapRow, receipt, machine, scanner, noFreshNode⟩ :=
    scheduled_save_step_matches_occurrence_protocol
  exact
    { semanticStep := Step.save canaryProof canarySemanticHeap
        canaryProofOccurrence
      concreteStep := concreteStep
      nativeStep := scheduled_save_step_inhabits_exact_native_type
      heapRowExact := by
        change heapProofRow canaryProof 1 canaryProofOccurrence ∈ saveAfter
        rw [canary_saved_heap_one_is_encoded_occurrence]
        exact heapRow
      receiptExact := by
        change saveReceiptRow canaryProof 1 canaryProofOccurrence ∈ saveAfter
        rw [canary_save_receipt_is_encoded_occurrence]
        exact receipt
      machineExact := machine
      scannerExact := scanner
      noFreshNode := noFreshNode }

#print axioms scheduled_save_step_matches_occurrence_protocol
#print axioms scheduled_save_step_inhabits_exact_native_type
#print axioms scheduled_save_commuting_square

end Mettapedia.Languages.Metamath.MM2CompressedProofSaveStepCanary
