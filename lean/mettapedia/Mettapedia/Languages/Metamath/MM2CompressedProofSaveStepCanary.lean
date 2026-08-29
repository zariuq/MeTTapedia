import Mettapedia.Languages.Metamath.MM2CompressedProofHeapProtocolCanary

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
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapProtocolCanary
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

#print axioms scheduled_save_step_matches_occurrence_protocol

end Mettapedia.Languages.Metamath.MM2CompressedProofSaveStepCanary
