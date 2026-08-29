import Mettapedia.Languages.Metamath.CompressedByteClassifierMM2GSLTBridge
import Mettapedia.Languages.Metamath.MM2CompressedProofSingleIndexAcceptCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofInvalidByteCanary

/-!
# Compact byte GSLT boundary to a bounded MM2 execution

This module joins one semantic byte-stage transformation to a small assembled
MM2 execution control.  It proves the exact classified row selected by the
compact GSLT is present in a concrete owner-bound scanner program, then reuses
the independently checked bounded execution witness for that same program.

The scope is deliberately bounded: one `A` byte selecting heap entry zero and
one malformed byte.  It is an execution boundary for the reusable byte-stage
transformation, not a claim of arbitrary compressed-proof adequacy.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2ExecutionBridge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2GSLTBridge

/-- The source request whose owner and position agree with the existing
single-index assembled execution control. -/
def terminalARequest : Request Atom where
  occurrence :=
    { owner := canaryProof
      position := 0
      byte := UInt8.ofNat 65 }
  phase := .between

/-- The concrete classifier observation determined by the compact source
request. -/
def terminalAClassifierRow : Atom :=
  compressedTerminalByteRow 65 0

/-- The GSLT-selected row is exactly the concrete terminal classifier row in
the bounded MM2 execution program. -/
theorem terminal_A_source_classifies_to_execution_row :
    Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classificationRow
      (.request (occurrenceToMM2 terminalARequest.occurrence)
        (phaseToMM2 terminalARequest.phase))
      (.outcome (occurrenceToMM2 terminalARequest.occurrence)
        (outcomeToMM2
          (authoredOutcome terminalARequest.phase
            terminalARequest.occurrence.byte))) =
      terminalAClassifierRow := by
  rw [sourceRun_classification_row_exact]
  rfl

/-- The exact row selected by the semantic transformation occurs in the same
bounded program for which the scheduler witness below was checked.  This is a
row-to-program membership fact, not a fresh replay of the scheduler. -/
theorem terminal_A_execution_program_contains_transformed_row :
    terminalAClassifierRow ∈ compressedSingleIndexProgram := by
  simp [terminalAClassifierRow, compressedSingleIndexProgram]

/-- The scheduler reaches the accepted observation from the same bounded
assembled program.  Its computation is deliberately imported rather than
re-elaborated here. -/
theorem terminal_A_scheduler_accepts :
    canaryAccepted ∈
      (cReflectiveSourceWorkQueueRunN .leaveInert 16
        compressedSingleIndexProgram).1 :=
  MM2CompressedProofSingleIndexAcceptCanary.compressed_single_index_run_accepts

/-- A malformed source byte uses the same semantic route, but selects the
strict invalid-byte classifier row rather than a compact heap action. -/
def invalidByteRequest : Request Atom where
  occurrence :=
    { owner := Mettapedia.Languages.Metamath.MM2CompressedProofInvalidByteCanary.proofOwner
      position := 0
      byte := UInt8.ofNat 33 }
  phase := .between

/-- The invalid-byte source request selects the exact public invalid-byte
classifier row used by the assembled MM2 fault directive. -/
theorem invalid_byte_source_classifies_to_execution_row :
    Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT.classificationRow
      (.request (occurrenceToMM2 invalidByteRequest.occurrence)
        (phaseToMM2 invalidByteRequest.phase))
      (.outcome (occurrenceToMM2 invalidByteRequest.occurrence)
        (outcomeToMM2
          (authoredOutcome invalidByteRequest.phase
            invalidByteRequest.occurrence.byte))) =
      compressedInvalidByteRow 33 := by
  rw [sourceRun_classification_row_exact]
  rfl

/-- The corresponding assembled MM2 rule produces the explicit malformed-byte
fault, not a proof action. -/
theorem invalid_byte_execution_faults :
    Mettapedia.Languages.Metamath.MM2CompressedProofInvalidByteCanary.invalidFault ∈
      cFireReflectiveSourceExecFact
        Mettapedia.Languages.Metamath.MM2CompressedProofInvalidByteCanary.invalidProgram
        compressedInvalidByteDirective :=
  MM2CompressedProofInvalidByteCanary.strict_invalid_byte_faults

#print axioms terminal_A_source_classifies_to_execution_row
#print axioms terminal_A_execution_program_contains_transformed_row
#print axioms terminal_A_scheduler_accepts
#print axioms invalid_byte_source_classifies_to_execution_row
#print axioms invalid_byte_execution_faults

end Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2ExecutionBridge
