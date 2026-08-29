import Mettapedia.Languages.Metamath.CompressedByteClassifierMM2Adapter

/-!
# Compact compressed-byte semantic trace in MM2 classifier-row vocabulary

This is a semantic trace projection for the compact compressed-proof GSLT
transform. It uses the generic terminating-stream construction to process
supplied byte occurrences into ordered target-row events, then encodes those
rows in the public MM2 vocabulary.

It is not raw proof input for an MM2 verifier. Classifier rows are
verifier-owned static inventory; the future source-data transform must instead
emit dynamic owner/cursor/word facts and let the generated verifier select this
inventory. This module does not provide those dynamic facts, heap rows, or
verdicts, and it does not run the MM2 scheduler or inspect a fixture name.
An invalid byte remains an explicit semantic classifier trace event and stops
the source-relative artifact at that occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2StreamData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.CompressedByteClassifierCore
open Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2Adapter
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission

/-- The owner is ordinary source data; it is retained by the reified events
rather than recovered from row enumeration. -/
def streamOwner : Atom := .symbol "compressed-row-transform-owner"

def terminalA : ByteOccurrence Atom where
  owner := streamOwner
  position := 0
  byte := UInt8.ofNat 65

def invalidByte : ByteOccurrence Atom where
  owner := streamOwner
  position := 1
  byte := UInt8.ofNat 48

def sourceArtifact : Artifact (scannerStreamStage Atom) :=
  emit (scannerStreamStage Atom) 0 .between [terminalA, invalidByte]

def sourceRun : Run (scannerStreamStage Atom) .between [terminalA, invalidByte] :=
  run (scannerStreamStage Atom) 0 .between [terminalA, invalidByte]

/-- The stream row carries both a classifier row and its semantic compact
outcome. Only the classifier row is rendered in this semantic trace; the
outcome is realized later by the MM2 dispatcher, so this encoding cannot
pre-run a proof action. -/
def scannerRowToMM2 (row : ScannerStreamRow) : Atom :=
  targetRowToMM2 row.targetRow

/-- Source-relative semantic rows become exact public MM2 vocabulary atoms,
with source occurrences retained beside the trace output. -/
def classifierTrace : EncodedArtifact (scannerStreamStage Atom) Atom :=
  encodeArtifact scannerRowToMM2 sourceArtifact

def terminalAEvent : Event (scannerStreamStage Atom) :=
  eventAt (scannerStreamStage Atom) 0 .between terminalA [invalidByte]

def invalidByteEvent : Event (scannerStreamStage Atom) :=
  eventAt (scannerStreamStage Atom) 1 .completed invalidByte []

def terminalAMM2Event : EncodedEvent (scannerStreamStage Atom) Atom :=
  encodeEvent scannerRowToMM2 terminalAEvent

def invalidByteMM2Event : EncodedEvent (scannerStreamStage Atom) Atom :=
  encodeEvent scannerRowToMM2 invalidByteEvent

/-- Exact ordered output for a successful compact index followed by an
explicit malformed-byte classifier row. -/
theorem classifierTrace_events_exact :
    classifierTrace.events = [terminalAMM2Event, invalidByteMM2Event] := by
  rfl

/-- The first emitted atom is the public terminal-byte row for compact index
zero. -/
theorem terminal_A_output_exact :
    terminalAMM2Event.output = compressedTerminalByteRow 65 0 := by
  rfl

/-- The second emitted atom is an explicit invalid-byte row.  It is not a
proof action, normal label, or acceptance observation. -/
theorem invalid_byte_output_exact :
    invalidByteMM2Event.output = compressedInvalidByteRow 48 := by
  rfl

/-- Encoding preserves every source occurrence position in order. -/
theorem classifierTrace_positions_exact :
    classifierTrace.events.map (fun event => event.source.position) = [0, 1] := by
  rfl

/-- The source transform stops at the malformed occurrence and retains no
invented row after it. -/
theorem sourceArtifact_stops_at_invalid_byte :
    sourceArtifact.endpoint =
      .stopped .completed invalidByte [] (.invalidByte (UInt8.ofNat 48)) := by
  rfl

theorem classifierTrace_preserves_source_endpoint :
    classifierTrace.endpoint = sourceArtifact.endpoint :=
  encodeArtifact_endpoint_exact scannerRowToMM2 sourceArtifact

theorem sourceRun_source_length : sourceRun.sourcePath.length = 2 := by
  rfl

theorem sourceRun_target_length : sourceRun.targetPath.length = 4 := by
  rfl

/-- The emitted artifact is carried by the exact classifier/dispatch GSLT
realization; encoding its rows adds no semantic transition. -/
theorem sourceRun_maps_exact :
    (Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.realization
      (scannerStreamStage Atom)).mapRoute sourceRun.sourcePath =
      sourceRun.targetPath :=
  sourceRun.map_exact

/-- Both trace rows are members of the public static MM2 verifier inventory.
This proves target-vocabulary alignment only; it does not authorize these rows
as caller-supplied MM2 input. -/
theorem terminal_A_output_is_static :
    terminalAMM2Event.output ∈ compressedVerifierStaticRows := by
  rw [terminal_A_output_exact]
  simpa [targetRowToMM2, ByteClass.row, classify] using terminal_A_mm2_row_is_static

theorem invalid_byte_output_is_static :
    invalidByteMM2Event.output ∈ compressedVerifierStaticRows := by
  rw [invalid_byte_output_exact]
  simpa [targetRowToMM2, ByteClass.row, classify] using invalid_byte_mm2_row_is_static

#print axioms classifierTrace_events_exact
#print axioms terminal_A_output_exact
#print axioms invalid_byte_output_exact
#print axioms classifierTrace_positions_exact
#print axioms sourceArtifact_stops_at_invalid_byte
#print axioms classifierTrace_preserves_source_endpoint
#print axioms sourceRun_source_length
#print axioms sourceRun_target_length
#print axioms sourceRun_maps_exact
#print axioms terminal_A_output_is_static
#print axioms invalid_byte_output_is_static

end Mettapedia.Languages.Metamath.CompressedByteClassifierCore.MM2StreamData
