import Mettapedia.GSLT.Core.TerminatingStreamingLinkedInventory
import Mettapedia.Languages.Metamath.CompressedByteClassifierCore

/-!
# Reified two-byte compact-index profile

This small profile connects one concrete Appendix-B multi-byte compact index
to the reusable terminating-stream and linked-inventory GSLT stages. The
source bytes are retained as occurrences, the classifier emits one target row
per byte, and the linked inventory carries those rows into a later verifier
stage. No normal proof labels are expanded here.

The `U A` spine is deliberately chosen because `U` opens a base-five prefix
and the following `A` selects index twenty. The companion trailing-`U`
control reaches the explicit end-of-input fault instead of inventing a
terminal index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CompressedByteMultiByteIndexProfile

open Mettapedia.GSLT
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission.LinkedInventory
open Mettapedia.GSLT.LinkedInventoryLoader
open Mettapedia.Languages.Metamath.CompressedByteClassifierCore

/-- The first Appendix-B continuation byte, retained as source occurrence
zero rather than inferred from a container position. -/
def prefixU : ByteOccurrence Unit where
  owner := ()
  position := 0
  byte := UInt8.ofNat 85

/-- The terminal byte completing the preceding prefix. -/
def terminalA : ByteOccurrence Unit where
  owner := ()
  position := 1
  byte := UInt8.ofNat 65

/-- The next terminal byte, used by the out-of-range-header control. -/
def terminalB : ByteOccurrence Unit where
  owner := ()
  position := 1
  byte := UInt8.ofNat 66

/-- A second prefix occurrence is distinct even though it has the same byte
value as `prefixU`. -/
def secondPrefixU : ByteOccurrence Unit where
  owner := ()
  position := 1
  byte := UInt8.ofNat 85

def questionAfterNestedPrefix : ByteOccurrence Unit where
  owner := ()
  position := 2
  byte := UInt8.ofNat 63

def multiByteIndexBytes : List (ByteOccurrence Unit) := [prefixU, terminalA]

/-- The semantic source stream and its classifier/dispatcher target route. -/
def multiByteIndexStream :
    StreamRun (scannerStreamStage Unit) .between multiByteIndexBytes :=
  runStream (scannerStreamStage Unit) .between multiByteIndexBytes

/-- The source-relative target-row artifact for the same stream. -/
def multiByteIndexRowRun :
    Run (scannerStreamStage Unit) .between multiByteIndexBytes :=
  run (scannerStreamStage Unit) 0 .between multiByteIndexBytes

def multiByteIndexRowArtifact : Artifact (scannerStreamStage Unit) :=
  multiByteIndexRowRun.artifact

def multiByteIndexClassifierRows : List ScannerStreamRow :=
  outputRows (fun row : ScannerStreamRow => row) multiByteIndexRowArtifact

/-- The final generic occurrence-indexed data artifact consumed by a later
MM2 verifier phase. It contains classifier rows, not decompressed labels. -/
def multiByteIndexInventory : ReifiedArtifact ScannerStreamRow :=
  lowerRun (fun row : ScannerStreamRow => row) multiByteIndexRowRun

/-- `U` opens the least-significant-first prefix state. -/
theorem prefixU_opens_index_prefix :
    authoredOutcome .between prefixU.byte = .decoded [] (.open [1]) := by
  decide +kernel

/-- The next `A` consumes that prefix and selects compact index twenty. -/
theorem terminalA_after_prefixU_selects_index_twenty :
    authoredOutcome (.open [1]) terminalA.byte =
      .decoded [.step 20] .completed := by
  decide +kernel

/-- The neighboring terminal byte computes the next compact index. Whether
that index is admitted remains the downstream header/heap machine's job. -/
theorem terminalB_after_prefixU_selects_index_twenty_one :
    authoredOutcome (.open [1]) terminalB.byte =
      .decoded [.step 21] .completed := by
  decide +kernel

/-- A second continuation extends the retained least-significant-first
prefix rather than overwriting it. -/
theorem secondPrefixU_extends_open_index :
    authoredOutcome (.open [1]) secondPrefixU.byte =
      .decoded [] (.open [1, 1]) := by
  decide +kernel

/-- A question marker has no ordinary unknown-step meaning while a nested
numeric index remains open. -/
theorem question_after_nested_prefix_faults :
    authoredOutcome (.open [1, 1]) questionAfterNestedPrefix.byte =
      .fault (.questionInsideOpenIndex [1, 1]) := by
  decide +kernel

/-- This profile has no hidden expansion: two byte occurrences and the
explicit finishing transition make a three-step source route. -/
theorem multiByteIndexStream_source_length :
    multiByteIndexStream.sourcePath.length = 3 := by
  rfl

/-- Each source byte remains classifier then dispatcher in the target route;
the end event remains explicit. -/
theorem multiByteIndexStream_target_length :
    multiByteIndexStream.targetPath.length = 5 := by
  rfl

theorem multiByteIndexStream_endpoint :
    multiByteIndexStream.endpoint = .finished .completed := by
  rfl

theorem multiByteIndexStream_maps_exact :
    (scannerStreamRealization Unit).mapRoute multiByteIndexStream.sourcePath =
      multiByteIndexStream.targetPath :=
  multiByteIndexStream.map_exact

/-- Reified rows retain both source positions and the phase threaded by the
source stream. -/
theorem multiByteIndexRowArtifact_events :
    multiByteIndexRowArtifact.events =
      [eventAt (scannerStreamStage Unit) 0 .between prefixU [terminalA],
       eventAt (scannerStreamStage Unit) 1 (.open [1]) terminalA []] := by
  rfl

theorem multiByteIndexRowArtifact_endpoint :
    multiByteIndexRowArtifact.endpoint = .finished .completed := by
  rfl

theorem multiByteIndexRowRun_maps_exact :
    (Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.realization
      (scannerStreamStage Unit)).mapRoute multiByteIndexRowRun.sourcePath =
      multiByteIndexRowRun.targetPath :=
  multiByteIndexRowRun.map_exact

/-- The target-data boundary has precisely the prefix row followed by the
terminal row carrying compact action twenty. -/
theorem multiByteIndexClassifierRows_exact :
    multiByteIndexClassifierRows =
      [{ targetRow := .prefixByte 85 1
         outcome := .decoded [] (.open [1]) },
       { targetRow := .terminalByte 65 0
         outcome := .decoded [.step 20] .completed }] := by
  rfl

/-- The generic linked-row codec recovers the exact two classifier rows. -/
theorem multiByteIndexInventory_decodes_exact :
    decodeInventory? multiByteIndexInventory.target =
      some multiByteIndexClassifierRows := by
  simpa [multiByteIndexInventory, multiByteIndexClassifierRows,
    multiByteIndexRowArtifact] using
    lowerRun_decodes_exact (fun row : ScannerStreamRow => row) multiByteIndexRowRun

/-- Occurrence-indexed loading consumes exactly one row per compact byte;
equal output values could not shorten this route. -/
theorem multiByteIndexInventory_load_length :
    (complete multiByteIndexClassifierRows).length = 2 := by
  rw [multiByteIndexClassifierRows_exact]
  rfl

/-- A trailing prefix finishes the byte stream with an open prefix state. -/
def trailingPrefixUStream :
    StreamRun (scannerStreamStage Unit) .between [prefixU] :=
  runStream (scannerStreamStage Unit) .between [prefixU]

theorem trailingPrefixUStream_endpoint :
    trailingPrefixUStream.endpoint = .finished (.open [1]) := by
  rfl

/-- The separate source-owned finalizer turns that retained open prefix into
the explicit incomplete-index fault. -/
theorem trailingPrefixU_finalization_fault :
    finalize (.open [1]) = .fault (.incompleteOpenIndex [1]) := by
  rfl

theorem trailingPrefixU_finalizer_target_length :
    (finalizerRealization.mapStep
      (Mettapedia.GSLT.ClassifierLowering.SourceStep.run
        (stage := finalizerStage) (.open [1]))).length = 2 := by
  exact finalizerRealization_step_length (.open [1])

/-- A nested-prefix error stops at its actual third byte. The remaining input
is empty here, but the stopped endpoint retains the open-prefix phase. -/
def nestedPrefixQuestionStream :
    StreamRun (scannerStreamStage Unit) .between
      [prefixU, secondPrefixU, questionAfterNestedPrefix] :=
  runStream (scannerStreamStage Unit) .between
    [prefixU, secondPrefixU, questionAfterNestedPrefix]

theorem nestedPrefixQuestionStream_endpoint :
    nestedPrefixQuestionStream.endpoint =
      .stopped (.open [1, 1]) questionAfterNestedPrefix []
        (.questionInsideOpenIndex [1, 1]) := by
  rfl

theorem nestedPrefixQuestionStream_source_length :
    nestedPrefixQuestionStream.sourcePath.length = 3 := by
  rfl

theorem nestedPrefixQuestionStream_target_length :
    nestedPrefixQuestionStream.targetPath.length = 6 := by
  rfl

#print axioms prefixU_opens_index_prefix
#print axioms terminalA_after_prefixU_selects_index_twenty
#print axioms terminalB_after_prefixU_selects_index_twenty_one
#print axioms secondPrefixU_extends_open_index
#print axioms question_after_nested_prefix_faults
#print axioms multiByteIndexStream_source_length
#print axioms multiByteIndexStream_target_length
#print axioms multiByteIndexStream_endpoint
#print axioms multiByteIndexStream_maps_exact
#print axioms multiByteIndexRowArtifact_events
#print axioms multiByteIndexRowArtifact_endpoint
#print axioms multiByteIndexRowRun_maps_exact
#print axioms multiByteIndexClassifierRows_exact
#print axioms multiByteIndexInventory_decodes_exact
#print axioms multiByteIndexInventory_load_length
#print axioms trailingPrefixUStream_endpoint
#print axioms trailingPrefixU_finalization_fault
#print axioms trailingPrefixU_finalizer_target_length
#print axioms nestedPrefixQuestionStream_endpoint
#print axioms nestedPrefixQuestionStream_source_length
#print axioms nestedPrefixQuestionStream_target_length

end Mettapedia.Languages.Metamath.CompressedByteMultiByteIndexProfile
