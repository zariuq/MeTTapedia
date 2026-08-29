import Mettapedia.GSLT.Core.TerminatingStreamingFinalization
import Mettapedia.Languages.Metamath.CompressedByteClassifierCore

/-!
# Composing compressed-byte scanning with end-of-input finalization

The compact byte scanner and end-of-input finalizer are independently
authored GSLT stages.  This module joins them through the reusable terminating
stream/finalizer construction: ordinary bytes retain their scanner
classification and dispatch, while an empty input suffix invokes the distinct
finalizer classifier and dispatch.

This is a semantic GSLT-to-GSLT composition.  It neither decompresses a proof
nor invokes the MM2 scheduler; the later MM2 inventory and dynamic-data
bridges remain separate realization stages.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.CompressedByteClassifierCore.FinalizationGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization

abbrev CombinedSourceTerm (Owner : Type) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.SourceTerm
    Phase (ByteOccurrence Owner) Fault FinalOutcome

abbrev CombinedTargetTerm (Owner : Type) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.TargetTerm
    Phase (ByteOccurrence Owner) Fault FinalOutcome ByteClass
      ScannerStreamRow EndClass EndRow

/-- The combined authored GSLT: scan compact bytes, then explicitly finalize
only after the source suffix is empty. -/
def sourceGSLT (Owner : Type) : GSLT :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.sourceGSLT
    (scannerStreamStage Owner) finalizerStage

/-- The target GSLT retains both the scanner's byte rows and the finalizer's
end-of-input row as separate classified intermediate states. -/
def targetGSLT (Owner : Type) : GSLT :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.targetGSLT
    (scannerStreamStage Owner) finalizerStage

def realization (Owner : Type) :
    OperationalRealization (sourceGSLT Owner) (targetGSLT Owner) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.realization
    (scannerStreamStage Owner) finalizerStage

/-- Closure OSLF observes the actual composed semantic route at macro-step
scale; it is not a separate hand-written modal account. -/
def reachabilityNTT (Owner : Type) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.reachabilityNTT
    (scannerStreamStage Owner) finalizerStage

private def terminalA : ByteOccurrence Unit where
  owner := ()
  position := 0
  byte := UInt8.ofNat 65

private def invalidOpenByte : ByteOccurrence Unit where
  owner := ()
  position := 0
  byte := UInt8.ofNat 48

/-- A complete compact byte stream is a single composed GSLT run: the byte
first reaches its completed scanner phase, then—and only after the input is
empty—the finalizer reaches the complete outcome. -/
def terminalAThenFinalize :
    Run (scannerStreamStage Unit) finalizerStage .between [terminalA] :=
  run (scannerStreamStage Unit) finalizerStage .between [terminalA]

theorem terminal_A_then_finalize_endpoint :
    terminalAThenFinalize.endpoint =
      .terminal (.finalized .completed .complete) := by
  rfl

theorem terminal_A_then_finalize_source_length :
    terminalAThenFinalize.sourcePath.length = 2 := by
  rfl

theorem terminal_A_then_finalize_target_length :
    terminalAThenFinalize.targetPath.length = 4 := by
  rfl

theorem terminal_A_then_finalize_maps_exact :
    (realization Unit).mapRoute terminalAThenFinalize.sourcePath =
      terminalAThenFinalize.targetPath :=
  terminalAThenFinalize.map_exact

/-- A malformed compact byte stops at its own source occurrence.  The
finalizer is not invoked on this nonempty failing prefix. -/
def invalidOpenStopsBeforeFinalizer :
    Run (scannerStreamStage Unit) finalizerStage (.open [1]) [invalidOpenByte] :=
  run (scannerStreamStage Unit) finalizerStage (.open [1]) [invalidOpenByte]

theorem invalid_open_stops_before_finalizer_endpoint :
    invalidOpenStopsBeforeFinalizer.endpoint =
      .terminal (.stopped (.open [1]) invalidOpenByte []
        (.invalidByte (UInt8.ofNat 48))) := by
  rfl

theorem invalid_open_stops_before_finalizer_target_length :
    invalidOpenStopsBeforeFinalizer.targetPath.length = 2 := by
  rfl

private def openPrefixPhase : Phase := .open [1]

/-- Positive finalizer control: an already completed compact proof reaches a
normal completed outcome at end of input. -/
theorem completed_end_is_complete :
    finalizerStage.authoredRun .completed = .complete := by
  rfl

/-- Negative finalizer control: an unfinished numeric prefix reaches an
explicit incomplete-index fault at end of input. -/
theorem open_prefix_end_is_fault :
    finalizerStage.authoredRun openPrefixPhase =
      .fault (.incompleteOpenIndex [1]) := by
  rfl

def openPrefixFinishStep :
    SourceStep (scannerStreamStage Unit) finalizerStage
      (.running openPrefixPhase [])
      (.terminal (.finalized openPrefixPhase
        (.fault (.incompleteOpenIndex [1])))) :=
  .finish openPrefixPhase

/-- The incomplete-prefix finalization is not a shortcut: it retains target
classification followed by target dispatch. -/
theorem open_prefix_finish_has_two_target_steps :
    ((realization Unit).mapStep openPrefixFinishStep).length = 2 := by
  change
    (Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.finishPath
      (scannerStreamStage Unit) finalizerStage openPrefixPhase).length = 2
  exact
    Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.finishPath_length
      (scannerStreamStage Unit) finalizerStage openPrefixPhase

def completedFinishStep :
    SourceStep (scannerStreamStage Unit) finalizerStage
      (.running Phase.completed [])
      (.terminal (.finalized Phase.completed FinalOutcome.complete)) :=
  .finish Phase.completed

/-- Completion uses the same two-step target shape rather than a special
direct accept edge. -/
theorem completed_finish_has_two_target_steps :
    ((realization Unit).mapStep completedFinishStep).length = 2 := by
  change
    (Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.finishPath
      (scannerStreamStage Unit) finalizerStage Phase.completed).length = 2
  exact
    Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization.finishPath_length
      (scannerStreamStage Unit) finalizerStage Phase.completed

#print axioms realization
#print axioms reachabilityNTT
#print axioms terminal_A_then_finalize_endpoint
#print axioms terminal_A_then_finalize_source_length
#print axioms terminal_A_then_finalize_target_length
#print axioms terminal_A_then_finalize_maps_exact
#print axioms invalid_open_stops_before_finalizer_endpoint
#print axioms invalid_open_stops_before_finalizer_target_length
#print axioms completed_end_is_complete
#print axioms open_prefix_end_is_fault
#print axioms open_prefix_finish_has_two_target_steps
#print axioms completed_finish_has_two_target_steps

end Mettapedia.Languages.Metamath.CompressedByteClassifierCore.FinalizationGSLT
