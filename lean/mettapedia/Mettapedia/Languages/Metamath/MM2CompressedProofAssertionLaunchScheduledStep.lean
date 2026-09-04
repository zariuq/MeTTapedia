import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchScheduler

/-!
# Assembled scheduled compressed assertion step

The matcher slice and cursor scheduler inventory are joined only after their
support theorems have been established independently.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchScheduledStep

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchScheduler
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSupport
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectAssertionScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- A proof-relevant scheduler inventory keeps the executable rows and their
selected continuation at one compact interface. -/
structure DirectAssertionSupportInterface where
  rows : List SourceExecFact
  selected :
    selectNextScheduled rows = some speculativeDirectAssertionDirective

/-- Scheduler-visible inventory after the proof-valued direct probe has been
exhausted.  Downstream proofs consume the interface projection rather than
re-elaborating the embedded executable atoms. -/
def directAssertionSupportInterface : DirectAssertionSupportInterface :=
  ⟨_, select_direct_assertion_from_canonical_inventory⟩

@[simp] theorem directAssertionSupportInterface_rows :
    directAssertionSupportInterface.rows =
      [speculativeDirectAssertionDirective, compressedProofStepDirective,
       compressedAssertionLaunchDirective, compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective] := by
  unfold directAssertionSupportInterface
  rfl

theorem canonicalDirectAssertionSpace_supported
    (context : DirectAssertionContext) :
    cSupportedSourceExecFacts (canonicalDirectAssertionSpace context) =
      directAssertionSupportInterface.rows := by
  unfold canonicalDirectAssertionSpace cSupportedSourceExecFacts
  rw [List.filterMap_append]
  change cSupportedSourceExecFacts (directAssertionMatchSlice context) ++
      cSupportedSourceExecFacts directAssertionSchedulerFrame = _
  rw [directAssertionMatchSlice_supported,
    directAssertionSchedulerFrame_supported]
  exact directAssertionSupportInterface_rows.symm

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchScheduledStep
