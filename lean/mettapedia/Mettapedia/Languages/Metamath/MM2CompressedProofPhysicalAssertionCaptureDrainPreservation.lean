import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionDataDrainPreservation
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoffCaptureFrame

/-!
# Normal-handoff capture preservation across the assertion drain

The compiler-owned loader and finish captures are ordinary data rows.  They
therefore survive the four obsolete executable probes without exposing the
captured rules to the drain proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionCaptureDrainPreservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionDataDrainPreservation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoffCaptureFrame

/-- Both compiler-owned normal-handoff captures survive the complete physical
predecessor drain as exact nominal rows. -/
theorem normalHandoffBridgeCaptureRows_survive_predecessor_drain
    (space : List Atom) (ready : AssertionPredecessorDrainReady space)
    (loaderMember : compressedNormalHandoffLoaderCaptureRow ∈ space)
    (finishMember : compressedNormalHandoffFinishCaptureRow ∈ space) :
    compressedNormalHandoffLoaderCaptureRow ∈
        afterLookupAdvanceProbe space ∧
      compressedNormalHandoffFinishCaptureRow ∈
        afterLookupAdvanceProbe space := by
  constructor
  · exact expression_symbol_row_survives_predecessor_drain space ready
      "mm-internal-compressed-normal-handoff-loader"
      [compressedNormalHandoffLoadRule]
      (by decide) (by decide) (by decide) loaderMember
  · exact expression_symbol_row_survives_predecessor_drain space ready
      "mm-internal-compressed-normal-handoff-finish"
      [compressedNormalHandoffFinishRule]
      (by decide) (by decide) (by decide) finishMember

/-- The two exact compiler captures survive into any endpoint related by the
physical four-step drain. -/
theorem normalHandoffBridgeCaptureRows_survive_physical_predecessor_drain
    (space final : List Atom) (ready : AssertionPredecessorDrainReady space)
    (drain : PhysicalAssertionPredecessorDrain space final)
    (loaderMember : compressedNormalHandoffLoaderCaptureRow ∈ space)
    (finishMember : compressedNormalHandoffFinishCaptureRow ∈ space) :
    compressedNormalHandoffLoaderCaptureRow ∈ final ∧
      compressedNormalHandoffFinishCaptureRow ∈ final := by
  constructor
  · exact expression_symbol_row_survives_physical_predecessor_drain
      space final ready drain
      "mm-internal-compressed-normal-handoff-loader"
      [compressedNormalHandoffLoadRule]
      (by decide) (by decide) (by decide) loaderMember
  · exact expression_symbol_row_survives_physical_predecessor_drain
      space final ready drain
      "mm-internal-compressed-normal-handoff-finish"
      [compressedNormalHandoffFinishRule]
      (by decide) (by decide) (by decide) finishMember

#print axioms normalHandoffBridgeCaptureRows_survive_predecessor_drain
#print axioms normalHandoffBridgeCaptureRows_survive_physical_predecessor_drain

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionCaptureDrainPreservation
