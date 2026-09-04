import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLaunchReflection

/-!
# Exact physical membership of the compressed normal-dispatch bridge

Support-key presence from the authored sink reflects to nominal membership
because the complete launch result has no bridge-key masquerader.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeExactMembership

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLaunchReflection
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

theorem sourceAssertionBridgeLaunchResult_bridge_mem
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)) :
    compressedNormalDispatchBridgeRule ∈
      sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion) := by
  have directivePresent : decoratedDirectAssertionDirective.atom ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion := by
    simp [sourceDecoratedAssertionBridgeReadySpace,
      sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  have support := physical_decorated_assertion_launch_support_present
    (sourceDecoratedAssertionBridgeReadySpace_exact_match context state ledger
      scanner index cursor assertion)
    listNodup morkNodup directivePresent
  apply mem_of_morkSupportContains_of_key_reflection support.2.2.2.2.2
  exact sourceAssertionBridgeLaunchResult_bridge_key_reflects context state
    ledger scanner index cursor assertion listNodup morkNodup directivePresent

#print axioms sourceAssertionBridgeLaunchResult_bridge_mem

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeExactMembership
