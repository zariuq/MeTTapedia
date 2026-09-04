import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation

/-!
# Physical authority at the compressed assertion bridge

The compressed assertion launcher publishes an owner-bound bridge executable.
Physical support uses compact keys, so key-level presence alone is not enough
to identify the live representative.  This module proves that no pre-launch
source row can occupy the bridge key.  Separate launch and drain modules use
that freshness result to recover and preserve exact nominal membership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeAuthority

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- No authored/source-derived row in the pre-launch assertion workspace can
occupy the physical key reserved for the compiler-captured bridge. -/
theorem sourceDecoratedAssertionBridgeReadySpace_bridge_key_fresh
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) {row : Atom}
    (member : row ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)
    (notLauncher : row ≠ decoratedDirectAssertionDirective.atom) :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule := by
  rcases (mem_sourceDecoratedAssertionBridgeReadySpace_iff context state ledger
      scanner index cursor assertion row).mp member with request | capture
  rcases (mem_sourceDecoratedAssertionRequestSpace_iff context state ledger
      scanner index cursor assertion row).mp request with canonical | additional
  · exact canonicalAssertionSpace_key_ne_bridge
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) canonical notLauncher
  · exact additionalRows_key_ne_bridge context state ledger scanner index
      assertion additional
  · exact captureRows_key_ne_bridge capture

#print axioms sourceDecoratedAssertionBridgeReadySpace_bridge_key_fresh

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeAuthority
