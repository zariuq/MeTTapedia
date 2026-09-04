import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeAuthority
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgePublishedKeyReflection

/-!
# Bridge-key reflection for the inherited live assertion workspace

After the selected launcher is removed, no inherited source row can occupy the
normal-dispatch bridge key.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLiveKeyReflection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeAuthority
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgePublishedKeyReflection
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

theorem sourceDecoratedAssertionBridgeReadyLive_bridge_key_reflects
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    AtomsWithin NormalDispatchBridgeKeyReflects
      (morkEraseSupport
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)
        decoratedDirectAssertionDirective.atom) := by
  change AtomsWithin
    (fun row => morkSupportKey row =
      morkSupportKey compressedNormalDispatchBridgeRule →
        row = compressedNormalDispatchBridgeRule) _
  exact morkEraseSupport_atomsWithin_key_reflects_of_fresh _ _ _
    (fun row member notLauncher =>
      sourceDecoratedAssertionBridgeReadySpace_bridge_key_fresh context state
        ledger scanner index cursor assertion member notLauncher)

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeLiveKeyReflection
