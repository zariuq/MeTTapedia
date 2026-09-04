import Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalNormalBridgeCapability
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch

/-!
# Source-relative normal-bridge capability

The only normal-dispatch bridge payload admitted by a source-derived decorated
assertion request is the bridge present in the compiled verifier frame.
Source-derived machine rows are dynamic data and cannot carry that capability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceNormalBridgeCapability

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection

theorem decodeNormalDispatchBridgeCapture_eq_none_of_dynamic
    {row : Atom} (dynamic : isDynamicRow row = true) :
    decodeNormalDispatchBridgeCapture row = none := by
  unfold decodeNormalDispatchBridgeCapture
  split <;> simp_all [isDynamicRow, dynamicRowHeads]

theorem sourceAssertionAdditionalRows_bridge_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) :
    NormalDispatchBridgeCapabilities compressedNormalDispatchBridgeRule
      (sourceAssertionAdditionalRows context state ledger scanner index
        assertion) := by
  intro row member payload decoded
  rw [decodeNormalDispatchBridgeCapture_eq_none_of_dynamic
    (sourceAssertionAdditionalRows_all_dynamic context state ledger scanner
      index assertion row member)] at decoded
  contradiction

theorem sourceDecoratedAssertionRequestSpace_bridge_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    NormalDispatchBridgeCapabilities compressedNormalDispatchBridgeRule
      (sourceDecoratedAssertionRequestSpace context state ledger scanner index
        cursor assertion) := by
  unfold sourceDecoratedAssertionRequestSpace
  apply NormalDispatchBridgeCapabilities.append
  · exact canonicalDecoratedDirectAssertionSpace_bridge_capabilities _
  · exact sourceAssertionAdditionalRows_bridge_capabilities context state
      ledger scanner index assertion

#print axioms decodeNormalDispatchBridgeCapture_eq_none_of_dynamic
#print axioms sourceAssertionAdditionalRows_bridge_capabilities
#print axioms sourceDecoratedAssertionRequestSpace_bridge_capabilities

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceNormalBridgeCapability
