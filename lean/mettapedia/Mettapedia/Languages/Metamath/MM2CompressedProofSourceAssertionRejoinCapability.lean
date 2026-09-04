import Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionRejoinCapability
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch

/-!
# Source-relative assertion-rejoin capability

Appending source-derived dynamic rows to the canonical decorated frame cannot
introduce another assertion-rejoin payload.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionRejoinCapability

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection

theorem decodeCompressedExecutableCapture_eq_none_of_dynamic
    {row : Atom} (dynamic : isDynamicRow row = true) :
    decodeCompressedExecutableCapture row = none := by
  unfold decodeCompressedExecutableCapture
  split <;> simp_all [isDynamicRow, dynamicRowHeads]

theorem sourceAssertionAdditionalRows_rejoin_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) :
    AssertionRejoinCapabilities compressedAssertionRejoinRule
      (sourceAssertionAdditionalRows context state ledger scanner index
        assertion) := by
  intro row member payload decoded
  rw [decodeCompressedExecutableCapture_eq_none_of_dynamic
    (sourceAssertionAdditionalRows_all_dynamic context state ledger scanner
      index assertion row member)] at decoded
  contradiction

theorem sourceDecoratedAssertionRequestSpace_rejoin_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    AssertionRejoinCapabilities compressedAssertionRejoinRule
      (sourceDecoratedAssertionRequestSpace context state ledger scanner index
        cursor assertion) := by
  unfold sourceDecoratedAssertionRequestSpace
  apply AssertionRejoinCapabilities.append
  · exact canonicalDecoratedDirectAssertionSpace_rejoin_capabilities _
  · exact sourceAssertionAdditionalRows_rejoin_capabilities context state
      ledger scanner index assertion

#print axioms decodeCompressedExecutableCapture_eq_none_of_dynamic
#print axioms sourceAssertionAdditionalRows_rejoin_capabilities
#print axioms sourceDecoratedAssertionRequestSpace_rejoin_capabilities

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionRejoinCapability
