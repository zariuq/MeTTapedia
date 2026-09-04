import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation

/-!
# Assertion-data key separation

The finite assertion data slice is physically distinct from the captured
normal-dispatch bridge by its certified non-executable constructor heads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.ProcessCalculi.MORK

theorem dataSlice_key_ne_bridge
    (context : DirectAssertionContext) {row : Atom}
    (member : row ∈ decoratedDirectAssertionDataSlice context) :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule := by
  obtain ⟨head, headExact, headPositive, headBound, nonExec⟩ :=
    decoratedDirectAssertionDataSlice_shortNonExecHead context member
  exact dynamicRow_key_ne_normalDispatchBridge head headExact headPositive
    headBound nonExec

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation
