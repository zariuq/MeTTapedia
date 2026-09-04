import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDataKeySeparation

/-!
# Assertion-scheduler key separation

Every predecessor scheduler directive is physically distinct from the
captured normal-dispatch bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.ProcessCalculi.MORK

theorem schedulerFrame_key_ne_bridge {row : Atom}
    (member : row ∈ decoratedDirectAssertionSchedulerFrame) :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule := by
  simp only [decoratedDirectAssertionSchedulerFrame, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with proof | cursor | fault | advance
  · exact proof ▸ compressedProofStep_key_ne_normalDispatchBridge
  · exact cursor ▸ decoratedCursorAssertion_key_ne_normalDispatchBridge
  · exact fault ▸ compressedHeapLookupFault_key_ne_normalDispatchBridge
  · exact advance ▸ compressedHeapLookupAdvance_key_ne_normalDispatchBridge

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation
