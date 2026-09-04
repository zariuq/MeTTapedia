import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedulerKeySeparation

/-!
# Static assertion-inventory key separation

Canonical verifier data and predecessor scheduler directives are physically
distinct from the captured normal-dispatch bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.ProcessCalculi.MORK

theorem canonicalAssertionSpace_key_ne_bridge
    (context : DirectAssertionContext) {row : Atom}
    (member : row ∈ canonicalDecoratedDirectAssertionSpace context)
    (notLauncher : row ≠ decoratedDirectAssertionDirective.atom) :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule := by
  rcases (mem_canonicalDecoratedDirectAssertionSpace_iff context row).mp
      member with matchMember | schedulerMember
  · rcases (mem_decoratedDirectAssertionMatchSlice_iff context row).mp
      matchMember with launcher | dataMember
    · exact (notLauncher launcher).elim
    · exact dataSlice_key_ne_bridge context dataMember
  · exact schedulerFrame_key_ne_bridge schedulerMember

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation
