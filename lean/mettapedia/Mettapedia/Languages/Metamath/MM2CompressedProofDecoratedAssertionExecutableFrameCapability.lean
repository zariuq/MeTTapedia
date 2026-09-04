import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
import Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Executable capability inventory for the decorated assertion frame

The decorated speculative presentation remains the authority for opaque
compressed continuations.  Supported `exec` shells and ordinary data rows do
not acquire carrier authority merely by sharing the same MM2 space.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionExecutableFrameCapability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

theorem decodeCompressedExecutableCapture_eq_none_of_supported
    {atom : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    decodeCompressedExecutableCapture directive.atom = none := by
  rw [extractSupportedSourceExecFact_atom decoded]
  have rawSome : (extractRawExecFact atom).isSome := by
    unfold extractSupportedSourceExecFact at decoded
    cases rawEq : extractRawExecFact atom <;> simp_all
  unfold extractRawExecFact at rawSome
  split at rawSome
  · rfl
  · contradiction

#print axioms decodeCompressedExecutableCapture_eq_none_of_supported

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionExecutableFrameCapability
