import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentationProperties

/-!
# Compiler origin of the decorated assertion capabilities

The speculative direct assertion rule is a member of the transformed target
inventory by a generic compiler law.  Its captured normal-dispatch bridge is
an explicit opaque row of the ordered verifier presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionOrigin

open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation

theorem decoratedDirectAssertionRule_mem_targetRules :
    decoratedDirectAssertionRule ∈ decoratedSpeculativeBody.targetRules := by
  exact (transformCompressedVerifierPresentation?_direct_rules_mem
    decoratedSpeculativeBody_build_exact).2

theorem decoratedDirectAssertionBridgeCaptureRow_mem_program :
    decoratedDirectAssertionBridgeCaptureRow ∈
      compressedSpeculativeOrderedVerifierExtensionProgram := by
  unfold compressedSpeculativeOrderedVerifierExtensionProgram
  unfold compressedNormalDispatchBridgeRows
  simp [decoratedDirectAssertionBridgeCaptureRow]

#print axioms decoratedDirectAssertionRule_mem_targetRules
#print axioms decoratedDirectAssertionBridgeCaptureRow_mem_program

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionOrigin
