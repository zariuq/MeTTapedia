import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData

/-- The generated direct proof handler retains the proof handler's complete
continuation while atomically widening and consuming the lookup cursor. -/
theorem speculative_direct_proof_sinks_exact :
    speculativeDirectProofDirective.rule.tmpl.sinks = directProofSinks := by
  rfl

#print axioms speculative_direct_proof_sinks_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
