import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation

/-!
# Fail-closed collision controls for the speculative compressed verifier

These controls exercise the concrete adapter with hostile physical
inventories.  They are isolated from the compiler module so ordinary users do
not pay for their closed evaluations.
-/

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentationCollisionCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation

/-- Duplicating a selected source rule is rejected before transformation. -/
theorem duplicate_selected_terminal_rule_rejected :
    transformCompressedVerifierPresentation?
        (compressedVerifierRules ++ [compressedTerminalRule])
        compressedVerifierStaticRows = none := by
  decide +kernel

/-- Supplying a rule already reserved for the derived direct layer is
rejected rather than collapsing two physical occurrences in MM2 support. -/
theorem preexisting_direct_rule_rejected :
    transformCompressedVerifierPresentation?
        (compressedVerifierRules ++ [compressedDirectProofRule])
        compressedVerifierStaticRows = none := by
  decide +kernel

/-- Supplying a persistent row already reserved for the direct layer is
rejected rather than treating its name as authority. -/
theorem preexisting_direct_handler_row_rejected :
    transformCompressedVerifierPresentation? compressedVerifierRules
        (compressedVerifierStaticRows ++ [compressedDirectProofHandlerRow]) =
      none := by
  decide +kernel

#print axioms duplicate_selected_terminal_rule_rejected
#print axioms preexisting_direct_rule_rejected
#print axioms preexisting_direct_handler_row_rejected

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentationCollisionCanary
