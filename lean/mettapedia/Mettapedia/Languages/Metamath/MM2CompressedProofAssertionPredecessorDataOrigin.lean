import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame

/-!
# Assertion predecessor data-slice origin

The finite non-scheduler slice contains exactly its source-derived pending and
lookup rows; every other row has a distinct fixed syntax head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDataOrigin

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.ProcessCalculi.MORK

theorem decoratedDirectAssertionDataSlice_predecessor_origin
    (context : DirectAssertionContext) :
    AtomsWithin (AssertionPredecessorRowOrigin context)
      (decoratedDirectAssertionDataSlice context) := by
  intro atom member
  simp only [decoratedDirectAssertionDataSlice, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact assertionPendingRow_origin context
  · exact assertionLookupRow_origin context
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-compressed-heap-assertion" rfl (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-compressed-machine" rfl (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-assertion-header" rfl (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-compressed-owned-runtime-rule" rfl (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-internal-compressed-normal-dispatch-bridge" rfl
      (by decide) (by decide)

#print axioms decoratedDirectAssertionDataSlice_predecessor_origin

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDataOrigin
