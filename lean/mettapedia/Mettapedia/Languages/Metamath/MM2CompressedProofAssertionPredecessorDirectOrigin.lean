import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface

/-!
# Assertion launcher-shell predecessor origin

The selected assertion launcher is a strictly decoded executable shell and
cannot inhabit either predecessor data-row family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDirectOrigin

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface

theorem decoratedDirectAssertionDirective_predecessor_origin
    (context : DirectAssertionContext) :
    AssertionPredecessorRowOrigin context
      decoratedDirectAssertionDirective.atom := by
  apply assertionPredecessorRowOrigin_of_shape_exclusion context
  · intro tail
    exact (decoratedDirectAssertionDirective_not_predecessor_shape tail).1
  · intro tail
    exact (decoratedDirectAssertionDirective_not_predecessor_shape tail).2

#print axioms decoratedDirectAssertionDirective_predecessor_origin

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDirectOrigin
