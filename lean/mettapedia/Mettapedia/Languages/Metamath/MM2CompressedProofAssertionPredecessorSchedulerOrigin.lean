import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch

/-!
# Assertion predecessor scheduler origin

Every inherited scheduler row is a strictly decoded executable shell, hence
cannot inhabit either predecessor data-row family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorSchedulerOrigin

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.ProcessCalculi.MORK

theorem decoratedDirectAssertionSchedulerFrame_predecessor_origin
    (context : DirectAssertionContext) :
    AtomsWithin (AssertionPredecessorRowOrigin context)
      decoratedDirectAssertionSchedulerFrame := by
  intro atom member
  apply assertionPredecessorRowOrigin_of_shape_exclusion context
  · intro tail
    exact (decoratedDirectAssertionSchedulerFrame_not_predecessor_shape
      member tail).1
  · intro tail
    exact (decoratedDirectAssertionSchedulerFrame_not_predecessor_shape
      member tail).2

#print axioms decoratedDirectAssertionSchedulerFrame_predecessor_origin

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorSchedulerOrigin
