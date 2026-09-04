import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDataOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDirectOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorSchedulerOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch

/-!
# Canonical assertion-frame predecessor origin

The finite compiler-produced assertion frame contains exactly one pending row
and one heap-lookup row.  Executable shells are excluded through their strict
syntax-decoder receipts, without unfolding their rule payloads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionPredecessorOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDataOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorDirectOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorSchedulerOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.ProcessCalculi.MORK

theorem canonicalDecoratedDirectAssertionSpace_predecessor_origin
  (context : DirectAssertionContext) :
    AtomsWithin (AssertionPredecessorRowOrigin context)
      (canonicalDecoratedDirectAssertionSpace context) := by
  intro atom member
  rcases (mem_canonicalDecoratedDirectAssertionSpace_iff context atom).mp
      member with matchMember | schedulerMember
  · rcases (mem_decoratedDirectAssertionMatchSlice_iff context atom).mp
      matchMember with direct | dataMember
    · subst atom
      exact decoratedDirectAssertionDirective_predecessor_origin context
    · exact decoratedDirectAssertionDataSlice_predecessor_origin context atom
        dataMember
  · exact decoratedDirectAssertionSchedulerFrame_predecessor_origin context
      atom schedulerMember

#print axioms canonicalDecoratedDirectAssertionSpace_predecessor_origin

end Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionPredecessorOrigin
