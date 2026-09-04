import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchContinuous
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSelect

/-!
# Scheduled and OSLF-classified compressed assertion launch

This module closes the concrete launch adapter: the canonical generated
matcher is selected by the ordinary MM2 scheduler, fires once, publishes the
complete normal-verifier interface, and inhabits the exact native target type
generated from the reflective MM2 execution GSLT.

The subsequent normal assertion calculation and compressed rejoin are
separate operational segments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSquare

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrameMatch
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSelect
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def canonicalDirectAssertionResult
    (context : DirectAssertionContext) : List Atom :=
  cFireReflectiveSourceExecFact
    (canonicalDirectAssertionSpace context)
    speculativeDirectAssertionDirective

/-- One complete, source-indexed launch boundary.  No source proof result is
stored in this witness: all target observations are produced by the actual
scheduled MM2 transition. -/
structure CanonicalDirectAssertionLaunchSquare
    (context : DirectAssertionContext) : Prop where
  exactMatcher :
    ExactDirectAssertionLaunch context
      (canonicalDirectAssertionSpace context)
  scheduled :
    cReflectiveSourceWorkQueueStep .leaveInert
        (canonicalDirectAssertionSpace context) =
      some (canonicalDirectAssertionResult context)
  publishesNormalInterface :
    ∀ row ∈ context.launchRows,
      row ∈ canonicalDirectAssertionResult context
  nativeTarget :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (canonicalDirectAssertionSpace context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (canonicalDirectAssertionResult context)).pred

theorem canonical_direct_assertion_launch_square
    (context : DirectAssertionContext) :
    CanonicalDirectAssertionLaunchSquare context where
  exactMatcher := canonical_exact_direct_assertion_launch context
  scheduled := by
    exact canonicalDirectAssertionSpace_steps context
  publishesNormalInterface := by
    intro row member
    exact direct_assertion_fire_adds_launch_rows context
      (canonicalDirectAssertionSpace context)
      (canonical_exact_direct_assertion_launch context) row member
  nativeTarget := by
    exact canonicalDirectAssertionSpace_inhabits_exact_native_target context

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSquare
