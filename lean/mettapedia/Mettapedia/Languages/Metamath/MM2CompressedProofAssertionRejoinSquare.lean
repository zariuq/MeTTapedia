import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Scheduled compressed-assertion rejoin square

The normal verifier's occurrence-indexed result is matched by the authored
rejoin directive, selected by the ordinary reflective scheduler, and emitted
as the exact compact successor interface.  The same transition inhabits the
native target type generated from the reflective MM2 execution GSLT.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinSquare

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private theorem rejoinDirective_decodes :
    extractSupportedSourceExecFact compressedAssertionRejoinDirective.atom =
      some compressedAssertionRejoinDirective := by
  change extractSupportedSourceExecFact compressedAssertionRejoinRule = _
  exact extract_compressedAssertionRejoinRule_exact

private theorem contextRow_no_supported (context : RejoinContext) :
    extractSupportedSourceExecFact context.contextRow = none := by
  rfl

private theorem returnedControlRow_no_supported (context : RejoinContext) :
    extractSupportedSourceExecFact context.returnedControlRow = none := by
  rfl

private theorem returnedStackRow_no_supported (context : RejoinContext) :
    extractSupportedSourceExecFact context.returnedStackRow = none := by
  rfl

private theorem normalStackSuccessorRow_no_supported
    (context : RejoinContext) :
    extractSupportedSourceExecFact context.normalStackSuccessorRow = none := by
  rfl

private theorem nodeSuccessorRow_no_supported (context : RejoinContext) :
    extractSupportedSourceExecFact context.nodeSuccessorRow = none := by
  rfl

private theorem normalLabelRow_no_supported (context : RejoinContext) :
    extractSupportedSourceExecFact context.normalLabelRow = none := by
  rfl

private theorem resumeCaptureRow_no_supported (context : RejoinContext) :
    extractSupportedSourceExecFact context.resumeCaptureRow = none := by
  rfl

/-- Exactly one executable directive is visible at the canonical rejoin
boundary; every other row is data or an inert capability carrier. -/
theorem canonical_rejoin_slice_supported (context : RejoinContext) :
    cSupportedSourceExecFacts context.matchSlice =
      [compressedAssertionRejoinDirective] := by
  unfold RejoinContext.matchSlice cSupportedSourceExecFacts
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [rejoinDirective_decodes, contextRow_no_supported,
    returnedControlRow_no_supported, returnedStackRow_no_supported,
    normalStackSuccessorRow_no_supported, nodeSuccessorRow_no_supported,
    normalLabelRow_no_supported, resumeCaptureRow_no_supported]

theorem canonical_rejoin_slice_selects_rejoin (context : RejoinContext) :
    selectNextScheduled (cSupportedSourceExecFacts context.matchSlice) =
      some compressedAssertionRejoinDirective := by
  rw [canonical_rejoin_slice_supported]
  rfl

/-- The canonical boundary takes the exact reflective step characterized by
the symbolic rejoin matcher. -/
theorem canonical_rejoin_slice_steps (context : RejoinContext) :
    cReflectiveSourceWorkQueueStep .leaveInert context.matchSlice =
      some (cFireReflectiveSourceExecFact context.matchSlice
        compressedAssertionRejoinDirective) := by
  simp only [cReflectiveSourceWorkQueueStep,
    canonical_rejoin_slice_selects_rejoin]

/-- The scheduled rejoin step inhabits the exact native target generated from
the reflective MM2 execution GSLT. -/
theorem canonical_rejoin_slice_inhabits_exact_native_target
    (context : RejoinContext) :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      context.matchSlice
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (cFireReflectiveSourceExecFact context.matchSlice
          compressedAssertionRejoinDirective)).pred := by
  apply (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    .leaveInert _ _).2
  exact canonical_rejoin_slice_steps context

def canonicalRejoinResult (context : RejoinContext) : List Atom :=
  cFireReflectiveSourceExecFact context.matchSlice
    compressedAssertionRejoinDirective

/-- One scheduled source-indexed assertion-rejoin boundary.  Its observations
come from the actual MM2 transition rather than a separately constructed
post-state. -/
structure CanonicalCompressedAssertionRejoinSquare
    (context : RejoinContext) : Prop where
  exactMatcher :
    ExactCompressedAssertionRejoin context context.matchSlice
  scheduled :
    cReflectiveSourceWorkQueueStep .leaveInert context.matchSlice =
      some (canonicalRejoinResult context)
  publishesCompactInterface :
    ∀ row ∈ context.outputRows,
      row ∈ canonicalRejoinResult context
  preservesNormalStack :
    context.returnedStackRow ∈ canonicalRejoinResult context
  nativeTarget :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      context.matchSlice
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (canonicalRejoinResult context)).pred

theorem canonical_compressed_assertion_rejoin_square
    (context : RejoinContext) :
    CanonicalCompressedAssertionRejoinSquare context where
  exactMatcher := canonical_exact_compressed_assertion_rejoin context
  scheduled := canonical_rejoin_slice_steps context
  publishesCompactInterface := canonical_rejoin_fire_adds_output_rows context
  preservesNormalStack :=
    canonical_rejoin_fire_preserves_returned_stack context
  nativeTarget := canonical_rejoin_slice_inhabits_exact_native_target context

section AxiomAudit

#print axioms canonical_rejoin_slice_supported
#print axioms canonical_rejoin_slice_selects_rejoin
#print axioms canonical_rejoin_slice_steps
#print axioms canonical_rejoin_slice_inhabits_exact_native_target
#print axioms canonical_compressed_assertion_rejoin_square

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinSquare
