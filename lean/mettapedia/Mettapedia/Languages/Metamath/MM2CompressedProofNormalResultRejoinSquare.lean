import Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Scheduled normal-result to compressed-rejoin square

The transformed normal verifier returns an occurrence-indexed result, and the
compressed verifier consumes that exact intermediate carrier.  Both firings
are selected by the ordinary reflective MM2 scheduler.  The two primitive
steps separately inhabit the exact native target types generated from the
reflective execution GSLT.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoinSquare

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private theorem normalResultDirective_decodes :
    extractSupportedSourceExecFact normalResultDirective.atom =
      some normalResultDirective := by
  change extractSupportedSourceExecFact
      normalAssertionResultCompleteRuleWithCompressedRejoin = _
  exact extract_normalResultRule_exact

private theorem bodyBuiltRow_no_supported (context : NormalResultContext) :
    extractSupportedSourceExecFact context.bodyBuiltRow = none := by
  rfl

private theorem rejoinCaptureRow_no_supported
    (context : NormalResultContext) :
    extractSupportedSourceExecFact context.rejoinCaptureRow = none := by
  rfl

private theorem contextRow_no_supported (context : NormalResultContext) :
    extractSupportedSourceExecFact context.rejoinContext.contextRow = none := by
  rfl

private theorem normalStackSuccessorRow_no_supported
    (context : NormalResultContext) :
    extractSupportedSourceExecFact
      context.rejoinContext.normalStackSuccessorRow = none := by
  rfl

private theorem nodeSuccessorRow_no_supported
    (context : NormalResultContext) :
    extractSupportedSourceExecFact context.rejoinContext.nodeSuccessorRow =
      none := by
  rfl

private theorem normalLabelRow_no_supported (context : NormalResultContext) :
    extractSupportedSourceExecFact context.rejoinContext.normalLabelRow =
      none := by
  rfl

private theorem resumeCaptureRow_no_supported
    (context : NormalResultContext) :
    extractSupportedSourceExecFact context.rejoinContext.resumeCaptureRow =
      none := by
  rfl

theorem normalToRejoinSlice_supported (context : NormalResultContext) :
    cSupportedSourceExecFacts (normalToRejoinSlice context) =
      [normalResultDirective] := by
  unfold normalToRejoinSlice cSupportedSourceExecFacts
  simp only [List.filterMap_cons, List.filterMap_append]
  rw [normalResultDirective_decodes, bodyBuiltRow_no_supported,
    rejoinCaptureRow_no_supported, contextRow_no_supported,
    normalStackSuccessorRow_no_supported, nodeSuccessorRow_no_supported,
    normalLabelRow_no_supported, resumeCaptureRow_no_supported]
  simp [compressedScannerRuleCaptureRows, compressedOwnedRuntimeRuleRow,
    extractSupportedSourceExecFact, extractRawExecFact]

theorem normalToRejoinSlice_selects_normal_result
    (context : NormalResultContext) :
    selectNextScheduled
        (cSupportedSourceExecFacts (normalToRejoinSlice context)) =
      some normalResultDirective := by
  rw [normalToRejoinSlice_supported]
  rfl

theorem normalToRejoinSlice_steps (context : NormalResultContext) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalToRejoinSlice context) =
      some (normalToRejoinAfter context) := by
  simp only [cReflectiveSourceWorkQueueStep,
    normalToRejoinSlice_selects_normal_result, normalToRejoinAfter]

private theorem selectNextScheduled_eq_of_mem_unique
    {facts : List SourceExecFact} {expected : SourceExecFact}
    (present : expected ∈ facts)
    (unique : ∀ candidate ∈ facts, candidate = expected) :
    selectNextScheduled facts = some expected := by
  cases facts with
  | nil => simp at present
  | cons head tail =>
      have headEq : head = expected := unique head (by simp)
      subst head
      unfold selectNextScheduled
      simp only [List.foldl_cons]
      induction tail with
      | nil => rfl
      | cons candidate remaining induction =>
          have candidateEq : candidate = expected :=
            unique candidate (by simp)
          subst candidate
          simp only [List.foldl_cons]
          rw [lexLt_irrefl]
          exact induction (by simp) (fun later laterMember =>
            unique later (List.mem_cons_of_mem expected laterMember))

theorem normalToRejoinAfter_selects_rejoin
    (context : NormalResultContext) :
    selectNextScheduled
        (cSupportedSourceExecFacts (normalToRejoinAfter context)) =
      some compressedAssertionRejoinDirective :=
  selectNextScheduled_eq_of_mem_unique
    (compressed_rejoin_supported_after_normal_result context)
    (normalToRejoinAfter_supported_unique context)

def normalResultRejoinResult (context : NormalResultContext) : List Atom :=
  cFireReflectiveSourceExecFact (normalToRejoinAfter context)
    compressedAssertionRejoinDirective

theorem normalToRejoinAfter_steps (context : NormalResultContext) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalToRejoinAfter context) =
      some (normalResultRejoinResult context) := by
  simp only [cReflectiveSourceWorkQueueStep,
    normalToRejoinAfter_selects_rejoin, normalResultRejoinResult]

theorem normalResultRejoin_run_two_exact
    (context : NormalResultContext) :
    cReflectiveSourceWorkQueueRunN .leaveInert 2
        (normalToRejoinSlice context) =
      (normalResultRejoinResult context, 2) := by
  simp [cReflectiveSourceWorkQueueRunN, normalToRejoinSlice_steps,
    normalToRejoinAfter_steps]

theorem normalToRejoinSlice_inhabits_exact_native_target
    (context : NormalResultContext) :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (normalToRejoinSlice context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (normalToRejoinAfter context)).pred := by
  apply (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    .leaveInert _ _).2
  exact normalToRejoinSlice_steps context

theorem normalToRejoinAfter_inhabits_exact_native_target
    (context : NormalResultContext) :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (normalToRejoinAfter context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (normalResultRejoinResult context)).pred := by
  apply (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    .leaveInert _ _).2
  exact normalToRejoinAfter_steps context

structure NormalResultCompressedRejoinSquare
    (context : NormalResultContext) : Prop where
  normalResultScheduled :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalToRejoinSlice context) =
      some (normalToRejoinAfter context)
  exactIntermediate :
    ExactCompressedAssertionRejoin context.rejoinContext
      (normalToRejoinAfter context)
  rejoinScheduled :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalToRejoinAfter context) =
      some (normalResultRejoinResult context)
  twoStepRun :
    cReflectiveSourceWorkQueueRunN .leaveInert 2
        (normalToRejoinSlice context) =
      (normalResultRejoinResult context, 2)
  publishesCompactInterface :
    ∀ row ∈ context.rejoinContext.outputRows,
      row ∈ normalResultRejoinResult context
  preservesReturnedNormalStack :
    context.rejoinContext.returnedStackRow ∈
      normalResultRejoinResult context
  normalResultNativeTarget :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (normalToRejoinSlice context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (normalToRejoinAfter context)).pred
  rejoinNativeTarget :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (normalToRejoinAfter context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (normalResultRejoinResult context)).pred

theorem normal_result_compressed_rejoin_square
    (context : NormalResultContext) :
    NormalResultCompressedRejoinSquare context where
  normalResultScheduled := normalToRejoinSlice_steps context
  exactIntermediate :=
    normal_result_fire_supplies_exact_compressed_rejoin context
  rejoinScheduled := normalToRejoinAfter_steps context
  twoStepRun := normalResultRejoin_run_two_exact context
  publishesCompactInterface :=
    normal_result_then_rejoin_publishes_compact_boundary context
  preservesReturnedNormalStack :=
    compressed_assertion_rejoin_fire_preserves_returned_stack _ _
      (returned_stack_live_after_normal_result context)
  normalResultNativeTarget :=
    normalToRejoinSlice_inhabits_exact_native_target context
  rejoinNativeTarget :=
    normalToRejoinAfter_inhabits_exact_native_target context

section AxiomAudit

#print axioms normalToRejoinSlice_supported
#print axioms normalToRejoinSlice_steps
#print axioms normalToRejoinAfter_selects_rejoin
#print axioms normalToRejoinAfter_steps
#print axioms normalResultRejoin_run_two_exact
#print axioms normalToRejoinSlice_inhabits_exact_native_target
#print axioms normalToRejoinAfter_inhabits_exact_native_target
#print axioms normal_result_compressed_rejoin_square

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoinSquare
