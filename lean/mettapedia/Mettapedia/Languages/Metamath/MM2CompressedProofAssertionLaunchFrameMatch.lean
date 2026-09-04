import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame

/-!
# Matcher extension for the compressed assertion launch frame

The canonical local match is transported into the assembled scheduler frame.
This is kept separate from row construction so the generic matcher proof does
not force re-elaboration of the source encoders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrameMatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

@[simp] theorem canonical_direct_assertion_live_exact
    (context : DirectAssertionContext) :
    directAssertionLive (canonicalDirectAssertionSpace context) =
      [context.pendingRow, context.lookupRow, context.heapRow,
       context.machineRow, context.headerRow, context.rejoinCaptureRow] ++
        directAssertionSchedulerFrame := by
  unfold directAssertionLive canonicalDirectAssertionSpace
  unfold directAssertionMatchSlice
  change
    (speculativeDirectAssertionDirective.atom ::
      ([context.pendingRow, context.lookupRow, context.heapRow,
        context.machineRow, context.headerRow, context.rejoinCaptureRow] ++
        directAssertionSchedulerFrame)).erase
          speculativeDirectAssertionDirective.atom = _
  rw [List.erase_cons_head]

theorem canonical_direct_assertion_full_read
    (context : DirectAssertionContext) :
    speculativeDirectAssertionDirective.atom ::
        directAssertionLive (canonicalDirectAssertionSpace context) =
      directAssertionMatchSlice context ++ directAssertionSchedulerFrame := by
  rw [canonical_direct_assertion_live_exact]
  rfl

private theorem assertion_slice_row_in_full
    (context : DirectAssertionContext) {substitution : Subst}
    (sliceRow : substitution ∈ directAssertionSliceRows context) :
    substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          directAssertionLive (canonicalDirectAssertionSpace context))
        speculativeDirectAssertionDirective.rule.input).map Prod.fst := by
  unfold directAssertionSliceRows at sliceRow
  rw [List.mem_map] at sliceRow ⊢
  obtain ⟨⟨sliceSubstitution, consumed⟩, matched, rfl⟩ := sliceRow
  refine ⟨(sliceSubstitution, consumed), ?_, rfl⟩
  rw [speculative_direct_assertion_input_exact] at matched ⊢
  rw [canonical_direct_assertion_full_read]
  exact Conformance.Computable.cmatchPattern_mono []
    (directAssertionMatchSlice context)
    (directAssertionMatchSlice context ++ directAssertionSchedulerFrame)
    (mkPattern directAssertionPatterns)
    (fun atom member => List.mem_append_left _ member)
    sliceSubstitution consumed matched

theorem canonical_exact_direct_assertion_launch
    (context : DirectAssertionContext) :
    ExactDirectAssertionLaunch context
      (canonicalDirectAssertionSpace context) := by
  rcases canonical_assertion_slice_instantiates_launch context with
    ⟨substitution, sliceRow, outputs⟩
  exact ⟨substitution, assertion_slice_row_in_full context sliceRow, outputs⟩

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrameMatch
