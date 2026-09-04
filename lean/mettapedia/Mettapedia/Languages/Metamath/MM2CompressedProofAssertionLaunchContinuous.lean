import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrameMatch
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd

/-!
# Concrete continuous assertion launch

This module fires the source-indexed assertion matcher established by the
representation module and proves that its complete normal-kernel interface is
published by the actual generated MM2 transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchContinuous

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrameMatch
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

private theorem directAssertionSinks_context_split :
    directAssertionSinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate] ++
      .add directAssertionContextTemplate ::
        [.add directAssertionNormalControlTemplate,
         .add directAssertionNormalLabelTemplate,
         .add directAssertionReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

private theorem directAssertionSinks_control_split :
    directAssertionSinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate] ++
      .add directAssertionNormalControlTemplate ::
        [.add directAssertionNormalLabelTemplate,
         .add directAssertionReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

private theorem directAssertionSinks_label_split :
    directAssertionSinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate] ++
      .add directAssertionNormalLabelTemplate ::
        [.add directAssertionReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

private theorem directAssertionSinks_reload_split :
    directAssertionSinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate] ++
      .add directAssertionReloadTemplate ::
        [.add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

/-- Every successful canonical launch publishes the complete normal-kernel
interface.  This is one concrete generated MM2 transition, not a reconstructed
post-state. -/
theorem direct_assertion_fire_adds_launch_rows
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDirectAssertionLaunch context space) :
    ∀ row ∈ context.launchRows,
      row ∈ cFireReflectiveSourceExecFact space
        speculativeDirectAssertionDirective := by
  intro row member
  rcases matched with
    ⟨substitution, rowMember, _pending, _lookup, _machine,
      contextRow, normalControl, normalLabel, reload, rejoinRule⟩
  simp only [DirectAssertionContext.launchRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_direct_assertion_sinks_exact]
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [directAssertionSinks_context_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember contextRow (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [directAssertionSinks_control_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember normalControl (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [directAssertionSinks_label_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember normalLabel (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [directAssertionSinks_reload_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember reload (by
        intro sink sinkMember
        simp only [List.mem_singleton] at sinkMember
        subst sink
        exact ⟨_, rfl⟩)
  · exact mem_cApplyReflectiveSinkBatch_append_add_of_row _ _
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate]
      (.var "compressed-assertion-rejoin-rule") compressedAssertionRejoinRule
      substitution rowMember rejoinRule

#print axioms direct_assertion_fire_adds_launch_rows

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchContinuous
