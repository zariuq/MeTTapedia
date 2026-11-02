import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePremiseReindexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProtectedProjection
import Mettapedia.GSLT.LanguageDef.CertificateGSLTContextMapProducts

/-! # Physical reindexing extends through an actual protected publication -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring.KernelOrigin

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value)
open InferenceRequestExecution (Occurrence)
open InferenceJudgmentBoards
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}
  {before after : Configuration Value Occurrence}
  {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)

theorem board_judgments (prior : Board before) :
    (origin.board prior).judgments = prior.judgments ++ [origin.conclusion] :=
  congrArg ClassifyingContext.judgments (origin.board_context prior)

def oldIndex (prior : Board before) (index : Fin prior.entries.length) :
    Fin (origin.board prior).entries.length :=
  ⟨index.val, by
    change index.val < (prior.entries ++ [(origin.output, origin.conclusion)]).length
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega⟩

def newIndex (prior : Board before) : Fin (origin.board prior).entries.length :=
  ⟨prior.entries.length, by
    change prior.entries.length < (prior.entries ++ [(origin.output, origin.conclusion)]).length
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega⟩

theorem old_occurrence (prior : Board before) (index : Fin prior.entries.length) :
    (origin.board prior).occurrenceAt (origin.oldIndex prior index) = prior.occurrenceAt index := by
  change (prior.entries ++ [(origin.output, origin.conclusion)])[index.val].1 =
    prior.entries[index.val].1
  rw [List.getElem_append_left index.isLt]

theorem new_occurrence (prior : Board before) :
    (origin.board prior).occurrenceAt (origin.newIndex prior) = origin.output := by
  change (prior.entries ++ [(origin.output, origin.conclusion)])[prior.entries.length].1 = origin.output
  simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]

/-- Carry the old physical position map through the new output, with only
the actual equality between displayed and physical board contexts transported. -/
noncomputable def extendedMap (first second : Board before) :
    ContextMap (origin.board first).judgments (origin.board second).judgments :=
  ((first.reorder second).extend origin.conclusion).transport
    (origin.board_judgments first).symm (origin.board_judgments second).symm

theorem extendedMap_value (first second : Board before)
    (index : Fin (origin.board second).judgments.length) :
    ((origin.extendedMap first second).position index).val =
      if inside : index.val < second.judgments.length then
        ((first.reorder second).position ⟨index.val, inside⟩).val
      else first.judgments.length := by
  unfold extendedMap
  rw [ContextMap.transport_position]
  simpa only [Fin.val_cast] using
    ContextMap.extend_position_value (first.reorder second) origin.conclusion
      (Fin.cast (congrArg List.length (origin.board_judgments second)) index)

/-- The carried permutation is the actual physical reindexing of the
resulting protected stores, including the same fresh output occurrence. -/
theorem extendedMap_is_reorder (first second : Board before) :
    origin.extendedMap first second = (origin.board first).reorder (origin.board second) := by
  apply ContextMap.ext
  funext index
  have direct := (origin.board first).reorder_occurrence (origin.board second) index
  have indirect : (origin.board first).occurrenceAt
      ((origin.board first).entryIndex ((origin.extendedMap first second).position index)) =
        (origin.board second).occurrenceAt ((origin.board second).entryIndex index) := by
    by_cases inside : index.val < second.judgments.length
    · let old : Fin second.entries.length := second.entryIndex ⟨index.val, inside⟩
      let mapped := first.entryIndex ((first.reorder second).position ⟨index.val, inside⟩)
      have sourceIndex :
          (origin.board first).entryIndex ((origin.extendedMap first second).position index) =
            origin.oldIndex first mapped := by
        apply Fin.ext
        have value := origin.extendedMap_value first second index
        rw [dif_pos inside] at value
        simpa only [Board.entryIndex, oldIndex, mapped] using value
      have targetIndex : (origin.board second).entryIndex index = origin.oldIndex second old := rfl
      rw [sourceIndex, targetIndex, origin.old_occurrence, origin.old_occurrence]
      exact first.reorder_occurrence second ⟨index.val, inside⟩
    · have last : index.val = second.entries.length := by
        have bound : index.val < second.judgments.length + 1 := by
          simpa only [origin.board_judgments, List.length_append, List.length_cons,
            List.length_nil] using index.isLt
        simp only [Board.judgments, List.length_map] at bound inside
        omega
      have sourceIndex :
          (origin.board first).entryIndex ((origin.extendedMap first second).position index) =
            origin.newIndex first := by
        apply Fin.ext
        have value := origin.extendedMap_value first second index
        rw [dif_neg inside] at value
        simpa only [Board.entryIndex, newIndex, Board.judgments, List.length_map] using value
      have targetIndex : (origin.board second).entryIndex index = origin.newIndex second :=
        Fin.ext last
      rw [sourceIndex, targetIndex, origin.new_occurrence, origin.new_occurrence]
  have same := (origin.board first).occurrenceAt_injective (indirect.trans direct.symm)
  simpa only [Board.premise_entry] using congrArg (origin.board first).premiseIndex same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring.KernelOrigin
