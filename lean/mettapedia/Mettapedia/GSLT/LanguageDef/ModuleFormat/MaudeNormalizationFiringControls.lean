import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoStageSimulation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatchingControls

/-! A nonlinear many-sorted row exercises inferred capture sorts and source
readback. A raw match containing Nat values cannot authorize an Element step. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.FiringControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open MatchingControls

private theorem original_source : prepared.source = theory := prepare_source preparation

theorem row_left_typed : Maude.HasSort theory.signature row.usedContext row.left "Element" := by
  apply Maude.HasSort.app (declaration := Maude.SortedControls.combine)
    (by simp [theory, Maude.SortedControls.theory, Maude.SortedControls.signature])
  exact .cons (.var (by decide_cbv)) (.cons (.var (by decide_cbv)) .nil)

theorem row_right_typed : Maude.HasSort theory.signature row.usedContext row.right "Element" :=
  .var (by decide_cbv)

theorem subject_typed : Maude.HasSort theory.signature [] same "Element" := by
  apply Maude.HasSort.app (declaration := Maude.SortedControls.combine)
    (by simp [theory, Maude.SortedControls.theory, Maude.SortedControls.signature])
  exact .cons e0_typed (.cons e0_typed .nil)

theorem captures_inferred :
    SortedBindingsIn prepared.language (freeContext []) (context row) [("X", encode e0)] := by
  apply matched_row_sorted prepared [] row same "Element" (prepare_valid preparation)
  · rw [original_source]
    decide_cbv
  · decide_cbv
  · rw [original_source]
    exact row_left_typed
  · rw [original_source]
    exact subject_typed
  · simp [row, same, e0, encode, matchPattern, matchArgs, mergeBindings]

theorem source_step_readback :
    ∃ target, encode e0 = encode target ∧ Maude.EquationReduction theory [] "Element" same target := by
  have readback := typed_root_readback prepared [] row same "Element" (bindings := [("X", encode e0)])
    (target := encode e0) (prepare_valid preparation)
    (by rw [original_source]; simp [theory]) rfl
    (by rw [original_source]; decide_cbv) (by decide_cbv)
    (by rw [original_source]; exact row_left_typed) (by rw [original_source]; exact row_right_typed)
    (by rw [original_source]; exact subject_typed)
    (by simp [row, same, e0, encode, matchPattern, matchArgs, mergeBindings])
    (by simp [row, encode, applyBindings])
  simpa only [original_source] using readback

theorem wrong_sort_subject_refused : ¬ Maude.HasSort theory.signature [] wrongSort "Element" := by
  intro typed
  obtain ⟨declaration, member, label, _, arguments⟩ := Maude.HasSort.operator_arguments typed rfl
  simp [theory, Maude.SortedControls.theory, Maude.SortedControls.signature] at member
  rcases member with rfl | rfl | rfl
  · simp [Maude.SortedControls.zero] at label
  · simp [Maude.SortedControls.unit] at label
  · cases arguments with
    | cons first rest => exact zero_not_element first

theorem wrong_sort_step_refused (target : Maude.Term) :
    ¬ Maude.EquationReduction theory [] "Element" wrongSort target := by
  intro step
  exact wrong_sort_subject_refused step.sorted.1

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.FiringControls
