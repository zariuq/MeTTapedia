import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagReadout
import Mettapedia.Languages.Maude.MutexInvariant

/-! The normalized ground marking relation is justified by actual mutex
source rule instances modulo its equations. Permit conservation is proved
independently; this bridge prevents the marking model from being a separate
operational oracle. Reflection modulo the full E theory remains separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.MutexSourceSteps

open Mettapedia.Languages
open Maude.MutexNormalization

private theorem token_context (context : Maude.VariableContext) (name : String)
    (allowed : name ∈ ["empty", "idle1", "idle2", "crit1", "crit2", "permit", "init"]) :
    Maude.HasSort Maude.Examples.mutex.signature context (token name) "Marking" := by
  apply Maude.HasSort.app (declaration := ⟨"mutex." ++ name, name, [], "Marking", {constructor := true}⟩)
  · simp only [Maude.Examples.mutex, Maude.Examples.markingOperators, List.mem_append, List.mem_map]
    exact .inl ⟨name, allowed, rfl⟩
  · exact .nil

private theorem merge_context {context : Maude.VariableContext} {left right : Maude.Term}
    (first : Maude.HasSort Maude.Examples.mutex.signature context left "Marking")
    (second : Maude.HasSort Maude.Examples.mutex.signature context right "Marking") :
    Maude.HasSort Maude.Examples.mutex.signature context (operation.merge left right) "Marking" := by
  have children : List.Forall₂ (Maude.HasSort Maude.Examples.mutex.signature context)
      [left, right] operation.declaration.arguments := by
    rw [operation.arguments]
    exact .cons (by simpa only [operation, mergeOperator] using first)
      (.cons (by simpa only [operation, mergeOperator] using second) .nil)
  simpa only [operation, mergeOperator, Maude.ACUOperation.merge] using Maude.HasSort.app operation.declared children

theorem row_schemas_sorted {row : Maude.Row} (member : row ∈ Maude.Examples.mutex.rules) :
    Maude.HasSort Maude.Examples.mutex.signature [] row.left "Marking" ∧
      Maude.HasSort Maude.Examples.mutex.signature [] row.right "Marking" := by
  simp only [Maude.Examples.mutex, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨merge_context (token_context [] "idle1" (by simp)) (token_context [] "permit" (by simp)),
      token_context [] "crit1" (by simp)⟩
  · exact ⟨token_context [] "crit1" (by simp),
      merge_context (token_context [] "idle1" (by simp)) (token_context [] "permit" (by simp))⟩
  · exact ⟨merge_context (token_context [] "idle2" (by simp)) (token_context [] "permit" (by simp)),
      token_context [] "crit2" (by simp)⟩
  · exact ⟨token_context [] "crit2" (by simp),
      merge_context (token_context [] "idle2" (by simp)) (token_context [] "permit" (by simp))⟩

theorem row_fires {row : Maude.Row} (member : row ∈ Maude.Examples.mutex.rules) :
    Maude.RawStep Maude.Examples.mutex [] "Marking" row.left row.right := by
  have checked : row.check Maude.Examples.mutex.signature = true := by
    have all : Maude.Examples.mutex.rules.all (Maude.Row.check Maude.Examples.mutex.signature) = true := by decide_cbv
    exact List.all_eq_true.mp all row member
  have conditions : row.conditions = [] := by
    simp only [Maude.Examples.mutex, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  exact ACUBagReadout.ground_row_fires member checked conditions (row_schemas_sorted member).1 (row_schemas_sorted member).2

theorem transition_source_step {source target : List Maude.Term}
    (step : GroundTransition source target) (sorted : operation.Sorted source) :
    Maude.Step Maude.Examples.mutex [] "Marking" (operation.fold source) (operation.fold target) := by
  cases step with
  | fire row residual member partition =>
    have selectedSorted := operation.flatten_sorted (by decide_cbv) (row_schemas_sorted member).1
    have residualSorted : operation.Sorted residual := fun term inside =>
      sorted term (partition.mem_iff.mpr (List.mem_append_right _ inside))
    have sourceToRedex : Maude.Equivalent Maude.Examples.mutex [] "Marking" (operation.fold source)
        (operation.merge row.left (operation.fold residual)) :=
      .trans (operation.fold_perm partition sorted)
        (.trans (operation.fold_append _ _ selectedSorted residualSorted)
          (operation.merge_left (.symm (operation.equivalent_fold_flatten (by decide_cbv) (row_schemas_sorted member).1))
            (operation.fold_sorted _ residualSorted)))
    refine ⟨_, _, sourceToRedex, operation.rawStep_with_residual (row_fires member) residual residualSorted, ?_⟩
    exact .trans (operation.merge_left
      (operation.equivalent_fold_flatten (by decide_cbv) (row_schemas_sorted member).2)
      (operation.fold_sorted _ residualSorted))
      (.symm (operation.fold_append _ _
        (operation.flatten_sorted (by decide_cbv) (row_schemas_sorted member).2) residualSorted))

theorem transition_sorted {source target : List Maude.Term}
    (step : GroundTransition source target) (sorted : operation.Sorted source) : operation.Sorted target := by
  cases step with
  | fire row residual member partition =>
    intro term inside
    rcases List.mem_append.mp inside with produced | retained
    · exact operation.flatten_sorted (by decide_cbv) (row_schemas_sorted member).2 term produced
    · exact sorted term (partition.mem_iff.mpr (List.mem_append_right _ retained))

private theorem reaches_then_step {source middle target : Maude.Term}
    (path : Maude.Reaches Maude.Examples.mutex [] "Marking" source middle)
    (last : Maude.Step Maude.Examples.mutex [] "Marking" middle target)
    (typed : Maude.HasSort Maude.Examples.mutex.signature [] target "Marking") :
    Maude.Reaches Maude.Examples.mutex [] "Marking" source target := by
  induction path with
  | refl _ => exact .next last (.refl typed)
  | next first rest ih => exact .next first (ih last)

theorem path_source_reaches {source target : List Maude.Term}
    (path : Relation.ReflTransGen GroundTransition source target) (sorted : operation.Sorted source) :
    operation.Sorted target ∧ Maude.Reaches Maude.Examples.mutex [] "Marking"
      (operation.fold source) (operation.fold target) := by
  induction path with
  | refl => exact ⟨sorted, .refl (operation.fold_sorted _ sorted)⟩
  | @tail middle target priorPath step ih =>
    refine ⟨transition_sorted step ih.1, ?_⟩
    exact reaches_then_step ih.2 (transition_source_step step ih.1)
      (operation.fold_sorted _ (transition_sorted step ih.1))

#print axioms transition_source_step
#print axioms path_source_reaches

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.MutexSourceSteps
