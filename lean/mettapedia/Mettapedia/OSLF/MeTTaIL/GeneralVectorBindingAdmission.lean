import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance

/-! Completeness of the existing root-input binding inference for declared
first-order vector schemas with unique metavariable declarations. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Syntax Match RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem inferred_admitted (rule : RewriteRule) (unique : (rule.typeContext.map Prod.fst).Nodup) :
    admittedFor rule (inferredSpec rule) = true := by
  simp only [admittedFor,inferredSpec,List.map_map,Function.comp_def,List.length_map,
    decide_true,unique,beq_self_eq_true,List.all_nil,Bool.and_true,Bool.true_and]
  apply List.all_eq_true.mpr
  intro entry member
  apply List.any_eq_true.mpr
  exact ⟨(entry.1,[]),List.mem_map.mpr ⟨entry,member,rfl⟩,by simp⟩

theorem inferred_sorts (language : LanguageDef) (rule : RewriteRule) :
    dependencySortsDeclared language (inferredSpec rule) = true := by
  simp [dependencySortsDeclared,inferredSpec]

private theorem root_arguments (patterns : List Pattern)
    (each : ∀ pattern ∈ patterns, rootInput 0 pattern = true) : rootArguments 0 patterns = true := by
  induction patterns with
  | nil => simp [rootArguments]
  | cons pattern patterns ih =>
    simp only [rootArguments,each pattern List.mem_cons_self,Bool.true_and]
    exact ih (fun child member => each child (List.mem_cons_of_mem _ member))

theorem vector_root {code : Pattern} (shape : VectorFirstOrder code) : rootInput 0 code = true := by
  induction shape with
  | metavariable _ => simp [rootInput]
  | constructor _ patterns _ ih => simpa only [rootInput] using root_arguments patterns ih
  | vector patterns _ ih =>
    simp only [rootInput,Option.isNone_none,Bool.true_or,Bool.and_true]
    exact root_arguments patterns ih

private theorem canonical_arguments (patterns : List Pattern)
    (each : ∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true) :
    Pattern.hasCanonicalBinderMetadataList patterns = true := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
    simp only [Pattern.hasCanonicalBinderMetadataList,each pattern List.mem_cons_self,Bool.true_and]
    exact ih (fun child member => each child (List.mem_cons_of_mem _ member))

theorem vector_canonical {code : Pattern} (shape : VectorFirstOrder code) :
    code.hasCanonicalBinderMetadata = true := by
  induction shape with
  | metavariable _ => rfl
  | constructor _ patterns _ ih => exact canonical_arguments patterns ih
  | vector patterns _ ih => exact canonical_arguments patterns ih

private theorem object_arguments (patterns : List Pattern)
    (each : ∀ pattern ∈ patterns, isObjectPattern pattern = true) : isObjectPatternList patterns = true := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
    simp only [isObjectPatternList,each pattern List.mem_cons_self,Bool.true_and]
    exact ih (fun child member => each child (List.mem_cons_of_mem _ member))

theorem vector_object {code : Pattern} (shape : VectorFirstOrder code) : isObjectPattern code = true := by
  induction shape with
  | metavariable _ => rfl
  | constructor _ patterns _ ih => exact object_arguments patterns ih
  | vector patterns _ ih =>
    simp only [isObjectPattern,Option.isNone_none,Bool.true_and]
    exact object_arguments patterns ih

private theorem binder_free_arguments (patterns : List Pattern)
    (each : ∀ pattern ∈ patterns, binderFree pattern = true) : binderFreeList patterns = true := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
    simp only [binderFreeList,each pattern List.mem_cons_self,Bool.true_and]
    exact ih (fun child member => each child (List.mem_cons_of_mem _ member))

theorem vector_binderFree {code : Pattern} (shape : VectorFirstOrder code) : binderFree code = true := by
  induction shape with
  | metavariable _ => rfl
  | constructor _ patterns _ ih => exact binder_free_arguments patterns ih
  | vector patterns _ ih => exact binder_free_arguments patterns ih

theorem compile_root_inputs (language : LanguageDef) (rule : RewriteRule)
    (omitted : rule.bindings = none) (root : rootInput 0 rule.left = true)
    (declared : rootDeclared rule = true) (unique : (rule.typeContext.map Prod.fst).Nodup) :
    compile? language rule = some ⟨inferredSpec rule,.inferredRootInputs⟩ := by
  simp only [compile?,omitted,root,declared,inferred_admitted rule unique,
    inferred_sorts language rule,Bool.and_self,if_true]

#print axioms inferred_admitted
#print axioms compile_root_inputs

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
