import Mettapedia.Languages.MM0.Kernel.FreeVariables

/-! # Binding, dependency and saturation controls for MM0 free variables -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.FreeVariablesControls

open Preterm

private def context : Context :=
  [.bound 0, .bound 0, .bound 0, .regular 1 {0, 1, 2}, .regular 1 ∅,
    .bound 1, .regular 0 ∅]

private def signature : TermSignature
  | 0 => some ⟨[.regular 1 ∅], 1, ∅⟩
  | 1 => some ⟨[.bound 0], 1, {0}⟩
  | 2 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 3 => some ⟨[.bound 0, .regular 1 ∅], 1, ∅⟩
  | 4 => some ⟨[.bound 0, .bound 0, .regular 1 {0}], 1, {1}⟩
  | 5 => some ⟨[.bound 0], 1, ∅⟩
  | 6 => some ⟨[.bound 0, .bound 0, .regular 1 {0, 1}], 1, ∅⟩
  | 7 => some ⟨[], 0, ∅⟩
  | _ => none

private def negation : Preterm := .applyArgs (.term 0) [.var 3]
private def quantified : Preterm := .applyArgs (.term 2) [.var 0, .var 3]
private def selective : Preterm := .applyArgs (.term 4) [.var 0, .var 1, .var 3]

/-- A surviving regular argument does not need a returned bound dependency. -/
theorem regular_contribution_without_return_dependency :
    freeVariables? signature context negation = some {0, 1, 2} := by decide

/-- A returned bound dependency does not need any regular argument. -/
theorem returned_dependency_without_regular_argument :
    freeVariables? signature context (.app (.term 1) (.var 0)) = some {0} := by decide

theorem regular_variable_uses_declared_dependencies :
    freeVariables? signature context (.var 3) = some {0, 1, 2} := by decide

theorem independent_regular_variable_has_no_free_bound_variable :
    freeVariables? signature context (.var 4) = some ∅ := by decide

theorem declared_binder_removes_only_its_image :
    freeVariables? signature context quantified = some {1, 2} := by decide

theorem bound_slot_without_regular_dependency_does_not_bind :
    freeVariables? signature context (.applyArgs (.term 3) [.var 0, .var 3]) =
      some {0, 1, 2} := by decide

theorem per_argument_binding_and_return_dependency_join :
    freeVariables? signature context selective = some {1, 2} := by decide

theorem unused_bound_argument_is_not_free :
    freeVariables? signature context (.app (.term 5) (.var 0)) = some ∅ := by decide

theorem nested_binders_compose :
    freeVariables? signature context
      (.applyArgs (.term 2) [.var 1, quantified]) = some {2} := by decide

theorem multiple_bound_dependencies_removed :
    freeVariables? signature context
      (.applyArgs (.term 6) [.var 0, .var 1, .var 3]) = some {2} := by decide

/-- Ordinary constructor typing permits aliased bound arguments. Distinctness
is a separate requirement of theorem substitution. -/
theorem aliased_bound_images_are_a_set :
    freeVariables? signature context
      (.applyArgs (.term 6) [.var 0, .var 0, .var 3]) = some {1, 2} := by decide

theorem selected_free_occurrence_has_independent_evidence :
    IsFree signature context selective 2 := by
  exact ⟨{1, 2}, (freeVariables_eq_some_iff _ _ _ _).mp
    per_argument_binding_and_return_dependency_join, by decide⟩

theorem bound_occurrence_is_not_free : ¬ IsFree signature context quantified 0 := by
  rintro ⟨free, proof, member⟩
  have same := Option.some.inj (proof.eval.symm.trans declared_binder_removes_only_its_image)
  subst free
  exact (by decide : 0 ∉ ({1, 2} : Finset Nat)) member

/-- Occurrence support still includes the supplied bound argument after binding. -/
theorem bound_occurrence_retained_in_support : HasVar context 0 quantified := by
  apply (hasVar_applyArgs_iff _ _ _ _).mpr
  exact .inr ⟨.var 0, by simp, .bound (by rfl)⟩

theorem undefined_variable_rejected :
    freeVariables? signature context (.var 7) = none := by decide

theorem undefined_term_rejected :
    freeVariables? signature context (.term 8) = none := by decide

theorem partial_application_rejected :
    freeVariables? signature context (.app (.term 2) (.var 0)) = none := by decide

theorem overapplication_rejected :
    freeVariables? signature context (.app (.term 7) (.var 0)) = none := by decide

theorem regular_variable_in_bound_slot_rejected :
    freeVariables? signature context (.app (.term 1) (.var 6)) = none := by decide

theorem wrong_sort_bound_argument_rejected :
    freeVariables? signature context (.app (.term 1) (.var 5)) = none := by decide

theorem partial_regular_argument_rejected :
    freeVariables? signature context (.app (.term 0) (.term 2)) = none := by decide

theorem undefined_nested_child_rejected :
    freeVariables? signature context (.app (.term 0) (.var 7)) = none := by decide

theorem partial_application_has_no_free_variable_derivation :
    ¬ ∃ free, FreeVars signature context (.app (.term 2) (.var 0)) free :=
  (freeVariables_none_iff _ _ _).mp partial_application_rejected

private def invalidSignature : TermSignature
  | 0 => some ⟨[.bound 0], 1, {1}⟩
  | 1 => some ⟨[.regular 1 ∅], 1, {0}⟩
  | 2 => some ⟨[.bound 0, .regular 1 {1}], 1, ∅⟩
  | _ => none

theorem out_of_range_return_dependency_rejected :
    freeVariables? invalidSignature context (.app (.term 0) (.var 0)) = none := by decide

theorem regular_slot_as_return_dependency_rejected :
    freeVariables? invalidSignature context (.app (.term 1) (.var 3)) = none := by decide

theorem regular_slot_as_binding_dependency_rejected :
    freeVariables? invalidSignature context
      (.applyArgs (.term 2) [.var 0, .var 3]) = none := by decide

/-- Typing alone does not certify the declaration's dependency metadata. -/
theorem invalid_dependency_can_remain_typed :
    HasType invalidSignature context (.app (.term 0) (.var 0)) [] 1 :=
  (infer_eq_some_iff _ _ _ _ _).mp (by decide)

private theorem signature_dependencies_bound (symbol : Nat) (declaration : TermDecl)
    (lookup : signature symbol = some declaration) : declaration.DependenciesBound := by
  unfold signature at lookup
  split at lookup <;> simp at lookup
  all_goals
    subst declaration
    constructor <;> simp

/-- All saturated well-typed expressions over this declared signature have
free-variable results, independently of their traversal depth and shape. -/
theorem typed_signature_has_total_free_variables {source : Preterm} {sort : Nat}
    (typing : HasType signature context source [] sort) :
    ∃ free, freeVariables? signature context source = some free :=
  typing.freeVariables_exists signature_dependencies_bound

theorem returned_and_regular_contributions_are_independent :
    FreeVars signature context negation {0, 1, 2} ∧
      FreeVars signature context (.app (.term 1) (.var 0)) {0} :=
  ⟨(freeVariables_eq_some_iff _ _ _ _).mp regular_contribution_without_return_dependency,
    (freeVariables_eq_some_iff _ _ _ _).mp returned_dependency_without_regular_argument⟩

end Mettapedia.Languages.MM0.Kernel.FreeVariablesControls
