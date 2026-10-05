import Mettapedia.Languages.MM0.Presentation.DeclarationAccess

/-! # Authored checks of preceding-scope MM0 contexts -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration

open Kernel ComputationalContext ComputationalTyping ComputationalProof
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => declarationProgram
local notation "A" => declarationEquations
local notation "H" => dataEqualityHost

private theorem bound_next_computes (checked : Bool) (context : Context) (indices : List Nat)
    (tail : Applies P H "mm0:form-bound-indices" [encodeContext context, encodeNaturals indices]
      (boolean (indices.all (Context.isBound context)))) :
    Applies P H "mm0:form-bound-next" [boolean checked, encodeContext context, encodeNaturals indices]
      (boolean (checked && indices.all (Context.isBound context))) := by
  cases checked with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[12]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

theorem bound_indices_computes (context : Context) (indices : List Nat) :
    Applies P H "mm0:form-bound-indices" [encodeContext context, encodeNaturals indices]
      (boolean (indices.all (Context.isBound context))) := by
  induction indices with
  | nil => exact ⟨3, by rw [declaration_apply _ (by decide)]; rfl⟩
  | cons first rest ih =>
      refine declaration_equation (equation := A[8]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView ((first :: rest).map natural), encodeContext context])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_computes _)
      · refine declaration_equation (equation := A[10]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
          (bound_next_computes _ context rest ih)
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (bound_index_computes context first)

theorem bound_dependencies_computes (context : Context) (dependencies : Finset Nat) :
    Applies P H "mm0:form-bound-indices" [encodeContext context, encodeDependencies dependencies]
      (boolean (decide (∀ index ∈ dependencies, Context.isBound context index = true))) := by
  have same : (dependencies.sort (· ≤ ·)).all (Context.isBound context) =
      decide (∀ index ∈ dependencies, Context.isBound context index = true) := by
    apply Bool.eq_iff_iff.mpr
    simp [List.all_eq_true]
  simpa only [encodeDependencies, same] using bound_indices_computes context (dependencies.sort (· ≤ ·))

private theorem binder_dependencies_computes (known : Bool) (context : Context) (dependencies : Finset Nat) :
    Applies P H "mm0:form-binder-deps" [boolean known, encodeContext context, encodeDependencies dependencies]
      (boolean (known && decide (∀ index ∈ dependencies, Context.isBound context index = true))) := by
  cases known with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[23]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (bound_dependencies_computes context dependencies)

theorem binder_computes (sorts : SortTable) (context : Context) (binder : Kernel.Binder) :
    Applies P H "mm0:form-binder" [encodeSorts sorts, encodeContext context, encodeBinder binder]
      (boolean (Context.checkBinder (sortsOf sorts) context binder)) := by
  cases binder with
  | bound sort =>
      refine declaration_equation (equation := A[20]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.symbol _ _ _ _) .nil))) ?_
      have run := sort_computes sorts sort .bound
      cases known : sortsOf sorts sort <;> simpa [Context.checkBinder, known, SortUse.name, SortUse.allows] using run
  | regular sort dependencies =>
      refine declaration_equation (equation := A[21]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean ((sortsOf sorts sort).any SortUse.regular.allows),
        encodeContext context, encodeDependencies dependencies]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.symbol _ _ _ _) .nil)))
          (sort_computes sorts sort .regular)
      · have next := binder_dependencies_computes ((sortsOf sorts sort).any SortUse.regular.allows) context dependencies
        cases known : sortsOf sorts sort <;> simpa [Context.checkBinder, known, SortUse.allows] using next

private theorem context_next_computes (sorts : SortTable) (initial : Context) (binder : Kernel.Binder)
    (remaining : Context) (checked : Bool)
    (tail : Applies P H "mm0:form-context-from"
      [encodeSorts sorts, encodeContext (initial ++ [binder]), encodeContext remaining]
      (boolean (Context.checkFrom (sortsOf sorts) (initial ++ [binder]) remaining))) :
    Applies P H "mm0:form-context-next"
      [boolean checked, encodeSorts sorts, encodeContext initial, encodeBinder binder, encodeContext remaining]
      (boolean (checked && Context.checkFrom (sortsOf sorts) (initial ++ [binder]) remaining)) := by
  cases checked with
  | false => exact ⟨1, by rw [declaration_apply _ (by decide)]; rfl⟩
  | true =>
      refine declaration_equation (equation := A[28]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) .nil))) tail
      refine Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (Evaluates.list (.cons (.variable (by rfl)) .nil)) .nil)) ?_
      simpa only [encodeContext, List.map_append, List.map_cons, List.map_nil] using
        append_reused (initial.map encodeBinder) [encodeBinder binder]

theorem context_from_computes (sorts : SortTable) (initial remaining : Context) :
    Applies P H "mm0:form-context-from" [encodeSorts sorts, encodeContext initial, encodeContext remaining]
      (boolean (Context.checkFrom (sortsOf sorts) initial remaining)) := by
  induction remaining generalizing initial with
  | nil => exact ⟨3, by rw [declaration_apply _ (by decide)]; rfl⟩
  | cons binder remaining ih =>
      refine declaration_equation (equation := A[24]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView ((binder :: remaining).map encodeBinder), encodeSorts sorts, encodeContext initial])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_computes _)
      · refine declaration_equation (equation := A[26]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
          (context_next_computes sorts initial binder remaining _ (ih (initial ++ [binder])))
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
          (binder_computes sorts initial binder)

theorem context_computes (sorts : SortTable) (context : Context) :
    Applies P H "mm0:form-context" [encodeSorts sorts, encodeContext context]
      (boolean (Context.check (sortsOf sorts) context)) := by
  refine declaration_equation (equation := A[29]) (by decide) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (Evaluates.list .nil) (.cons (.variable (by rfl)) .nil)))
    (context_from_computes sorts [] context)

theorem context_accepts_iff (sorts : SortTable) (context : Context) :
    Applies P H "mm0:form-context" [encodeSorts sorts, encodeContext context] (.sym "True") ↔
      Context.WellFormed (sortsOf sorts) context := by
  rw [← Context.check_iff]
  constructor
  · intro accepted
    have same := accepted.deterministic (context_computes sorts context)
    cases checked : Context.check (sortsOf sorts) context with
    | false => simp [checked, boolean] at same
    | true => rfl
  · intro accepted
    simpa [accepted, boolean] using context_computes sorts context

theorem context_refuses_iff (sorts : SortTable) (context : Context) :
    Applies P H "mm0:form-context" [encodeSorts sorts, encodeContext context] (.sym "False") ↔
      ¬ Context.WellFormed (sortsOf sorts) context := by
  rw [← Context.check_iff]
  constructor
  · intro refused accepted
    have same := refused.deterministic (context_computes sorts context)
    simp [accepted, boolean] at same
  · intro refused
    cases checked : Context.check (sortsOf sorts) context with
    | true => exact False.elim (refused checked)
    | false => simpa [checked, boolean] using context_computes sorts context

end Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration
