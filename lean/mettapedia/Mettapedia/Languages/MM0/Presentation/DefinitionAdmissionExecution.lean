import Mettapedia.Languages.MM0.Presentation.DefinitionAdmissionProgram

/-! # Actual context construction and residual-variable checks for MM0 bodies -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalDeclaration
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => bodyProgram
local notation "A" => bodyEquations
local notation "H" => dataEqualityHost

theorem declaration_suffix_reused (head : String) (used : head ∈ declarationEquations.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies declarationProgram H head arguments result) :
    Applies P H head arguments result :=
  declaration_reused head (by
    simp only [declarationProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr used) arguments result computed

theorem body_view_computes (values : List Term) :
    Applies P H "nik:list-view" [.list values] (listView values) := .primitive (by rfl) (by rfl)

theorem body_append_computes (left right : List Term) :
    Applies P H "nik:list-append" [.list left, .list right] (.list (left ++ right)) :=
  declaration_reused _ (by decide) _ _ (ComputationalDeclaration.append_reused left right)

theorem body_infer_computes (table : SignatureTable) (context : Context) (expression : Preterm) :
    Applies P H "mm0:infer" [encodeTable table, encodeContext context, encode expression]
      (encodeType (Preterm.infer (signatureOf table) context expression)) :=
  declaration_reused _ (by decide) _ _
    (ComputationalDeclaration.typing_reused _ (by decide) _ _ (infer_computes table context expression))

theorem dummy_context_computes (sorts : List Nat) :
    Applies P H "mm0:dummy-context" [encodeNaturals sorts]
      (encodeContext (sorts.map Kernel.Binder.bound)) := by
  induction sorts with
  | nil => exact ⟨3, by rw [body_apply _ (by decide)]; rfl⟩
  | cons first rest ih =>
      refine body_equation (equation := A[0]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView ((first :: rest).map natural)]) (by simp [Special]) (.cons ?_ .nil) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (body_view_computes _)
      · refine body_equation (equation := A[2]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call
          (values := [encodeBinder (.bound first), encodeContext (rest.map Kernel.Binder.bound)])
          (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) (.primitive (by rfl) (by rfl))
        · exact Evaluates.list (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil))
        · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) ih

theorem difference_computes (source removed : List Nat) :
    Applies P H "nik:nat-difference" [encodeNaturals source, encodeNaturals removed]
      (encodeNaturals (ComputationalFreeVariables.subtract source removed)) :=
  free_reused _ (by decide) _ _ (ComputationalFreeVariables.difference_reused source removed)

theorem free_variables_reused (table : SignatureTable) (context : Context) (expression : Preterm) :
    Applies P H "mm0:free-variables" [encodeTable table, encodeContext context, encode expression]
      (ComputationalSupport.encodeResult (ComputationalFreeVariables.indices? (signatureOf table) context expression)) :=
  free_reused _ (by decide) _ _ (ComputationalFreeVariables.free_variables_computes table context expression)

private theorem free_view_computes (free : List Nat) :
    Applies P H "mm0:body-free-view" [listView (free.map natural)] (boolean free.isEmpty) := by
  cases free <;> exact ⟨1, by rw [body_apply _ (by decide)]; rfl⟩

theorem subtract_empty_is_subset (free : List Nat) (dependencies : Finset Nat) :
    (ComputationalFreeVariables.subtract free (dependencies.sort (· ≤ ·))).isEmpty =
      decide (free.toFinset ⊆ dependencies) := by
  apply Bool.eq_iff_iff.mpr
  simp [ComputationalFreeVariables.subtract, List.filter_eq_nil_iff, Finset.subset_iff]

theorem body_free_computes (free : Option (List Nat)) (dependencies : Finset Nat) :
    Applies P H "mm0:body-free" [ComputationalSupport.encodeResult free, encodeDependencies dependencies]
      (boolean (match free with | none => false | some free => decide (free.toFinset ⊆ dependencies))) := by
  cases free with
  | none => exact ⟨1, by rw [body_apply _ (by decide)]; rfl⟩
  | some free =>
      change Applies P H "mm0:body-free"
        [ComputationalSupport.encodeResult (some free), encodeDependencies dependencies]
        (boolean (decide (free.toFinset ⊆ dependencies)))
      rw [← subtract_empty_is_subset]
      refine body_equation (equation := A[4]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (free_view_computes _)
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (body_view_computes _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (difference_computes free (dependencies.sort (· ≤ ·)))

theorem free_check_meaning (signature : TermSignature) (context : Context)
    (expression : Preterm) (dependencies : Finset Nat) :
    (match ComputationalFreeVariables.indices? signature context expression with
      | none => false | some free => decide (free.toFinset ⊆ dependencies)) =
    (match Preterm.freeVariables? signature context expression with
      | none => false | some free => decide (free ⊆ dependencies)) := by
  rw [← ComputationalFreeVariables.indices_meaning]
  cases ComputationalFreeVariables.indices? signature context expression <;> rfl

theorem body_free_checked (table : SignatureTable) (context : Context)
    (expression : Preterm) (dependencies : Finset Nat) :
    Applies P H "mm0:body-free"
      [ComputationalSupport.encodeResult (ComputationalFreeVariables.indices? (signatureOf table) context expression),
        encodeDependencies dependencies]
      (boolean (match Preterm.freeVariables? (signatureOf table) context expression with
        | none => false | some free => decide (free ⊆ dependencies))) := by
  simpa only [free_check_meaning] using body_free_computes
    (ComputationalFreeVariables.indices? (signatureOf table) context expression) dependencies

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission
