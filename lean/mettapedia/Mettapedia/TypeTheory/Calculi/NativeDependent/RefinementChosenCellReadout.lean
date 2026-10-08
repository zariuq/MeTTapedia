import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModelMapCorrectedComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementChosenContextFixedPoint

/-!
# Independent complete readings of chosen comparison cells

Variable-preserving presentation arrows become equality arrows at genuine
chosen mixed scopes. The canonical corrected comparison consequently reads
the equality of two independent complete mixed-scope interpretations. This
earns the local declaration square without defining admission by reference
to the canonical cell itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Presentation

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem variable_arrow_eqToHom {Γ Δ : Context D} (same : Γ = Δ)
    (arrow : Γ ⟶ Δ) (positions : HEq arrow.substitution
      (TermExpr.var : Fin Γ.arity → TermExpr S Γ.arity)) : arrow = eqToHom same := by
  cases same
  exact Hom.ext (eq_of_heq positions)

theorem comparison_hom_chosen {Γ : Context D} (chosen : Chosen D Γ) :
    (comparison Γ).hom = eqToHom (selectedContext_fixed chosen) :=
  variable_arrow_eqToHom (selectedContext_fixed chosen) (comparison Γ).hom HEq.rfl

theorem comparison_inv_chosen {Γ : Context D} (chosen : Chosen D Γ) :
    (comparison Γ).inv = eqToHom (selectedContext_fixed chosen).symm :=
  variable_arrow_eqToHom (selectedContext_fixed chosen).symm (comparison Γ).inv HEq.rfl

theorem quotientNormalizer_obj_chosen {Γ : quotientContext D} (chosen : Chosen D Γ.as) :
    (quotientNormalizer D).obj Γ = Γ :=
  congrArg (fun context => (quotientProjection D).obj context) (selectedContext_fixed chosen)

theorem quotientComparison_hom_chosen {Γ : quotientContext D} (chosen : Chosen D Γ.as) :
    (quotientComparison Γ).hom = eqToHom (quotientNormalizer_obj_chosen chosen) := by
  change (quotientProjection D).map (comparison Γ.as).hom = _
  rw [comparison_hom_chosen chosen, eqToHom_map]

theorem quotientComparison_inv_chosen {Γ : quotientContext D} (chosen : Chosen D Γ.as) :
    (quotientComparison Γ).inv = eqToHom (quotientNormalizer_obj_chosen chosen).symm := by
  change (quotientProjection D).map (comparison Γ.as).inv = _
  rw [comparison_inv_chosen chosen, eqToHom_map]

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Presentation

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Refinement.Abstract

universe u z p
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
  {targetModel : LocalModel.{max u z,max u z,max u z,max u z,p} C}
  {target : ModelData S C targetModel}
variable (headers : HeaderFormation D)
  (first second : ModelMap (Interpretation.sourceData.{u,z} headers) target)

theorem contextIso_hom_mixed {n : Nat} {Γ : QuotientCwf.QContext D}
    (mixed : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n Γ) :
    (contextIso headers first second).hom.app Γ =
      eqToHom (ContextualBase.Context.ext (context_equal_mixed headers first second mixed)) := by
  rw [contextIso_hom_component]
  rw [Presentation.quotientComparison_hom_chosen (Presentation.chosen_of_scope mixed),
    Presentation.quotientComparison_inv_chosen (Presentation.chosen_of_scope mixed),
    eqToHom_map, eqToHom_map]
  simp only [eqToHom_trans]

theorem correctedIso_hom_mixed {n : Nat} {Γ : QuotientCwf.QContext D}
    (mixed : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n Γ) :
    (correctedIso headers first second).hom.base.app ⟨ULift.up Γ⟩ =
      eqToHom (ContextualBase.Context.ext (context_equal_mixed headers first second mixed)) :=
  contextIso_hom_mixed headers first second mixed

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison
