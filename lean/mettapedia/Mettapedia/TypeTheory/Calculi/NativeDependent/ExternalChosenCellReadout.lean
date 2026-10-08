import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapLiftedCorrectedComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalChosenContextFixedPoint

/-!
# Complete comparison readings at independent finite telescopes

Actual variable-preserving presentation arrows become equality comparisons
on the chosen finite-comprehension image. The model comparison therefore
agrees with the equality earned by evaluating the same independently authored
telescope in both models. This is a local declaration reading, stated without
defining admission by reference to the canonical comparison itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes

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

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.LiftedModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u z
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}} {target : ModelData S C}
variable (headers : HeaderFormation D)
  (first second : ModelMap (SyntacticModel.data headers).commonUniverseLift.{u,u,u,u,u,z} target)

/-- On any supplied genuine finite source telescope, the canonical cell
recovers the equality of the two independent complete telescope evaluations. -/
theorem contextIso_hom_telescope {n : Nat} {Γ : quotientContext D}
    (telescope : Telescope (QuotientCwf.withTerminal D) n Γ) :
    (contextIso headers first second).hom.app Γ =
      eqToHom (ContextualBase.Context.ext (context_equal_telescope headers first second telescope)) := by
  rw [contextIso_hom_component]
  rw [Presentation.quotientComparison_hom_chosen (Presentation.chosen_of_telescope telescope),
    Presentation.quotientComparison_inv_chosen (Presentation.chosen_of_telescope telescope),
    eqToHom_map, eqToHom_map]
  simp only [eqToHom_trans]

/-- The corrected comparison retains that same complete reading after the
source carrier and contextual wrappers are restored. -/
theorem correctedIso_hom_telescope {n : Nat} {Γ : quotientContext D}
    (telescope : Telescope (QuotientCwf.withTerminal D) n Γ) :
    (correctedIso headers first second).hom.base.app ⟨ULift.up Γ⟩ =
      eqToHom (ContextualBase.Context.ext (context_equal_telescope headers first second telescope)) :=
  contextIso_hom_telescope headers first second telescope

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.LiftedModelMapComparison
