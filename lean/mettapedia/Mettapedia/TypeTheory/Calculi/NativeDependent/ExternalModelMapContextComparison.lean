import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapChosenComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualPresentation

/-!
# Context comparison of generated dependent model maps

The earned finite-telescope readbacks identify the two model-map functors after
chosen presentation. Conjugating that equality through the actual presentation
isomorphism gives a natural isomorphism on every retained raw context and every
admitted substitution. This is an actual context comparison; the displayed
logical coherence and its classifying uniqueness are further obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{u, u, u, u}} {target : ModelData S C}

/-- The actual model-map base functor with the syntactic context wrapper
removed from its source objects. Substitution arrows are unchanged. -/
def contextFunctor {headers : HeaderFormation D}
    (mapping : ModelMap (SyntacticModel.data headers) target) :
    quotientContext D ⥤ C.toCwf.base.Context where
  obj Γ := mapping.morphism.toFamilyMorphism.base.obj ⟨Γ⟩
  map arrow := mapping.morphism.toFamilyMorphism.base.map arrow
  map_id Γ := mapping.morphism.toFamilyMorphism.base.map_id ⟨Γ⟩
  map_comp first second := mapping.morphism.toFamilyMorphism.base.map_comp first second

variable (headers : HeaderFormation D)
  (first second : ModelMap (SyntacticModel.data headers) target)

theorem normalized_functor_equal :
    Presentation.quotientNormalizer D ⋙ contextFunctor first =
      Presentation.quotientNormalizer D ⋙ contextFunctor second := by
  apply Functor.hext
  · intro Γ
    apply ContextualBase.Context.ext
    exact context_equal_telescope headers first second (Presentation.selectedTelescope Γ.as)
  · intro Γ Δ arrow
    exact arrow_heq_telescope headers first second (Presentation.selectedTelescope Γ.as)
      (Presentation.selectedTelescope Δ.as) ((Presentation.quotientNormalizer D).map arrow)

/-- Every raw admitted context retains its original object. The component
is transported through the actual generated presentation isomorphism. -/
noncomputable def contextIso : contextFunctor first ≅ contextFunctor second :=
  (Functor.leftUnitor (contextFunctor first)).symm ≪≫
    (Functor.isoWhiskerRight (Presentation.quotientNormalizerIso D) (contextFunctor first)).symm ≪≫
      eqToIso (normalized_functor_equal headers first second) ≪≫
        Functor.isoWhiskerRight (Presentation.quotientNormalizerIso D) (contextFunctor second) ≪≫
          Functor.leftUnitor (contextFunctor second)

set_option backward.isDefEq.respectTransparency false in
/-- The component is the actual conjugation, including the retained
source and destination context presentations. -/
theorem contextIso_hom_component (Γ : quotientContext D) :
    (contextIso headers first second).hom.app Γ =
      (contextFunctor first).map (Presentation.quotientComparison Γ).inv ≫
        eqToHom (congrArg (fun functor => functor.obj Γ)
          (normalized_functor_equal headers first second)) ≫
          (contextFunctor second).map (Presentation.quotientComparison Γ).hom := by
  simp only [contextIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.leftUnitor_inv_app, Category.id_comp,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, eqToIso.hom, eqToHom_app]
  erw [Category.comp_id]
  rfl

/-- Naturality covers every actual quotient substitution, not only the
substitutions used by the primitive declarations. -/
theorem contextIso_naturality {Γ Δ : quotientContext D} (arrow : Γ ⟶ Δ) :
    (contextFunctor first).map arrow ≫ (contextIso headers first second).hom.app Δ =
      (contextIso headers first second).hom.app Γ ≫ (contextFunctor second).map arrow :=
  (contextIso headers first second).hom.naturality arrow

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ModelMapComparison
