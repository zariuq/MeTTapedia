import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModelMapChosenComparison

/-!
# Natural comparison retaining authored mixed contexts

The earned mixed-scope comparisons identify the two actual model functors
after chosen presentation. Conjugating through the independent raw-context
presentation isomorphisms gives a natural isomorphism on every retained raw
context and every admitted guarded substitution. No equality quotient of
raw context objects is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualPredicateModel
open Refinement.Abstract

universe u z p
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
  {targetModel : LocalModel.{max u z,max u z,max u z,max u z,p} C}
  {target : ModelData S C targetModel}

def contextFunctor {headers : HeaderFormation D}
    (mapping : ModelMap (Interpretation.sourceData.{u,z} headers) target) :
    quotientContext D ⥤ C.toCwf.base.Context where
  obj Γ := mapping.morphism.toFamilyMorphism.base.obj ⟨ULift.up Γ⟩
  map arrow := mapping.morphism.toFamilyMorphism.base.map (ULift.up arrow)
  map_id Γ := mapping.morphism.toFamilyMorphism.base.map_id ⟨ULift.up Γ⟩
  map_comp {Γ Δ Θ} first second := by
    let first' : (⟨ULift.up Γ⟩ : (Interpretation.SourceModel.{u,z} D).toCwf.base.Context) ⟶
      ⟨ULift.up Δ⟩ := ULift.up first
    let second' : (⟨ULift.up Δ⟩ : (Interpretation.SourceModel.{u,z} D).toCwf.base.Context) ⟶
      ⟨ULift.up Θ⟩ := ULift.up second
    exact mapping.morphism.toFamilyMorphism.base.map_comp first' second'

variable (headers : HeaderFormation D)
  (first second : ModelMap (Interpretation.sourceData.{u,z} headers) target)

theorem normalized_functor_equal :
    Presentation.quotientNormalizer D ⋙ contextFunctor first =
      Presentation.quotientNormalizer D ⋙ contextFunctor second := by
  apply Functor.hext
  · intro Γ
    apply ContextualBase.Context.ext
    exact context_equal_mixed headers first second (Presentation.selectedScopeData Γ.as)
  · intro Γ Δ arrow
    exact arrow_heq_mixed headers first second (Presentation.selectedScopeData Γ.as)
      (Presentation.selectedScopeData Δ.as)
      (ULift.up ((Presentation.quotientNormalizer D).map arrow))

noncomputable def contextIso : contextFunctor first ≅ contextFunctor second :=
  (Functor.leftUnitor (contextFunctor first)).symm ≪≫
    (Functor.isoWhiskerRight (Presentation.quotientNormalizerIso D) (contextFunctor first)).symm ≪≫
      eqToIso (normalized_functor_equal headers first second) ≪≫
        Functor.isoWhiskerRight (Presentation.quotientNormalizerIso D) (contextFunctor second) ≪≫
          Functor.leftUnitor (contextFunctor second)

theorem contextIso_hom_component (Γ : quotientContext D) :
    (contextIso headers first second).hom.app Γ =
      (contextFunctor first).map (Presentation.quotientComparison Γ).inv ≫
        eqToHom (congrArg (fun functor => functor.obj Γ)
          (normalized_functor_equal headers first second)) ≫
          (contextFunctor second).map (Presentation.quotientComparison Γ).hom := by
  simp only [contextIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, eqToIso.hom, eqToHom_app]
  erw [Category.comp_id]
  rfl

theorem contextIso_naturality {Γ Δ : quotientContext D} (arrow : Γ ⟶ Δ) :
    (contextFunctor first).map arrow ≫ (contextIso headers first second).hom.app Δ =
      (contextIso headers first second).hom.app Γ ≫ (contextFunctor second).map arrow :=
  (contextIso headers first second).hom.naturality arrow

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison
