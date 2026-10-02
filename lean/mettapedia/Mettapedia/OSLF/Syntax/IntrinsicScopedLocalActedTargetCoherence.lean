import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetTransport
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetPostcompositionCoherence
import Mettapedia.OSLF.Syntax.CategoricalBindingTargetCoherence

/-!
# Coherence of qualified operational target changes

Identity and successive target changes compare by natural model
isomorphisms. Their classification comparisons are inherited from actual
postcomposition through the proved model equivalence.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v u' v' u'' v''

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D'] [HasPullbacks D']
variable {D'' : Type u''} [Category.{v''} D''] [CartesianMonoidalCategory D''] [HasPullbacks D'']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

/-- The adjointified unit of the checked classification equivalence. -/
def coherentClassificationUnit :
    𝟭 (CategoricalModel R equations (D := D)) ≅ classifyFunctor ⋙ modelFunctor :=
  (classificationEquivalence (R := R) (equations := equations) (D := D)).unitIso

/-- The classification unit and counit satisfy the equivalence triangle. -/
theorem coherentClassificationUnit_triangle (M : CategoricalModel R equations (D := D)) :
    counitNatIso.hom.app (classifyFunctor.obj M) =
      classifyFunctor.map (coherentClassificationUnit.inv.app M) :=
  (classificationEquivalence (R := R) (equations := equations) (D := D)).counit_app_functor M

/-- Identity transport is naturally isomorphic to the original model. -/
def transportModelsIdentityIso :
    transportModels (R := R) (equations := equations) (𝟭 D) ≅
      𝟭 (CategoricalModel R equations (D := D)) :=
  transportModelsRecoveryIso (𝟭 D) ≪≫
    Functor.isoWhiskerLeft classifyFunctor
      (Functor.isoWhiskerRight postcomposeStructuredIdentityIso modelFunctor) ≪≫
    Functor.isoWhiskerLeft classifyFunctor (Functor.leftUnitor modelFunctor) ≪≫
    coherentClassificationUnit.symm

set_option backward.isDefEq.respectTransparency false in
/-- The classification comparison for identity transport agrees with the
identity model comparison, using the equivalence triangle law. -/
theorem targetClassification_identity (M : CategoricalModel R equations (D := D)) :
    (targetClassificationIso (R := R) (equations := equations) (𝟭 D)).hom.app M ≫
      postcomposeStructuredIdentityIso.hom.app (classifyFunctor.obj M) =
    classifyFunctor.map (transportModelsIdentityIso.hom.app M) := by
  have triangle := coherentClassificationUnit_triangle M
  have natural := counitNatIso.hom.naturality
    (postcomposeStructuredIdentityIso.hom.app (classifyFunctor.obj M))
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.id_map] at natural
  simp only [targetClassificationIso, transportModelsIdentityIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app, Functor.map_comp,
    Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [Category.id_comp, _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  slice_lhs 2 3 => rw [← natural, triangle]

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the natural classification comparisons for identity target
change, including the functor unitors. -/
theorem targetClassification_identity_iso :
    Functor.isoWhiskerRight (transportModelsIdentityIso (R := R) (equations := equations))
        classifyFunctor ≪≫ Functor.leftUnitor classifyFunctor =
    targetClassificationIso (R := R) (equations := equations) (𝟭 D) ≪≫
      Functor.isoWhiskerLeft classifyFunctor postcomposeStructuredIdentityIso ≪≫
        Functor.rightUnitor classifyFunctor := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Functor.comp_obj]
  erw [Category.comp_id, Category.comp_id]
  exact (targetClassification_identity M).symm

variable (H : D ⥤ D') (K : D' ⥤ D'')
variable [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]
variable [PreservesFiniteProducts K] [PreservesLimitsOfShape WalkingCospan K]
variable [ExponentialPreservation K]

/-- Transporting twice agrees naturally with transporting along the
composite target change. -/
def transportModelsCompositionIso :
    transportModels (R := R) (equations := equations) H ⋙ transportModels K ≅
      transportModels (H ⋙ K) :=
  Functor.isoWhiskerRight (transportModelsRecoveryIso H) (transportModels K) ≪≫
    Functor.isoWhiskerLeft (recoveredTargetTransport H) (transportModelsRecoveryIso K) ≪≫
    Functor.isoWhiskerLeft (classifyFunctor ⋙ postcomposeStructured H)
      (Functor.isoWhiskerRight counitNatIso (postcomposeStructured K ⋙ modelFunctor)) ≪≫
    Functor.isoWhiskerLeft (classifyFunctor ⋙ postcomposeStructured H)
      (Functor.leftUnitor (postcomposeStructured K ⋙ modelFunctor)) ≪≫
    Functor.isoWhiskerLeft classifyFunctor
      (Functor.isoWhiskerRight (postcomposeStructuredCompositionIso H K) modelFunctor) ≪≫
    (transportModelsRecoveryIso (H ⋙ K)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The classification square for two changes of target agrees with the
square for their composite, through the natural model comparison. -/
theorem targetClassification_composition (M : CategoricalModel R equations (D := D)) :
    classifyFunctor.map ((transportModelsCompositionIso H K).hom.app M) ≫
      (targetClassificationIso (H ⋙ K)).hom.app M =
    (targetClassificationIso K).hom.app ((transportModels H).obj M) ≫
      (postcomposeStructured K).map ((targetClassificationIso H).hom.app M) ≫
        (postcomposeStructuredCompositionIso H K).hom.app (classifyFunctor.obj M) := by
  have restage := (transportModelsRecoveryIso K).hom.naturality
    ((transportModelsRecoveryIso H).hom.app M)
  have first := (counitNatIso (D := D'')).hom.naturality
    ((postcomposeStructured K).map (classifyFunctor.map ((transportModelsRecoveryIso H).hom.app M)))
  have second := (counitNatIso (D := D'')).hom.naturality
    ((postcomposeStructured K).map ((counitNatIso (D := D')).hom.app
      ((postcomposeStructured H).obj (classifyFunctor.obj M))))
  have third := (counitNatIso (D := D'')).hom.naturality
    ((postcomposeStructuredCompositionIso H K).hom.app (classifyFunctor.obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at restage first second third
  simp only [targetClassificationIso, transportModelsCompositionIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Functor.map_comp, Category.assoc, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  erw [_root_.CategoryTheory.Functor.map_id, _root_.CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.id_comp, Category.id_comp]
  slice_lhs 5 6 =>
    rw [← Functor.map_comp, (transportModelsRecoveryIso (H ⋙ K)).inv_hom_id_app]
    erw [_root_.CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  slice_lhs 1 2 => rw [← Functor.map_comp, restage, Functor.map_comp]
  slice_lhs 4 5 => rw [third]
  slice_lhs 3 4 => rw [second]
  slice_lhs 2 3 => rw [first]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the natural classification squares for successive target
changes, with the required functor associators. -/
theorem targetClassification_composition_iso :
    Functor.isoWhiskerRight (transportModelsCompositionIso (R := R) (equations := equations) H K)
        classifyFunctor ≪≫ targetClassificationIso (H ⋙ K) =
    Functor.associator (transportModels H) (transportModels K) classifyFunctor ≪≫
      Functor.isoWhiskerLeft (transportModels H) (targetClassificationIso K) ≪≫
        (Functor.associator (transportModels H) classifyFunctor (postcomposeStructured K)).symm ≪≫
          Functor.isoWhiskerRight (targetClassificationIso H) (postcomposeStructured K) ≪≫
            Functor.associator classifyFunctor (postcomposeStructured H) (postcomposeStructured K) ≪≫
              Functor.isoWhiskerLeft classifyFunctor (postcomposeStructuredCompositionIso H K) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp]
  exact targetClassification_composition H K M

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
