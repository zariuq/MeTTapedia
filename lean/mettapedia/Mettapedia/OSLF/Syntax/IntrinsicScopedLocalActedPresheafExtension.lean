import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionCore
import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionIso
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedEquivalence

/-!
# The presheaf classifier's cocomplete universal property

A cocontinuous interpretation is a functor on the actual presheaves whose
Yoneda restriction has the existing chosen binding and event structure.
Its morphisms are all natural transformations. Left Kan extension and
restriction give an equivalence, which composes with the independently
defined model classification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.CategoryTheory.PresheafStructuredExtension

universe w u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {R : List (LocalRule S)} {equations : List (EqAxiom S schema)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- Functors preserving density colimits with chosen structure on their
actual Yoneda restriction. -/
structure CocontinuousInterpretation where
  carrier : Presheaves.{w, 0, 0, v} (Classifier R equations) ⥤ D
  cocontinuous : PreservesColimitsOfSize.{0, max w v} carrier
  program : Preserving ((authoredEquationPresentation S equations).quotientFunctor ⋙
    programSection R equations ⋙ embedding.{w, 0, 0, v} ⋙ carrier)
  pullback : ∀ {a b : Classifier R equations} (f : b ⟶ a)
    (j : Judgment (modelAt equations a.base)),
    IsPullback ((embedding.{w, 0, 0, v} ⋙ carrier).map (reindex R equations f j))
      ((embedding.{w, 0, 0, v} ⋙ carrier).map
        (projection R equations b (mapJudgment (modelMap equations f.base) j)))
      ((embedding.{w, 0, 0, v} ⋙ carrier).map (projection R equations a j))
      ((embedding.{w, 0, 0, v} ⋙ carrier).map f)

instance : Category (CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D)) where
  Hom L K := L.carrier ⟶ K.carrier
  id L := 𝟙 L.carrier
  comp f g := f ≫ g
  id_comp := by intros; exact Category.id_comp _
  comp_id := by intros; exact Category.comp_id _
  assoc := by intros; exact Category.assoc _ _ _

namespace CocontinuousInterpretation

/-- The structured restriction is actual precomposition with Yoneda. -/
def restriction (L : CocontinuousInterpretation.{w, u, v}
    (R := R) (equations := equations) (D := D)) : StructuredFunctor R equations (D := D) where
  carrier := embedding.{w, 0, 0, v} ⋙ L.carrier
  program := L.program
  pullback := L.pullback

/-- Restriction on every natural transformation. -/
def restrictionFunctor :
    CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D) ⥤
      StructuredFunctor R equations (D := D) where
  obj L := L.restriction
  map α := Functor.whiskerLeft embedding.{w, 0, 0, v} α
  map_id L := by apply NatTrans.ext; rfl
  map_comp α β := by apply NatTrans.ext; rfl

variable [HasColimitsOfSize.{0, max w v} D]

/-- Extend the actual classifying carrier; its restriction structure is
derived by transporting along the left-Kan-extension unit. -/
def extend (F : StructuredFunctor R equations (D := D)) :
    CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D) where
  carrier := (embedding.{w, 0, 0, v} (C := Classifier R equations)).lan.obj F.carrier
  cocontinuous := extension_cocontinuous F.carrier
  program := (F.ofIso ((unitIso.{w, 0, 0, v, u}).app F.carrier)).program
  pullback := (F.ofIso ((unitIso.{w, 0, 0, v, u}).app F.carrier)).pullback

/-- Extension acts by the actual left Kan extension on all maps. -/
def extensionFunctor : StructuredFunctor R equations (D := D) ⥤
    CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D) where
  obj F := extend F
  map α := (embedding.{w, 0, 0, v} (C := Classifier R equations)).lan.map α
  map_id F := (embedding.{w, 0, 0, v} (C := Classifier R equations)).lan.map_id F.carrier
  map_comp α β := (embedding.{w, 0, 0, v} (C := Classifier R equations)).lan.map_comp α β

/-- Unit naturality includes all classifier arrows and all noninvertible
maps of structured interpretations. -/
def extensionUnitIso : 𝟭 (StructuredFunctor R equations (D := D)) ≅
    extensionFunctor.{w, u, v} ⋙ restrictionFunctor :=
  NatIso.ofComponents
    (fun F => {
      hom := ((unitIso.{w, 0, 0, v, u}).app F.carrier).hom
      inv := ((unitIso.{w, 0, 0, v, u}).app F.carrier).inv
      hom_inv_id := ((unitIso.{w, 0, 0, v, u}).app F.carrier).hom_inv_id
      inv_hom_id := ((unitIso.{w, 0, 0, v, u}).app F.carrier).inv_hom_id })
    (fun {_F _G} α => (unitIso.{w, 0, 0, v, u}).hom.naturality α)

/-- The density adjunction counit is invertible on every interpretation. -/
def extensionCounitIso : restrictionFunctor.{w, u, v} ⋙ extensionFunctor ≅
    𝟭 (CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D)) :=
  NatIso.ofComponents
    (fun L => {
      hom := (((embedding.{w, 0, 0, v} (C := Classifier R equations)).lanAdjunction D).counit.app L.carrier)
      inv := (@asIso _ _ _ _
        (((embedding.{w, 0, 0, v} (C := Classifier R equations)).lanAdjunction D).counit.app L.carrier)
        (isIso_counit (L := ⟨L.carrier, L.cocontinuous⟩))).inv
      hom_inv_id := (@asIso _ _ _ _
        (((embedding.{w, 0, 0, v} (C := Classifier R equations)).lanAdjunction D).counit.app L.carrier)
        (isIso_counit (L := ⟨L.carrier, L.cocontinuous⟩))).hom_inv_id
      inv_hom_id := (@asIso _ _ _ _
        (((embedding.{w, 0, 0, v} (C := Classifier R equations)).lanAdjunction D).counit.app L.carrier)
        (isIso_counit (L := ⟨L.carrier, L.cocontinuous⟩))).inv_hom_id })
    (fun {_L _K} α =>
      (((embedding.{w, 0, 0, v} (C := Classifier R equations)).lanAdjunction D).counit.naturality α))

/-- Structured restriction and cocontinuous extension are inverse on
objects and all maps, through their natural unit and counit. -/
def structuredEquivalence : StructuredFunctor R equations (D := D) ≌
    CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D) :=
  _root_.CategoryTheory.Equivalence.mk extensionFunctor.{w, u, v} restrictionFunctor
    extensionUnitIso extensionCounitIso

/-- Density makes arbitrary extension maps uniquely determined by their
actual Yoneda restriction, including on nonrepresentable presheaves. -/
theorem restriction_map_injective
    {L K : CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D)} :
    Function.Injective ((restrictionFunctor.{w, u, v}).map (X := L) (Y := K)) :=
  (structuredEquivalence.{w, u, v}).inverse.map_injective

variable [HasPullbacks D]

/-- Models in a suitably cocomplete target are classified by cocontinuous
presheaf functors whose Yoneda restrictions preserve the specified structure. -/
def classificationEquivalence : CategoricalModel R equations (D := D) ≌
    CocontinuousInterpretation.{w, u, v} (R := R) (equations := equations) (D := D) :=
  (IntrinsicScopedLocalActedCategoricalModels.classificationEquivalence
    (R := R) (equations := equations) (D := D)).trans structuredEquivalence.{w, u, v}

/-- The extension is the left Kan extension of the model's actual
classifying functor, with no additional target preservation requirement. -/
theorem classification_carrier (M : CategoricalModel R equations (D := D)) :
    ((classificationEquivalence.{w, u, v}).functor.obj M).carrier =
      (embedding.{w, 0, 0, v} (C := Classifier R equations)).lan.obj M.classifyingFunctor := rfl

/-- Restriction recovers the existing classifying interpretation naturally. -/
def classificationRestrictionIso :
    (classificationEquivalence.{w, u, v} (R := R) (equations := equations) (D := D)).functor ⋙
      restrictionFunctor ≅ classifyFunctor :=
  (Functor.isoWhiskerLeft classifyFunctor extensionUnitIso.symm)

/-- Every program, event, substitution and rule arrow agrees with its
extension on the Yoneda image, by naturality of the actual Kan unit. -/
theorem generator_comparison (M : CategoricalModel R equations (D := D))
    {a b : Classifier R equations} (f : a ⟶ b) :
    M.classifyingFunctor.map f ≫
        ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).hom.app b =
      ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).hom.app a ≫
        ((classificationEquivalence.{w, u, v}).functor.obj M).carrier.map
          (embedding.{w, 0, 0, v}.map f) :=
  (((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).hom.naturality f)

end CocontinuousInterpretation
end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
