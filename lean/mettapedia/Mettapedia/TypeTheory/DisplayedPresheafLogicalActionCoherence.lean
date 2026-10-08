import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherence
import Mettapedia.TypeTheory.DependentProductRestrictionEvaluation

/-!
# Coherence of native logical comparison maps

Theory restriction retains the dependent codomain through comprehension.
The canonical comparisons for dependent sums and selected right-Kan
products compose on their full categories of evidence families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution DisplayedPresheafIndexedCwfBridge
open DisplayedPresheafSlicePi DisplayedPresheafSigmaFunctor
open DisplayedPresheafPi
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation DisplayedPresheafTheoryTransformationCoherence
open DependentProductNativeComparison DependentProductRestrictionAction
open CategoryIndexedFamilyGeneralPi
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

theorem restrictionFunctor_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) :
    restrictionFunctor (F ⋙ G) P =
      restrictionFunctor G P ⋙ restrictionFunctor F (G.op ⋙ P) := rfl

theorem codomainFunctor_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    codomainFunctor (F ⋙ G) P A =
      codomainFunctor G P A ⋙ codomainFunctor F (G.op ⋙ P) (restrictFamily G P A) := rfl

/-- The canonical dependent-pair comparisons compose without changing
either supplied component of the pair. -/
theorem sumComparison_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    (sumComparison (F ⋙ G) P A B).hom =
      (restrictionFunctor F (G.op ⋙ P)).map (sumComparison G P A B).hom ≫
        (sumComparison F (G.op ⋙ P) (restrictFamily G P A)
          ((codomainFunctor G P A).obj B)).hom := by
  ext point value
  rfl

/-- Coherence holds for the entire natural sum comparison, including all
maps of the dependent codomain. -/
theorem sumIso_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    (sumIso (F ⋙ G) P A).hom =
      whiskerRight (sumIso G P A).hom (restrictionFunctor F (G.op ⋙ P)) ≫
        whiskerLeft (codomainFunctor G P A)
          (sumIso F (G.op ⋙ P) (restrictFamily G P A)).hom := by
  ext B point value
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chosen native product comparison agrees with restriction of every
dependent function, followed by the actual codomain regrouping. -/
theorem productComparison_section (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    productComparison F P A B ≫
        ((nativeIso (restrictFamily F P A)).hom.app
          (displayedToTotalElements (restrictFamily F P A) ⋙
            (codomainFunctor F P A).obj B)) =
      whiskerLeft (Functor.Elements.precomp F.op P)
          ((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)) ≫
        DependentProductRestriction.comparison (Functor.Elements.precomp F.op P) A
          (displayedToTotalElements A ⋙ B) ≫
        (sectionProduct (restrictFamily F P A)).map (codomainComparison F P A B).hom := by
  unfold productComparison
  let route := Functor.Elements.precomp F.op P
  let codomain := displayedToTotalElements A ⋙ B
  let regrouping := (codomainComparison F P A B).hom
  let restricted := restrictFamily F P A
  let comparison := nativeRestriction route A codomain
  let sectionIso := nativeIso restricted
  change (comparison ≫ (CategoryOfElements.π restricted).ran.map regrouping) ≫
      sectionIso.hom.app _ =
    (whiskerLeft route ((nativeIso A).hom.app codomain) ≫
      DependentProductRestriction.comparison route A codomain) ≫
        (sectionProduct restricted).map regrouping
  calc
    _ = comparison ≫ ((CategoryOfElements.π restricted).ran.map regrouping ≫
        sectionIso.hom.app _) := Category.assoc _ _ _
    _ = comparison ≫ (sectionIso.hom.app _ ≫
        (sectionProduct restricted).map regrouping) :=
      congrArg (fun operation => comparison ≫ operation) (sectionIso.hom.naturality regrouping)
    _ = (comparison ≫ sectionIso.hom.app _) ≫
        (sectionProduct restricted).map regrouping := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun operation => operation ≫ (sectionProduct restricted).map regrouping)
      (nativeRestriction_section route A codomain)

set_option backward.isDefEq.respectTransparency false in
/-- Every future-argument readout is preserved by the canonical Π map.
The claim quantifies over the supplied function, future arrow and witness. -/
theorem productComparison_readout (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (point future : (F.op ⋙ P).Elements) (arrow : point ⟶ future)
    (function : (restrictFamily F P (piDisplayed A B)).obj point)
    (argument : (restrictFamily F P A).obj future) :
    ((((nativeIso (restrictFamily F P A)).hom.app
        (displayedToTotalElements (restrictFamily F P A) ⋙
          (codomainFunctor F P A).obj B)).app point
            ((productComparison F P A B).app point function)).app future arrow argument) =
      ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
          ((Functor.Elements.precomp F.op P).obj point) function).app
        ((Functor.Elements.precomp F.op P).obj future)
        ((Functor.Elements.precomp F.op P).map arrow) argument) := by
  have square := congrArg (fun operation => operation.app point function)
    (productComparison_section F P A B)
  have readout := congrArg (fun value :
      DependentSection (restrictFamily F P A)
        (displayedToTotalElements (restrictFamily F P A) ⋙
          (codomainFunctor F P A).obj B) point => value.app future arrow argument) square
  change _ = (codomainComparison F P A B).hom.app ⟨future, argument⟩
    (((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
      ((Functor.Elements.precomp F.op P).obj point) function).app
        ((Functor.Elements.precomp F.op P).obj future)
        ((Functor.Elements.precomp F.op P).map arrow) argument)) at readout
  erw [codomainComparison_app] at readout
  exact readout

set_option backward.isDefEq.respectTransparency false in
theorem codomainComparison_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    (codomainComparison (F ⋙ G) P A B).hom =
      whiskerLeft (Functor.Elements.precomp
        (Functor.Elements.precomp F.op (G.op ⋙ P)) (restrictFamily G P A))
          (codomainComparison G P A B).hom ≫
        (codomainComparison F (G.op ⋙ P) (restrictFamily G P A)
          ((codomainFunctor G P A).obj B)).hom := by
  ext point value
  erw [codomainComparison_app, NatTrans.comp_app, whiskerLeft_app,
    codomainComparison_app, codomainComparison_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity theory route gives the identity chosen product map. -/
theorem productComparison_identity (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    productComparison (𝟭 C) P A B = 𝟙 (piDisplayed A B) := by
  have regrouping : (codomainComparison (𝟭 C) P A B).hom =
      𝟙 (displayedToTotalElements A ⋙ B) := by
    ext point value
    erw [codomainComparison_app]
  unfold productComparison
  erw [regrouping, _root_.CategoryTheory.Functor.map_id, Category.comp_id]
  exact DependentProductRestrictionEvaluation.restriction_identity A
    (displayedToTotalElements A ⋙ B)

set_option backward.isDefEq.respectTransparency false in
/-- Colax Π comparison composition as an equality of full natural maps
between categories of dependent codomains. -/
theorem productMap_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    productMap (F ⋙ G) P A =
      whiskerRight (productMap G P A) (restrictionFunctor F (G.op ⋙ P)) ≫
        whiskerLeft (codomainFunctor G P A)
          (productMap F (G.op ⋙ P) (restrictFamily G P A)) := by
  apply NatTrans.ext
  funext B
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro function
  let first := Functor.Elements.precomp F.op (G.op ⋙ P)
  let second := Functor.Elements.precomp G.op P
  let middle := restrictFamily G P A
  let final := restrictFamily (F ⋙ G) P A
  let middleBody := (codomainFunctor G P A).obj B
  let finalBody := displayedToTotalElements final ⋙ (codomainFunctor (F ⋙ G) P A).obj B
  let sectionIso := ((nativeIso final).app finalBody).app point
  apply sectionIso.toEquiv.injective
  apply DependentSection.ext
  intro future arrow argument
  have direct := productComparison_readout (F ⋙ G) P A B
    point future arrow function argument
  have firstReadout := productComparison_readout F (G.op ⋙ P) middle middleBody
    point future arrow ((productComparison G P A B).app (first.obj point) function) argument
  have secondReadout := productComparison_readout G P A B
    (first.obj point) (first.obj future) (first.map arrow) function argument
  exact direct.trans (firstReadout.trans secondReadout).symm

theorem codomainFunctor_identity (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    codomainFunctor (𝟭 C) P A = 𝟭 (DisplayedFamily (totalSpace A)) := rfl

theorem sumIso_identity (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    (sumIso (𝟭 C) P A).hom = 𝟙 (sumFunctor A) := by
  ext B point value
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem productMap_identity (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    productMap (𝟭 C) P A = 𝟙 (displayedProductFunctor A) := by
  apply NatTrans.ext
  funext B
  exact productComparison_identity P A B

end Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherence
