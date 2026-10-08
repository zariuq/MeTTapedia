import Mettapedia.TypeTheory.DependentProductArgumentTransport
import Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherence

/-!
# Dependent-product coherence of theory transformations

The body of a dependent function transports covariantly, while its argument
transports contravariantly. The mixed comparison retains that distinction
for every theory transformation. Reversible world restriction requires the
separate future-argument coverage condition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafIndexedCwfBridge
open DisplayedPresheafSlicePi DisplayedPresheafPi
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation DisplayedPresheafTheoryTransformationCoherence
open DisplayedPresheafLogicalActionCoherence DisplayedPresheafSlice
open CategoryIndexedFamilyGeneralPi DependentProductNativeComparison
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G H : C ⥤ D}

/-- The actual element arrows form a natural transformation between the
two world routes, after the base-context substitution. -/
def elementTransformation (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) :
    Functor.Elements.precomp G.op P ⟶
      (baseMap change P).mapElements ⋙ Functor.Elements.precomp F.op P where
  app := elementArrow change P
  naturality _ _ arrow := by
    apply CategoryOfElements.ext P
    exact (NatTrans.op change).naturality arrow.val

/-- The supplied argument is changed at its own contextual point. -/
def argumentRoute (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    (restrictFamily G P A).Elements ⥤ (restrictFamily F P A).Elements :=
  (familyMap change P A).mapElements ⋙
    Functor.Elements.precomp (baseMap change P).mapElements (restrictFamily F P A)

/-- Argument transport and transport of the complete comprehension receipt
reach the same total-context point and substitution arrow. -/
theorem argumentRoute_totalSquare (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    argumentRoute change P A ⋙ displayedToTotalElements (restrictFamily F P A) =
      displayedToTotalElements (restrictFamily G P A) ⋙
        (totalEvidenceMap change P A).mapElements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (totalSpace (restrictFamily F P A))
  erw [displayedToTotalElements_underlying]
  change arrow.val.val =
    ((totalEvidenceMap change P A).mapElements.map
      ((displayedToTotalElements (restrictFamily G P A)).map arrow)).val
  erw [displayedToTotalElements_underlying]

theorem bodyChange_target (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    reindexDisplayed (totalComparison G P A).hom
        (reindexDisplayed (baseMap change (totalSpace A))
          (restrictFamily F (totalSpace A) B)) =
      reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B) := by
  have square := totalEvidenceMap_square change P A
  exact congrArg (fun operation =>
    operation.mapElements ⋙ restrictFamily F (totalSpace A) B) square.symm

def bodyElementArrow (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (point : (totalSpace (restrictFamily G P A)).Elements) :
    ((totalComparison G P A).hom.mapElements ⋙
        Functor.Elements.precomp G.op (totalSpace A)).obj point ⟶
      ((totalEvidenceMap change P A).mapElements ⋙ (totalComparison F P A).hom.mapElements ⋙
        Functor.Elements.precomp F.op (totalSpace A)).obj point :=
  CategoryOfElements.homMk _ _ ((NatTrans.op change).app point.1)
    (totalMap_of_base_arrow A (elementArrow change P ⟨point.1, point.2.1⟩) point.2.2)

set_option backward.isDefEq.respectTransparency false in
/-- Covariant transport of the complete dependent result witness. -/
def bodyChange (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    (codomainFunctor G P A).obj B ⟶
      reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B) where
  app point := B.map (bodyElementArrow change P A point)
  naturality first second arrow := by
    ext evidence
    change B.map (bodyElementArrow change P A second)
        (B.map (((totalComparison G P A).hom.mapElements ⋙
          Functor.Elements.precomp G.op (totalSpace A)).map arrow) evidence) =
      B.map (((totalEvidenceMap change P A).mapElements ⋙
        (totalComparison F P A).hom.mapElements ⋙
          Functor.Elements.precomp F.op (totalSpace A)).map arrow)
            (B.map (bodyElementArrow change P A first) evidence)
    rw [← B.map_comp_apply, ← B.map_comp_apply]
    apply congrArg (fun route => B.map route evidence)
    apply CategoryOfElements.ext (totalSpace A)
    exact (NatTrans.op change).naturality arrow.val

theorem bodyElementArrow_argument (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (point : (G.op ⋙ P).Elements)
    (argument : (restrictFamily G P A).obj point) :
    bodyElementArrow change P A
        ((displayedToTotalElements (restrictFamily G P A)).obj ⟨point, argument⟩) =
      (displayedToTotalElements A).map
        (argumentMap A (elementArrow change P point) argument) := by
  apply CategoryOfElements.ext (totalSpace A)
  erw [displayedToTotalElements_underlying]
  rfl

theorem argumentBody_target (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    argumentRoute change P A ⋙
        (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B) =
      displayedToTotalElements (restrictFamily G P A) ⋙
        reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B) :=
  congrArg (fun route => route ⋙ (codomainFunctor F P A).obj B)
    (argumentRoute_totalSquare change P A)

set_option backward.isDefEq.respectTransparency false in
theorem argumentBody_target_app (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (point : (restrictFamily G P A).Elements) :
    (eqToHom (argumentBody_target change P A B)).app point = 𝟙 _ := by
  rw [eqToHom_app]
  rfl

/-- Evaluation at the transported argument, followed by the earned
comprehension regrouping. This is a full natural body map. -/
noncomputable def argumentEvaluation (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    CategoryOfElements.π (restrictFamily G P A) ⋙
        reindexDisplayed (baseMap change P)
          (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) ⟶
      displayedToTotalElements (restrictFamily G P A) ⋙
        reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B) :=
  Functor.whiskerLeft (argumentRoute change P A)
      (generalPiEvaluation (context := Cat.of (F.op ⋙ P).Elements)
        (restrictFamily F P A)
        (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)) ≫
    eqToHom (argumentBody_target change P A B)

/-- Functions move in the opposite direction from their supplied
arguments; the codomain remembers the complete transported receipt. -/
noncomputable def productArgumentMap (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    reindexDisplayed (baseMap change P)
        (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) ⟶
      piDisplayed (restrictFamily G P A)
        (reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B)) :=
  generalPiTranspose (context := Cat.of (G.op ⋙ P).Elements)
    (restrictFamily G P A) (argumentEvaluation change P A B)

set_option backward.isDefEq.respectTransparency false in
/-- Every future readout uses the same supplied function, mapped base
arrow and transported argument. -/
theorem productArgumentMap_readout (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (point future : (G.op ⋙ P).Elements) (arrow : point ⟶ future)
    (function : (reindexDisplayed (baseMap change P)
      (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B))).obj point)
    (argument : (restrictFamily G P A).obj future) :
    ((((nativeIso (restrictFamily G P A)).hom.app
        (displayedToTotalElements (restrictFamily G P A) ⋙
          reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B))).app
            point ((productArgumentMap change P A B).app point function)).app future arrow argument) =
      ((((nativeIso (restrictFamily F P A)).hom.app
        (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)).app
          ((baseMap change P).mapElements.obj point) function).app
        ((baseMap change P).mapElements.obj future)
        ((baseMap change P).mapElements.map arrow) ((familyMap change P A).app future argument)) := by
  have square := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun operation => operation.app point)
      (nativeIso_abstraction (restrictFamily G P A) (argumentEvaluation change P A B))) function
  have readout := congrArg (fun functionValue :
    DependentSection (restrictFamily G P A)
      (displayedToTotalElements (restrictFamily G P A) ⋙
        reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B)) point =>
      functionValue.app future arrow argument) square
  change _ = (eqToHom (argumentBody_target change P A B)).app ⟨future, argument⟩
    ((generalPiEvaluation (context := Cat.of (F.op ⋙ P).Elements)
      (restrictFamily F P A)
      (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)).app
        ((argumentRoute change P A).obj ⟨future, argument⟩)
          ((piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)).map
            ((baseMap change P).mapElements.map arrow) function)) at readout
  rw [argumentBody_target_app] at readout
  have evaluation := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun operation => operation.app
      ((argumentRoute change P A).obj ⟨future, argument⟩))
      (nativeIso_evaluation (restrictFamily F P A)
        (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)))
      ((piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)).map
        ((baseMap change P).mapElements.map arrow) function)
  have natural := (((nativeIso (restrictFamily F P A)).hom.app
    (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)).naturality_apply
      ((baseMap change P).mapElements.map arrow) function)
  erw [← evaluation] at readout
  change _ = ((((nativeIso (restrictFamily F P A)).hom.app
      (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)).app
        ((baseMap change P).mapElements.obj future)
          ((piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)).map
            ((baseMap change P).mapElements.map arrow) function)).app
      ((baseMap change P).mapElements.obj future) (𝟙 _)
      ((familyMap change P A).app future argument)) at readout
  erw [natural] at readout
  change _ = ((((nativeIso (restrictFamily F P A)).hom.app
      (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)).app
        ((baseMap change P).mapElements.obj point) function).app
      ((baseMap change P).mapElements.obj future)
      (((baseMap change P).mapElements.map arrow) ≫ 𝟙 _)
      ((familyMap change P A).app future argument)) at readout
  rw [Category.comp_id] at readout
  exact readout

set_option backward.isDefEq.respectTransparency false in
/-- The displayed argument action is the existing native world comparison,
followed by the general contravariant argument map and the actual
comprehension regrouping. The two constructions agree on whole functions. -/
theorem productArgumentMap_nativeFactorization (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    productArgumentMap change P A B =
      nativeRestriction (baseMap change P).mapElements (restrictFamily F P A)
          (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B) ≫
        DependentProductArgumentTransport.nativePrecomposition (familyMap change P A)
          (DependentProductRestriction.restrictedFamily (baseMap change P).mapElements
            (restrictFamily F P A)
            (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)) ≫
          (CategoryOfElements.π (restrictFamily G P A)).ran.map
            (eqToHom (argumentBody_target change P A B)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro function
  apply (((nativeIso (restrictFamily G P A)).app
    (displayedToTotalElements (restrictFamily G P A) ⋙
      reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B))).app
        point).toEquiv.injective
  apply DependentSection.ext
  intro future arrow argument
  let transported :=
    (DependentProductArgumentTransport.nativePrecomposition (familyMap change P A)
      (DependentProductRestriction.restrictedFamily (baseMap change P).mapElements
        (restrictFamily F P A)
        (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B))).app point
      ((nativeRestriction (baseMap change P).mapElements (restrictFamily F P A)
        (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)).app
          point function)
  have regroup := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun operation => operation.app point)
      ((nativeIso (restrictFamily G P A)).hom.naturality
        (eqToHom (argumentBody_target change P A B)))) transported
  have readout := congrArg (fun functionValue :
    DependentSection (restrictFamily G P A)
      (displayedToTotalElements (restrictFamily G P A) ⋙
        reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B)) point =>
      functionValue.app future arrow argument) regroup
  change _ = (eqToHom (argumentBody_target change P A B)).app ⟨future, argument⟩
    (((((nativeIso (restrictFamily G P A)).hom.app
      (argumentRoute change P A ⋙
        (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B))).app
        point transported).app future arrow argument)) at readout
  rw [argumentBody_target_app] at readout
  change _ = ((((nativeIso (restrictFamily G P A)).hom.app
    (argumentRoute change P A ⋙
      (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B))).app
        point transported).app future arrow argument) at readout
  have argumentReadout := DependentProductArgumentTransport.nativePrecomposition_readout
    (familyMap change P A)
    (DependentProductRestriction.restrictedFamily (baseMap change P).mapElements
      (restrictFamily F P A)
      (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B))
    ((nativeRestriction (baseMap change P).mapElements (restrictFamily F P A)
      (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)).app
        point function) future arrow argument
  have baseReadout := DependentProductArgumentTransport.nativeRestriction_readout
    (baseMap change P).mapElements (restrictFamily F P A)
    (displayedToTotalElements (restrictFamily F P A) ⋙ (codomainFunctor F P A).obj B)
    function future arrow ((familyMap change P A).app future argument)
  exact (productArgumentMap_readout change P A B point future arrow function argument).trans
    (readout.trans (argumentReadout.trans baseReadout)).symm

set_option backward.isDefEq.respectTransparency false in
theorem productBodyMap_readout {Q : Cᵒᵖ ⥤ Type u} (A : DisplayedFamily Q)
    {B B' : DisplayedFamily (totalSpace A)} (operation : B ⟶ B')
    (point future : Q.Elements) (arrow : point ⟶ future)
    (function : (piDisplayed A B).obj point) (argument : A.obj future) :
    ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B')).app point
        (((displayedProductFunctor A).map operation).app point function)).app
      future arrow argument) =
      operation.app ((displayedToTotalElements A).obj ⟨future, argument⟩)
        (((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app point function).app
          future arrow argument)) := by
  have square := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun map => map.app point)
      ((nativeIso A).hom.naturality (Functor.whiskerLeft (displayedToTotalElements A) operation)))
    function
  exact congrArg (fun functionValue : DependentSection A (displayedToTotalElements A ⋙ B') point =>
    functionValue.app future arrow argument) square

set_option backward.isDefEq.respectTransparency false in
/-- Theory transformations satisfy the full mixed native Π square.
The result-family arrow is covariant and the function arrow explicitly
precomposes every argument with its actual transformation. -/
theorem product_mixed_square (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    productComparison G P A B ≫
        (displayedProductFunctor (restrictFamily G P A)).map (bodyChange change P A B) =
      familyMap change P (piDisplayed A B) ≫
        (reindexFunctor (baseMap change P)).map (productComparison F P A B) ≫
          productArgumentMap change P A B := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro function
  apply (((nativeIso (restrictFamily G P A)).app
    (displayedToTotalElements (restrictFamily G P A) ⋙
      reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B))).app
        point).toEquiv.injective
  apply DependentSection.ext
  intro future arrow argument
  change ((((nativeIso (restrictFamily G P A)).hom.app
      (displayedToTotalElements (restrictFamily G P A) ⋙
        reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B))).app point
      (((displayedProductFunctor (restrictFamily G P A)).map (bodyChange change P A B)).app point
        ((productComparison G P A B).app point function))).app future arrow argument) =
    ((((nativeIso (restrictFamily G P A)).hom.app
      (displayedToTotalElements (restrictFamily G P A) ⋙
        reindexDisplayed (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B))).app point
      ((productArgumentMap change P A B).app point
        ((productComparison F P A B).app ((baseMap change P).mapElements.obj point)
          ((familyMap change P (piDisplayed A B)).app point function)))).app future arrow argument)
  rw [productBodyMap_readout, productComparison_readout,
    productArgumentMap_readout, productComparison_readout]
  change B.map (bodyElementArrow change P A
      ((displayedToTotalElements (restrictFamily G P A)).obj ⟨future, argument⟩))
      (((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
        ((Functor.Elements.precomp G.op P).obj point) function).app
          ((Functor.Elements.precomp G.op P).obj future)
          ((Functor.Elements.precomp G.op P).map arrow) argument)) = _
  rw [bodyElementArrow_argument]
  let original := (((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
    ((Functor.Elements.precomp G.op P).obj point) function)
  have sectionNatural := (((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).naturality_apply
    (elementArrow change P point) function)
  change _ = ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
      ((Functor.Elements.precomp F.op P).obj ((baseMap change P).mapElements.obj point))
      ((piDisplayed A B).map (elementArrow change P point) function)).app
    ((Functor.Elements.precomp F.op P).obj ((baseMap change P).mapElements.obj future))
    ((Functor.Elements.precomp F.op P).map ((baseMap change P).mapElements.map arrow))
    (A.map (elementArrow change P future) argument))
  erw [sectionNatural]
  change (displayedToTotalElements A ⋙ B).map
      (argumentMap A (elementArrow change P future) argument)
        (original.app ((Functor.Elements.precomp G.op P).obj future)
          ((Functor.Elements.precomp G.op P).map arrow) argument) =
    original.app ((Functor.Elements.precomp F.op P).obj ((baseMap change P).mapElements.obj future))
      (elementArrow change P point ≫
        (Functor.Elements.precomp F.op P).map ((baseMap change P).mapElements.map arrow))
      (A.map (elementArrow change P future) argument)
  rw [original.naturality]
  exact congrArg (fun route => original.app
    ((Functor.Elements.precomp F.op P).obj ((baseMap change P).mapElements.obj future)) route
      (A.map (elementArrow change P future) argument))
    ((elementTransformation change P).naturality arrow)

noncomputable def coveredProductIso (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp route.op P) A point).Initial] :
    restrictFamily route P (piDisplayed A B) ≅
      piDisplayed (restrictFamily route P A) ((codomainFunctor route P A).obj B) :=
  nativeRestrictionIso (Functor.Elements.precomp route.op P) A
      (displayedToTotalElements A ⋙ B) ≪≫
    (CategoryOfElements.π (restrictFamily route P A)).ran.mapIso
      (codomainComparison route P A B)

theorem coveredProductIso_hom (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp route.op P) A point).Initial] :
    (coveredProductIso route P A B).hom = productComparison route P A B := rfl

/-- Future-argument coverage supplies an isomorphism on the full category
of dependent codomains, with the existing colax map as its hom. -/
noncomputable def coveredProductNaturalIso (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp route.op P) A point).Initial] :
    displayedProductFunctor A ⋙ restrictionFunctor route P ≅
      codomainFunctor route P A ⋙ displayedProductFunctor (restrictFamily route P A) :=
  NatIso.ofComponents (fun B => coveredProductIso route P A B)
    (fun operation => (productMap route P A).naturality operation)

theorem coveredProductNaturalIso_hom (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp route.op P) A point).Initial] :
    (coveredProductNaturalIso route P A).hom = productMap route P A := by
  apply NatTrans.ext
  funext B
  exact coveredProductIso_hom route P A B

/-- Under coverage of the incoming observer route, the mixed action has
an ordinary natural function transport. The inverse used here is earned
from future-argument initiality, separately from the theory 2-cell. -/
noncomputable def coveredProductTransformation (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial] :
    codomainFunctor G P A ⋙ displayedProductFunctor (restrictFamily G P A) ⟶
      codomainFunctor F P A ⋙ displayedProductFunctor (restrictFamily F P A) ⋙
        reindexFunctor (baseMap change P) :=
  (coveredProductNaturalIso G P A).inv ≫
    Functor.whiskerLeft (displayedProductFunctor A) (familyTransformation change P) ≫
      Functor.whiskerRight (productMap F P A) (reindexFunctor (baseMap change P))

theorem coveredProductTransformation_app (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial]
    (B : DisplayedFamily (totalSpace A)) :
    (coveredProductTransformation change P A).app B =
      (coveredProductIso G P A B).inv ≫ familyMap change P (piDisplayed A B) ≫
        (reindexFunctor (baseMap change P)).map (productComparison F P A B) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The qualified action respects the canonical comparison on its full
natural transformation, including every codomain evidence map. -/
theorem coveredProductTransformation_square (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial] :
    productMap G P A ≫ coveredProductTransformation change P A =
      Functor.whiskerLeft (displayedProductFunctor A) (familyTransformation change P) ≫
        Functor.whiskerRight (productMap F P A) (reindexFunctor (baseMap change P)) := by
  rw [← coveredProductNaturalIso_hom]
  unfold coveredProductTransformation
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary transport obtained by coverage still obeys the argument-
contravariant mixed law, rather than replacing it by an unsupported
unqualified preservation rule. -/
theorem coveredProductTransformation_mixed (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial]
    (B : DisplayedFamily (totalSpace A)) :
    (coveredProductTransformation change P A).app B ≫ productArgumentMap change P A B =
      (displayedProductFunctor (restrictFamily G P A)).map (bodyChange change P A B) := by
  apply (cancel_epi (coveredProductIso G P A B).hom).mp
  have square := congrArg (fun operation => operation.app B)
    (coveredProductTransformation_square change P A)
  change productComparison G P A B ≫ (coveredProductTransformation change P A).app B =
    familyMap change P (piDisplayed A B) ≫
      (reindexFunctor (baseMap change P)).map (productComparison F P A B) at square
  rw [coveredProductIso_hom, ← Category.assoc]
  change (productComparison G P A B ≫ (coveredProductTransformation change P A).app B) ≫
      productArgumentMap change P A B = _
  rw [square, Category.assoc]
  exact (product_mixed_square change P A B).symm

/-- Actual comprehension totals of the local native dependent products. -/
noncomputable abbrev nativeProductTotals (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) : DisplayedFamily (totalSpace A) ⥤ (Cᵒᵖ ⥤ Type u) :=
  codomainFunctor route P A ⋙ displayedProductFunctor (restrictFamily route P A) ⋙
    comprehensionTotals (route.op ⋙ P)

noncomputable abbrev productTotalComparison (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    displayedProductFunctor A ⋙ totalRestriction route P ⟶ nativeProductTotals route P A :=
  Functor.whiskerRight (productMap route P A) (comprehensionTotals (route.op ⋙ P))

noncomputable def coveredProductTotalIso (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp route.op P) A point).Initial] :
    displayedProductFunctor A ⋙ totalRestriction route P ≅ nativeProductTotals route P A :=
  Functor.isoWhiskerRight (coveredProductNaturalIso route P A)
    (comprehensionTotals (route.op ⋙ P))

theorem coveredProductTotalIso_hom (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp route.op P) A point).Initial] :
    (coveredProductTotalIso route P A).hom = productTotalComparison route P A := by
  exact congrArg (fun operation =>
    Functor.whiskerRight operation (comprehensionTotals (route.op ⋙ P)))
      (coveredProductNaturalIso_hom route P A)

/-- The corrected native Π action retains the base value and full function
as a comprehension receipt. Incoming coverage earns its reconstruction. -/
noncomputable def coveredProductTotalTransformation (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial] :
    nativeProductTotals G P A ⟶ nativeProductTotals F P A :=
  (coveredProductTotalIso G P A).inv ≫
    Functor.whiskerLeft (displayedProductFunctor A) (totalTransformation change P) ≫
      productTotalComparison F P A

set_option backward.isDefEq.respectTransparency false in
theorem coveredProductTotalTransformation_square (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial] :
    productTotalComparison G P A ≫ coveredProductTotalTransformation change P A =
      Functor.whiskerLeft (displayedProductFunctor A) (totalTransformation change P) ≫
        productTotalComparison F P A := by
  rw [← coveredProductTotalIso_hom]
  unfold coveredProductTotalTransformation
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- This total map is exactly the previously constructed family action,
followed by its actual dependent base-context change. -/
theorem coveredProductTotalTransformation_corrected (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial]
    (B : DisplayedFamily (totalSpace A)) :
    (coveredProductTotalTransformation change P A).app B =
      totalHom ((coveredProductTransformation change P A).app B) ≫
        totalReindexMap (baseMap change P)
          (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) := by
  apply (cancel_epi ((coveredProductTotalIso G P A).hom.app B)).mp
  have square := congrArg (fun operation => operation.app B)
    (coveredProductTotalTransformation_square change P A)
  change totalHom (productComparison G P A B) ≫
      (coveredProductTotalTransformation change P A).app B =
    totalEvidenceMap change P (piDisplayed A B) ≫ totalHom (productComparison F P A B) at square
  rw [coveredProductTotalIso_hom]
  change totalHom (productComparison G P A B) ≫
      (coveredProductTotalTransformation change P A).app B = _
  rw [square]
  have familySquare := congrArg (fun operation => operation.app B)
    (coveredProductTransformation_square change P A)
  change productComparison G P A B ≫ (coveredProductTransformation change P A).app B =
    familyMap change P (piDisplayed A B) ≫
      (reindexFunctor (baseMap change P)).map (productComparison F P A B) at familySquare
  have first := (comprehensionTotals (G.op ⋙ P)).map_comp
    (productComparison G P A B) ((coveredProductTransformation change P A).app B)
  have second := (comprehensionTotals (G.op ⋙ P)).map_comp
    (familyMap change P (piDisplayed A B))
    ((reindexFunctor (baseMap change P)).map (productComparison F P A B))
  calc
    _ = (totalHom (familyMap change P (piDisplayed A B)) ≫
        totalReindexMap (baseMap change P) (restrictFamily F P (piDisplayed A B))) ≫
          totalHom (productComparison F P A B) := rfl
    _ = (totalHom (familyMap change P (piDisplayed A B)) ≫
        totalHom ((reindexFunctor (baseMap change P)).map (productComparison F P A B))) ≫
          totalReindexMap (baseMap change P)
            (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) := by
      erw [Category.assoc, ← totalHom_reindex, ← Category.assoc]
    _ = totalHom (familyMap change P (piDisplayed A B) ≫
        (reindexFunctor (baseMap change P)).map (productComparison F P A B)) ≫
          totalReindexMap (baseMap change P)
            (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) := by
      erw [← second]
      rfl
    _ = totalHom (productComparison G P A B ≫ (coveredProductTransformation change P A).app B) ≫
          totalReindexMap (baseMap change P)
            (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) := by erw [familySquare]
    _ = _ := by
      exact (congrArg (fun operation => operation ≫
        totalReindexMap (baseMap change P)
          (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B))) first).trans
        (Category.assoc _ _ _)

/-- Units for the actual corrected Π action on full native comprehension
totals. Equality includes each supplied function witness. -/
theorem coveredProductTotalTransformation_identity (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp F.op P) A point).Initial] :
    coveredProductTotalTransformation (𝟙 F) P A = 𝟙 (nativeProductTotals F P A) := by
  have unit : Functor.whiskerLeft (displayedProductFunctor A) (𝟙 (totalRestriction F P)) =
      𝟙 (displayedProductFunctor A ⋙ totalRestriction F P) := rfl
  unfold coveredProductTotalTransformation
  rw [totalTransformation_identity, unit, Category.id_comp,
    ← coveredProductTotalIso_hom, Iso.inv_hom_id]

/-- Vertical composition for full corrected native Π maps. Only the
incoming and intermediate future-argument reconstructions are inverted;
the final route can retain its noninvertible colax comparison. -/
theorem coveredProductTotalTransformation_composition (first : F ⟶ G) (second : G ⟶ H)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A point).Initial]
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp H.op P) A point).Initial] :
    coveredProductTotalTransformation (first ≫ second) P A =
      coveredProductTotalTransformation second P A ≫
        coveredProductTotalTransformation first P A := by
  unfold coveredProductTotalTransformation
  rw [totalTransformation_composition, Functor.whiskerLeft_comp,
    ← coveredProductTotalIso_hom G P A]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Horizontal factorization on complete products of composed world routes.
Coverage is needed exactly at the incoming and intermediate routes. -/
theorem coveredProductTotalTransformation_horizontal {E : Type u} [Category.{u} E]
    {F G : C ⥤ D} {H K : D ⥤ E} (first : F ⟶ G) (second : H ⟶ K)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (F ⋙ K).op P) A point).Initial]
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (G ⋙ K).op P) A point).Initial] :
    coveredProductTotalTransformation (first ◫ second) P A =
      coveredProductTotalTransformation (whiskerRight first K) P A ≫
        coveredProductTotalTransformation (whiskerLeft F second) P A := by
  rw [NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight,
    coveredProductTotalTransformation_composition]

/-- The two orders of horizontal witness transport agree. Both possible
intermediate routes have their own future-argument reconstruction. -/
theorem coveredProductTotalTransformation_interchange {E : Type u} [Category.{u} E]
    {F G : C ⥤ D} {H K : D ⥤ E} (first : F ⟶ G) (second : H ⟶ K)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (F ⋙ K).op P) A point).Initial]
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (G ⋙ H).op P) A point).Initial]
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (G ⋙ K).op P) A point).Initial] :
    coveredProductTotalTransformation (whiskerRight first K) P A ≫
        coveredProductTotalTransformation (whiskerLeft F second) P A =
      coveredProductTotalTransformation (whiskerLeft G second) P A ≫
        coveredProductTotalTransformation (whiskerRight first H) P A := by
  rw [← coveredProductTotalTransformation_composition,
    ← coveredProductTotalTransformation_composition, whiskerLeft_comp_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
/-- Reconstructing the complete product and then using the canonical
staged comprehension comparison commutes with horizontal theory change.
This compares the actual original function receipts, including base values. -/
theorem coveredProductTotalTransformation_horizontal_square {E : Type u} [Category.{u} E]
    {F G : C ⥤ D} {H K : D ⥤ E} (first : F ⟶ G) (second : H ⟶ K)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (F ⋙ H).op P) A point).Initial]
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (G ⋙ K).op P) A point).Initial] :
    coveredProductTotalTransformation (first ◫ second) P A ≫
        (coveredProductTotalIso (F ⋙ H) P A).inv ≫
          whiskerLeft (displayedProductFunctor A) (totalCompositionIso F H P).hom =
      (coveredProductTotalIso (G ⋙ K) P A).inv ≫
        whiskerLeft (displayedProductFunctor A) (totalCompositionIso G K P).hom ≫
        whiskerLeft (displayedProductFunctor A)
          (whiskerRight (totalTransformation second P)
            (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves G)) ≫
        whiskerLeft (displayedProductFunctor A)
          (whiskerLeft (totalRestriction H P)
            (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheavesMap first)) := by
  unfold coveredProductTotalTransformation
  rw [← coveredProductTotalIso_hom (F ⋙ H) P A]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have square := congrArg (fun operation => whiskerLeft (displayedProductFunctor A) operation)
    (totalTransformation_horizontal_square first second P)
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp] at square
  exact congrArg (fun operation => (coveredProductTotalIso (G ⋙ K) P A).inv ≫ operation) square

end Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherence
