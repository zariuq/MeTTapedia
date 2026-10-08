import Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherence
import Mettapedia.TypeTheory.DisplayedPresheafSliceSigma

/-!
# Dependent-sum coherence of theory transformations

A theory transformation transports both coordinates of a dependent pair.
The second coordinate follows the transported first witness through the
actual comprehension map. Reassociation by the native sum comparison
identifies this construction with transport of the original sum family.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSumTransformationCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSigma DisplayedPresheafSliceSigma DisplayedPresheafSigmaFunctor
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation DisplayedPresheafTheoryTransformationCoherence
open DisplayedPresheafProductTransformationCoherence
open CategoryIndexedFamilyGeneralPi
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G H : C ⥤ D}

/-- Transport a complete pair receipt by first transporting its dependent
body over the transported argument, then regrouping the native sum. -/
def sumTotalMap (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    totalSpace (sigmaDisplayed (restrictFamily G P A) ((codomainFunctor G P A).obj B)) ⟶
      totalSpace (sigmaDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) :=
  (sigmaTotalIso (restrictFamily G P A) ((codomainFunctor G P A).obj B)).hom ≫
    totalHom (bodyChange change P A B) ≫
      totalReindexMap (totalEvidenceMap change P A) ((codomainFunctor F P A).obj B) ≫
        (sigmaTotalIso (restrictFamily F P A) ((codomainFunctor F P A).obj B)).inv

set_option backward.isDefEq.respectTransparency false in
theorem sumTotalMap_value (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (world : Cᵒᵖ)
    (receipt : (totalSpace (sigmaDisplayed (restrictFamily G P A)
      ((codomainFunctor G P A).obj B))).obj world) :
    (sumTotalMap change P A B).app world receipt =
      (⟨(baseMap change P).app world receipt.1,
        ⟨(familyMap change P A).app ⟨world, receipt.1⟩ receipt.2.1,
          (bodyChange change P A B).app ⟨world, ⟨receipt.1, receipt.2.1⟩⟩ receipt.2.2⟩⟩ :
        (totalSpace (sigmaDisplayed (restrictFamily F P A)
          ((codomainFunctor F P A).obj B))).obj world) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The independent pair construction commutes with the actual chosen
sum comparisons. Equality retains both components of every receipt. -/
theorem sumTotalMap_square (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    totalHom (sumComparison G P A B).hom ≫ sumTotalMap change P A B =
      totalEvidenceMap change P (sigmaDisplayed A B) ≫
        totalHom (sumComparison F P A B).hom := by
  ext world receipt
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  change B.map (bodyElementArrow change P A ⟨world, ⟨receipt.1, receipt.2.1⟩⟩)
      receipt.2.2 =
    B.map ((DisplayedPresheafIndexedCwfBridge.displayedToTotalElements A).map
      (argumentMap A
        (elementArrow change P ⟨world, receipt.1⟩) receipt.2.1)) receipt.2.2
  exact congrArg (fun route => B.map route receipt.2.2)
    (bodyElementArrow_argument change P A
      (show (G.op ⋙ P).Elements from ⟨world, receipt.1⟩) receipt.2.1)

set_option backward.isDefEq.respectTransparency false in
theorem sumTotalMap_projection (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    sumTotalMap change P A B ≫
        totalProjection (sigmaDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)) =
      totalProjection (sigmaDisplayed (restrictFamily G P A) ((codomainFunctor G P A).obj B)) ≫
        baseMap change P := by
  ext world receipt
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sumTotalMap_identity (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    sumTotalMap (𝟙 F) P A B =
      𝟙 (totalSpace (sigmaDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B))) := by
  dsimp only [codomainFunctor] at *
  let comparison := (comprehensionTotals (F.op ⋙ P)).mapIso (sumComparison F P A B)
  apply (cancel_epi comparison.hom).mp
  change totalHom (sumComparison F P A B).hom ≫ _ =
    totalHom (sumComparison F P A B).hom ≫ _
  rw [sumTotalMap_square, totalEvidenceMap_identity, Category.id_comp]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem sumTotalMap_composition (first : F ⟶ G) (second : G ⟶ H)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    sumTotalMap (first ≫ second) P A B =
      sumTotalMap second P A B ≫ sumTotalMap first P A B := by
  dsimp only [codomainFunctor] at *
  let comparison := (comprehensionTotals (H.op ⋙ P)).mapIso (sumComparison H P A B)
  apply (cancel_epi comparison.hom).mp
  change totalHom (sumComparison H P A B).hom ≫ _ =
    totalHom (sumComparison H P A B).hom ≫ (_ ≫ _)
  rw [sumTotalMap_square, totalEvidenceMap_composition, ← Category.assoc,
    sumTotalMap_square]
  erw [Category.assoc, sumTotalMap_square]

abbrev sumTotals (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    DisplayedFamily (totalSpace A) ⥤ (Cᵒᵖ ⥤ Type u) :=
  codomainFunctor F P A ⋙ sumFunctor (restrictFamily F P A) ⋙
    comprehensionTotals (F.op ⋙ P)

set_option backward.isDefEq.respectTransparency false in
theorem sumTotalMap_naturality (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) {B B' : DisplayedFamily (totalSpace A)} (operation : B ⟶ B') :
    (sumTotals G P A).map operation ≫ sumTotalMap change P A B' =
      sumTotalMap change P A B ≫ (sumTotals F P A).map operation := by
  ext world receipt
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  exact (operation.naturality_apply
    (bodyElementArrow change P A ⟨world, ⟨receipt.1, receipt.2.1⟩⟩) receipt.2.2).symm

/-- A transformation on complete dependent-pair totals, natural in every
map of the supplied dependent codomain. -/
def sumTransformation (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    sumTotals G P A ⟶ sumTotals F P A where
  app := sumTotalMap change P A
  naturality _ _ operation := sumTotalMap_naturality change P A operation

/-- The chosen native sum comparison is also natural after comprehension. -/
def sumTotalsComparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    sumFunctor A ⋙ totalRestriction F P ≅ sumTotals F P A :=
  NatIso.ofComponents
    (fun B => (comprehensionTotals (F.op ⋙ P)).mapIso (sumComparison F P A B)) (by
      intro B B' operation
      ext world receipt
      rfl)

theorem sumTransformation_square (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    (sumTotalsComparison G P A).hom ≫ sumTransformation change P A =
      whiskerLeft (sumFunctor A) (totalTransformation change P) ≫
        (sumTotalsComparison F P A).hom := by
  apply NatTrans.ext
  funext B
  exact sumTotalMap_square change P A B

theorem sumTransformation_identity (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    sumTransformation (𝟙 F) P A = 𝟙 (sumTotals F P A) := by
  apply NatTrans.ext
  funext B
  exact sumTotalMap_identity F P A B

theorem sumTransformation_composition (first : F ⟶ G) (second : G ⟶ H)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    sumTransformation (first ≫ second) P A =
      sumTransformation second P A ≫ sumTransformation first P A := by
  apply NatTrans.ext
  funext B
  exact sumTotalMap_composition first second P A B

/-- The actual covariant pair transport gives a contravariant action of
theory transformations. Both pair coordinates are retained. -/
def sumActionFunctor (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    (C ⥤ D)ᵒᵖ ⥤ (DisplayedFamily (totalSpace A) ⥤ (Cᵒᵖ ⥤ Type u)) where
  obj F := sumTotals F.unop P A
  map change := sumTransformation change.unop P A
  map_id F := sumTransformation_identity F.unop P A
  map_comp first second := sumTransformation_composition second.unop first.unop P A

variable {E : Type u} [Category.{u} E]

/-- The staged sum comparison uses the chosen sum comparisons and the
comprehension comparison of the two theory routes. -/
def sumCompositionIso (F : C ⥤ D) (K : D ⥤ E) (P : Eᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    sumTotals (F ⋙ K) P A ≅
      sumTotals K P A ⋙ Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves F :=
  (sumTotalsComparison (F ⋙ K) P A).symm ≪≫
    Functor.isoWhiskerLeft (sumFunctor A) (totalCompositionIso F K P) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sumTotalsComparison K P A)
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves F)

set_option backward.isDefEq.respectTransparency false in
/-- Horizontal composition commutes with staged native summation on each
complete pair receipt, including the transported dependent body. -/
theorem sumTransformation_horizontal_square {F G : C ⥤ D} {H K : D ⥤ E}
    (first : F ⟶ G) (second : H ⟶ K) (P : Eᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    sumTransformation (first ◫ second) P A ≫ (sumCompositionIso F H P A).hom =
      (sumCompositionIso G K P A).hom ≫
        whiskerRight (sumTransformation second P A)
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves G) ≫
            whiskerLeft (sumTotals H P A)
              (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheavesMap first) := by
  ext B world receipt
  have square := congrArg
    (fun operation => operation.app (sigmaDisplayed A B))
    (totalTransformation_horizontal_square first second P)
  have readout := congrArg (fun operation => operation.app world receipt) square
  convert readout using 1 <;> rfl

end Mettapedia.TypeTheory.DisplayedPresheafSumTransformationCoherence
