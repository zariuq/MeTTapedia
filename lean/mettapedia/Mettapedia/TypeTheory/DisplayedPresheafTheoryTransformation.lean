import Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionAction
import Mettapedia.GSLT.Topos.PresheafLogicalTransport

/-!
# Theory transformations in the proof-valued native model

A natural transformation of theories acts contravariantly on their
presheaves. Its displayed action transports each supplied witness along
the actual element arrow. Comprehension agrees with the existing action
on total dependent types, including identity and vertical composition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformation

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryRestrictionAction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G H : C ⥤ D}

def baseMap (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) : G.op ⋙ P ⟶ F.op ⋙ P :=
  Functor.whiskerRight (NatTrans.op change) P

def elementArrow (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (point : (G.op ⋙ P).Elements) :
    (Functor.Elements.precomp G.op P).obj point ⟶
      (Functor.Elements.precomp F.op P).obj ((baseMap change P).mapElements.obj point) :=
  CategoryOfElements.homMk _ _ ((NatTrans.op change).app point.1) rfl

def familyMap (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    restrictFamily G P A ⟶ reindexDisplayed (baseMap change P) (restrictFamily F P A) where
  app point := A.map (elementArrow change P point)
  naturality first second arrow := by
    ext evidence
    change A.map (elementArrow change P second)
        (A.map ((Functor.Elements.precomp G.op P).map arrow) evidence) =
      A.map ((Functor.Elements.precomp F.op P).map ((baseMap change P).mapElements.map arrow))
        (A.map (elementArrow change P first) evidence)
    rw [← A.map_comp_apply, ← A.map_comp_apply]
    apply congrArg (fun route => A.map route evidence)
    apply CategoryOfElements.ext P
    exact (NatTrans.op change).naturality arrow.val

theorem familyMap_naturality (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    {A B : DisplayedFamily P} (evidenceMap : A ⟶ B) :
    (restrictionFunctor G P).map evidenceMap ≫ familyMap change P B =
      familyMap change P A ≫
        (reindexFunctor (baseMap change P)).map ((restrictionFunctor F P).map evidenceMap) := by
  ext point evidence
  exact (evidenceMap.naturality_apply (elementArrow change P point) evidence).symm

/-- A transformation on the actual categories of evidence families. -/
def familyTransformation (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) :
    restrictionFunctor G P ⟶ restrictionFunctor F P ⋙ reindexFunctor (baseMap change P) where
  app := familyMap change P
  naturality _ _ evidenceMap := familyMap_naturality change P evidenceMap

def totalEvidenceMap (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    totalSpace (restrictFamily G P A) ⟶ totalSpace (restrictFamily F P A) :=
  totalHom (familyMap change P A) ≫
    totalReindexMap (baseMap change P) (restrictFamily F P A)

theorem totalEvidenceMap_projection (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    totalEvidenceMap change P A ≫ totalProjection (restrictFamily F P A) =
      totalProjection (restrictFamily G P A) ≫ baseMap change P := by
  ext world value
  rfl

/-- The displayed map and the pre-existing total-category action are
the same witness transport after the native comprehension comparison. -/
theorem totalEvidenceMap_square (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    totalEvidenceMap change P A ≫ (totalComparison F P A).hom =
      (totalComparison G P A).hom ≫ Functor.whiskerRight (NatTrans.op change) (totalSpace A) := by
  ext world value
  change (⟨(baseMap change P).app world value.1,
      A.map (elementArrow change P ⟨world, value.1⟩) value.2⟩ :
      TotalAt A (F.op.obj world)) =
    totalMap A ((NatTrans.op change).app world) ⟨value.1, value.2⟩
  exact (totalMap_of_base_arrow A (elementArrow change P ⟨world, value.1⟩) value.2).symm

theorem totalEvidenceMap_identity (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    totalEvidenceMap (𝟙 F) P A = 𝟙 (totalSpace (restrictFamily F P A)) := by
  apply (cancel_mono (totalComparison F P A).hom).mp
  rw [totalEvidenceMap_square, Category.id_comp]
  ext world value
  exact totalMap_id A (F.op.obj world) value

theorem totalEvidenceMap_composition (first : F ⟶ G) (second : G ⟶ H)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    totalEvidenceMap (first ≫ second) P A =
      totalEvidenceMap second P A ≫ totalEvidenceMap first P A := by
  apply (cancel_mono (totalComparison F P A).hom).mp
  rw [totalEvidenceMap_square, Category.assoc, totalEvidenceMap_square,
    ← Category.assoc, totalEvidenceMap_square, Category.assoc]
  ext world value
  exact totalMap_comp A ((NatTrans.op second).app world) ((NatTrans.op first).app world) value

end Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformation
