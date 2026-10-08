import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformation

/-!
# Horizontal coherence of dependent theory transformations

The displayed action of a theory transformation transports its actual
witnesses along element arrows. Whiskering and interchange agree with
the successive displayed actions. Native comprehension presents the same
action on total presheaves, with its canonical composition comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryRestrictionAction DisplayedPresheafTheoryTransformation

universe u
variable {B C D E : Type u}
variable [Category.{u} B] [Category.{u} C] [Category.{u} D] [Category.{u} E]

/-- Precomposition of a theory change restricts its actual displayed map. -/
theorem familyMap_whiskerLeft {F G : C ⥤ D} (K : B ⥤ C) (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    familyMap (whiskerLeft K change) P A =
      whiskerLeft (Functor.Elements.precomp K.op (G.op ⋙ P)) (familyMap change P A) := by
  ext point evidence
  rfl

/-- Postcomposition restricts the family before transporting its witness. -/
theorem familyMap_whiskerRight {F G : C ⥤ D} (change : F ⟶ G) (K : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    familyMap (whiskerRight change K) P A =
      familyMap change (K.op ⋙ P) (restrictFamily K P A) := by
  ext point evidence
  rfl

/-- Comprehension totals, retaining every dependent witness while forgetting
only which fixed slice contains the comprehension projection. -/
abbrev comprehensionTotals (P : Dᵒᵖ ⥤ Type u) :
    DisplayedFamily P ⥤ (Dᵒᵖ ⥤ Type u) :=
  totalFunctor P ⋙ Over.forget P

abbrev totalRestriction (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    DisplayedFamily P ⥤ (Cᵒᵖ ⥤ Type u) :=
  restrictionFunctor F P ⋙ comprehensionTotals (F.op ⋙ P)

theorem totalEvidenceMap_naturality {F G : C ⥤ D} (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) {A A' : DisplayedFamily P} (operation : A ⟶ A') :
    (totalRestriction G P).map operation ≫ totalEvidenceMap change P A' =
      totalEvidenceMap change P A ≫ (totalRestriction F P).map operation := by
  ext world receipt
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  exact (operation.naturality_apply (elementArrow change P ⟨world, receipt.1⟩)
    receipt.2).symm

/-- The supplied evidence maps act naturally on all dependent families. -/
def totalTransformation {F G : C ⥤ D} (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) :
    totalRestriction G P ⟶ totalRestriction F P where
  app := totalEvidenceMap change P
  naturality _ _ operation := totalEvidenceMap_naturality change P operation

theorem totalTransformation_identity (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    totalTransformation (𝟙 F) P = 𝟙 (totalRestriction F P) := by
  ext A world receipt
  exact congrArg (fun map => map.app world receipt) (totalEvidenceMap_identity (F := F) P A)

theorem totalTransformation_composition {F G H : C ⥤ D}
    (first : F ⟶ G) (second : G ⟶ H) (P : Dᵒᵖ ⥤ Type u) :
    totalTransformation (first ≫ second) P =
      totalTransformation second P ≫ totalTransformation first P := by
  ext A world receipt
  exact congrArg (fun map => map.app world receipt)
    (totalEvidenceMap_composition first second P A)

/-- A functor on theory transformations whose values are the actual
dependent-family comprehension functors. -/
def totalActionFunctor (P : Dᵒᵖ ⥤ Type u) :
    (C ⥤ D)ᵒᵖ ⥤ (DisplayedFamily P ⥤ (Cᵒᵖ ⥤ Type u)) where
  obj F := totalRestriction F.unop P
  map change := totalTransformation change.unop P
  map_id F := totalTransformation_identity F.unop P
  map_comp first second := totalTransformation_composition second.unop first.unop P

/-- Comprehension of a restricted family agrees naturally with restriction
of its evidence-bearing total. -/
def totalRestrictionIso (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    totalRestriction F P ≅
      comprehensionTotals P ⋙ Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves F :=
  NatIso.ofComponents (totalComparison F P) (by
    intro A A' operation
    ext world receipt
    rfl)

theorem totalTransformation_square {F G : C ⥤ D} (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) :
    totalTransformation change P ≫ (totalRestrictionIso F P).hom =
      (totalRestrictionIso G P).hom ≫
        whiskerLeft (comprehensionTotals P)
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheavesMap change) := by
  ext A world receipt
  exact congrArg (fun map => map.app world receipt) (totalEvidenceMap_square change P A)

/-- The composition comparison includes the actual intermediate dependent
family rather than replacing it with its support predicate. -/
def totalCompositionIso (F : C ⥤ D) (K : D ⥤ E) (P : Eᵒᵖ ⥤ Type u) :
    totalRestriction (F ⋙ K) P ≅
      totalRestriction K P ⋙ Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves F :=
  NatIso.ofComponents (fun A => totalComparison F (K.op ⋙ P) (restrictFamily K P A)) (by
    intro A A' operation
    ext world receipt
    rfl)

theorem totalTransformation_whiskerLeft {F G : C ⥤ D} (K : B ⥤ C)
    (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) :
    totalTransformation (whiskerLeft K change) P ≫ (totalCompositionIso K F P).hom =
      (totalCompositionIso K G P).hom ≫
        whiskerRight (totalTransformation change P)
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves K) := by
  ext A world receipt
  rfl

theorem totalTransformation_whiskerRight {F G : C ⥤ D} (change : F ⟶ G)
    (K : D ⥤ E) (P : Eᵒᵖ ⥤ Type u) :
    totalTransformation (whiskerRight change K) P =
      whiskerLeft (restrictionFunctor K P) (totalTransformation change (K.op ⋙ P)) := by
  ext A world receipt
  rfl

/-- Both orders of horizontal composition transport the same actual
dependent witness. This is equality of the total natural transformations. -/
theorem totalTransformation_interchange {F G : C ⥤ D} {H K : D ⥤ E}
    (first : F ⟶ G) (second : H ⟶ K) (P : Eᵒᵖ ⥤ Type u) :
    totalTransformation (whiskerRight first K) P ≫
        totalTransformation (whiskerLeft F second) P =
      totalTransformation (whiskerLeft G second) P ≫
        totalTransformation (whiskerRight first H) P := by
  rw [← totalTransformation_composition, ← totalTransformation_composition,
    whiskerLeft_comp_whiskerRight]

theorem totalTransformation_horizontal {F G : C ⥤ D} {H K : D ⥤ E}
    (first : F ⟶ G) (second : H ⟶ K) (P : Eᵒᵖ ⥤ Type u) :
    totalTransformation (first ◫ second) P =
      totalTransformation (whiskerRight first K) P ≫
        totalTransformation (whiskerLeft F second) P := by
  rw [NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight, totalTransformation_composition]

/-- The horizontal comparison is compatible with comprehension of both
intermediate theories. -/
theorem totalTransformation_horizontal_square {F G : C ⥤ D} {H K : D ⥤ E}
    (first : F ⟶ G) (second : H ⟶ K) (P : Eᵒᵖ ⥤ Type u) :
    totalTransformation (first ◫ second) P ≫ (totalCompositionIso F H P).hom =
      (totalCompositionIso G K P).hom ≫
        whiskerRight (totalTransformation second P)
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves G) ≫
        (whiskerLeft (totalRestriction H P)
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheavesMap first)) := by
  rw [totalTransformation_horizontal, totalTransformation_interchange]
  rw [Category.assoc, totalTransformation_whiskerRight]
  ext A world receipt
  change (⟨_, _⟩ : TotalAt (restrictFamily H P A) (F.op.obj world)) =
    totalMap (restrictFamily H P A) ((NatTrans.op first).app world)
      ((totalEvidenceMap second P A).app (G.op.obj world) receipt)
  exact (totalMap_of_base_arrow (restrictFamily H P A)
    (elementArrow first (H.op ⋙ P) ⟨world,
      (baseMap second P).app (G.op.obj world) receipt.1⟩)
      (A.map (elementArrow second P ⟨G.op.obj world, receipt.1⟩) receipt.2)).symm

/-- Coherent terms are transported as their supplied sections. -/
theorem totalEvidenceMap_term {F G : C ⥤ D} (change : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) (term : A.sections) :
    sectionLift (restrictFamily G P A) (restrictTerm G P A term) ≫
        totalEvidenceMap change P A =
      baseMap change P ≫ sectionLift (restrictFamily F P A) (restrictTerm F P A term) := by
  ext world value
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  exact term.property (elementArrow change P ⟨world, value⟩)

/-- The comprehension comparison for a composite translation is the same
as the staged comparisons on the actual evidence-bearing totals. -/
theorem totalRestrictionIso_composition (F : C ⥤ D) (K : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) :
    (totalRestrictionIso (F ⋙ K) P).hom =
      (totalCompositionIso F K P).hom ≫
        whiskerRight (totalRestrictionIso K P).hom
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves F) := by
  ext A world receipt
  rfl

/-- Reassociation of three stages gives the same comprehension comparison. -/
theorem totalCompositionIso_associativity (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) :
    (totalCompositionIso (F ⋙ G) H P).hom =
      (totalCompositionIso F (G ⋙ H) P).hom ≫
        whiskerRight (totalCompositionIso G H P).hom
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves F) := by
  ext A world receipt
  rfl

theorem totalCompositionIso_left_identity (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    (totalCompositionIso (𝟭 C) F P).hom = 𝟙 (totalRestriction F P) := by
  ext A world receipt
  rfl

theorem totalCompositionIso_right_identity (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    (totalCompositionIso F (𝟭 D) P).hom = (totalRestrictionIso F P).hom := by
  ext A world receipt
  rfl

end Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherence
