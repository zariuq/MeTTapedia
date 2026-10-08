import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformation
import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherence
import Mettapedia.GSLT.Core.ContextualPseudoCwfBicategory

/-!
# Composition coherence of the native theory CwF action

The actual restriction action of a composite theory functor is compared
with composition in the existing bicategory of pseudo CwF morphisms.
The comparisons retain the chosen native comprehension and its evidence.
Theory transformations respect horizontal composition through these
canonical corrected comparisons. This is a semantic CwF action; it does
not assert classifier preservation by arbitrary noninvertible 2-cells.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfComposition

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryCwf DisplayedPresheafTheoryCwfTransformation
open DisplayedPresheafTheoryTransformationCoherence

universe u
variable {B C D E : Type u}
variable [Category.{u} B] [Category.{u} C] [Category.{u} D] [Category.{u} E]

set_option backward.isDefEq.respectTransparency false in
private theorem native_identity_naturality (P : Cᵒᵖ ⥤ Type u)
    {A A' : TypeOver (presheafCwf.{u, u, u} C) P} (arrow : A ⟶ A') :
    arrow ≫ (TypeOver.identityObjectIso A').inv =
      (TypeOver.identityObjectIso A).inv ≫
        (TypeOver.reindexFunctor (C := presheafCwf.{u, u, u} C) (𝟙 P)).map arrow :=
  (TypeOver.identityReindexIso (C := presheafCwf.{u, u, u} C) P).inv.naturality arrow

set_option backward.isDefEq.respectTransparency false in
private theorem native_identity_lift (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    (TypeOver.identityObjectIso (⟨A⟩ : TypeOver (presheafCwf.{u, u, u} C) P)).inv.substitution ≫
      TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C) (𝟙 P) A =
        𝟙 (totalSpace A) := by
  let comparison := TypeOver.identityObjectIso
    (⟨A⟩ : TypeOver (presheafCwf.{u, u, u} C) P)
  have lift :
      TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C) (𝟙 P) A =
        comparison.hom.substitution :=
    (TypeOver.identityObjectIso_hom_substitution
      (C := presheafCwf.{u, u, u} C) (⟨A⟩ : TypeOver (presheafCwf.{u, u, u} C) P)).symm
  calc
    _ = comparison.inv.substitution ≫ comparison.hom.substitution :=
      congrArg (fun arrow => comparison.inv.substitution ≫ arrow) lift
    _ = _ := congrArg TypeOver.Hom.substitution comparison.inv_hom_id

/-- Restriction of a composite and iterated restriction agree on actual
context objects and substitutions. -/
def compositionBaseIso (F : C ⥤ D) (G : D ⥤ E) :
    contextFunctor (F ⋙ G) ≅ contextFunctor G ⋙ contextFunctor F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro source target substitution
    apply NatTrans.ext
    funext world
    rfl)

set_option backward.isDefEq.respectTransparency false in
theorem composition_type_arrow (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u)
    {A A' : TypeOver (presheafCwf.{u, u, u} E) P} (arrow : A ⟶ A') :
    ((pseudoMorphism (F ⋙ G)).mapTypeFunctor P).map arrow =
      (((pseudoMorphism G).comp (pseudoMorphism F)).mapTypeFunctor P).map arrow := by
  apply TypeOver.Hom.ext
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem composition_comprehension (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    ((pseudoMorphism (F ⋙ G)).comprehensionIso P A).hom =
      (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A).hom := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The displayed component of the direct-to-staged comparison uses the
canonical identity lift on the common restricted native family. -/
def compositionComponent (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : TypeOver (presheafCwf.{u, u, u} E) P) :
    (pseudoMorphism (F ⋙ G)).mapTypeObject A ⟶
      TypeOver.reindexObject ((compositionBaseIso F G).hom.app ⟨P⟩)
        (((pseudoMorphism G).comp (pseudoMorphism F)).mapTypeObject A) :=
  (TypeOver.identityObjectIso
    (⟨restrictFamily (F ⋙ G) P A.val⟩ : TypeOver (presheafCwf.{u, u, u} C) ((F ⋙ G).op ⋙ P))).inv

set_option backward.isDefEq.respectTransparency false in
theorem compositionComponent_naturality (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u)
    {A A' : TypeOver (presheafCwf.{u, u, u} E) P} (arrow : A ⟶ A') :
    ((pseudoMorphism (F ⋙ G)).mapTypeFunctor P).map arrow ≫ compositionComponent F G P A' =
      compositionComponent F G P A ≫
        (TypeOver.reindexFunctor (C := presheafCwf.{u, u, u} C)
          ((compositionBaseIso F G).hom.app ⟨P⟩)).map
          ((((pseudoMorphism G).comp (pseudoMorphism F)).mapTypeFunctor P).map arrow) := by
  let mappedArrow :
      (⟨restrictFamily (F ⋙ G) P A.val⟩ : TypeOver (presheafCwf.{u, u, u} C) ((F ⋙ G).op ⋙ P)) ⟶
        ⟨restrictFamily (F ⋙ G) P A'.val⟩ :=
    ((pseudoMorphism (F ⋙ G)).mapTypeFunctor P).map arrow
  have natural := native_identity_naturality ((F ⋙ G).op ⋙ P) mappedArrow
  have equalArrow := congrArg (fun nativeArrow =>
    compositionComponent F G P A ≫
      (TypeOver.reindexFunctor (C := presheafCwf.{u, u, u} C)
        ((compositionBaseIso F G).hom.app ⟨P⟩)).map nativeArrow)
    (composition_type_arrow F G P arrow)
  exact natural.trans equalArrow

set_option backward.isDefEq.respectTransparency false in
theorem compositionComponent_comprehension (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : TypeOver (presheafCwf.{u, u, u} E) P) :
    ((pseudoMorphism (F ⋙ G)).comprehensionIso P A.val).hom ≫
        (compositionComponent F G P A).substitution ≫
          TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
            ((compositionBaseIso F G).hom.app ⟨P⟩)
            (((pseudoMorphism G).comp (pseudoMorphism F)).mapType A.val) =
      (compositionBaseIso F G).hom.app ⟨totalSpace A.val⟩ ≫
        (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A.val).hom := by
  have lift := native_identity_lift ((F ⋙ G).op ⋙ P) (restrictFamily (F ⋙ G) P A.val)
  calc
    _ = ((pseudoMorphism (F ⋙ G)).comprehensionIso P A.val).hom ≫
        𝟙 (totalSpace (restrictFamily (F ⋙ G) P A.val)) :=
      congrArg (fun tail => ((pseudoMorphism (F ⋙ G)).comprehensionIso P A.val).hom ≫ tail) lift
    _ = ((pseudoMorphism (F ⋙ G)).comprehensionIso P A.val).hom := Category.comp_id _
    _ = _ := (composition_comprehension F G P A.val).trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The corrected comparison from direct to staged CwF restriction. Its
displayed arrow is the canonical identity-reindexing comparison, with the
actual direct and staged arrow actions identified by the preceding law. -/
def compositionComparison (F : C ⥤ D) (G : D ⥤ E) :
    CorrectedTransformationData (pseudoMorphism (F ⋙ G))
      ((pseudoMorphism G).comp (pseudoMorphism F)) where
  base := (compositionBaseIso F G).hom
  family := compositionComponent F G
  family_naturality := compositionComponent_naturality F G
  comprehension_coherence := compositionComponent_comprehension F G

set_option backward.isDefEq.respectTransparency false in
def compositionInverseComponent (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : TypeOver (presheafCwf.{u, u, u} E) P) :
    ((pseudoMorphism G).comp (pseudoMorphism F)).mapTypeObject A ⟶
      TypeOver.reindexObject ((compositionBaseIso F G).inv.app ⟨P⟩)
        ((pseudoMorphism (F ⋙ G)).mapTypeObject A) :=
  (TypeOver.identityObjectIso
    (⟨restrictFamily (F ⋙ G) P A.val⟩ : TypeOver (presheafCwf.{u, u, u} C) ((F ⋙ G).op ⋙ P))).inv

set_option backward.isDefEq.respectTransparency false in
theorem compositionComponent_inverse_naturality (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u)
    {A A' : TypeOver (presheafCwf.{u, u, u} E) P} (arrow : A ⟶ A') :
    (((pseudoMorphism G).comp (pseudoMorphism F)).mapTypeFunctor P).map arrow ≫
        compositionInverseComponent F G P A' =
      compositionInverseComponent F G P A ≫
        (TypeOver.reindexFunctor (C := presheafCwf.{u, u, u} C)
          ((compositionBaseIso F G).inv.app ⟨P⟩)).map
          (((pseudoMorphism (F ⋙ G)).mapTypeFunctor P).map arrow) := by
  let mappedArrow :
      (⟨restrictFamily (F ⋙ G) P A.val⟩ : TypeOver (presheafCwf.{u, u, u} C) ((F ⋙ G).op ⋙ P)) ⟶
        ⟨restrictFamily (F ⋙ G) P A'.val⟩ :=
    ((pseudoMorphism (F ⋙ G)).mapTypeFunctor P).map arrow
  have natural := native_identity_naturality ((F ⋙ G).op ⋙ P) mappedArrow
  have sameArrow := congrArg (fun nativeArrow =>
    nativeArrow ≫ compositionInverseComponent F G P A') (composition_type_arrow F G P arrow)
  exact sameArrow.symm.trans natural

set_option backward.isDefEq.respectTransparency false in
theorem compositionComponent_inverse_comprehension (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : TypeOver (presheafCwf.{u, u, u} E) P) :
    (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A.val).hom ≫
        (compositionInverseComponent F G P A).substitution ≫
          TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
            ((compositionBaseIso F G).inv.app ⟨P⟩)
            ((pseudoMorphism (F ⋙ G)).mapType A.val) =
      (compositionBaseIso F G).inv.app ⟨totalSpace A.val⟩ ≫
        ((pseudoMorphism (F ⋙ G)).comprehensionIso P A.val).hom := by
  have lift := native_identity_lift ((F ⋙ G).op ⋙ P) (restrictFamily (F ⋙ G) P A.val)
  calc
    _ = (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A.val).hom ≫
        𝟙 (totalSpace (restrictFamily (F ⋙ G) P A.val)) :=
      congrArg (fun tail =>
        (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A.val).hom ≫ tail) lift
    _ = (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A.val).hom :=
      Category.comp_id _
    _ = _ := (composition_comprehension F G P A.val).symm.trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison uses the same canonical reindexing lift, in
the opposite base direction. -/
def compositionComparisonInv (F : C ⥤ D) (G : D ⥤ E) :
    CorrectedTransformationData ((pseudoMorphism G).comp (pseudoMorphism F))
      (pseudoMorphism (F ⋙ G)) where
  base := (compositionBaseIso F G).inv
  family := compositionInverseComponent F G
  family_naturality := compositionComponent_inverse_naturality F G
  comprehension_coherence := compositionComponent_inverse_comprehension F G

/-- Direct and staged restriction are isomorphic in the genuine corrected
hom category, not merely equal on the support of their evidence. -/
def compositionIso (F : C ⥤ D) (G : D ⥤ E) :
    pseudoMorphism (F ⋙ G) ≅ (pseudoMorphism G).comp (pseudoMorphism F) where
  hom := compositionComparison F G
  inv := compositionComparisonInv F G
  hom_inv_id := CorrectedTransformationData.ext_of_base_eq _ _
    (compositionBaseIso F G).hom_inv_id
  inv_hom_id := CorrectedTransformationData.ext_of_base_eq _ _
    (compositionBaseIso F G).inv_hom_id

/-- The identity theory acts by the actual identity on native context
objects and natural substitutions. -/
def identityBaseIso (C : Type u) [Category.{u} C] :
    contextFunctor (𝟭 C) ≅ 𝟭 (presheafCwf.{u, u, u} C).base.Context :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro source target substitution
    apply NatTrans.ext
    funext world
    rfl)

set_option backward.isDefEq.respectTransparency false in
theorem identity_type_arrow (P : Cᵒᵖ ⥤ Type u)
    {A A' : TypeOver (presheafCwf.{u, u, u} C) P} (arrow : A ⟶ A') :
    ((pseudoMorphism (𝟭 C)).mapTypeFunctor P).map arrow = arrow := by
  apply TypeOver.Hom.ext
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem identity_comprehension (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    ((pseudoMorphism (𝟭 C)).comprehensionIso P A).hom = 𝟙 (totalSpace A) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

set_option backward.isDefEq.respectTransparency false in
def identityComponent (P : Cᵒᵖ ⥤ Type u)
    (A : TypeOver (presheafCwf.{u, u, u} C) P) :
    (pseudoMorphism (𝟭 C)).mapTypeObject A ⟶
      TypeOver.reindexObject ((identityBaseIso C).hom.app ⟨P⟩)
        ((PseudoCwfMorphism.identity (presheafCwfWithTerminal.{u, u, u} C)).mapTypeObject A) :=
  (TypeOver.identityObjectIso A).inv

set_option backward.isDefEq.respectTransparency false in
theorem identityComponent_naturality (P : Cᵒᵖ ⥤ Type u)
    {A A' : TypeOver (presheafCwf.{u, u, u} C) P} (arrow : A ⟶ A') :
    ((pseudoMorphism (𝟭 C)).mapTypeFunctor P).map arrow ≫ identityComponent P A' =
      identityComponent P A ≫
        (TypeOver.reindexFunctor (C := presheafCwf.{u, u, u} C)
          ((identityBaseIso C).hom.app ⟨P⟩)).map
          (((PseudoCwfMorphism.identity (presheafCwfWithTerminal C)).mapTypeFunctor P).map arrow) := by
  have native := native_identity_naturality P arrow
  have sameArrow := congrArg (fun nativeArrow => nativeArrow ≫ identityComponent P A')
    (identity_type_arrow P arrow)
  exact sameArrow.trans native

set_option backward.isDefEq.respectTransparency false in
theorem identityComponent_comprehension (P : Cᵒᵖ ⥤ Type u)
    (A : TypeOver (presheafCwf.{u, u, u} C) P) :
    ((pseudoMorphism (𝟭 C)).comprehensionIso P A.val).hom ≫
        (identityComponent P A).substitution ≫
          TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
            ((identityBaseIso C).hom.app ⟨P⟩) A.val =
      (identityBaseIso C).hom.app ⟨totalSpace A.val⟩ ≫
        ((PseudoCwfMorphism.identity (presheafCwfWithTerminal C)).comprehensionIso P A.val).hom := by
  have lift := native_identity_lift P A.val
  calc
    _ = ((pseudoMorphism (𝟭 C)).comprehensionIso P A.val).hom ≫ 𝟙 (totalSpace A.val) :=
      congrArg (fun tail => ((pseudoMorphism (𝟭 C)).comprehensionIso P A.val).hom ≫ tail) lift
    _ = ((pseudoMorphism (𝟭 C)).comprehensionIso P A.val).hom := Category.comp_id _
    _ = _ := (identity_comprehension P A.val).trans (Category.id_comp _).symm

/-- The genuine corrected unit comparison of the native semantic action. -/
def identityComparison (C : Type u) [Category.{u} C] :
    CorrectedTransformationData (pseudoMorphism (𝟭 C))
      (PseudoCwfMorphism.identity (presheafCwfWithTerminal.{u, u, u} C)) where
  base := (identityBaseIso C).hom
  family := identityComponent
  family_naturality := identityComponent_naturality
  comprehension_coherence := identityComponent_comprehension

set_option backward.isDefEq.respectTransparency false in
def identityInverseComponent (P : Cᵒᵖ ⥤ Type u)
    (A : TypeOver (presheafCwf.{u, u, u} C) P) :
    (PseudoCwfMorphism.identity (presheafCwfWithTerminal.{u, u, u} C)).mapTypeObject A ⟶
      TypeOver.reindexObject ((identityBaseIso C).inv.app ⟨P⟩)
        ((pseudoMorphism (𝟭 C)).mapTypeObject A) :=
  (TypeOver.identityObjectIso A).inv

set_option backward.isDefEq.respectTransparency false in
theorem identityInverseComponent_naturality (P : Cᵒᵖ ⥤ Type u)
    {A A' : TypeOver (presheafCwf.{u, u, u} C) P} (arrow : A ⟶ A') :
    ((PseudoCwfMorphism.identity (presheafCwfWithTerminal C)).mapTypeFunctor P).map arrow ≫
        identityInverseComponent P A' =
      identityInverseComponent P A ≫
        (TypeOver.reindexFunctor (C := presheafCwf.{u, u, u} C)
          ((identityBaseIso C).inv.app ⟨P⟩)).map
          (((pseudoMorphism (𝟭 C)).mapTypeFunctor P).map arrow) := by
  have native := native_identity_naturality P arrow
  have sameArrow := congrArg (fun nativeArrow => identityInverseComponent P A ≫
    (TypeOver.reindexFunctor (C := presheafCwf.{u, u, u} C) (𝟙 P)).map nativeArrow)
    (identity_type_arrow P arrow)
  exact native.trans sameArrow.symm

set_option backward.isDefEq.respectTransparency false in
theorem identityInverseComponent_comprehension (P : Cᵒᵖ ⥤ Type u)
    (A : TypeOver (presheafCwf.{u, u, u} C) P) :
    ((PseudoCwfMorphism.identity (presheafCwfWithTerminal C)).comprehensionIso P A.val).hom ≫
        (identityInverseComponent P A).substitution ≫
          TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
            ((identityBaseIso C).inv.app ⟨P⟩) ((pseudoMorphism (𝟭 C)).mapType A.val) =
      (identityBaseIso C).inv.app ⟨totalSpace A.val⟩ ≫
        ((pseudoMorphism (𝟭 C)).comprehensionIso P A.val).hom := by
  have lift := native_identity_lift P A.val
  calc
    _ = (𝟙 (totalSpace A.val)) ≫ 𝟙 (totalSpace A.val) :=
      congrArg (fun tail => (𝟙 (totalSpace A.val)) ≫ tail) lift
    _ = _ := congrArg (fun arrow => (𝟙 (totalSpace A.val)) ≫ arrow)
      (identity_comprehension P A.val).symm

def identityComparisonInv (C : Type u) [Category.{u} C] :
    CorrectedTransformationData
      (PseudoCwfMorphism.identity (presheafCwfWithTerminal.{u, u, u} C))
      (pseudoMorphism (𝟭 C)) where
  base := (identityBaseIso C).inv
  family := identityInverseComponent
  family_naturality := identityInverseComponent_naturality
  comprehension_coherence := identityInverseComponent_comprehension

/-- The unit comparison is invertible in the corrected hom category. -/
def identityIso (C : Type u) [Category.{u} C] :
    pseudoMorphism (𝟭 C) ≅ PseudoCwfMorphism.identity (presheafCwfWithTerminal.{u, u, u} C) where
  hom := identityComparison C
  inv := identityComparisonInv C
  hom_inv_id := CorrectedTransformationData.ext_of_base_eq _ _ (identityBaseIso C).hom_inv_id
  inv_hom_id := CorrectedTransformationData.ext_of_base_eq _ _ (identityBaseIso C).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- The comprehension comparison of the actual pseudo composite is the
previously constructed composition comparison on dependent totals. -/
theorem composition_total_comparison (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A).inv =
      ((totalCompositionIso F G P).hom ≫
        Functor.whiskerRight (totalRestrictionIso G P).hom
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves F)).app A := by
  have staged := NatTrans.congr_app (totalRestrictionIso_composition F G P) A
  have actual :
      (((pseudoMorphism G).comp (pseudoMorphism F)).comprehensionIso P A).inv =
        (totalRestrictionIso (F ⋙ G) P).hom.app A := by
    apply NatTrans.ext
    funext world
    apply ConcreteCategory.hom_ext
    intro receipt
    rfl
  exact actual.trans staged

set_option backward.isDefEq.respectTransparency false in
theorem context_horizontal_square {F G : C ⥤ D} {H K : D ⥤ E}
    (first : F ⟶ G) (second : H ⟶ K) :
    contextTransformation (first ◫ second) ≫ (compositionBaseIso F H).hom =
      (compositionBaseIso G K).hom ≫
        (CorrectedTransformationData.horizontal (correctedTransformation second)
          (correctedTransformation first)).base := by
  apply NatTrans.ext
  funext context
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  let singleton : DisplayedFamily context.val := (Functor.const _).obj PUnit
  have total := NatTrans.congr_app
    (totalTransformation_horizontal_square first second context.val) singleton
  have component := NatTrans.congr_app total world
  have receipt := ConcreteCategory.congr_hom component
    (show (totalSpace (restrictFamily (G ⋙ K) context.val singleton)).obj world from
      ⟨value, PUnit.unit⟩)
  exact congrArg Sigma.fst receipt

set_option backward.isDefEq.respectTransparency false in
/-- Horizontal theory transformation agrees with the genuine horizontal
operation in the corrected CwF bicategory. The source and target comparison
cells remain explicit. The displayed action is forced by the proved
comprehension squares, not discarded by the faithful base argument. -/
theorem corrected_horizontal_square {F G : C ⥤ D} {H K : D ⥤ E}
    (first : F ⟶ G) (second : H ⟶ K) :
    correctedTransformation (first ◫ second) ≫ (compositionIso F H).hom =
      (compositionIso G K).hom ≫
        CorrectedTransformationData.horizontal (correctedTransformation second)
          (correctedTransformation first) :=
  CorrectedTransformationData.ext_of_base_eq _ _ (context_horizontal_square first second)

set_option backward.isDefEq.respectTransparency false in
/-- The theory left unit corresponds to the CwF right unit, as required
by contravariant restriction. -/
theorem left_identity_coherence (F : C ⥤ D) :
    (compositionIso (𝟭 C) F).hom ≫
        CorrectedTransformationData.leftWhisker (pseudoMorphism F) (identityIso C).hom ≫
          CorrectedTransformationData.rightUnitor (pseudoMorphism F) =
      correctedTransformation (Functor.leftUnitor F).inv := by
  apply CorrectedTransformationData.ext_of_base_eq
  apply NatTrans.ext
  funext context
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  exact (context.val.map_id_apply (F.op.obj world) value).symm

set_option backward.isDefEq.respectTransparency false in
/-- The theory right unit corresponds to the CwF left unit. -/
theorem right_identity_coherence (F : C ⥤ D) :
    (compositionIso F (𝟭 D)).hom ≫
        CorrectedTransformationData.rightWhisker (identityIso D).hom (pseudoMorphism F) ≫
          CorrectedTransformationData.leftUnitor (pseudoMorphism F) =
      correctedTransformation (Functor.rightUnitor F).inv := by
  apply CorrectedTransformationData.ext_of_base_eq
  apply NatTrans.ext
  funext context
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  exact (context.val.map_id_apply (F.op.obj world) value).symm

set_option backward.isDefEq.respectTransparency false in
/-- Both parenthesizations of three theory stages yield the same corrected
CwF comparison, including the existing CwF associator and the actual
contravariant action of the theory associator. -/
theorem associativity_coherence (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    (compositionIso (F ⋙ G) H).hom ≫
        CorrectedTransformationData.leftWhisker (pseudoMorphism H) (compositionIso F G).hom =
      correctedTransformation (Functor.associator F G H).inv ≫
        (compositionIso F (G ⋙ H)).hom ≫
          CorrectedTransformationData.rightWhisker (compositionIso G H).hom (pseudoMorphism F) ≫
            CorrectedTransformationData.associator (pseudoMorphism H)
              (pseudoMorphism G) (pseudoMorphism F) := by
  apply CorrectedTransformationData.ext_of_base_eq
  apply NatTrans.ext
  funext context
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  exact (context.val.map_id_apply ((F ⋙ G ⋙ H).op.obj world) value).symm

end Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfComposition
