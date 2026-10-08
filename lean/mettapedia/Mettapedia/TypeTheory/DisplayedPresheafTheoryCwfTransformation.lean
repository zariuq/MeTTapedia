import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwf
import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformation
import Mettapedia.GSLT.Core.ContextualPseudoCwfTransformation

/-!
# Corrected native CwF transformations induced by theory transformations

A supplied natural theory transformation induces its actual contravariant
base action and transports displayed evidence along the corresponding
element arrow. The corrected comprehension square identifies that action
with the total-context action. Naturality in every native display map is
proved from the cartesian comprehension laws and the base naturality square.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryCwf DisplayedPresheafTheoryTransformation

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G : C ⥤ D}

def contextTransformation (change : F ⟶ G) : contextFunctor G ⟶ contextFunctor F where
  app context := baseMap change context.val
  naturality := by
    intro source target substitution
    exact (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheavesMap change).naturality substitution

/-- A native display-map component uses the actual family transport on
total evidence, rather than a chosen or truncated certificate. -/
def displayedComponent (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (presheafCwf.{u, u, u} D) P) :
    (pseudoMorphism G).mapTypeObject A ⟶
      TypeOver.reindexObject (baseMap change P) ((pseudoMorphism F).mapTypeObject A) where
  substitution := totalHom (familyMap change P A.val)
  over := totalHom_projection (familyMap change P A.val)

theorem displayedComponent_lift (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (presheafCwf.{u, u, u} D) P) :
    (displayedComponent change P A).substitution ≫
      TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
        (baseMap change P) ((pseudoMorphism F).mapType A.val) =
      baseMap change (totalSpace A.val) := by
  exact totalEvidenceMap_square change P A.val

theorem corrected_comprehension (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (presheafCwf.{u, u, u} D) P) :
    ((pseudoMorphism G).comprehensionIso P A.val).hom ≫
        (displayedComponent change P A).substitution ≫
          TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
            (baseMap change P) ((pseudoMorphism F).mapType A.val) =
      (contextTransformation change).app ⟨totalSpace A.val⟩ ≫
        ((pseudoMorphism F).comprehensionIso P A.val).hom := by
  exact totalEvidenceMap_square change P A.val

set_option backward.isDefEq.respectTransparency false in
/-- The displayed component is natural in all native display arrows,
including arrows supplied in the CwF interface rather than as family maps. -/
theorem displayedComponent_naturality (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    {A B : TypeOver (presheafCwf.{u, u, u} D) P} (arrow : A ⟶ B) :
    ((pseudoMorphism G).mapTypeFunctor P).map arrow ≫ displayedComponent change P B =
      displayedComponent change P A ≫
        (TypeOver.reindexFunctor (baseMap change P)).map
          (((pseudoMorphism F).mapTypeFunctor P).map arrow) := by
  apply TypeOver.extensionSubstitution_cancel (C := presheafCwf.{u, u, u} C)
    (Γ := G.op ⋙ P) (Δ := F.op ⋙ P)
    (source := (pseudoMorphism G).mapTypeObject A)
    (B := (pseudoMorphism F).mapTypeObject B) (baseMap change P)
  change
    ((((pseudoMorphism G).mapTypeFunctor P).map arrow).substitution ≫
      (displayedComponent change P B).substitution) ≫
        TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
          (baseMap change P) ((pseudoMorphism F).mapType B.val) =
    ((displayedComponent change P A).substitution ≫
      (TypeOver.reindexArrow (baseMap change P)
        (((pseudoMorphism F).mapTypeFunctor P).map arrow)).substitution) ≫
        TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
          (baseMap change P) ((pseudoMorphism F).mapType B.val)
  rw [Category.assoc, displayedComponent_lift]
  rw [Category.assoc]
  have lift := TypeOver.extensionSubstitution_naturality (baseMap change P)
    (((pseudoMorphism F).mapTypeFunctor P).map arrow)
  change
    (TypeOver.reindexArrow (baseMap change P)
      (((pseudoMorphism F).mapTypeFunctor P).map arrow)).substitution ≫
      TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
        (baseMap change P) ((pseudoMorphism F).mapType B.val) =
    TypeOver.extensionSubstitution (C := presheafCwf.{u, u, u} C)
        (baseMap change P) ((pseudoMorphism F).mapType A.val) ≫
      (((pseudoMorphism F).mapTypeFunctor P).map arrow).substitution at lift
  rw [lift, ← Category.assoc, displayedComponent_lift]
  exact (contextTransformation change).naturality
    (show (⟨totalSpace A.val⟩ : (presheafCwf.{u, u, u} D).base.Context) ⟶ ⟨totalSpace B.val⟩ from
      arrow.substitution)

/-- This is a genuine 2-cell of the existing pseudo-CwF morphism category,
with its corrected comprehension condition derived for the supplied theory map. -/
def correctedTransformation (change : F ⟶ G) :
    CorrectedTransformationData (pseudoMorphism G) (pseudoMorphism F) where
  base := contextTransformation change
  family := displayedComponent change
  family_naturality := displayedComponent_naturality change
  comprehension_coherence := corrected_comprehension change

set_option backward.isDefEq.respectTransparency false in
theorem correctedTransformation_identity (F : C ⥤ D) :
    correctedTransformation (𝟙 F) = CorrectedTransformationData.identity (pseudoMorphism F) := by
  apply CorrectedTransformationData.ext_of_base_eq
  apply NatTrans.ext
  funext context
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  exact context.val.map_id_apply (F.op.obj world) value

set_option backward.isDefEq.respectTransparency false in
theorem correctedTransformation_composition {H : C ⥤ D}
    (first : F ⟶ G) (second : G ⟶ H) :
    correctedTransformation (first ≫ second) =
      CorrectedTransformationData.vertical (correctedTransformation second)
        (correctedTransformation first) := by
  apply CorrectedTransformationData.ext_of_base_eq
  apply NatTrans.ext
  funext context
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  exact context.val.map_comp_apply ((NatTrans.op second).app world)
    ((NatTrans.op first).app world) value

/-- The actual semantic CwF action on theories and their transformations.
Its 2-cells are corrected native CwF transformations; this does not assert
unrestricted equality of product or classifier comparisons. -/
def theoryFunctor : (C ⥤ D)ᵒᵖ ⥤
    PseudoCwfMorphism (presheafCwfWithTerminal.{u, u, u} D)
      (presheafCwfWithTerminal.{u, u, u} C) where
  obj theory := pseudoMorphism theory.unop
  map transformation := correctedTransformation transformation.unop
  map_id theory := correctedTransformation_identity theory.unop
  map_comp first second := correctedTransformation_composition second.unop first.unop

end Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformation
