import Mettapedia.TypeTheory.ContextualLocalUniversesDisplay
import Mettapedia.TypeTheory.ContextualLocalUniversesMorphism
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformation

/-!
# Corrected theory transformations on native local presentations

The displayed action carries the actual decoded evidence along the theory
transformation. External parameter contexts and names remain part of its
source and target presentations. The comprehension square records the
complete total-evidence transport, including its base substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalTheoryTransformation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice DisplayedPresheafCwf
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryTransformation
open ContextualLocalUniverses ContextualLocalUniversesMorphism

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G : C ⥤ D}

abbrev nativeLocalModel (D : Type u) [Category.{u} D] :=
  localCwfWithTerminal (presheafCwfWithTerminal.{u, u, u} D)

instance localTypeCategory (P : Dᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (nativeLocalModel D).toCwf P) :=
  TypeOver.instCategory (C := (nativeLocalModel D).toCwf) (Γ := P)

local instance bareLocalTypeCategory (P : Dᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (localCwf (presheafCwf.{u, u, u} D)) P) :=
  TypeOver.instCategory (C := localCwf (presheafCwf.{u, u, u} D)) (Γ := P)

def localMorphism (F : C ⥤ D) : PseudoCwfMorphism (nativeLocalModel D) (nativeLocalModel C) :=
  (strictAction (DisplayedPresheafTheoryCwf.strictMorphism F)).toPseudo

set_option backward.isDefEq.respectTransparency false in
def displayedComponent (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (nativeLocalModel D).toCwf P) :
    (localMorphism G).mapTypeObject A ⟶
      TypeOver.reindexObject (baseMap change P) ((localMorphism F).mapTypeObject A) where
  substitution := totalHom (familyMap change P A.val.decoded)
  over := totalHom_projection (familyMap change P A.val.decoded)

theorem displayedComponent_lift (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (nativeLocalModel D).toCwf P) :
    (displayedComponent change P A).substitution ≫
      TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf)
        (baseMap change P) ((localMorphism F).mapType A.val) =
      baseMap change (totalSpace A.val.decoded) :=
  totalEvidenceMap_square change P A.val.decoded

/-- Decoding the constructed local display component is the independently
constructed native evidence transport. Its complete substitution agrees. -/
theorem decoder_component (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (nativeLocalModel D).toCwf P) :
    (displayDecoder (presheafCwf.{u, u, u} C) (G.op ⋙ P)).map
      (displayedComponent change P A) =
        DisplayedPresheafTheoryCwfTransformation.displayedComponent change P
          ((displayDecoder (presheafCwf.{u, u, u} D) P).obj A) := TypeOver.Hom.ext rfl

theorem displayedComponent_value (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (nativeLocalModel D).toCwf P) (world : Cᵒᵖ)
    (receipt : (totalSpace (restrictFamily G P A.val.decoded)).obj world) :
    ((displayedComponent change P A).substitution).app world receipt =
      ⟨receipt.1, (familyMap change P A.val.decoded).app ⟨world, receipt.1⟩ receipt.2⟩ := rfl

theorem corrected_comprehension (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : TypeOver (nativeLocalModel D).toCwf P) :
    ((localMorphism G).comprehensionIso P A.val).hom ≫
        (displayedComponent change P A).substitution ≫
          TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf)
            (baseMap change P) ((localMorphism F).mapType A.val) =
      (DisplayedPresheafTheoryCwfTransformation.contextTransformation change).app
        ⟨totalSpace A.val.decoded⟩ ≫
          ((localMorphism F).comprehensionIso P A.val).hom :=
  totalEvidenceMap_square change P A.val.decoded

set_option backward.isDefEq.respectTransparency false in
theorem displayedComponent_naturality (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    {A B : TypeOver (nativeLocalModel D).toCwf P} (arrow : A ⟶ B) :
    ((localMorphism G).mapTypeFunctor P).map arrow ≫ displayedComponent change P B =
      displayedComponent change P A ≫
        (TypeOver.reindexFunctor (baseMap change P)).map
          (((localMorphism F).mapTypeFunctor P).map arrow) := by
  apply TypeOver.Hom.ext
  have native := DisplayedPresheafTheoryCwfTransformation.displayedComponent_naturality
    change P ((displayDecoder (presheafCwf.{u, u, u} D) P).map arrow)
  exact congrArg (fun result => result.substitution) native

/-- The full supplied local presentation and actual decoded evidence form
a corrected cell. Both coherence obligations were derived above. -/
def correctedTransformation (change : F ⟶ G) :
    CorrectedTransformationData (localMorphism G) (localMorphism F) where
  base := DisplayedPresheafTheoryCwfTransformation.contextTransformation change
  family := displayedComponent change
  family_naturality := displayedComponent_naturality change
  comprehension_coherence := corrected_comprehension change

set_option backward.isDefEq.respectTransparency false in
theorem correctedTransformation_identity (F : C ⥤ D) :
    correctedTransformation (𝟙 F) = CorrectedTransformationData.identity (localMorphism F) := by
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

def theoryFunctor : (C ⥤ D)ᵒᵖ ⥤
    PseudoCwfMorphism (nativeLocalModel D) (nativeLocalModel C) where
  obj theory := localMorphism theory.unop
  map transformation := correctedTransformation transformation.unop
  map_id theory := correctedTransformation_identity theory.unop
  map_comp first second := correctedTransformation_composition second.unop first.unop

end Mettapedia.TypeTheory.NativeLocalTheoryTransformation
