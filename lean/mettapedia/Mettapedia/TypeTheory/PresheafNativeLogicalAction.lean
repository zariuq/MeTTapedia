import Mettapedia.TypeTheory.NativeLocalTheoryPseudofunctor
import Mettapedia.TypeTheory.NativeLocalDisplayComparisons
import Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherence
import Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherence
import Mettapedia.TypeTheory.DisplayedPresheafSumTransformationCoherence
import Mettapedia.TypeTheory.PresheafClosedComprehension

/-!
# Logical comparisons of the native presheaf action

The logical comparison arrows below live in the display categories of the
actual native contextual action. Their complete comprehension substitutions
compose with that action and its corrected theory transformations. Dependent
sums have invertible comparisons; dependent products have colax comparisons,
with inverses exactly when the stated future-argument condition supplies
them. Contextual truth values use their sieve comparison, which is lax for a
general theory transformation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeLogicalAction

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf DisplayedPresheafSliceSubstitution
open ContextualLocalUniverses NativeLocalTypeFormers
open NativeLocalTheoryRestriction NativeLocalTheoryTransformation
open NativeLocalDisplayComparisons

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

local instance decodedCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} ((presheafCwf.{u, u, u} C).Ty P) :=
  inferInstanceAs (Category.{u} (DisplayedFamily.{u, u, u, u} P))

theorem totalHom_composition {P : Cᵒᵖ ⥤ Type u}
    {A B H : DisplayedFamily P} (first : A ⟶ B) (second : B ⟶ H) :
    totalHom (first ≫ second) = totalHom first ≫ totalHom second := by
  ext world receipt
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Mapping the complete display arrow is the actual contextual arrow
action, rather than only a map between equal fibre carriers. -/
theorem action_displayHom (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A B : NativeType P) (operation : A.decoded ⟶ B.decoded) :
    ((localMorphism F).mapTypeFunctor P).map (displayHom A B operation) =
      displayHom (restrict F A) (restrict F B)
        ((DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F P).map operation) := by
  apply TypeOver.Hom.ext
  simp only [StrictCwfMorphism.toPseudo_mapTypeArrow,
    StrictCwfMorphism.mapTypeArrow, StrictCwfMorphism.comprehensionIso,
    localMorphism, ContextualLocalUniversesMorphism.strictAction,
    ContextualLocalUniversesMorphism.familyAction,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

attribute [local irreducible] NativeLocalTypeFormers.sigma

set_option backward.isDefEq.respectTransparency true in
theorem sum_family_identity (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    (sumIso (𝟭 D) A B).hom = 𝟙 (sigma A B).decoded := by
  rcases B with ⟨parameters, family, name⟩
  let B : NativeType (totalSpace A.decoded) := ⟨parameters, family, name⟩
  apply (Iso.cancel_iso_hom_right _ _
    (eqToIso (C := DisplayedFamily P) (sigmaDecode A B))).mp
  have identity := sumIso_identity A B
  change (sumIso (𝟭 D) A B).hom ≫
    (eqToIso (C := DisplayedFamily P) (sigmaDecode A B)).hom =
      (eqToIso (C := DisplayedFamily P) (sigmaDecode A B)).hom at identity
  exact identity.trans (Category.id_comp (obj := DisplayedFamily P) _).symm

set_option backward.isDefEq.respectTransparency false in
theorem product_family_identity (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    productMap (𝟭 D) A B = 𝟙 (pi A B).decoded := by
  apply (Iso.cancel_iso_hom_right _ _ (piDecodeIso A B)).mp
  rcases B with ⟨parameters, family, name⟩
  let B : NativeType (totalSpace A.decoded) := ⟨parameters, family, name⟩
  have identity := productMap_identity A B
  change productMap (𝟭 D) A B ≫ (piDecodeIso A B).hom =
    (piDecodeIso A B).hom at identity
  exact identity.trans (Category.id_comp (obj := DisplayedFamily P) _).symm

set_option backward.isDefEq.respectTransparency true in
theorem sum_family_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    (sumIso (F ⋙ G) A B).hom =
      (DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F (G.op ⋙ P)).map
          (sumIso G A B).hom ≫
        (sumIso F (restrict G A) (body G A B)).hom := by
  rcases B with ⟨parameters, family, name⟩
  let B : NativeType (totalSpace A.decoded) := ⟨parameters, family, name⟩
  apply (Iso.cancel_iso_hom_right _ _ (eqToIso (C := DisplayedFamily ((F ⋙ G).op ⋙ P))
    (sigmaDecode (restrict (F ⋙ G) A) (body (F ⋙ G) A _)))).mp
  have staged := sum_decoder_square F (restrict G A) (body G A B)
  have direct := sumIso_composition F G A B
  rw [Functor.map_comp] at direct
  have paste := direct.trans (congrArg (fun operation =>
    (DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F (G.op ⋙ P)).map
      (sumIso G A B).hom ≫ operation) staged.symm)
  exact paste.trans (Category.assoc (obj := DisplayedFamily ((F ⋙ G).op ⋙ P))
    _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem product_family_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    productMap (F ⋙ G) A B =
      (DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F (G.op ⋙ P)).map
          (productMap G A B) ≫
        productMap F (restrict G A) (body G A B) := by
  rcases B with ⟨parameters, family, name⟩
  let B : NativeType (totalSpace A.decoded) := ⟨parameters, family, name⟩
  apply (Iso.cancel_iso_hom_right _ _
    (piDecodeIso (restrict (F ⋙ G) A) (body (F ⋙ G) A _))).mp
  have staged := product_decoder_square F (restrict G A) (body G A B)
  have direct := productMap_composition F G A B
  rw [Functor.map_comp] at direct
  rw [restriction_cast_hom, Category.id_comp (obj := DisplayedFamily (F.op ⋙ G.op ⋙ P))]
    at staged
  have paste := direct.trans (congrArg (fun operation =>
    (DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F (G.op ⋙ P)).map
      (productMap G A B) ≫ operation) staged.symm)
  convert paste.trans
    (Category.assoc (obj := DisplayedFamily ((F ⋙ G).op ⋙ P)) _ _ _).symm using 1
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sum_display_identity (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    (sumDisplayIso (𝟭 D) A B).hom = 𝟙 (⟨sigma A B⟩ :
      TypeOver (nativeLocalModel D).toCwf P) := by
  change displayHom (sigma A B) (sigma A B) (sumIso (𝟭 D) A B).hom = _
  rw [sum_family_identity]
  exact displayHom_identity (sigma A B)

set_option backward.isDefEq.respectTransparency false in
theorem product_display_identity (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    productDisplayMap (𝟭 D) A B = 𝟙 (⟨pi A B⟩ :
      TypeOver (nativeLocalModel D).toCwf P) := by
  change displayHom (pi A B) (pi A B) (productMap (𝟭 D) A B) = _
  rw [product_family_identity]
  exact displayHom_identity (pi A B)

set_option backward.isDefEq.respectTransparency false in
theorem sum_display_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    (sumDisplayIso (F ⋙ G) A B).hom =
      ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map (sumDisplayIso G A B).hom ≫
        (sumDisplayIso F (restrict G A) (body G A B)).hom := by
  change displayHom _ _ (sumIso (F ⋙ G) A B).hom =
    ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map
      (displayHom _ _ (sumIso G A B).hom) ≫ displayHom _ _ _
  rw [action_displayHom]
  apply TypeOver.Hom.ext
  change totalHom (sumIso (F ⋙ G) A B).hom =
    totalHom ((DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F (G.op ⋙ P)).map
      (sumIso G A B).hom) ≫ totalHom (sumIso F (restrict G A) (body G A B)).hom
  rw [sum_family_composition]
  exact totalHom_composition _ _

set_option backward.isDefEq.respectTransparency false in
theorem product_display_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    productDisplayMap (F ⋙ G) A B =
      ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map (productDisplayMap G A B) ≫
        productDisplayMap F (restrict G A) (body G A B) := by
  change displayHom _ _ (productMap (F ⋙ G) A B) =
    ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map
      (displayHom _ _ (productMap G A B)) ≫ displayHom _ _ _
  rw [action_displayHom]
  apply TypeOver.Hom.ext
  change totalHom (productMap (F ⋙ G) A B) =
    totalHom ((DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F (G.op ⋙ P)).map
      (productMap G A B)) ≫ totalHom (productMap F (restrict G A) (body G A B))
  rw [product_family_composition]
  exact totalHom_composition _ _

/-- The native truth presentation decodes to the genuine sieve family. -/
def nativeTruth (P : Cᵒᵖ ⥤ Type u) : NativeType P :=
  LocalType.present (DisplayedPresheafClassifier.propositions P)

def truthDisplay (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    (⟨restrict F (nativeTruth P)⟩ : TypeOver (nativeLocalModel C).toCwf (F.op ⋙ P)) ⟶
      ⟨nativeTruth (F.op ⋙ P)⟩ :=
  displayHom _ _ (DisplayedPresheafClassifierCoherence.comparison F P)

theorem truth_display_identity (P : Cᵒᵖ ⥤ Type u) :
    truthDisplay (𝟭 C) P = 𝟙 (⟨nativeTruth P⟩ : TypeOver (nativeLocalModel C).toCwf P) := by
  unfold truthDisplay
  rw [DisplayedPresheafClassifierCoherence.comparison_identity]
  exact displayHom_identity (nativeTruth P)

set_option backward.isDefEq.respectTransparency false in
theorem truth_display_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) :
    truthDisplay (F ⋙ G) P =
      ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map (truthDisplay G P) ≫
        truthDisplay F (G.op ⋙ P) := by
  unfold truthDisplay
  rw [action_displayHom, ← displayHom_composition,
    DisplayedPresheafClassifierCoherence.comparison_composition]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The classifier comparison is attached to the same comprehension
comparison used by the actual native contextual action. -/
theorem characteristic_contextual_square (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (predicate : A.decoded ⟶ (nativeTruth P).decoded) :
    DisplayedPresheafClassifier.totalCharacteristic
        ((DisplayedPresheafTheoryRestrictionAction.restrictionFunctor F P).map predicate ≫
          DisplayedPresheafClassifierCoherence.comparison F P) =
      ((localMorphism F).comprehensionIso P A).inv ≫
        Functor.whiskerLeft F.op (DisplayedPresheafClassifier.totalCharacteristic predicate) ≫
          Mettapedia.GSLT.Topos.ClassifierRestriction.comparison F :=
  DisplayedPresheafClassifierCoherence.characteristic_restriction F P A.decoded predicate

end Mettapedia.TypeTheory.PresheafNativeLogicalAction
