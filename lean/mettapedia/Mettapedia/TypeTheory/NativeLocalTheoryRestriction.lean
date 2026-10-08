import Mettapedia.TypeTheory.ContextualLocalUniversesMorphism
import Mettapedia.TypeTheory.NativeLocalTypeDecoding
import Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherence
import Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionIso
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwf

/-!
# Theory restriction of native local family presentations

The actual local contextual action retains parameter contexts, families,
names and supplied sections. Its dependent codomain is reassociated through
the earned comprehension comparison. Decoding compares the resulting local
sum by an isomorphism and the local product by a colax map. The product map
is invertible only under the existing future-argument coverage condition.

The comparison below applies the chosen native right-Kan product, rather
than defining a second interpretation of dependent functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.NativeLocalTheoryRestriction

open _root_.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafPi NativeLocalTypeFormers ContextualLocalUniverses
open DisplayedPresheafIndexedCwfBridge

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {X : Face.{u, u, u} D}

def restrict (F : C ⥤ D) (A : NativeType X) : NativeType (F.op ⋙ X) where
  parameters := F.op ⋙ A.parameters
  family := restrictFamily F A.parameters A.family
  name := Functor.whiskerLeft F.op A.name

theorem restrict_is_structured_action (F : C ⥤ D) (A : NativeType X) :
    restrict F A = ContextualLocalUniversesMorphism.typeAction
      (DisplayedPresheafTheoryCwf.strictMorphism F) A := rfl

theorem decode_restriction (F : C ⥤ D) (A : NativeType X) :
    (restrict F A).decoded = restrictFamily F X A.decoded :=
  ContextualLocalUniversesMorphism.decoding_square
    (DisplayedPresheafTheoryCwf.strictMorphism F) A

theorem restriction_cast_hom (F : C ⥤ D) (A : NativeType X) :
    (eqToIso (C := DisplayedFamily (F.op ⋙ X)) (decode_restriction F A)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext point
  erw [eqToHom_app]
  rfl

@[simp] theorem restrict_identity (A : NativeType X) : restrict (𝟭 D) A = A := by
  cases A
  rfl

@[simp] theorem restrict_composition {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) {P : Face.{u, u, u} E} (A : NativeType P) :
    restrict (F ⋙ G) A = restrict F (restrict G A) := rfl

def body (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    NativeType (totalSpace (restrict F A).decoded) where
  parameters := F.op ⋙ B.parameters
  family := restrictFamily F B.parameters B.family
  name := (totalComparison F X A.decoded).hom ≫ Functor.whiskerLeft F.op B.name

theorem decode_body (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (body F A B).decoded = (codomainFunctor F X A.decoded).obj B.decoded := rfl

@[simp] theorem body_identity (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) : body (𝟭 D) A B = B := by
  cases B
  rfl

@[simp] theorem body_composition {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) {P : Face.{u, u, u} E} (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    body (F ⋙ G) A B = body F (restrict G A) (body G A B) := by
  cases B
  rfl

/-- The comparison retains both parameter presentations while carrying
the actual decoded dependent pairs. -/
noncomputable def sumIso (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (show DisplayedFamily (F.op ⋙ X) from (restrict F (sigma A B)).decoded) ≅
      (show DisplayedFamily (F.op ⋙ X) from (sigma (restrict F A) (body F A B)).decoded) :=
  eqToIso (C := DisplayedFamily (F.op ⋙ X)) (decode_restriction F (sigma A B)) ≪≫
    (restrictionFunctor F X).mapIso (eqToIso (C := DisplayedFamily X) (sigmaDecode A B)) ≪≫
    sumComparison F X A.decoded B.decoded ≪≫
    (eqToIso (C := DisplayedFamily (F.op ⋙ X))
      (sigmaDecode (restrict F A) (body F A B))).symm

/-- No inverse is postulated for an arbitrary change of theory. -/
noncomputable def productMap (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (show DisplayedFamily (F.op ⋙ X) from (restrict F (pi A B)).decoded) ⟶
      (show DisplayedFamily (F.op ⋙ X) from (pi (restrict F A) (body F A B)).decoded) :=
  (eqToIso (C := DisplayedFamily (F.op ⋙ X)) (decode_restriction F (pi A B))).hom ≫
    (restrictionFunctor F X).map (piDecodeIso A B).hom ≫
    productComparison F X A.decoded B.decoded ≫
    (piDecodeIso (restrict F A) (body F A B)).inv

/-- The local comparison computes the complete native function readout. -/
theorem product_decoder_square (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    productMap F A B ≫ (piDecodeIso (restrict F A) (body F A B)).hom =
      (eqToIso (C := DisplayedFamily (F.op ⋙ X)) (decode_restriction F (pi A B))).hom ≫
        (restrictionFunctor F X).map (piDecodeIso A B).hom ≫
        productComparison F X A.decoded B.decoded := by
  simp only [productMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Equality holds at every admitted future arrow and supplied argument. -/
theorem product_future_readout (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (point future : (F.op ⋙ X).Elements) (arrow : point ⟶ future)
    (function : (restrict F (pi A B)).decoded.obj point)
    (argument : (restrict F A).decoded.obj future) :
    ((((DependentProductNativeComparison.nativeIso (restrictFamily F X A.decoded)).hom.app
        (displayedToTotalElements (restrictFamily F X A.decoded) ⋙
          (codomainFunctor F X A.decoded).obj B.decoded)).app point
      ((piDecodeIso (restrict F A) (body F A B)).hom.app point
        ((productMap F A B).app point function))).app future arrow argument) =
    ((((DependentProductNativeComparison.nativeIso A.decoded).hom.app
        (displayedToTotalElements A.decoded ⋙ B.decoded)).app
      ((Functor.Elements.precomp F.op X).obj point)
      ((piDecodeIso A B).hom.app ((Functor.Elements.precomp F.op X).obj point)
        function)).app ((Functor.Elements.precomp F.op X).obj future)
      ((Functor.Elements.precomp F.op X).map arrow) argument) := by
  have square := congrArg (fun operation :
    (show DisplayedFamily (F.op ⋙ X) from (restrict F (pi A B)).decoded) ⟶
      piDisplayed (restrictFamily F X A.decoded) ((codomainFunctor F X A.decoded).obj B.decoded) =>
    operation.app point function) (product_decoder_square F A B)
  change (piDecodeIso (restrict F A) (body F A B)).hom.app point
      ((productMap F A B).app point function) =
    (productComparison F X A.decoded B.decoded).app point
      ((piDecodeIso A B).hom.app ((Functor.Elements.precomp F.op X).obj point) function)
      at square
  rw [square]
  exact DisplayedPresheafLogicalActionCoherence.productComparison_readout F X A.decoded
    B.decoded point future arrow _ argument

noncomputable def productIso (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp F.op X) A.decoded point).Initial] :
    (show DisplayedFamily (F.op ⋙ X) from (restrict F (pi A B)).decoded) ≅
      (show DisplayedFamily (F.op ⋙ X) from (pi (restrict F A) (body F A B)).decoded) :=
  eqToIso (C := DisplayedFamily (F.op ⋙ X)) (decode_restriction F (pi A B)) ≪≫
    (restrictionFunctor F X).mapIso (piDecodeIso A B) ≪≫
    DependentProductNativeComparison.nativeRestrictionIso
      (Functor.Elements.precomp F.op X) A.decoded (displayedToTotalElements A.decoded ⋙ B.decoded) ≪≫
    (CategoryOfElements.π (restrictFamily F X A.decoded)).ran.mapIso
      (codomainComparison F X A.decoded B.decoded) ≪≫
    (piDecodeIso (restrict F A) (body F A B)).symm

theorem productIso_hom (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp F.op X) A.decoded point).Initial] :
    (productIso F A B).hom = productMap F A B := by
  simp only [productIso, productMap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    DependentProductNativeComparison.nativeRestrictionIso_hom, productComparison,
    Category.assoc]

/-- An equivalence of theories supplies future coverage; it need not be
the identity on worlds, types or evidence. -/
noncomputable def productEquivalence (F : C ⥤ D) [F.IsEquivalence]
    (A : NativeType X) (B : NativeType (totalSpace A.decoded)) :
    (show DisplayedFamily (F.op ⋙ X) from (restrict F (pi A B)).decoded) ≅
      (show DisplayedFamily (F.op ⋙ X) from (pi (restrict F A) (body F A B)).decoded) :=
  eqToIso (C := DisplayedFamily (F.op ⋙ X)) (decode_restriction F (pi A B)) ≪≫
    (restrictionFunctor F X).mapIso (piDecodeIso A B) ≪≫
    DisplayedPresheafTheoryRestrictionIso.productIso F X A.decoded B.decoded ≪≫
    (piDecodeIso (restrict F A) (body F A B)).symm

theorem productEquivalence_hom (F : C ⥤ D) [F.IsEquivalence]
    (A : NativeType X) (B : NativeType (totalSpace A.decoded)) :
    (productEquivalence F A B).hom = productMap F A B := by
  simp only [productEquivalence, productMap, Iso.trans_hom, Functor.mapIso_hom,
    DisplayedPresheafTheoryRestrictionIso.productIso_hom, Iso.symm_hom]

/-- Identity coherence is stated through the canonical decoding maps,
without identifying distinct external presentations by fiat. -/
theorem productMap_identity (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    productMap (𝟭 D) A B ≫ (piDecodeIso (restrict (𝟭 D) A) (body (𝟭 D) A B)).hom =
      (restrictionFunctor (𝟭 D) X).map (piDecodeIso A B).hom := by
  rw [product_decoder_square, restriction_cast_hom,
    DisplayedPresheafLogicalActionCoherence.productComparison_identity]
  exact (Category.id_comp _).trans (Category.comp_id _)

theorem sum_decoder_square (F : C ⥤ D) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (sumIso F A B).hom ≫ (eqToIso (C := DisplayedFamily (F.op ⋙ X))
      (sigmaDecode (restrict F A) (body F A B))).hom =
      (restrictionFunctor F X).map (eqToIso (C := DisplayedFamily X) (sigmaDecode A B)).hom ≫
        (sumComparison F X A.decoded B.decoded).hom := by
  simp only [sumIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Functor.mapIso_hom, restriction_cast_hom, Category.id_comp]

theorem sumIso_identity (A : NativeType X) (B : NativeType (totalSpace A.decoded)) :
    (sumIso (𝟭 D) A B).hom ≫ (eqToIso (C := DisplayedFamily X)
      (sigmaDecode (restrict (𝟭 D) A) (body (𝟭 D) A B))).hom =
      (restrictionFunctor (𝟭 D) X).map (eqToIso (C := DisplayedFamily X) (sigmaDecode A B)).hom := by
  rw [sum_decoder_square]
  have identity : (sumComparison (𝟭 D) X A.decoded B.decoded).hom = 𝟙 _ := by
    apply NatTrans.ext
    funext point
    rfl
  rw [identity]
  exact Category.comp_id (obj := DisplayedFamily X)
    ((restrictionFunctor (𝟭 D) X).map (eqToIso (C := DisplayedFamily X) (sigmaDecode A B)).hom)

variable {E : Type u} [Category.{u} E]

private theorem sum_composition_after_readout (F : C ⥤ D) (G : D ⥤ E)
    (P : Face.{u, u, u} E) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) (H : DisplayedFamily P)
    (readout : H ⟶ DisplayedPresheafSigma.sigmaDisplayed A B) :
    (restrictionFunctor (F ⋙ G) P).map readout ≫ (sumComparison (F ⋙ G) P A B).hom =
      (restrictionFunctor F (G.op ⋙ P)).map
        ((restrictionFunctor G P).map readout ≫ (sumComparison G P A B).hom) ≫
          (sumComparison F (G.op ⋙ P) (restrictFamily G P A)
            ((codomainFunctor G P A).obj B)).hom := by
  rw [Functor.map_comp, DisplayedPresheafLogicalActionCoherence.sumComparison_composition]
  exact (Category.assoc (obj := DisplayedFamily ((F ⋙ G).op ⋙ P))
    ((restrictionFunctor F (G.op ⋙ P)).map ((restrictionFunctor G P).map readout))
    ((restrictionFunctor F (G.op ⋙ P)).map (sumComparison G P A B).hom)
    (sumComparison F (G.op ⋙ P) (restrictFamily G P A)
      ((codomainFunctor G P A).obj B)).hom).symm

theorem productMap_composition (F : C ⥤ D) (G : D ⥤ E)
    {P : Face.{u, u, u} E} (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    productMap (F ⋙ G) A B ≫
        (piDecodeIso (restrict (F ⋙ G) A) (body (F ⋙ G) A B)).hom =
      (restrictionFunctor F (G.op ⋙ P)).map
        (productMap G A B ≫ (piDecodeIso (restrict G A) (body G A B)).hom) ≫
          productComparison F (G.op ⋙ P) (restrictFamily G P A.decoded)
            ((codomainFunctor G P A.decoded).obj B.decoded) := by
  rw [product_decoder_square, product_decoder_square]
  simp only [restriction_cast_hom, Category.id_comp, Functor.map_comp]
  have composition := congrArg (fun operation => operation.app B.decoded)
    (DisplayedPresheafLogicalActionCoherence.productMap_composition F G P A.decoded)
  change productComparison (F ⋙ G) P A.decoded B.decoded =
    (restrictionFunctor F (G.op ⋙ P)).map (productComparison G P A.decoded B.decoded) ≫
      productComparison F (G.op ⋙ P) (restrictFamily G P A.decoded)
        ((codomainFunctor G P A.decoded).obj B.decoded) at composition
  rw [composition]
  exact (Category.assoc (obj := DisplayedFamily ((F ⋙ G).op ⋙ P))
    ((restrictionFunctor F (G.op ⋙ P)).map
      ((restrictionFunctor G P).map (piDecodeIso A B).hom))
    ((restrictionFunctor F (G.op ⋙ P)).map (productComparison G P A.decoded B.decoded))
    (productComparison F (G.op ⋙ P) (restrictFamily G P A.decoded)
      ((codomainFunctor G P A.decoded).obj B.decoded))).symm

attribute [local irreducible] NativeLocalTypeFormers.sigma

set_option backward.isDefEq.respectTransparency true in
theorem sumIso_composition (F : C ⥤ D) (G : D ⥤ E)
    {P : Face.{u, u, u} E} (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    (sumIso (F ⋙ G) A B).hom ≫ (eqToIso (C := DisplayedFamily ((F ⋙ G).op ⋙ P))
        (sigmaDecode (restrict (F ⋙ G) A) (body (F ⋙ G) A B))).hom =
      (restrictionFunctor F (G.op ⋙ P)).map
        ((sumIso G A B).hom ≫ (eqToIso (C := DisplayedFamily (G.op ⋙ P))
          (sigmaDecode (restrict G A) (body G A B))).hom) ≫
            (sumComparison F (G.op ⋙ P) (restrictFamily G P A.decoded)
              ((codomainFunctor G P A.decoded).obj B.decoded)).hom := by
  have stages := sum_composition_after_readout F G P A.decoded B.decoded
    (show DisplayedFamily P from (sigma A B).decoded)
    (eqToIso (C := DisplayedFamily P) (sigmaDecode A B)).hom
  have first := sum_decoder_square (F ⋙ G) A B
  have second := sum_decoder_square G A B
  refine first.trans (stages.trans ?_)
  exact congrArg (fun operation :
    (show DisplayedFamily (G.op ⋙ P) from (restrict G (sigma A B)).decoded) ⟶
      DisplayedPresheafSigma.sigmaDisplayed (restrict G A).decoded (body G A B).decoded =>
    (restrictionFunctor F (G.op ⋙ P)).map operation ≫
      (sumComparison F (G.op ⋙ P) (restrictFamily G P A.decoded)
        ((codomainFunctor G P A.decoded).obj B.decoded)).hom) second.symm

end Mettapedia.TypeTheory.NativeLocalTheoryRestriction
