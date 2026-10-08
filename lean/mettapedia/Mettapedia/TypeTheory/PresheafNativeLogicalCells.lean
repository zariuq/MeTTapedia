import Mettapedia.TypeTheory.PresheafNativeLogicalAction

/-!
# Logical comparisons and the actual native theory cells

Dependent-pair transport changes both supplied witnesses, with the second
witness following the actual changed argument. The comparison with the
native external presentation is an isomorphism of complete total contexts.
These maps agree with the corrected contextual theory cell before and after
rebuilding the dependent sum. All identity and composition laws retain the
supplied program point and evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeLogicalCells

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf DisplayedPresheafSliceSubstitution
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation DisplayedPresheafTheoryTransformationCoherence
open ContextualLocalUniverses NativeLocalTypeFormers
open NativeLocalTheoryRestriction NativeLocalTheoryTransformation NativeLocalDisplayComparisons
open PresheafNativeLogicalAction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G H : C ⥤ D}

private theorem conjugated_identity {K : Type*} [Category K] {X Y : K}
    (decoder : X ≅ Y) : decoder.hom ≫ 𝟙 Y ≫ decoder.inv = 𝟙 X := by
  rw [Category.id_comp, Iso.hom_inv_id]

private theorem conjugated_composition {K : Type*} [Category K]
    {X Y Z A B E : K} (first : X ≅ A) (middle : Y ≅ B) (last : Z ≅ E)
    (f : A ⟶ B) (g : B ⟶ E) :
    first.hom ≫ (f ≫ g) ≫ last.inv =
      (first.hom ≫ f ≫ middle.inv) ≫ (middle.hom ≫ g ≫ last.inv) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem conjugated_readout {K : Type*} [Category K]
    {X Y A B : K} (incoming : X ≅ A) (outgoing : Y ≅ B) (operation : A ⟶ B) :
    (incoming.hom ≫ operation ≫ outgoing.inv) ≫ outgoing.hom =
      incoming.hom ≫ operation := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem comparison_paste {K : Type*} [Category K]
    {X Y A B S T V W : K}
    (incoming : S ≅ V) (outgoing : T ≅ W)
    (source : X ⟶ A) (target : Y ⟶ B)
    (nativeSource : X ⟶ S) (nativeTarget : Y ⟶ T)
    (decodedSource : A ⟶ V) (decodedTarget : B ⟶ W)
    (nativeCell : X ⟶ Y) (decodedCell : A ⟶ B) (rebuiltCell : V ⟶ W)
    (sourceSquare : nativeSource ≫ incoming.hom = source ≫ decodedSource)
    (targetSquare : nativeTarget ≫ outgoing.hom = target ≫ decodedTarget)
    (naturalSquare : source ≫ decodedCell = nativeCell ≫ target)
    (logicalSquare : decodedSource ≫ rebuiltCell = decodedCell ≫ decodedTarget) :
    nativeSource ≫ (incoming.hom ≫ rebuiltCell ≫ outgoing.inv) =
      nativeCell ≫ nativeTarget := by
  apply (Iso.cancel_iso_hom_right _ _ outgoing).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, sourceSquare, Category.assoc, logicalSquare,
    ← Category.assoc, naturalSquare, Category.assoc, ← targetSquare]

local instance nativeDisplayCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (localCwf (presheafCwf.{u, u, u} C)) P) :=
  TypeOver.instCategory (C := localCwf (presheafCwf.{u, u, u} C)) (Γ := P)

attribute [local irreducible] NativeLocalTypeFormers.sigma NativeLocalTypeFormers.pi

def completeCell (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) (A : NativeType P) :
    totalSpace (restrict G A).decoded ⟶ totalSpace (restrict F A).decoded :=
  ((correctedTransformation change).family P ⟨A⟩).substitution ≫
    TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf)
      (baseMap change P) ((localMorphism F).mapType A)

/-- The whole native family cell is the independently constructed
dependent evidence map, including its base-context substitution. -/
theorem completeCell_decodes (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) :
    completeCell change P A = totalEvidenceMap change P A.decoded := rfl

noncomputable def sumDecoderTotal (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    totalSpace (sigma A B).decoded ≅
      totalSpace (DisplayedPresheafSigma.sigmaDisplayed A.decoded B.decoded) :=
  (comprehensionTotals P).mapIso (eqToIso (C := DisplayedFamily P) (sigmaDecode A B))

noncomputable def sumCell (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded)) :
    totalSpace (sigma (restrict G A) (body G A B)).decoded ⟶
      totalSpace (sigma (restrict F A) (body F A B)).decoded :=
  (sumDecoderTotal (G.op ⋙ P) (restrict G A) (body G A B)).hom ≫
    DisplayedPresheafSumTransformationCoherence.sumTotalMap change P A.decoded B.decoded ≫
      (sumDecoderTotal (F.op ⋙ P) (restrict F A) (body F A B)).inv

set_option backward.isDefEq.respectTransparency true in
/-- The independent dependent-pair transport is the exact readout of
the native complete cell, including the second argument's dependency. -/
theorem sum_cell_decoder (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded)) :
    sumCell change P A B ≫
        (sumDecoderTotal (F.op ⋙ P) (restrict F A) (body F A B)).hom =
      (sumDecoderTotal (G.op ⋙ P) (restrict G A) (body G A B)).hom ≫
        DisplayedPresheafSumTransformationCoherence.sumTotalMap change P A.decoded B.decoded :=
  conjugated_readout _ _ _

set_option backward.isDefEq.respectTransparency true in
theorem sum_decoder_total_square (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded)) :
    (sumDisplayIso route A B).hom.substitution ≫
        (sumDecoderTotal (route.op ⋙ P) (restrict route A) (body route A B)).hom =
      totalHom ((restrictionFunctor route P).map
          (eqToIso (C := DisplayedFamily P) (sigmaDecode A B)).hom) ≫
        totalHom (sumComparison route P A.decoded B.decoded).hom := by
  change totalHom (sumIso route A B).hom ≫ totalHom _ = _
  exact (totalHom_composition _ _).symm.trans
    ((congrArg totalHom (sum_decoder_square route A B)).trans (totalHom_composition _ _))

set_option backward.isDefEq.respectTransparency true in
/-- Rebuilding a native dependent sum commutes with its actual corrected
theory cell on complete program-and-pair receipts. -/
theorem sum_cell_square (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded)) :
    (sumDisplayIso G A B).hom.substitution ≫ sumCell change P A B =
      completeCell change P (sigma A B) ≫ (sumDisplayIso F A B).hom.substitution := by
  exact comparison_paste _ _ _ _ _ _ _ _ _ _ _
    (sum_decoder_total_square G P A B) (sum_decoder_total_square F P A B)
    (totalEvidenceMap_naturality change P
      (eqToIso (C := DisplayedFamily P) (sigmaDecode A B)).hom)
    (DisplayedPresheafSumTransformationCoherence.sumTotalMap_square change P A.decoded B.decoded)

set_option backward.isDefEq.respectTransparency true in
theorem sum_cell_identity (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded)) :
    sumCell (𝟙 F) P A B = 𝟙 _ := by
  let decoder := sumDecoderTotal (F.op ⋙ P) (restrict F A) (body F A B)
  exact (congrArg (fun operation => decoder.hom ≫ operation ≫ decoder.inv)
    (DisplayedPresheafSumTransformationCoherence.sumTotalMap_identity F P A.decoded B.decoded)).trans
      (conjugated_identity decoder)

set_option backward.isDefEq.respectTransparency true in
theorem sum_cell_composition (first : F ⟶ G) (second : G ⟶ H)
    (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    sumCell (first ≫ second) P A B = sumCell second P A B ≫ sumCell first P A B := by
  let incoming := sumDecoderTotal (H.op ⋙ P) (restrict H A) (body H A B)
  let middle := sumDecoderTotal (G.op ⋙ P) (restrict G A) (body G A B)
  let outgoing := sumDecoderTotal (F.op ⋙ P) (restrict F A) (body F A B)
  exact (congrArg (fun operation => incoming.hom ≫ operation ≫ outgoing.inv)
    (DisplayedPresheafSumTransformationCoherence.sumTotalMap_composition
      first second P A.decoded B.decoded)).trans
        (conjugated_composition incoming middle outgoing _ _)

noncomputable def productDecoderTotal (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) :
    totalSpace (pi A B).decoded ≅
      totalSpace (DisplayedPresheafPi.piDisplayed A.decoded B.decoded) :=
  (comprehensionTotals P).mapIso (piDecodeIso A B)

/-- Incoming coverage reconstructs the source function. The outgoing
route retains its canonical colax comparison and needs no inverse. -/
noncomputable def productCell (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A.decoded point).Initial] :
    totalSpace (pi (restrict G A) (body G A B)).decoded ⟶
      totalSpace (pi (restrict F A) (body F A B)).decoded :=
  (productDecoderTotal (G.op ⋙ P) (restrict G A) (body G A B)).hom ≫
    (DisplayedPresheafProductTransformationCoherence.coveredProductTotalTransformation
      change P A.decoded).app B.decoded ≫
        (productDecoderTotal (F.op ⋙ P) (restrict F A) (body F A B)).inv

set_option backward.isDefEq.respectTransparency true in
theorem product_decoder_total_square (route : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded)) :
    (productDisplayMap route A B).substitution ≫
        (productDecoderTotal (route.op ⋙ P) (restrict route A) (body route A B)).hom =
      totalHom ((restrictionFunctor route P).map (piDecodeIso A B).hom) ≫
        totalHom (productComparison route P A.decoded B.decoded) := by
  have square := product_decoder_square route A B
  rw [restriction_cast_hom] at square
  have identity := Category.id_comp (obj := DisplayedFamily (route.op ⋙ P))
    ((restrictionFunctor route P).map (piDecodeIso A B).hom ≫
      productComparison route P A.decoded B.decoded)
  exact (totalHom_composition _ _).symm.trans
    ((congrArg totalHom (square.trans identity)).trans (totalHom_composition _ _))

set_option backward.isDefEq.respectTransparency true in
theorem product_cell_square (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A.decoded point).Initial] :
    (productDisplayMap G A B).substitution ≫ productCell change P A B =
      completeCell change P (pi A B) ≫ (productDisplayMap F A B).substitution := by
  have square := congrArg (fun operation => operation.app B.decoded)
    (DisplayedPresheafProductTransformationCoherence.coveredProductTotalTransformation_square
      change P A.decoded)
  exact comparison_paste _ _ _ _ _ _ _ _ _ _ _
    (product_decoder_total_square G P A B) (product_decoder_total_square F P A B)
    (totalEvidenceMap_naturality change P (piDecodeIso A B).hom) square

set_option backward.isDefEq.respectTransparency true in
theorem product_cell_identity (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : NativeType P) (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp F.op P) A.decoded point).Initial] :
    productCell (𝟙 F) P A B = 𝟙 _ := by
  let decoder := productDecoderTotal (F.op ⋙ P) (restrict F A) (body F A B)
  have identity := congrArg (fun operation :
      DisplayedPresheafProductTransformationCoherence.nativeProductTotals F P A.decoded ⟶
        DisplayedPresheafProductTransformationCoherence.nativeProductTotals F P A.decoded =>
      operation.app B.decoded)
    (DisplayedPresheafProductTransformationCoherence.coveredProductTotalTransformation_identity
      P A.decoded (F := F))
  exact (congrArg (fun operation => decoder.hom ≫ operation ≫ decoder.inv) identity).trans
    (conjugated_identity decoder)

set_option backward.isDefEq.respectTransparency true in
theorem product_cell_composition (first : F ⟶ G) (second : G ⟶ H)
    (P : Dᵒᵖ ⥤ Type u) (A : NativeType P)
    (B : NativeType (totalSpace A.decoded))
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp G.op P) A.decoded point).Initial]
    [∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp H.op P) A.decoded point).Initial] :
    productCell (first ≫ second) P A B =
      productCell second P A B ≫ productCell first P A B := by
  let incoming := productDecoderTotal (H.op ⋙ P) (restrict H A) (body H A B)
  let middle := productDecoderTotal (G.op ⋙ P) (restrict G A) (body G A B)
  let outgoing := productDecoderTotal (F.op ⋙ P) (restrict F A) (body F A B)
  have composition := congrArg (fun operation :
      DisplayedPresheafProductTransformationCoherence.nativeProductTotals H P A.decoded ⟶
        DisplayedPresheafProductTransformationCoherence.nativeProductTotals F P A.decoded =>
      operation.app B.decoded)
    (DisplayedPresheafProductTransformationCoherence.coveredProductTotalTransformation_composition
      first second P A.decoded)
  exact (congrArg (fun operation => incoming.hom ≫ operation ≫ outgoing.inv) composition).trans
    (conjugated_composition incoming middle outgoing _ _)

/-- Truth comparison is lax for an actual noninvertible theory cell,
measured on the native complete comprehension receipt's sieve coordinate. -/
theorem truth_cell_lax (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) (world : Cᵒᵖ)
    (receipt : (totalSpace (restrict G (nativeTruth P)).decoded).obj world) :
    @LE.le (Sieve world.unop) inferInstance
      ((truthDisplay G P).substitution.app world receipt).2
      ((truthDisplay F P).substitution.app world
        ((completeCell change P (nativeTruth P)).app world receipt)).2 :=
  DisplayedPresheafClassifierCoherence.transformation_le change P
    ⟨world, receipt.1⟩ receipt.2

end Mettapedia.TypeTheory.PresheafNativeLogicalCells
