import Mettapedia.CategoryTheory.ClosedFunctorComparisonCalibration
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationObjects
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationNormalizationReadout

/-!
# Complete native arrow squares from independent constructor readings

Whole local arrow readings at separately chosen object presentations are
transported through an actual closed functor square. The resulting product
and function comparisons are the canonical ones. The supplied readings are
of individual arrows; substitution and function-argument preservation are
earned from the functor square and its universal comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ClosedFunctorNativeReadout

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open _root_.CategoryTheory.Limits (PreservesLimitsOfShape WalkingPair)
open RelativeClosedSyntax.Interpretation

universe v u₁ u₂ u₃
variable {C : Type u₁} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable {D : Type u₂} [Category.{v} D] [CartesianMonoidalCategory D] [MonoidalClosed D]
variable {E : Type u₃} [Category.{v} E] [CartesianMonoidalCategory E] [MonoidalClosed E]
variable (first : C ⥤ D) (middle : D ⥤ E) (last : C ⥤ E)
variable [PreservesLimitsOfShape (Discrete WalkingPair) first]
variable [PreservesLimitsOfShape (Discrete WalkingPair) middle]
variable [PreservesLimitsOfShape (Discrete WalkingPair) last]
variable [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last]
variable (square : first ⋙ middle ≅ last)

omit [CartesianMonoidalCategory C] [MonoidalClosed C]
    [CartesianMonoidalCategory D] [MonoidalClosed D]
    [CartesianMonoidalCategory E] [MonoidalClosed E]
    [PreservesLimitsOfShape (Discrete WalkingPair) first]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [PreservesLimitsOfShape (Discrete WalkingPair) last]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem canonical_source_read {source before target : D} (arrow : source ⟶ target)
    (comparison : source ⟶ before) [IsIso comparison] (same : source = before)
    (calibrated : comparison = eqToHom same) (reading : ArrowValue D)
    (complete : (⟨source,target,arrow⟩ : ArrowValue D) = reading) :
    (⟨before,target,inv comparison ≫ arrow⟩ : ArrowValue D) = reading := by
  have inverse : inv comparison = eqToHom same.symm := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [calibrated, eqToHom_trans, eqToHom_refl]
  rw [inverse]
  exact (ArrowValue.cast_source arrow same).symm.trans complete

def objectChange (A : C) (before : D) (after : E) (sourceSame : first.obj A = before)
    (targetSame : last.obj A = after) : middle.obj before ≅ after :=
  (middle.mapIso (eqToIso sourceSame)).symm ≪≫ square.app A ≪≫ eqToIso targetSame

def productChange {A B : C} {sourceA sourceB : D} {targetA targetB : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB) :
    middle.obj (sourceA ⊗ sourceB) ≅ targetA ⊗ targetB :=
  asIso (CartesianMonoidalCategory.prodComparison middle sourceA sourceB) ≪≫
    tensorIso (objectChange first middle last square A sourceA targetA sourceSameA targetSameA)
      (objectChange first middle last square B sourceB targetB sourceSameB targetSameB)

def functionChange {A B : C} {sourceA sourceB : D} {targetA targetB : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB) :
    middle.obj (sourceA ⟶[D] sourceB) ≅ (targetA ⟶[E] targetB) :=
  asIso ((expComparison middle sourceA).natTrans.app sourceB) ≪≫
    RelativeClosedSyntax.FunctorNormalization.functionIso
      (objectChange first middle last square A sourceA targetA sourceSameA targetSameA)
      (objectChange first middle last square B sourceB targetB sourceSameB targetSameB)

omit [CartesianMonoidalCategory C] [MonoidalClosed C]
    [CartesianMonoidalCategory D] [MonoidalClosed D]
    [PreservesLimitsOfShape (Discrete WalkingPair) first]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [PreservesLimitsOfShape (Discrete WalkingPair) last]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem functionIso_cast {A B X Y : E} (firstSame : A = X) (secondSame : B = Y) :
    RelativeClosedSyntax.FunctorNormalization.functionIso (eqToIso firstSame) (eqToIso secondSame) =
      eqToIso (congrArg₂ (fun input output : E => input ⟶[E] output) firstSame secondSame) := by
  cases firstSame
  cases secondSame
  exact RelativeClosedSyntax.InterpretationNormalization.functionIso_refl A B

set_option backward.isDefEq.respectTransparency false in
theorem function_component_calibrated {A B : C} {sourceA sourceB : D} {targetA targetB : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB)
    (sourceBodySame : first.obj (A ⟶[C] B) = (sourceA ⟶[D] sourceB))
    (targetBodySame : last.obj (A ⟶[C] B) = (targetA ⟶[E] targetB))
    (sourceCalibrated : (expComparison first A).natTrans.app B ≫
      (RelativeClosedSyntax.FunctorNormalization.functionIso
        (eqToIso sourceSameA) (eqToIso sourceSameB)).hom = eqToHom sourceBodySame)
    (targetCalibrated : (expComparison last A).natTrans.app B ≫
      (RelativeClosedSyntax.FunctorNormalization.functionIso
        (eqToIso targetSameA) (eqToIso targetSameB)).hom = eqToHom targetBodySame) :
    objectChange first middle last square (A ⟶[C] B) (sourceA ⟶[D] sourceB) (targetA ⟶[E] targetB)
        sourceBodySame targetBodySame =
      functionChange first middle last square sourceSameA sourceSameB targetSameA targetSameB := by
  cases sourceSameA
  cases sourceSameB
  cases targetSameA
  cases targetSameB
  have sourceIso : asIso ((expComparison first A).natTrans.app B) = eqToIso sourceBodySame := by
    apply Iso.ext
    change (expComparison first A).natTrans.app B = eqToHom sourceBodySame
    have read : (expComparison first A).natTrans.app B ≫
        𝟙 ((ihom (first.obj A)).obj (first.obj B)) = eqToHom sourceBodySame := by
      simpa only [eqToIso_refl, RelativeClosedSyntax.InterpretationNormalization.functionIso_refl,
        Iso.refl_hom] using sourceCalibrated
    exact (Category.comp_id _).symm.trans read
  have targetIso : asIso ((expComparison last A).natTrans.app B) = eqToIso targetBodySame := by
    apply Iso.ext
    change (expComparison last A).natTrans.app B = eqToHom targetBodySame
    have read : (expComparison last A).natTrans.app B ≫
        𝟙 ((ihom (last.obj A)).obj (last.obj B)) = eqToHom targetBodySame := by
      simpa only [eqToIso_refl, RelativeClosedSyntax.InterpretationNormalization.functionIso_refl,
        Iso.refl_hom] using targetCalibrated
    exact (Category.comp_id _).symm.trans read
  unfold objectChange
  rw [← sourceIso, ← targetIso]
  change ClosedFunctorComparisonCalibration.functionChange first middle last square A B = _
  apply Iso.ext
  have canonical := ClosedFunctorComparisonCalibration.function_readout first middle last square A B
  simp only [functionChange, objectChange, eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm,
    Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, asIso_hom,
    RelativeClosedSyntax.FunctorNormalization.functionIso]
  change _ = (expComparison middle (first.obj A)).natTrans.app (first.obj B) ≫
    ((pre (square.inv.app A)).app (middle.obj (first.obj B)) ≫
      (ihom (last.obj A)).map (square.hom.app B))
  simpa only [Category.assoc] using canonical

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem complete_product_arrow {A B X : C} (arrow : A ⊗ B ⟶ X)
    {sourceA sourceB sourceX : D} {targetA targetB targetX : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (sourceSameX : first.obj X = sourceX)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB)
    (targetSameX : last.obj X = targetX)
    (sourceArrow : sourceA ⊗ sourceB ⟶ sourceX) (targetArrow : targetA ⊗ targetB ⟶ targetX)
    (sourceRead : (⟨first.obj A ⊗ first.obj B,first.obj X,
      inv (CartesianMonoidalCategory.prodComparison first A B) ≫ first.map arrow⟩ : ArrowValue D) =
        ⟨sourceA ⊗ sourceB,sourceX,sourceArrow⟩)
    (targetRead : (⟨last.obj A ⊗ last.obj B,last.obj X,
      inv (CartesianMonoidalCategory.prodComparison last A B) ≫ last.map arrow⟩ : ArrowValue E) =
        ⟨targetA ⊗ targetB,targetX,targetArrow⟩) :
    (productChange first middle last square sourceSameA sourceSameB targetSameA targetSameB).inv ≫
      middle.map sourceArrow ≫ (objectChange first middle last square X sourceX targetX
        sourceSameX targetSameX).hom = targetArrow := by
  cases sourceSameA
  cases sourceSameB
  cases sourceSameX
  cases targetSameA
  cases targetSameB
  cases targetSameX
  have firstReading := ArrowValue.arrow_injective sourceRead
  have lastReading := ArrowValue.arrow_injective targetRead
  rw [← firstReading, ← lastReading]
  have canonical := ClosedFunctorComparisonCalibration.product_readout first middle last square A B
  have comparison : productChange first middle last square rfl rfl rfl rfl =
      ClosedFunctorComparisonCalibration.productChange first middle last square A B := by
    apply Iso.ext
    simpa only [productChange, objectChange, eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm,
      Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, asIso_hom, tensorIso_hom, Iso.app_hom] using canonical.symm
  rw [comparison]
  simpa only [objectChange, eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl, Iso.app_hom] using
      ClosedFunctorComparisonCalibration.complete_product_arrow first middle last square arrow

theorem complete_function_arrow {A B X : C} (arrow : (A ⟶[C] B) ⟶ X)
    {sourceA sourceB sourceX : D} {targetA targetB targetX : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (sourceSameX : first.obj X = sourceX)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB)
    (targetSameX : last.obj X = targetX)
    (sourceArrow : (sourceA ⟶[D] sourceB) ⟶ sourceX)
    (targetArrow : (targetA ⟶[E] targetB) ⟶ targetX)
    (sourceRead : (⟨(first.obj A ⟶[D] first.obj B),first.obj X,
      inv ((expComparison first A).natTrans.app B) ≫ first.map arrow⟩ : ArrowValue D) =
        ⟨(sourceA ⟶[D] sourceB),sourceX,sourceArrow⟩)
    (targetRead : (⟨(last.obj A ⟶[E] last.obj B),last.obj X,
      inv ((expComparison last A).natTrans.app B) ≫ last.map arrow⟩ : ArrowValue E) =
        ⟨(targetA ⟶[E] targetB),targetX,targetArrow⟩) :
    (functionChange first middle last square sourceSameA sourceSameB targetSameA targetSameB).inv ≫
      middle.map sourceArrow ≫ (objectChange first middle last square X sourceX targetX
        sourceSameX targetSameX).hom = targetArrow := by
  cases sourceSameA
  cases sourceSameB
  cases sourceSameX
  cases targetSameA
  cases targetSameB
  cases targetSameX
  have firstReading := ArrowValue.arrow_injective sourceRead
  have lastReading := ArrowValue.arrow_injective targetRead
  rw [← firstReading, ← lastReading]
  have canonical := ClosedFunctorComparisonCalibration.function_readout first middle last square A B
  have comparison : functionChange first middle last square rfl rfl rfl rfl =
      ClosedFunctorComparisonCalibration.functionChange first middle last square A B := by
    apply Iso.ext
    simp only [functionChange, objectChange, eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm,
      Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, asIso_hom,
      RelativeClosedSyntax.FunctorNormalization.functionIso]
    change (expComparison middle (first.obj A)).natTrans.app (first.obj B) ≫
        ((pre (square.inv.app A)).app (middle.obj (first.obj B)) ≫
          (ihom (last.obj A)).map (square.hom.app B)) = _
    simpa only [Category.assoc] using canonical.symm
  rw [comparison]
  simpa only [objectChange, eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl, Iso.app_hom] using
      ClosedFunctorComparisonCalibration.complete_function_arrow first middle last square arrow

end Mettapedia.CategoryTheory.ClosedFunctorNativeReadout
