import Mettapedia.CategoryTheory.ClosedFunctorNativeReadout

/-!
# Product components of a calibrated closed interpretation square

Independent chosen object readings calibrate the complete comparison on a
product object. Its projections and arbitrary supplied pairs then give the
same canonical native square. Ordinary local arrow readings are transported
through the actual natural isomorphism without choosing new callbacks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ClosedFunctorProductComponentCalibration

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open _root_.CategoryTheory.Limits (PreservesLimitsOfShape WalkingPair)
open RelativeClosedSyntax.Interpretation ClosedFunctorNativeReadout

universe v u₁ u₂ u₃
variable {C : Type u₁} [Category.{v} C] [CartesianMonoidalCategory C]
variable {D : Type u₂} [Category.{v} D] [CartesianMonoidalCategory D]
variable {E : Type u₃} [Category.{v} E] [CartesianMonoidalCategory E]
variable (first : C ⥤ D) (middle : D ⥤ E) (last : C ⥤ E)
variable [PreservesLimitsOfShape (Discrete WalkingPair) first]
variable [PreservesLimitsOfShape (Discrete WalkingPair) middle]
variable [PreservesLimitsOfShape (Discrete WalkingPair) last]
variable (square : first ⋙ middle ≅ last)

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    [PreservesLimitsOfShape (Discrete WalkingPair) first]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [PreservesLimitsOfShape (Discrete WalkingPair) last] in
theorem tensorIso_cast {A B X Y : E} (firstSame : A = X) (secondSame : B = Y) :
    tensorIso (eqToIso firstSame) (eqToIso secondSame) =
      eqToIso (congrArg₂ (fun left right : E => left ⊗ right) firstSame secondSame) := by
  cases firstSame
  cases secondSame
  apply Iso.ext
  exact id_tensorHom_id A B

theorem product_component_calibrated {A B : C} {sourceA sourceB : D} {targetA targetB : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB)
    (sourcePairSame : first.obj (A ⊗ B) = sourceA ⊗ sourceB)
    (targetPairSame : last.obj (A ⊗ B) = targetA ⊗ targetB)
    (sourceCalibrated : prodComparison first A B ≫
      (tensorIso (eqToIso sourceSameA) (eqToIso sourceSameB)).hom = eqToHom sourcePairSame)
    (targetCalibrated : prodComparison last A B ≫
      (tensorIso (eqToIso targetSameA) (eqToIso targetSameB)).hom = eqToHom targetPairSame) :
    objectChange first middle last square (A ⊗ B) (sourceA ⊗ sourceB) (targetA ⊗ targetB)
        sourcePairSame targetPairSame =
      productChange first middle last square sourceSameA sourceSameB targetSameA targetSameB := by
  cases sourceSameA
  cases sourceSameB
  cases targetSameA
  cases targetSameB
  have sourceIso : asIso (prodComparison first A B) = eqToIso sourcePairSame := by
    apply Iso.ext
    change prodComparison first A B = eqToHom sourcePairSame
    have read : prodComparison first A B ≫ 𝟙 (first.obj A ⊗ first.obj B) = eqToHom sourcePairSame := by
      simpa only [eqToIso_refl, tensorIso_hom, Iso.refl_hom, id_tensorHom_id] using sourceCalibrated
    exact (Category.comp_id _).symm.trans read
  have targetIso : asIso (prodComparison last A B) = eqToIso targetPairSame := by
    apply Iso.ext
    change prodComparison last A B = eqToHom targetPairSame
    have read : prodComparison last A B ≫ 𝟙 (last.obj A ⊗ last.obj B) = eqToHom targetPairSame := by
      simpa only [eqToIso_refl, tensorIso_hom, Iso.refl_hom, id_tensorHom_id] using targetCalibrated
    exact (Category.comp_id _).symm.trans read
  unfold objectChange
  rw [← sourceIso, ← targetIso]
  change ClosedFunctorComparisonCalibration.productChange first middle last square A B = _
  apply Iso.ext
  have canonical := ClosedFunctorComparisonCalibration.product_readout first middle last square A B
  simpa only [productChange, objectChange, eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm,
    Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, asIso_hom, tensorIso_hom, Iso.app_hom] using canonical

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [CartesianMonoidalCategory E]
    [PreservesLimitsOfShape (Discrete WalkingPair) first]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [PreservesLimitsOfShape (Discrete WalkingPair) last] in
theorem complete_object_arrow {A X : C} (arrow : A ⟶ X)
    {sourceA sourceX : D} {targetA targetX : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameX : first.obj X = sourceX)
    (targetSameA : last.obj A = targetA) (targetSameX : last.obj X = targetX)
    (sourceArrow : sourceA ⟶ sourceX) (targetArrow : targetA ⟶ targetX)
    (sourceRead : (⟨first.obj A,first.obj X,first.map arrow⟩ : ArrowValue D) =
      ⟨sourceA,sourceX,sourceArrow⟩)
    (targetRead : (⟨last.obj A,last.obj X,last.map arrow⟩ : ArrowValue E) =
      ⟨targetA,targetX,targetArrow⟩) :
    (objectChange first middle last square A sourceA targetA sourceSameA targetSameA).inv ≫
      middle.map sourceArrow ≫
        (objectChange first middle last square X sourceX targetX sourceSameX targetSameX).hom = targetArrow := by
  cases sourceSameA
  cases sourceSameX
  cases targetSameA
  cases targetSameX
  rw [← ArrowValue.arrow_injective sourceRead, ← ArrowValue.arrow_injective targetRead]
  simpa only [objectChange, eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl, Iso.app_inv, Iso.app_hom, Functor.comp_map] using NatIso.naturality_1 square arrow

omit [CartesianMonoidalCategory C] [PreservesLimitsOfShape (Discrete WalkingPair) first]
    [PreservesLimitsOfShape (Discrete WalkingPair) last] in
theorem product_first {A B : C} {sourceA sourceB : D} {targetA targetB : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB) :
    (productChange first middle last square sourceSameA sourceSameB targetSameA targetSameB).hom ≫
      fst targetA targetB = middle.map (fst sourceA sourceB) ≫
        (objectChange first middle last square A sourceA targetA sourceSameA targetSameA).hom := by
  simp only [productChange, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_fst, prodComparison_fst_assoc]

omit [CartesianMonoidalCategory C] [PreservesLimitsOfShape (Discrete WalkingPair) first]
    [PreservesLimitsOfShape (Discrete WalkingPair) last] in
theorem product_second {A B : C} {sourceA sourceB : D} {targetA targetB : E}
    (sourceSameA : first.obj A = sourceA) (sourceSameB : first.obj B = sourceB)
    (targetSameA : last.obj A = targetA) (targetSameB : last.obj B = targetB) :
    (productChange first middle last square sourceSameA sourceSameB targetSameA targetSameB).hom ≫
      snd targetA targetB = middle.map (snd sourceA sourceB) ≫
        (objectChange first middle last square B sourceB targetB sourceSameB targetSameB).hom := by
  simp only [productChange, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_snd, prodComparison_snd_assoc]

end Mettapedia.CategoryTheory.ClosedFunctorProductComponentCalibration
