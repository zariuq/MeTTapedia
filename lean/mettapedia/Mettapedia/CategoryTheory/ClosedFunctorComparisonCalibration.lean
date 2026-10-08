import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence
import Mathlib.CategoryTheory.Whiskering

/-!
# Native product and function comparisons recovered from a whole functor square

An actual natural isomorphism between a composite closed functor and a
second closed functor determines the comparisons on products and complete
function objects. Conjugating by the first and second functors' canonical
comparisons gives exactly the middle functor's canonical comparison, with
both endpoint changes retained. No chosen-object preservation is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ClosedFunctorComparisonCalibration

open _root_.CategoryTheory MonoidalCategory
open _root_.CategoryTheory.Limits (PreservesLimitsOfShape WalkingPair)
open CartesianMonoidalCategory MonoidalClosed

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

def productChange (A B : C) : middle.obj (first.obj A ⊗ first.obj B) ≅ last.obj A ⊗ last.obj B :=
  (middle.mapIso (asIso (CartesianMonoidalCategory.prodComparison first A B))).symm ≪≫
    square.app (A ⊗ B) ≪≫ asIso (CartesianMonoidalCategory.prodComparison last A B)

def functionChange (A B : C) : middle.obj (first.obj A ⟶[D] first.obj B) ≅
    (last.obj A ⟶[E] last.obj B) :=
  (middle.mapIso (asIso ((expComparison first A).natTrans.app B))).symm ≪≫
    square.app (A ⟶[C] B) ≪≫ asIso ((expComparison last A).natTrans.app B)

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem product_readout (A B : C) : (productChange first middle last square A B).hom =
    CartesianMonoidalCategory.prodComparison middle (first.obj A) (first.obj B) ≫
      (square.hom.app A ⊗ₘ square.hom.app B) := by
  have actual := CartesianClosedFunctorCoherence.product_naturalIso square A B
  rw [prodComparison_comp] at actual
  apply (cancel_epi (middle.map (CartesianMonoidalCategory.prodComparison first A B))).mp
  change middle.map (CartesianMonoidalCategory.prodComparison first A B) ≫
      (middle.map (inv (CartesianMonoidalCategory.prodComparison first A B)) ≫
        square.hom.app (A ⊗ B) ≫ CartesianMonoidalCategory.prodComparison last A B) = _
  simp only [← Category.assoc, ← middle.map_comp, IsIso.hom_inv_id, middle.map_id, Category.id_comp]
  simpa only [Category.assoc] using actual.symm

omit [MonoidalClosedFunctor middle] in
theorem function_readout (A B : C) : (functionChange first middle last square A B).hom =
    (expComparison middle (first.obj A)).natTrans.app (first.obj B) ≫
      (pre (square.inv.app A)).app (middle.obj (first.obj B)) ≫
        (ihom (last.obj A)).map (square.hom.app B) := by
  have actual := CartesianClosedFunctorCoherence.exponential_naturalIso square A B
  rw [CartesianClosedFunctorCoherence.exponential_composition] at actual
  apply (cancel_epi (middle.map ((expComparison first A).natTrans.app B))).mp
  change middle.map ((expComparison first A).natTrans.app B) ≫
      (middle.map (inv ((expComparison first A).natTrans.app B)) ≫
        square.hom.app (A ⟶[C] B) ≫ (expComparison last A).natTrans.app B) = _
  simp only [← Category.assoc, ← middle.map_comp, IsIso.hom_inv_id, middle.map_id, Category.id_comp]
  simpa only [Category.assoc, Functor.comp_obj] using actual.symm

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem product_first (A B : C) : (productChange first middle last square A B).hom ≫
    fst (last.obj A) (last.obj B) =
      middle.map (fst (first.obj A) (first.obj B)) ≫ square.hom.app A := by
  rw [product_readout]
  simp only [Category.assoc, tensorHom_fst, prodComparison_fst_assoc]

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem product_second (A B : C) : (productChange first middle last square A B).hom ≫
    snd (last.obj A) (last.obj B) =
      middle.map (snd (first.obj A) (first.obj B)) ≫ square.hom.app B := by
  rw [product_readout]
  simp only [Category.assoc, tensorHom_snd, prodComparison_snd_assoc]

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem product_supplied {Z : D} (A B : C) (left : Z ⟶ first.obj A) (right : Z ⟶ first.obj B) :
    middle.map (lift left right) ≫ (productChange first middle last square A B).hom =
      lift (middle.map left ≫ square.hom.app A) (middle.map right ≫ square.hom.app B) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, product_first, ← Category.assoc, ← middle.map_comp, lift_fst, lift_fst]
  · rw [Category.assoc, product_second, ← Category.assoc, ← middle.map_comp, lift_snd, lift_snd]

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
    [PreservesLimitsOfShape (Discrete WalkingPair) middle]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor middle] [MonoidalClosedFunctor last] in
theorem complete_product_arrow {A B X : C} (arrow : A ⊗ B ⟶ X) :
    (productChange first middle last square A B).inv ≫
      middle.map (inv (CartesianMonoidalCategory.prodComparison first A B) ≫ first.map arrow) ≫
        square.hom.app X =
      inv (CartesianMonoidalCategory.prodComparison last A B) ≫ last.map arrow := by
  simp only [productChange, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, asIso_hom,
    asIso_inv, Iso.app_inv]
  simp only [middle.map_comp, Category.assoc]
  rw [← middle.map_comp_assoc, IsIso.hom_inv_id, middle.map_id, Category.id_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun value => inv (CartesianMonoidalCategory.prodComparison last A B) ≫ value)
      (NatIso.naturality_1 square arrow)

omit [PreservesLimitsOfShape (Discrete WalkingPair) middle] [MonoidalClosedFunctor middle] in
theorem complete_function_arrow {A B X : C} (arrow : (A ⟶[C] B) ⟶ X) :
    (functionChange first middle last square A B).inv ≫
      middle.map (inv ((expComparison first A).natTrans.app B) ≫ first.map arrow) ≫
        square.hom.app X =
      inv ((expComparison last A).natTrans.app B) ≫ last.map arrow := by
  simp only [functionChange, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, asIso_hom,
    asIso_inv, Iso.app_inv]
  simp only [middle.map_comp, Category.assoc]
  rw [← middle.map_comp_assoc, IsIso.hom_inv_id, middle.map_id, Category.id_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun value => inv ((expComparison last A).natTrans.app B) ≫ value)
      (NatIso.naturality_1 square arrow)

end Mettapedia.CategoryTheory.ClosedFunctorComparisonCalibration
