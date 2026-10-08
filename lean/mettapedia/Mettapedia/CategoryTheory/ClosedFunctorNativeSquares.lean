import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationObjects

/-!
# Complete product and function squares through a closed functor

Canonical product and exponential comparisons transport independently
chosen object isomorphisms. Product projections, arbitrary pairs and the
entire postcomposition function action commute. The latter uses naturality
of both the exponential comparison and contravariant argument change.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ClosedFunctorNativeSquares

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open _root_.CategoryTheory.Limits (PreservesLimitsOfShape WalkingPair)

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable {D : Type u₂} [Category.{v} D] [CartesianMonoidalCategory D] [MonoidalClosed D]
variable (mapping : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) mapping]
variable [MonoidalClosedFunctor mapping]

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosedFunctor mapping] in
def product {A B : C} {X Y : D} (first : mapping.obj A ≅ X) (second : mapping.obj B ≅ Y) :
    mapping.obj (A ⊗ B) ≅ X ⊗ Y :=
  asIso (prodComparison mapping A B) ≪≫ tensorIso first second

def function {A B : C} {X Y : D} (argument : mapping.obj A ≅ X) (result : mapping.obj B ≅ Y) :
    mapping.obj (A ⟶[C] B) ≅ (X ⟶[D] Y) :=
  asIso ((expComparison mapping A).natTrans.app B) ≪≫
    RelativeClosedSyntax.FunctorNormalization.functionIso argument result

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosedFunctor mapping] in
theorem product_first {A B : C} {X Y : D} (first : mapping.obj A ≅ X) (second : mapping.obj B ≅ Y) :
    (product mapping first second).hom ≫ fst X Y = mapping.map (fst A B) ≫ first.hom := by
  simp only [product, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_fst, prodComparison_fst_assoc]

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosedFunctor mapping] in
theorem product_second {A B : C} {X Y : D} (first : mapping.obj A ≅ X) (second : mapping.obj B ≅ Y) :
    (product mapping first second).hom ≫ snd X Y = mapping.map (snd A B) ≫ second.hom := by
  simp only [product, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_snd, prodComparison_snd_assoc]

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosedFunctor mapping] in
theorem product_supplied {A B Z : C} {X Y : D}
    (first : mapping.obj A ≅ X) (second : mapping.obj B ≅ Y)
    (left : Z ⟶ A) (right : Z ⟶ B) :
    mapping.map (lift left right) ≫ (product mapping first second).hom =
      lift (mapping.map left ≫ first.hom) (mapping.map right ≫ second.hom) := by
  apply hom_ext
  · rw [Category.assoc, product_first, ← Category.assoc, ← mapping.map_comp, lift_fst, lift_fst]
  · rw [Category.assoc, product_second, ← Category.assoc, ← mapping.map_comp, lift_snd, lift_snd]

omit [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosedFunctor mapping] in
theorem product_arrow_square {A B E F : C} {X Y Z W : D}
    (first : mapping.obj A ≅ X) (second : mapping.obj B ≅ Y)
    (nextFirst : mapping.obj E ≅ Z) (nextSecond : mapping.obj F ≅ W)
    (left : A ⟶ E) (right : B ⟶ F) (targetLeft : X ⟶ Z) (targetRight : Y ⟶ W)
    (leftSquare : mapping.map left ≫ nextFirst.hom = first.hom ≫ targetLeft)
    (rightSquare : mapping.map right ≫ nextSecond.hom = second.hom ≫ targetRight) :
    mapping.map (lift (fst A B ≫ left) (snd A B ≫ right)) ≫
      (product mapping nextFirst nextSecond).hom =
        (product mapping first second).hom ≫ lift (fst X Y ≫ targetLeft) (snd X Y ≫ targetRight) := by
  rw [product_supplied]
  apply hom_ext
  · simp only [Category.assoc, lift_fst]
    rw [mapping.map_comp, Category.assoc, leftSquare]
    simpa only [Category.assoc] using
      congrArg (fun value => value ≫ targetLeft) (product_first mapping first second).symm
  · simp only [Category.assoc, lift_snd]
    rw [mapping.map_comp, Category.assoc, rightSquare]
    simpa only [Category.assoc] using
      congrArg (fun value => value ≫ targetRight) (product_second mapping first second).symm

theorem function_postcomposition {A B E : C} {X Y Z : D}
    (argument : mapping.obj A ≅ X) (before : mapping.obj B ≅ Y) (after : mapping.obj E ≅ Z)
    (sourceArrow : B ⟶ E) (targetArrow : Y ⟶ Z)
    (localSquare : mapping.map sourceArrow ≫ after.hom = before.hom ≫ targetArrow) :
    mapping.map ((ihom A).map sourceArrow) ≫ (function mapping argument after).hom =
      (function mapping argument before).hom ≫ (ihom X).map targetArrow := by
  have exponent := ((expComparison mapping A).natTrans).naturality sourceArrow
  change mapping.map ((ihom A).map sourceArrow) ≫ (expComparison mapping A).natTrans.app E =
    (expComparison mapping A).natTrans.app B ≫ (ihom (mapping.obj A)).map (mapping.map sourceArrow) at exponent
  have changeArgument := (pre argument.inv).naturality (mapping.map sourceArrow)
  change (ihom (mapping.obj A)).map (mapping.map sourceArrow) ≫ (pre argument.inv).app (mapping.obj E) =
    (pre argument.inv).app (mapping.obj B) ≫ (ihom X).map (mapping.map sourceArrow) at changeArgument
  simp only [function, Iso.trans_hom, asIso_hom, RelativeClosedSyntax.FunctorNormalization.functionIso]
  change mapping.map ((ihom A).map sourceArrow) ≫
    ((expComparison mapping A).natTrans.app E ≫
      (pre argument.inv).app (mapping.obj E) ≫ (ihom X).map after.hom) =
    ((expComparison mapping A).natTrans.app B ≫
      (pre argument.inv).app (mapping.obj B) ≫ (ihom X).map before.hom) ≫ (ihom X).map targetArrow
  rw [← Category.assoc, ← Category.assoc, exponent]
  simp only [Category.assoc]
  rw [← Category.assoc ((ihom (mapping.obj A)).map (mapping.map sourceArrow))
    ((pre argument.inv).app (mapping.obj E)) ((ihom X).map after.hom), changeArgument]
  simp only [Category.assoc]
  rw [← Functor.map_comp, localSquare, Functor.map_comp]

end Mettapedia.CategoryTheory.ClosedFunctorNativeSquares
