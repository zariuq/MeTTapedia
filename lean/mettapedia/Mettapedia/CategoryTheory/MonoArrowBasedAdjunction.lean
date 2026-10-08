import Mettapedia.CategoryTheory.MonoArrowImageAdjunction
import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Image and comprehension as an adjunction over the base

The image and comprehension functors strictly retain their base objects.
Their unit and counit are vertical transformations, and the ordinary triangle
identities lift to the actual bicategory of based categories. Cartesian
preservation by image additionally requires stability of images under base
change; it is not inferred from this based adjunction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageAdjunction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasImages C] [HasImageMaps C]

abbrev arrowBased (C : Type u) [Category.{v} C] : BasedCategory C :=
  BasedCategory.ofFunctor (Arrow.rightFunc (C := C))

abbrev predicateBased (C : Type u) [Category.{v} C] : BasedCategory C :=
  BasedCategory.ofFunctor (projection C)

def basedImage : BasedFunctor (arrowBased C) (predicateBased C) where
  toFunctor := image
  w := image_codomain

def basedComprehension : BasedFunctor (predicateBased C) (arrowBased C) where
  toFunctor := comprehension C
  w := rfl

def basedUnit : BasedNatTrans (BasedFunctor.id (arrowBased C))
    (BasedFunctor.comp basedImage basedComprehension) where
  toNatTrans := adjunction.unit
  isHomLift' object := by
    change Arrow C at object
    apply IsHomLift.of_fac _ _ _ rfl rfl
    change 𝟙 object.right =
      𝟙 object.right ≫ (adjunction.unit.app object).right ≫ 𝟙 object.right
    rw [adjunction_unit, unitSquare_right]
    exact (Category.id_comp _).symm.trans (Category.id_comp _).symm

def basedCounit : BasedNatTrans
    (BasedFunctor.comp basedComprehension basedImage) (BasedFunctor.id (predicateBased C)) where
  toNatTrans := adjunction.counit
  isHomLift' predicate := by
    change Predicate C at predicate
    apply IsHomLift.of_fac _ _ _ rfl rfl
    change 𝟙 predicate.obj.right =
      𝟙 predicate.obj.right ≫ (adjunction.counit.app predicate).hom.right ≫
        𝟙 predicate.obj.right
    rw [adjunction_counit, descend_right]
    exact (Category.id_comp _).symm.trans (Category.id_comp _).symm

def basedAdjunction : Bicategory.Adjunction
    (B := BasedCategory.{v, max u v} C) (a := arrowBased C) (b := predicateBased C)
    (basedImage (C := C)) (basedComprehension (C := C)) where
  unit := basedUnit
  counit := basedCounit
  left_triangle := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext object
    change Arrow C at object
    apply (projection C).map_injective
    let first := Bicategory.leftZigzag (B := BasedCategory.{v, max u v} C)
      (f := basedImage (C := C)) (g := basedComprehension (C := C))
      (basedUnit (C := C)) (basedCounit (C := C))
    let second := (Bicategory.leftUnitor (B := BasedCategory.{v, max u v} C)
      (basedImage (C := C))).hom ≫
      (Bicategory.rightUnitor (B := BasedCategory.{v, max u v} C)
        (basedImage (C := C))).inv
    have : (projection C).IsHomLift (𝟙 object.right) (first.toNatTrans.app object) :=
      BasedNatTrans.isHomLift first rfl
    have : (projection C).IsHomLift (𝟙 object.right) (second.toNatTrans.app object) :=
      BasedNatTrans.isHomLift second rfl
    exact (IsHomLift.fac' (projection C) (𝟙 object.right)
      (first.toNatTrans.app object)).trans
      (IsHomLift.fac' (projection C) (𝟙 object.right)
        (second.toNatTrans.app object)).symm
  right_triangle := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext predicate
    change Predicate C at predicate
    apply square_into_predicate_ext (predicate := predicate)
    let first := Bicategory.rightZigzag (B := BasedCategory.{v, max u v} C)
      (f := basedImage (C := C)) (g := basedComprehension (C := C))
      (basedUnit (C := C)) (basedCounit (C := C))
    let second := (Bicategory.rightUnitor (B := BasedCategory.{v, max u v} C)
      (basedComprehension (C := C))).hom ≫
      (Bicategory.leftUnitor (B := BasedCategory.{v, max u v} C)
        (basedComprehension (C := C))).inv
    have : Arrow.rightFunc.IsHomLift (𝟙 predicate.obj.right) (first.toNatTrans.app predicate) :=
      BasedNatTrans.isHomLift first rfl
    have : Arrow.rightFunc.IsHomLift (𝟙 predicate.obj.right) (second.toNatTrans.app predicate) :=
      BasedNatTrans.isHomLift second rfl
    exact (IsHomLift.fac' (Arrow.rightFunc (C := C)) (𝟙 predicate.obj.right)
      (first.toNatTrans.app predicate)).trans
      (IsHomLift.fac' (Arrow.rightFunc (C := C)) (𝟙 predicate.obj.right)
        (second.toNatTrans.app predicate)).symm

theorem basedAdjunction_unit_readout (object : Arrow C) :
    basedAdjunction.unit.toNatTrans.app object = unitSquare object := adjunction_unit object

theorem basedAdjunction_counit_readout (predicate : Predicate C) :
    basedAdjunction.counit.toNatTrans.app predicate = descend (𝟙 predicate.obj) :=
  adjunction_counit predicate

end Mettapedia.CategoryTheory.MonoArrowImageAdjunction
