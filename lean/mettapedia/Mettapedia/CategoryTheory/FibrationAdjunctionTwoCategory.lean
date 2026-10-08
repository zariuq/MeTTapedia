import Mettapedia.CategoryTheory.AdjunctionTwoCategory
import Mettapedia.CategoryTheory.FibrationCodomainCoherence
import Mettapedia.CategoryTheory.MonoArrowImageCartesian
import Mettapedia.CategoryTheory.ElementaryTopos

/-!
# The adjunction-object target for fibrations

The ambient bicategory has actual adjunctions in the bicategory of
fibrations as objects. The image-comprehension construction below is a
genuine object: image preserves Cartesian arrows by stable elementary
topos images, and both complete triangle identities use the original
image adjunction. Higher-order and closed-comprehension profiles are
additional object structure, rather than part of the ambient morphism type.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory
open FibrationTwoCategory MonoArrowImageAdjunction

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

universe u v

set_option linter.checkUnivs false in
abbrev FibrationAdjunctionTwoCategory :=
  AdjunctionTwoCategory Fibration.{u,v}

namespace FibrationAdjunctionTwoCategory

variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]
  [CartesianMonoidalCategory C] [MonoidalClosed C] [HasImages C] [HasImageMaps C]
variable (classifier : Subobject.Classifier C)

/-- The left adjoint retains the actual image factorization and its
complete Cartesian universal property. -/
def imageMap : codomain C ⟶ predicates C where
  square := {
    left := (MonoArrowImageAdjunction.image (C := C)).toCatHom
    right := (𝟭 C).toCatHom
    comm := by apply Cat.ext; rfl }
  cartesian := by
    intro first second square supplied
    change Arrow.rightFunc.IsCartesian square.right square at supplied
    have := supplied
    exact image_preserves_cartesian classifier square

def imageUnit : 𝟙 (codomain C) ⟶ imageMap classifier ≫ comprehensionMap C where
  hom := {
    left := (adjunction (C := C)).unit.toCatHom₂
    right := NatTrans.toCatHom₂ (𝟙 (𝟭 C))
    compatible := by
      apply heq_of_eq
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      change 𝟙 object.right = ((adjunction (C := C)).unit.app object).right
      rw [adjunction_unit, unitSquare_right] }

def imageCounit : comprehensionMap C ≫ imageMap classifier ⟶ 𝟙 (predicates C) where
  hom := {
    left := (adjunction (C := C)).counit.toCatHom₂
    right := NatTrans.toCatHom₂ (𝟙 (𝟭 C))
    compatible := by
      apply heq_of_eq
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      change 𝟙 object.obj.right =
        ((adjunction (C := C)).counit.app object).hom.right
      rw [adjunction_counit, descend_right]
      rfl }

def imageAdjunction : imageMap classifier ⊣ comprehensionMap C where
  unit := imageUnit classifier
  counit := imageCounit classifier
  left_triangle := by
    apply Fibration.Cell.ext
    apply StrictTwoArrow.Cell.ext
    · apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      simp [leftZigzag, bicategoricalComp, imageUnit, imageCounit, imageMap]
    · apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      simp [leftZigzag, bicategoricalComp, imageUnit, imageCounit, imageMap]
  right_triangle := by
    apply Fibration.Cell.ext
    apply StrictTwoArrow.Cell.ext
    · apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      simpa [rightZigzag, bicategoricalComp, imageUnit, imageCounit, imageMap,
        comprehensionMap, Cat.eqToHom_app] using
        (adjunction (C := C)).right_triangle_components object
    · apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext object
      simp [rightZigzag, bicategoricalComp, imageUnit, imageCounit, imageMap,
        comprehensionMap]

def imageObject : FibrationAdjunctionTwoCategory.{max u v,v} :=
  ⟨codomain C, predicates C, imageMap classifier, comprehensionMap C,
    imageAdjunction classifier⟩

@[simp] theorem imageUnit_total_left (object : Arrow C) :
    ((imageUnit classifier).hom.left.toNatTrans.app object).left =
      factorThruImage object.hom := by
  exact congrArg Arrow.Hom.left (adjunction_unit object)

@[simp] theorem imageUnit_total_right (object : Arrow C) :
    ((imageUnit classifier).hom.left.toNatTrans.app object).right =
      𝟙 object.right := by
  exact congrArg Arrow.Hom.right (adjunction_unit object)

@[simp] theorem imageCounit_total (predicate : Predicate C) :
    (imageCounit classifier).hom.left.toNatTrans.app predicate = descend (𝟙 predicate.obj) :=
  adjunction_counit predicate

/-- No image-existence or image-stability assumption is added to the
elementary-topos bundle: both are derived before forming this object. -/
def ofElementaryTopos (topos : ElementaryTopos.{max u v,v}) :
    FibrationAdjunctionTwoCategory.{max u v,v} :=
  imageObject topos.classifier

end FibrationAdjunctionTwoCategory
end Mettapedia.CategoryTheory
