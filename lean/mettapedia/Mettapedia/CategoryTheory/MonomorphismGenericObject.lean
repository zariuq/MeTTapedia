import Mettapedia.CategoryTheory.FibrationGenericObject
import Mettapedia.CategoryTheory.FibrationCodomainAction
import Mettapedia.CategoryTheory.MonoArrowFibration
import Mathlib.CategoryTheory.Subobject.Classifier.Defs

/-!
# The actual generic object of the monomorphism fibration

The classifier's truth monomorphism is generic. Its original pullback
square gives a Cartesian total arrow from each supplied monomorphism.
Conversely, a Cartesian arrow to truth forms that pullback, so the
classifier's independent uniqueness theorem determines its base map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.MonomorphismGenericObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoArrowImageAdjunction FibrationTwoCategory FibrationGenericObject

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]
  (classifier : Subobject.Classifier C)

def truth : Predicate C := ⟨Arrow.mk classifier.truth, by
  change Mono classifier.truth
  infer_instance⟩

def classification (predicate : Predicate C) : predicate ⟶ truth classifier :=
  ObjectProperty.homMk
    (Arrow.homMk (classifier.χ₀ predicate.obj.left) (classifier.χ predicate.obj.hom)
      (classifier.isPullback predicate.obj.hom).w.symm)

theorem classification_cartesian (predicate : Predicate C) :
    (projection C).IsCartesian (classifier.χ predicate.obj.hom)
      (classification classifier predicate) :=
  (cartesian_iff_pullback (classification classifier predicate)).2
    (classifier.isPullback predicate.obj.hom).flip

def generic : Generic (predicates C) where
  object := truth classifier
  classifies predicate := by
    change ∃! route : predicate.obj.right ⟶ classifier.Ω,
      ∃ arrow : predicate ⟶ truth classifier, (projection C).IsCartesian route arrow
    let : Mono predicate.obj.hom := predicate.property
    refine ⟨classifier.χ predicate.obj.hom,
      ⟨classification classifier predicate, classification_cartesian classifier predicate⟩, ?_⟩
    rintro route ⟨arrow, cartesian⟩
    let := cartesian
    have base : route = arrow.hom.right :=
      IsHomLift.eq_of_isHomLift (projection C)
        (a := predicate) (b := truth classifier) route arrow
    have square := (cartesian_iff_pullback arrow).1 (by simpa only [← base] using cartesian)
    exact base.trans (classifier.uniq predicate.obj.hom square.flip)

theorem characteristic_readout (predicate : Predicate C) :
    (generic classifier).characteristic predicate = classifier.χ predicate.obj.hom := by
  apply Eq.symm
  exact (generic classifier).unique predicate _ (classification classifier predicate)
    (classification_cartesian classifier predicate)

theorem classification_substitution {first second : Predicate C} (arrow : first ⟶ second)
    (cartesian : (projection C).IsCartesian arrow.hom.right arrow) :
    classifier.χ first.obj.hom = arrow.hom.right ≫ classifier.χ second.obj.hom := by
  rw [← characteristic_readout classifier first, ← characteristic_readout classifier second]
  exact (generic classifier).characteristic_substitution arrow cartesian

end Mettapedia.CategoryTheory.MonomorphismGenericObject
