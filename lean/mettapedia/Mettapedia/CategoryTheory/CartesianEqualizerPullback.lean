import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Product equalizers with their complete pullback universal property

The matching object is independently formed as a product equalizer.
Both projections and the full universal lift retain their supplied arrows.
The pullback property follows from the product and equalizer properties.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.CartesianEqualizerPullback

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteLimits C]
variable {left right target : C} (before : left ⟶ target) (after : right ⟶ target)

def firstMap (before : left ⟶ target) (_after : right ⟶ target) : left ⊗ right ⟶ target :=
  CartesianMonoidalCategory.fst _ _ ≫ before
def secondMap (_before : left ⟶ target) (after : right ⟶ target) : left ⊗ right ⟶ target :=
  CartesianMonoidalCategory.snd _ _ ≫ after
def object : C := equalizer (firstMap before after) (secondMap before after)
def first : object before after ⟶ left :=
  equalizer.ι (firstMap before after) (secondMap before after) ≫ CartesianMonoidalCategory.fst _ _
def second : object before after ⟶ right :=
  equalizer.ι (firstMap before after) (secondMap before after) ≫ CartesianMonoidalCategory.snd _ _

theorem condition : first before after ≫ before = second before after ≫ after := by
  simpa only [first, second, firstMap, secondMap, Category.assoc] using
    equalizer.condition (firstMap before after) (secondMap before after)

def cone : PullbackCone before after := PullbackCone.mk (first before after) (second before after)
  (condition before after)

def lift {stage : C} (left : stage ⟶ left) (right : stage ⟶ right)
    (matching : left ≫ before = right ≫ after) : stage ⟶ object before after :=
  equalizer.lift (CartesianMonoidalCategory.lift left right) (by
    simpa only [firstMap, secondMap, ← Category.assoc, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd] using matching)

@[simp] theorem lift_first {stage : C} (left : stage ⟶ left) (right : stage ⟶ right)
    (matching : left ≫ before = right ≫ after) : lift before after left right matching ≫ first before after = left := by
  rw [lift, first, ← Category.assoc, equalizer.lift_ι, CartesianMonoidalCategory.lift_fst]

@[simp] theorem lift_second {stage : C} (left : stage ⟶ left) (right : stage ⟶ right)
    (matching : left ≫ before = right ≫ after) : lift before after left right matching ≫ second before after = right := by
  rw [lift, second, ← Category.assoc, equalizer.lift_ι, CartesianMonoidalCategory.lift_snd]

theorem hom_ext {stage : C} {first second : stage ⟶ object before after}
    (sameLeft : first ≫ CartesianEqualizerPullback.first before after = second ≫ CartesianEqualizerPullback.first before after)
    (sameRight : first ≫ CartesianEqualizerPullback.second before after = second ≫ CartesianEqualizerPullback.second before after) :
    first = second := by
  apply (cancel_mono (equalizer.ι (firstMap before after) (secondMap before after))).mp
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [CartesianEqualizerPullback.first, Category.assoc] using sameLeft
  · simpa only [CartesianEqualizerPullback.second, Category.assoc] using sameRight

def isLimit : IsLimit (cone before after) :=
  PullbackCone.IsLimit.mk _
    (fun supplied => lift before after supplied.fst supplied.snd supplied.condition)
    (fun supplied => lift_first before after supplied.fst supplied.snd supplied.condition)
    (fun supplied => lift_second before after supplied.fst supplied.snd supplied.condition)
    (fun supplied _candidate left right => hom_ext before after
      (left.trans (lift_first before after supplied.fst supplied.snd supplied.condition).symm)
      (right.trans (lift_second before after supplied.fst supplied.snd supplied.condition).symm))

end Mettapedia.CategoryTheory.CartesianEqualizerPullback
