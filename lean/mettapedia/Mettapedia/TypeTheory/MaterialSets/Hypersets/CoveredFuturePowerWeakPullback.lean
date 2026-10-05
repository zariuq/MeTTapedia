import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor
import Mettapedia.TypeTheory.ContextualImageFactorization

/-!
# Actual weak-pullback comparison for small-covered future powers

The argument pullback retains both coordinates and their image equality.
Two covered predicates with the same direct image construct the full stable
relation of matching pairs. Filtering pairs of their actual small receipts
constructs its cover at the original bound. Both projected images are the
original predicates.

The canonical power comparison is therefore pointwise surjective. Its
matching relation supplies a natural right inverse, without choosing a
single match. This does not identify all relations with the same projected
images, supply a natural inverse to a small cover, or establish collection
or indexed finality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerWeakPullback

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

open Mettapedia.TypeTheory.ContextualImageFactorization
  (pullback pullbackFirst pullbackSecond pullback_square)

universe u v w t
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} {F : D ⥤ Type t}

def matchingPredicate (first : NaturalHom A B) (second : NaturalHom F B) (point : D)
    (left : Predicate A point) (right : Predicate F point) : Predicate (pullback first second) point where
  holds argument := left.holds ⟨argument.1, argument.2.val.1⟩ ∧
    right.holds ⟨argument.1, argument.2.val.2⟩
  closed move available :=
    ⟨left.closed ((futureArguments (pullbackFirst first second) point).map move) available.1,
      right.closed ((futureArguments (pullbackSecond first second) point).map move) available.2⟩

def matchesEnumeration (first : NaturalHom A B) (second : NaturalHom F B) (point : D)
    {left : Predicate A point} {right : Predicate F point}
    (leftCover : Enumeration left) (rightCover : Enumeration right) :
    Enumeration (matchingPredicate first second point left right) where
  Carrier future := {receipts : leftCover.Carrier future × rightCover.Carrier future //
    first.app future.1 (leftCover.value future receipts.1) =
      second.app future.1 (rightCover.value future receipts.2)}
  value future receipt :=
    ⟨(leftCover.value future receipt.val.1, rightCover.value future receipt.val.2), receipt.property⟩
  covered future argument := by
    constructor
    · rintro ⟨leftTruth, rightTruth⟩
      obtain ⟨leftReceipt, leftEq⟩ := (leftCover.covered future argument.val.1).mp leftTruth
      obtain ⟨rightReceipt, rightEq⟩ := (rightCover.covered future argument.val.2).mp rightTruth
      have square := (congrArg (first.app future.1) leftEq).trans
        (argument.property.trans (congrArg (second.app future.1) rightEq).symm)
      exact ⟨⟨(leftReceipt, rightReceipt), square⟩, Subtype.ext (Prod.ext leftEq rightEq)⟩
    · rintro ⟨receipt, same⟩
      have leftEq := congrArg (fun pair : (pullback first second).obj future.1 => pair.val.1) same
      have rightEq := congrArg (fun pair : (pullback first second).obj future.1 => pair.val.2) same
      exact ⟨(leftCover.covered future argument.val.1).mpr ⟨receipt.val.1, leftEq⟩,
        (rightCover.covered future argument.val.2).mpr ⟨receipt.val.2, rightEq⟩⟩

def matchingPower (first : NaturalHom A B) (second : NaturalHom F B) (point : D)
    (left : Power A point) (right : Power F point) : Power (pullback first second) point :=
  ⟨matchingPredicate first second point left.val right.val, by
    obtain ⟨leftCover⟩ := left.property
    obtain ⟨rightCover⟩ := right.property
    exact ⟨matchesEnumeration first second point leftCover rightCover⟩⟩

theorem matching_first (first : NaturalHom A B) (second : NaturalHom F B) (point : D)
    (left : Power A point) (right : Power F point)
    (sameImage : imagePower first point left = imagePower second point right) :
    imagePower (pullbackFirst first second) point (matchingPower first second point left right) = left := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨pair, same, holds⟩
    change pair.val.1 = argument.2 at same
    have result := holds.1
    rw [same] at result
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact result
  · intro holds
    have imageTruth := congrArg (fun predicate : Power B point =>
      predicate.val.holds ⟨argument.1, first.app argument.1.1 argument.2⟩) sameImage
    have rightTruth := Eq.mp imageTruth
      (show (imagePower first point left).val.holds
        ⟨argument.1, first.app argument.1.1 argument.2⟩ from ⟨argument.2, rfl, holds⟩)
    obtain ⟨other, same, admitted⟩ := rightTruth
    exact ⟨⟨(argument.2, other), same.symm⟩, rfl, holds, admitted⟩

theorem matching_second (first : NaturalHom A B) (second : NaturalHom F B) (point : D)
    (left : Power A point) (right : Power F point)
    (sameImage : imagePower first point left = imagePower second point right) :
    imagePower (pullbackSecond first second) point (matchingPower first second point left right) = right := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨pair, same, holds⟩
    change pair.val.2 = argument.2 at same
    have result := holds.2
    rw [same] at result
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact result
  · intro holds
    have imageTruth := congrArg (fun predicate : Power B point =>
      predicate.val.holds ⟨argument.1, second.app argument.1.1 argument.2⟩) sameImage
    have leftTruth := Eq.mpr imageTruth
      (show (imagePower second point right).val.holds
        ⟨argument.1, second.app argument.1.1 argument.2⟩ from ⟨argument.2, rfl, holds⟩)
    obtain ⟨other, same, admitted⟩ := leftTruth
    exact ⟨⟨(other, argument.2), same⟩, rfl, admitted, holds⟩

def comparison (first : NaturalHom A B) (second : NaturalHom F B) :
    NaturalHom (family (pullback first second)) (pullback (imageHom first) (imageHom second)) where
  app point (predicate : Power (pullback first second) point) :=
    ⟨(imagePower (pullbackFirst first second) point predicate,
      imagePower (pullbackSecond first second) point predicate), by
      change imagePower first point (imagePower (pullbackFirst first second) point predicate) =
        imagePower second point (imagePower (pullbackSecond first second) point predicate)
      rw [imagePower_comp, imagePower_comp, pullback_square]⟩
  naturality step predicate := by
    apply Subtype.ext
    exact Prod.ext (imagePower_restrict (pullbackFirst first second) step predicate)
      (imagePower_restrict (pullbackSecond first second) step predicate)

def matchingSection (first : NaturalHom A B) (second : NaturalHom F B) :
    NaturalHom (pullback (imageHom first) (imageHom second)) (family (pullback first second)) where
  app point pair := matchingPower first second point pair.val.1 pair.val.2
  naturality step pair := by
    apply Subtype.ext
    apply Predicate.ext
    intro argument
    exact Iff.rfl

theorem comparison_matching (first : NaturalHom A B) (second : NaturalHom F B)
    (point : D) (pair : (pullback (imageHom first) (imageHom second)).obj point) :
    (comparison first second).app point ((matchingSection first second).app point pair) = pair := by
  apply Subtype.ext
  exact Prod.ext (matching_first first second point pair.val.1 pair.val.2 pair.property)
    (matching_second first second point pair.val.1 pair.val.2 pair.property)

/-- The natural canonical section chooses the complete matching relation,
not an individual receipt or a representative of any class. -/
theorem comparison_has_natural_right_inverse (first : NaturalHom A B) (second : NaturalHom F B) :
    (matchingSection first second).comp (comparison first second) =
      identityHom (pullback (imageHom first) (imageHom second)) := by
  apply NaturalHom.ext
  exact comparison_matching first second

theorem comparison_surjective (first : NaturalHom A B) (second : NaturalHom F B) (point : D) :
    Function.Surjective ((comparison first second).app point) :=
  fun pair => ⟨(matchingSection first second).app point pair, comparison_matching first second point pair⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerWeakPullback
