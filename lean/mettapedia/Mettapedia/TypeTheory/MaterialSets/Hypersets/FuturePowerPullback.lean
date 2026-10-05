import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctor

/-!
# Actual pullbacks and full-future image comparison

The pullback carrier retains both argument coordinates and the equality of
their images. Its maps, projections, universal lift and inverse equations
are constructed explicitly. Existential images and inverse images of stable
future predicates satisfy Beck--Chevalley on this actual pullback, with all
future labels and argument coordinates retained.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerPullback

open CategoryTheory FuturePowerFamilies FuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D]
variable {A B F X : D ⥤ Type u}

def pullback (first : NaturalHom A B) (second : NaturalHom F B) : D ⥤ Type u where
  obj point := {pair : A.obj point × F.obj point // first.app point pair.1 = second.app point pair.2}
  map step := TypeCat.ofHom (fun pair => ⟨(A.map step pair.1.1, F.map step pair.1.2),
    (first.naturality step pair.1.1).symm.trans
      ((congrArg (B.map step) pair.2).trans (second.naturality step pair.1.2))⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro pair
    apply Subtype.ext
    exact Prod.ext (A.map_id_apply point pair.1.1) (F.map_id_apply point pair.1.2)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro pair
    apply Subtype.ext
    exact Prod.ext (A.map_comp_apply earlier later pair.1.1)
      (F.map_comp_apply earlier later pair.1.2)

def firstProjection (first : NaturalHom A B) (second : NaturalHom F B) :
    NaturalHom (pullback first second) A where
  app _ pair := pair.1.1
  naturality _ _ := rfl

def secondProjection (first : NaturalHom A B) (second : NaturalHom F B) :
    NaturalHom (pullback first second) F where
  app _ pair := pair.1.2
  naturality _ _ := rfl

theorem projection_square (first : NaturalHom A B) (second : NaturalHom F B) :
    (firstProjection first second).comp first = (secondProjection first second).comp second := by
  apply NaturalHom.ext
  intro _ pair
  exact pair.2

def lift (first : NaturalHom A B) (second : NaturalHom F B)
    (left : NaturalHom X A) (right : NaturalHom X F)
    (square : ∀ point value, first.app point (left.app point value) = second.app point (right.app point value)) :
    NaturalHom X (pullback first second) where
  app point value := ⟨(left.app point value, right.app point value), square point value⟩
  naturality step value := Subtype.ext
    (Prod.ext (left.naturality step value) (right.naturality step value))

theorem lift_first (first : NaturalHom A B) (second : NaturalHom F B)
    (left : NaturalHom X A) (right : NaturalHom X F) (square) :
    (lift first second left right square).comp (firstProjection first second) = left := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem lift_second (first : NaturalHom A B) (second : NaturalHom F B)
    (left : NaturalHom X A) (right : NaturalHom X F) (square) :
    (lift first second left right square).comp (secondProjection first second) = right := by
  apply NaturalHom.ext
  intro _ _
  rfl

/-- Both actual projections determine the whole pullback map. Equality
proofs do not replace or erase either retained argument coordinate. -/
theorem lift_unique (first : NaturalHom A B) (second : NaturalHom F B)
    (left : NaturalHom X A) (right : NaturalHom X F) (square)
    (candidate : NaturalHom X (pullback first second))
    (leftLaw : ∀ point value, (candidate.app point value).1.1 = left.app point value)
    (rightLaw : ∀ point value, (candidate.app point value).1.2 = right.app point value) :
    candidate = lift first second left right square := by
  apply NaturalHom.ext
  intro point value
  exact Subtype.ext (Prod.ext (leftLaw point value) (rightLaw point value))

/-- The complete-future Beck--Chevalley equation, derived from the explicit
pullback pair carrier. No preimage or observed representative is selected. -/
theorem image_inverseImage_beckChevalley (first : NaturalHom A B) (second : NaturalHom F B)
    (point : D) (predicate : Predicate A point) :
    inverseImage second point (image first point predicate) =
      image (secondProjection first second) point
        (inverseImage (firstProjection first second) point predicate) := by
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨value, same, holds⟩
    exact ⟨⟨(value, argument.2), same⟩, rfl, holds⟩
  · rintro ⟨pair, same, holds⟩
    exact ⟨pair.1.1, pair.2.trans (congrArg (second.app _) same), holds⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerPullback
