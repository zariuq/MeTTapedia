import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraBisimulation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerWeakPullback

/-!
# Constructed pullback coalgebras through complete future matching

Given two genuine coalgebra maps to a common target, their argument
pullback receives an actual coalgebra. At a retained pair the complete
matching relation supplies every future pair of children with equal
target readings. Its original small covers are explicitly constructed by
the weak-pullback theorem.

Both projections satisfy the entire future-image coalgebra equation.
No counterpart is selected, and uniqueness of this pullback coalgebra or
indexed finality is not asserted. On originally small argument families
the actual pullback argument carrier is still small.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraPullback

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open CoveredFuturePowerWeakPullback
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization
  (pullback pullbackFirst pullbackSecond)

universe u v w t
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} {F : D ⥤ Type t}
variable (left : NaturalHom A (family A)) (right : NaturalHom F (family F))
variable (target : NaturalHom B (family B))
variable (first : NaturalHom A B) (second : NaturalHom F B)
variable (firstSquare : left.comp (imageHom first) = first.comp target)
variable (secondSquare : right.comp (imageHom second) = second.comp target)

include firstSquare secondSquare

theorem same_image (point : D) (pair : (pullback first second).obj point) :
    imagePower first point (left.app point pair.val.1) =
      imagePower second point (right.app point pair.val.2) := by
  have leftEq := congrArg (fun map : NaturalHom A (family B) => map.app point pair.val.1) firstSquare
  have rightEq := congrArg (fun map : NaturalHom F (family B) => map.app point pair.val.2) secondSquare
  exact leftEq.trans ((congrArg (target.app point) pair.property).trans rightEq.symm)

def childPair : NaturalHom (pullback first second) (pullback (imageHom first) (imageHom second)) where
  app point pair := ⟨(left.app point pair.val.1, right.app point pair.val.2),
    same_image left right target first second firstSquare secondSquare point pair⟩
  naturality step pair := by
    apply Subtype.ext
    exact Prod.ext (left.naturality step pair.val.1) (right.naturality step pair.val.2)

def coalgebra : NaturalHom (pullback first second) (family (pullback first second)) :=
  (childPair left right target first second firstSquare secondSquare).comp (matchingSection first second)

theorem coalgebra_truth (point : D) (pair : (pullback first second).obj point)
    (argument : Arguments (pullback first second) point) :
    ((coalgebra left right target first second firstSquare secondSquare).app point pair).val.holds argument ↔
      (left.app point pair.val.1).val.holds ⟨argument.1, argument.2.val.1⟩ ∧
        (right.app point pair.val.2).val.holds ⟨argument.1, argument.2.val.2⟩ := Iff.rfl

theorem first_square :
    (coalgebra left right target first second firstSquare secondSquare).comp
        (imageHom (pullbackFirst first second)) =
      (pullbackFirst first second).comp left := by
  apply NaturalHom.ext
  intro point pair
  exact matching_first first second point (left.app point pair.val.1) (right.app point pair.val.2)
    (same_image left right target first second firstSquare secondSquare point pair)

theorem second_square :
    (coalgebra left right target first second firstSquare secondSquare).comp
        (imageHom (pullbackSecond first second)) =
      (pullbackSecond first second).comp right := by
  apply NaturalHom.ext
  intro point pair
  exact matching_second first second point (left.app point pair.val.1) (right.app point pair.val.2)
    (same_image left right target first second firstSquare secondSquare point pair)

theorem comparison_square :
    (coalgebra left right target first second firstSquare secondSquare).comp (comparison first second) =
      childPair left right target first second firstSquare secondSquare := by
  apply NaturalHom.ext
  intro point pair
  exact comparison_matching first second point
    ((childPair left right target first second firstSquare secondSquare).app point pair)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraPullback
