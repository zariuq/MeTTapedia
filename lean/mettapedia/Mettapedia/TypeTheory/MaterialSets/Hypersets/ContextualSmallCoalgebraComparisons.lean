import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraGenerators

/-!
# Comparing small coalgebra presentations through a common execution

Composition preserves the whole future-image coalgebra equation. Canonical
readings therefore commute with every actual map between small coalgebras.
Two small presentations mapping to the same, possibly larger, execution
give equal readings whenever their complete endpoint values agree.

The comparison is constructed through the actual matching pullback
coalgebra. It neither chooses a presentation of an arbitrary large source
nor proves indexed finality or internal Collection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraComparisons

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open ContextualSmallCoalgebraGenerators
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization
  (pullback pullbackFirst pullbackSecond)

universe u v w t
variable {D : Type u} [Category.{u} D]

theorem compose_square {A : D ⥤ Type v} {B : D ⥤ Type w} {F : D ⥤ Type t}
    (source : NaturalHom A (family A)) (middle : NaturalHom B (family B))
    (target : NaturalHom F (family F)) (first : NaturalHom A B) (second : NaturalHom B F)
    (firstSquare : source.comp (imageHom first) = first.comp middle)
    (secondSquare : middle.comp (imageHom second) = second.comp target) :
    source.comp (imageHom (first.comp second)) = (first.comp second).comp target := by
  apply NaturalHom.ext
  intro point argument
  have earlier := congrArg (fun operation : NaturalHom A (family B) => operation.app point argument)
    firstSquare
  have later := congrArg (fun operation : NaturalHom B (family F) =>
    operation.app point (first.app point argument)) secondSquare
  exact (imagePower_comp first second point (source.app point argument)).symm.trans
    ((congrArg (imagePower second point) earlier).trans later)

theorem canonical_of_map (source target : Code D) (operation : NaturalHom source.carrier target.carrier)
    (square : source.coalgebra.comp (imageHom operation) = operation.comp target.coalgebra) :
    canonical source = operation.comp (canonical target) :=
  maps_equal_into_separated source.coalgebra quotientCoalgebra (canonical source)
    (operation.comp (canonical target)) (canonical_square source)
    (compose_square source.coalgebra target.coalgebra quotientCoalgebra operation (canonical target)
      square (canonical_square target)) quotient_separated

section CommonReading

variable (left right : Code D) {A : D ⥤ Type v} (target : NaturalHom A (family A))
variable (first : NaturalHom left.carrier A) (second : NaturalHom right.carrier A)
variable (firstSquare : left.coalgebra.comp (imageHom first) = first.comp target)
variable (secondSquare : right.coalgebra.comp (imageHom second) = second.comp target)

include firstSquare secondSquare

def pullbackCode : Code D :=
  ⟨pullback first second,
    ContextualCoalgebraPullback.coalgebra left.coalgebra right.coalgebra target
      first second firstSquare secondSquare⟩

theorem same_reading (point : D) (leftValue : left.carrier.obj point) (rightValue : right.carrier.obj point)
    (same : first.app point leftValue = second.app point rightValue) :
    (canonical left).app point leftValue = (canonical right).app point rightValue := by
  let joined := pullbackCode left right target first second firstSquare secondSquare
  let pair : joined.carrier.obj point := ⟨(leftValue, rightValue), same⟩
  have earlier := canonical_of_map joined left (pullbackFirst first second)
    (ContextualCoalgebraPullback.first_square left.coalgebra right.coalgebra target first second
      firstSquare secondSquare)
  have later := canonical_of_map joined right (pullbackSecond first second)
    (ContextualCoalgebraPullback.second_square left.coalgebra right.coalgebra target first second
      firstSquare secondSquare)
  exact (congrArg (fun operation : NaturalHom joined.carrier (quotient (D := D)) =>
    operation.app point pair) earlier).symm.trans
      (congrArg (fun operation : NaturalHom joined.carrier (quotient (D := D)) =>
        operation.app point pair) later)

end CommonReading

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraComparisons
