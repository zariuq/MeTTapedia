import Mettapedia.OSLF.Syntax.FiniteBranchingBisimulation
import Mettapedia.CategoryTheory.FinitePowersetSpan
import Mettapedia.TypeTheory.IndexedGSOSCoalgebraMonad

/-!
# Finite bisimulation spans through actual free GSOS lifting

Every coalgebra span induces a two-sided bisimulation relation on its
endpoint images. The actual free-term coalgebra functor therefore lifts an
admitted bisimulation span. Complete successor images are compared; no
final coalgebra, cofree existence, or quotient decoder is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Bisimulation

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open IndexedPolynomial

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {left right middle : Endofunctor.Coalgebra (behaviourFunctor S Actions)}

def imageRelation (first : middle ⟶ left) (second : middle ⟶ right) :
    Relation left right :=
  fun base sort value other => ∃ point : middle.V base sort,
    first.f base sort point = value ∧ second.f base sort point = other

/-- Actual coalgebra squares earn both successor-set comparisons. -/
theorem image_admitted (first : middle ⟶ left) (second : middle ⟶ right) :
    Admitted left right (imageRelation first second) := by
  rintro base sort _ _ ⟨point, rfl, rfl⟩ action
  have firstSquare := congrArg (fun arrow => arrow base sort point action) first.h
  have secondSquare := congrArg (fun arrow => arrow base sort point action) second.h
  change FinitePowerset.map (first.f base sort) (middle.str base sort point action) =
    left.str base sort (first.f base sort point) action at firstSquare
  change FinitePowerset.map (second.f base sort) (middle.str base sort point action) =
    right.str base sort (second.f base sort point) action at secondSquare
  rw [← firstSquare, ← secondSquare]
  exact FinitePowersetSpan.images_related (imageRelation first second base sort)
    (first.f base sort) (second.f base sort) (middle.str base sort point action)
    (fun successor _ => ⟨successor, rfl, rfl⟩)

variable (law : IndexedGSOS.Law S.polynomial (behaviourFunctor S Actions))
variable (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions))
variable (relation : Relation left right) (admitted : Admitted left right relation)

/-- The relation is the image of the independently constructed lifted span. -/
def freeRelation : Relation (IndexedGSOS.Operational.liftObject law left)
    (IndexedGSOS.Operational.liftObject law right) :=
  imageRelation
    (IndexedGSOS.Operational.liftMap law (firstMorphism left right relation admitted))
    (IndexedGSOS.Operational.liftMap law (secondMorphism left right relation admitted))

theorem free_relation_admitted :
    Admitted (IndexedGSOS.Operational.liftObject law left)
      (IndexedGSOS.Operational.liftObject law right)
      (freeRelation law left right relation admitted) :=
  image_admitted
    (IndexedGSOS.Operational.liftMap law (firstMorphism left right relation admitted))
    (IndexedGSOS.Operational.liftMap law (secondMorphism left right relation admitted))

/-- A witness retains a complete free term of related endpoint pairs. -/
theorem free_relation_readout (base : PUnit.{u + 1}) (sort : S.Srt)
    (value : S.polynomial.Free left.V base sort)
    (other : S.polynomial.Free right.V base sort) :
    freeRelation law left right relation admitted base sort value other ↔
      ∃ term : S.polynomial.Free (Pairs left right relation) base sort,
        Free.map S.polynomial (fun base sort => first left right relation base sort)
          base sort term = value ∧
        Free.map S.polynomial (fun base sort => second left right relation base sort)
          base sort term = other := Iff.rfl

end Mettapedia.OSLF.FiniteBranching.Bisimulation
