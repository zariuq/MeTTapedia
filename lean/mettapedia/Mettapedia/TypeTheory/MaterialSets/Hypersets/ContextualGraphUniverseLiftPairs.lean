import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphOrderedPairs

/-!
# Independently formed contextual pairs at the successor bound

Raising an actual lower pair and independently pairing its raised operands
give full-future matching values. Both membership directions handle arbitrary
upper elements. The same comparison applies to Kuratowski ordered pairs,
retaining the exact two-component observation kernel.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLiftPairs

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphOrderedPairs

universe u
variable {D : Type u} [Category.{u} D]
variable {point : ContextualGraphUniverseLift.Raised (D := D)}

def pairForth (left right : Value D point.down)
    (element : Value (ContextualGraphUniverseLift.Raised (D := D)) point)
    (membership : Member element (ContextualGraphUniverseLift.value (pair left right))) :
    Member element (pair (ContextualGraphUniverseLift.value left)
      (ContextualGraphUniverseLift.value right)) := by
  let child := ContextualGraphUniverseLift.childDecoder (pair left right) membership.1
  have elementSame : Equal element
      (ContextualGraphUniverseLift.value (childValue D (pair left right) child)) := membership.2
  cases pairEliminate (Member.atChild (pair left right) child) with
  | inl same =>
    exact Member.transportChild (elementSame.trans (ContextualGraphUniverseLift.preserve same)).symm
      (pairFirst (ContextualGraphUniverseLift.value left) (ContextualGraphUniverseLift.value right))
  | inr same =>
    exact Member.transportChild (elementSame.trans (ContextualGraphUniverseLift.preserve same)).symm
      (pairSecond (ContextualGraphUniverseLift.value left) (ContextualGraphUniverseLift.value right))

def pairBack (left right : Value D point.down)
    (element : Value (ContextualGraphUniverseLift.Raised (D := D)) point)
    (membership : Member element (pair (ContextualGraphUniverseLift.value left)
      (ContextualGraphUniverseLift.value right))) :
    Member element (ContextualGraphUniverseLift.value (pair left right)) :=
  match pairEliminate membership with
  | .inl same => Member.transportChild same.symm
      (ContextualGraphUniverseLift.memberPreserve (pairFirst left right))
  | .inr same => Member.transportChild same.symm
      (ContextualGraphUniverseLift.memberPreserve (pairSecond left right))

/-- Both pair constructions retain all actual future arrows; arbitrary
upper members are compared without assuming they are lower images. -/
def pairComparison (left right : Value D point.down) :
    Equal (ContextualGraphUniverseLift.value (pair left right))
      (pair (ContextualGraphUniverseLift.value left) (ContextualGraphUniverseLift.value right)) :=
  extensionality
    (fun _ arrival element membership => pairForth
      (move D arrival.down left) (move D arrival.down right) element membership)
    (fun _ arrival element membership => pairBack
      (move D arrival.down left) (move D arrival.down right) element membership)

def singletonComparison (value : Value D point.down) :
    Equal (ContextualGraphUniverseLift.value (singleton value))
      (singleton (ContextualGraphUniverseLift.value value)) := pairComparison value value

def orderedPairComparison (left right : Value D point.down) :
    Equal (ContextualGraphUniverseLift.value (orderedPair left right))
      (orderedPair (ContextualGraphUniverseLift.value left) (ContextualGraphUniverseLift.value right)) :=
  (pairComparison (singleton left) (pair left right)).trans
    (pairCongr (singletonComparison left) (pairComparison left right))

theorem orderedPair_kernel (left right nextLeft nextRight : Value D point.down) :
    Nonempty (Equal
      (orderedPair (ContextualGraphUniverseLift.value left) (ContextualGraphUniverseLift.value right))
      (orderedPair (ContextualGraphUniverseLift.value nextLeft) (ContextualGraphUniverseLift.value nextRight))) ↔
      Nonempty (Equal left nextLeft) ∧ Nonempty (Equal right nextRight) := by
  rw [ContextualGraphOrderedPairs.orderedPair_kernel]
  exact and_congr (ContextualGraphUniverseLift.matching_iff left nextLeft)
    (ContextualGraphUniverseLift.matching_iff right nextRight)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLiftPairs
