import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryView
import Mettapedia.GSLT.LanguageDef.CostRegionTree
import Mathlib.Tactic

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

theorem mixed_pair_size_lt_of_left_boundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftPayload rightPayload leftAbstract : Pattern}
    (leftReached : CostStaticPlanReached source color targetFree leftPayload
      leftAbstract)
    (leftBoundary : leftReached.BoundaryView)
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightBound : sizeOf rightPayload ≤ sizeOf rightNode.term.1) :
    sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
  have leftMember : leftBoundary.stopped.certified.typed ∈
      leftNode.plan.boundaryTable.entries :=
    leftEmbedding.subset (by
      rw [leftBoundary.entries_eq]
      simp)
  have leftStrict :=
    leftNode.plan.boundary_content_size_lt_of_isStaticRoot
      leftNode.rootStatic leftBoundary.stopped.certified.typed leftMember
  rw [leftBoundary.content_eq] at leftStrict
  omega

theorem mixed_pair_size_lt_of_right_boundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftPayload rightPayload rightAbstract : Pattern}
    (rightReached : CostStaticPlanReached source color targetFree rightPayload
      rightAbstract)
    (rightBoundary : rightReached.BoundaryView)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (leftBound : sizeOf leftPayload ≤ sizeOf leftNode.term.1) :
    sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
  have rightMember : rightBoundary.stopped.certified.typed ∈
      rightNode.plan.boundaryTable.entries :=
    rightEmbedding.subset (by
      rw [rightBoundary.entries_eq]
      simp)
  have rightStrict :=
    rightNode.plan.boundary_content_size_lt_of_isStaticRoot
      rightNode.rootStatic rightBoundary.stopped.certified.typed rightMember
  rw [rightBoundary.content_eq] at rightStrict
  omega

-- The exact arithmetic obligations needed when the producer descends.
example (wire : String) (arguments : List Pattern) (rootSize : Nat)
    (bound : sizeOf (.apply wire arguments : Pattern) ≤ rootSize) :
    sizeOf arguments ≤ rootSize := by
  simp at bound ⊢
  omega

example (head : Pattern) (tail : List Pattern) (rootSize : Nat)
    (bound : sizeOf (head :: tail) ≤ rootSize) :
    sizeOf head ≤ rootSize ∧ sizeOf tail ≤ rootSize := by
  simp at bound ⊢
  omega

example (binder : Option String) (body : Pattern) (rootSize : Nat)
    (bound : sizeOf (.lambda binder body : Pattern) ≤ rootSize) :
    sizeOf body ≤ rootSize := by
  simp at bound ⊢
  omega

example (arity : Nat) (binders : List String) (body : Pattern)
    (rootSize : Nat)
    (bound : sizeOf (.multiLambda arity binders body : Pattern) ≤ rootSize) :
    sizeOf body ≤ rootSize := by
  simp at bound ⊢
  omega

example (collectionType : CollType) (elements : List Pattern)
    (rest : Option String) (rootSize : Nat)
    (bound : sizeOf (.collection collectionType elements rest : Pattern) ≤
      rootSize) :
    sizeOf elements ≤ rootSize := by
  simp at bound ⊢
  omega

end Mettapedia.GSLT.LanguageDef
