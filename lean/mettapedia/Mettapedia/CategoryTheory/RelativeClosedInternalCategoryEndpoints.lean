import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryGenerators

/-!
# Endpoint laws in the independently generated evidence theory

The declared endpoint equations earn both unit readouts and both composition
readouts. Complete raw matching pairs then supply unit insertion and the
three-edge composability object. These are admitted expressions in the
endpoint theory; no target category or interpretation provides their proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Endpoints

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory

universe k

variable {C : Type k} [Category.{k} C] (vertex : C)

def vertexObject : Object (endpointSignature vertex) :=
  (endpointInclusion vertex).object (RelativeClosedInternalCategory.vertexObject vertex)

def edgeObject : Object (endpointSignature vertex) :=
  (endpointInclusion vertex).object (RelativeClosedInternalCategory.edgeObject vertex)

def source : RawHom (edgeObject vertex) (vertexObject vertex) :=
  (endpointInclusion vertex).rawArrow (RelativeClosedInternalCategory.source vertex)

def target : RawHom (edgeObject vertex) (vertexObject vertex) :=
  (endpointInclusion vertex).rawArrow (RelativeClosedInternalCategory.target vertex)

def unit : RawHom (vertexObject vertex) (edgeObject vertex) :=
  (endpointInclusion vertex).rawArrow (RelativeClosedInternalCategory.unit vertex)

def composable : Object (endpointSignature vertex) := PresentedPullback.object (target vertex) (source vertex)

def first : RawHom (composable vertex) (edgeObject vertex) := PresentedPullback.first (target vertex) (source vertex)

def second : RawHom (composable vertex) (edgeObject vertex) := PresentedPullback.second (target vertex) (source vertex)

def composition : RawHom (composable vertex) (edgeObject vertex) :=
  (endpointInclusion vertex).rawArrow (RelativeClosedInternalCategory.composition vertex)

theorem unit_source : classOf ((unit vertex).compose (source vertex)) =
    classOf (RawHom.identity (vertexObject vertex)) :=
  endpoint_equation vertex (ULift.up EndpointLaw.unitSource)

theorem unit_target : classOf ((unit vertex).compose (target vertex)) =
    classOf (RawHom.identity (vertexObject vertex)) :=
  endpoint_equation vertex (ULift.up EndpointLaw.unitTarget)

theorem composition_source : classOf ((composition vertex).compose (source vertex)) =
    classOf ((first vertex).compose (source vertex)) :=
  endpoint_equation vertex (ULift.up EndpointLaw.compositionSource)

theorem composition_target : classOf ((composition vertex).compose (target vertex)) =
    classOf ((second vertex).compose (target vertex)) :=
  endpoint_equation vertex (ULift.up EndpointLaw.compositionTarget)

def unitLeftPair : RawHom (edgeObject vertex) (composable vertex) :=
  PresentedPullback.lift (target vertex) (source vertex)
    ((source vertex).compose (unit vertex)) (RawHom.identity (edgeObject vertex)) (by
      have law := unit_target vertex
      simpa only [classOf_compose, classOf_identity, Category.assoc, Category.id_comp,
        Category.comp_id] using congrArg (fun arrow : vertexObject vertex ⟶ vertexObject vertex =>
          (classOf (source vertex) : edgeObject vertex ⟶ vertexObject vertex) ≫ arrow) law)

def unitRightPair : RawHom (edgeObject vertex) (composable vertex) :=
  PresentedPullback.lift (target vertex) (source vertex)
    (RawHom.identity (edgeObject vertex)) ((target vertex).compose (unit vertex)) (by
      have law := unit_source vertex
      simpa only [classOf_compose, classOf_identity, Category.assoc, Category.id_comp,
        Category.comp_id] using (congrArg (fun arrow : vertexObject vertex ⟶ vertexObject vertex =>
          (classOf (target vertex) : edgeObject vertex ⟶ vertexObject vertex) ≫ arrow) law).symm)

def triples : Object (endpointSignature vertex) :=
  PresentedPullback.object ((second vertex).compose (target vertex)) (source vertex)

def initialPair : RawHom (triples vertex) (composable vertex) :=
  PresentedPullback.first ((second vertex).compose (target vertex)) (source vertex)

def tripleFirst : RawHom (triples vertex) (edgeObject vertex) :=
  (initialPair vertex).compose (first vertex)

def tripleMiddle : RawHom (triples vertex) (edgeObject vertex) :=
  (initialPair vertex).compose (second vertex)

def tripleLast : RawHom (triples vertex) (edgeObject vertex) :=
  PresentedPullback.second ((second vertex).compose (target vertex)) (source vertex)

theorem triple_first_matching : classOf ((tripleFirst vertex).compose (target vertex)) =
    classOf ((tripleMiddle vertex).compose (source vertex)) := by
  have matching := PresentedPullback.condition (target vertex) (source vertex)
  simpa only [tripleFirst, tripleMiddle, first, second, classOf_compose, Category.assoc] using
    congrArg (fun arrow : composable vertex ⟶ vertexObject vertex =>
        (classOf (initialPair vertex) : triples vertex ⟶ composable vertex) ≫ arrow) matching

theorem triple_second_matching : classOf ((tripleMiddle vertex).compose (target vertex)) =
    classOf ((tripleLast vertex).compose (source vertex)) := by
  simpa only [tripleMiddle, tripleLast, initialPair, classOf_compose, Category.assoc] using
    PresentedPullback.condition ((second vertex).compose (target vertex)) (source vertex)

def composedFirst : RawHom (triples vertex) (edgeObject vertex) :=
  (initialPair vertex).compose (composition vertex)

theorem composed_first_matching : classOf ((composedFirst vertex).compose (target vertex)) =
    classOf ((tripleLast vertex).compose (source vertex)) := by
  calc
    classOf ((composedFirst vertex).compose (target vertex)) =
        classOf ((tripleMiddle vertex).compose (target vertex)) := by
      simpa only [composedFirst, tripleMiddle, classOf_compose, Category.assoc] using
        congrArg (fun arrow : composable vertex ⟶ vertexObject vertex =>
        (classOf (initialPair vertex) : triples vertex ⟶ composable vertex) ≫ arrow) (composition_target vertex)
    _ = _ := triple_second_matching vertex

def composedLastPair : RawHom (triples vertex) (composable vertex) :=
  PresentedPullback.lift (target vertex) (source vertex) (tripleMiddle vertex) (tripleLast vertex)
    (triple_second_matching vertex)

def composedLast : RawHom (triples vertex) (edgeObject vertex) :=
  (composedLastPair vertex).compose (composition vertex)

theorem composed_last_matching : classOf ((tripleFirst vertex).compose (target vertex)) =
    classOf ((composedLast vertex).compose (source vertex)) := by
  have law := congrArg (fun arrow : composable vertex ⟶ vertexObject vertex =>
      (classOf (composedLastPair vertex) : triples vertex ⟶ composable vertex) ≫ arrow)
    (composition_source vertex)
  have projection : classOf ((composedLastPair vertex).compose (first vertex)) =
      classOf (tripleMiddle vertex) := by
    simpa only [composedLastPair, first] using
      PresentedPullback.lift_first (target vertex) (source vertex)
        (tripleMiddle vertex) (tripleLast vertex) (triple_second_matching vertex)
  have read : classOf ((composedLast vertex).compose (source vertex)) =
      classOf ((tripleMiddle vertex).compose (source vertex)) := by
    have afterProjection : classOf (((composedLastPair vertex).compose (first vertex)).compose (source vertex)) =
        classOf ((tripleMiddle vertex).compose (source vertex)) :=
      Quotient.sound (RawHom.compose_respects (classOf_eq_iff.mp projection)
        (show (source vertex) ≈ source vertex from ⟨.reflexivity (source vertex).admitted.some⟩))
    have original : classOf ((composedLast vertex).compose (source vertex)) =
        classOf (((composedLastPair vertex).compose (first vertex)).compose (source vertex)) := by
      simpa only [composedLast, classOf_compose, Category.assoc] using law
    exact original.trans afterProjection
  exact (triple_first_matching vertex).trans read.symm

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Endpoints
