import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryPresentation
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelDiagrams
import Mettapedia.CategoryTheory.RelativeClosedSyntaxPullbackInterpretation

/-!
# Complete category-equation readings from independent operations

The endpoint assignment reads unit insertion, independently formed triples
and both nested associations. All matching lifts use the actual semantic
pullback property. No category law is required to compute either side.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.EquationReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w z

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : Meaning.Operations (base.obj vertex))

def assignment : Assignment C
    (EquationExtension.extendedSymbols symbols (ULift.{k} EndpointLaw)) D :=
  EquationExtension.extendAssignment (Meaning.assignment vertex base meaning)

theorem edge_read : (assignment vertex base meaning).evaluateObject (Endpoints.edgeObject vertex).code =
    some meaning.edge :=
  (EquationExtension.evaluate_object_original (signature vertex) (endpointDeclaration vertex)
    (Meaning.assignment vertex base meaning) edgeCode).trans (Meaning.edge_read vertex base meaning)

theorem vertex_read : (assignment vertex base meaning).evaluateObject (Endpoints.vertexObject vertex).code =
    some (base.obj vertex) :=
  (EquationExtension.evaluate_object_original (signature vertex) (endpointDeclaration vertex)
    (Meaning.assignment vertex base meaning) (.base vertex)).trans (Meaning.vertex_read vertex base meaning)

theorem source_read : (assignment vertex base meaning).evaluateArrow (Endpoints.source vertex).code =
    some ⟨meaning.edge,base.obj vertex,meaning.source⟩ := rfl

theorem target_read : (assignment vertex base meaning).evaluateArrow (Endpoints.target vertex).code =
    some ⟨meaning.edge,base.obj vertex,meaning.target⟩ := rfl

theorem unit_read : (assignment vertex base meaning).evaluateArrow (Endpoints.unit vertex).code =
    some ⟨base.obj vertex,meaning.edge,meaning.unit⟩ := rfl

theorem composition_read : (assignment vertex base meaning).evaluateArrow (Endpoints.composition vertex).code =
    some ⟨meaning.toGraph.composable,meaning.edge,meaning.composition⟩ := rfl

theorem composable_read : (assignment vertex base meaning).evaluateObject (Endpoints.composable vertex).code =
    some meaning.toGraph.composable :=
  PullbackInterpretation.object_read (assignment vertex base meaning)
    (Endpoints.target vertex) (Endpoints.source vertex) meaning.target meaning.source
    (edge_read vertex base meaning) (edge_read vertex base meaning) (vertex_read vertex base meaning)
    (target_read vertex base meaning) (source_read vertex base meaning)

theorem first_read : (assignment vertex base meaning).evaluateArrow (Endpoints.first vertex).code =
    some ⟨meaning.toGraph.composable,meaning.edge,meaning.toGraph.first⟩ :=
  PullbackInterpretation.first_read (assignment vertex base meaning)
    (Endpoints.target vertex) (Endpoints.source vertex) meaning.target meaning.source
    (edge_read vertex base meaning) (edge_read vertex base meaning) (vertex_read vertex base meaning)
    (target_read vertex base meaning) (source_read vertex base meaning)

theorem second_read : (assignment vertex base meaning).evaluateArrow (Endpoints.second vertex).code =
    some ⟨meaning.toGraph.composable,meaning.edge,meaning.toGraph.second⟩ :=
  PullbackInterpretation.second_read (assignment vertex base meaning)
    (Endpoints.target vertex) (Endpoints.source vertex) meaning.target meaning.source
    (edge_read vertex base meaning) (edge_read vertex base meaning) (vertex_read vertex base meaning)
    (target_read vertex base meaning) (source_read vertex base meaning)

variable (endpointLaws : Meaning.EndpointLaws vertex base meaning)

abbrev operations := ModelDiagrams.endpoints vertex base meaning endpointLaws
abbrev triple := ModelDiagrams.triples vertex base meaning endpointLaws

theorem pair_read {context : Object (endpointSignature vertex)}
    (first : RawHom context (Endpoints.edgeObject vertex))
    (second : RawHom context (Endpoints.edgeObject vertex))
    (matching : classOf (first.compose (Endpoints.target vertex)) =
      classOf (second.compose (Endpoints.source vertex)))
    {stage : D} (contextRead : (assignment vertex base meaning).evaluateObject context.code = some stage)
    (p q : stage ⟶ meaning.edge) (commutes : p ≫ meaning.target = q ≫ meaning.source)
    (firstRead : (assignment vertex base meaning).evaluateArrow first.code = some ⟨stage,meaning.edge,p⟩)
    (secondRead : (assignment vertex base meaning).evaluateArrow second.code = some ⟨stage,meaning.edge,q⟩) :
    (assignment vertex base meaning).evaluateArrow
      (PresentedPullback.lift (Endpoints.target vertex) (Endpoints.source vertex) first second matching).code =
      some ⟨stage,meaning.toGraph.composable,
        InternalCategoryPresentedDiagrams.pairLift (operations vertex base meaning endpointLaws) p q commutes⟩ := by
  rw [ModelDiagrams.pair_lift_read]
  exact PullbackInterpretation.lift_read (assignment vertex base meaning)
    (Endpoints.target vertex) (Endpoints.source vertex) meaning.target meaning.source
    (edge_read vertex base meaning) (edge_read vertex base meaning) (vertex_read vertex base meaning)
    (target_read vertex base meaning) (source_read vertex base meaning)
    first second matching contextRead p q commutes firstRead secondRead

theorem unit_left_read : (assignment vertex base meaning).evaluateArrow (Endpoints.unitLeftPair vertex).code =
    some ⟨meaning.edge,meaning.toGraph.composable,
      InternalCategoryPresentedDiagrams.pairLift (operations vertex base meaning endpointLaws)
        (meaning.source ≫ meaning.unit) (𝟙 meaning.edge)
        (by
          change (meaning.source ≫ meaning.unit) ≫ meaning.target = (𝟙 meaning.edge) ≫ meaning.source
          simp only [Category.assoc,endpointLaws.unitTarget,Category.comp_id,Category.id_comp])⟩ :=
  pair_read vertex base meaning endpointLaws _ _ _ (edge_read vertex base meaning) _ _ _
    ((assignment vertex base meaning).evaluate_compose _ _ (source_read vertex base meaning) (unit_read vertex base meaning))
    ((assignment vertex base meaning).evaluate_identity (edge_read vertex base meaning))

theorem unit_right_read : (assignment vertex base meaning).evaluateArrow (Endpoints.unitRightPair vertex).code =
    some ⟨meaning.edge,meaning.toGraph.composable,
      InternalCategoryPresentedDiagrams.pairLift (operations vertex base meaning endpointLaws)
        (𝟙 meaning.edge) (meaning.target ≫ meaning.unit)
        (by
          change (𝟙 meaning.edge) ≫ meaning.target = (meaning.target ≫ meaning.unit) ≫ meaning.source
          simp only [Category.assoc,endpointLaws.unitSource,Category.comp_id,Category.id_comp])⟩ :=
  pair_read vertex base meaning endpointLaws _ _ _ (edge_read vertex base meaning) _ _ _
    ((assignment vertex base meaning).evaluate_identity (edge_read vertex base meaning))
    ((assignment vertex base meaning).evaluate_compose _ _ (target_read vertex base meaning) (unit_read vertex base meaning))

theorem middle_target_read :
    (assignment vertex base meaning).evaluateArrow ((Endpoints.second vertex).compose (Endpoints.target vertex)).code =
      some ⟨meaning.toGraph.composable,base.obj vertex,meaning.toGraph.second ≫ meaning.target⟩ :=
  (assignment vertex base meaning).evaluate_compose _ _ (second_read vertex base meaning) (target_read vertex base meaning)

theorem triple_read : (assignment vertex base meaning).evaluateObject (Endpoints.triples vertex).code =
    some (triple vertex base meaning endpointLaws).pt :=
  PullbackInterpretation.object_read (assignment vertex base meaning)
    ((Endpoints.second vertex).compose (Endpoints.target vertex)) (Endpoints.source vertex)
    (meaning.toGraph.second ≫ meaning.target) meaning.source
    (composable_read vertex base meaning) (edge_read vertex base meaning) (vertex_read vertex base meaning)
    (middle_target_read vertex base meaning) (source_read vertex base meaning)

theorem initial_pair_read : (assignment vertex base meaning).evaluateArrow (Endpoints.initialPair vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.toGraph.composable,
      (triple vertex base meaning endpointLaws).fst⟩ :=
  PullbackInterpretation.first_read (assignment vertex base meaning)
    ((Endpoints.second vertex).compose (Endpoints.target vertex)) (Endpoints.source vertex)
    (meaning.toGraph.second ≫ meaning.target) meaning.source
    (composable_read vertex base meaning) (edge_read vertex base meaning) (vertex_read vertex base meaning)
    (middle_target_read vertex base meaning) (source_read vertex base meaning)

theorem triple_last_read : (assignment vertex base meaning).evaluateArrow (Endpoints.tripleLast vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.edge,
      (triple vertex base meaning endpointLaws).snd⟩ :=
  PullbackInterpretation.second_read (assignment vertex base meaning)
    ((Endpoints.second vertex).compose (Endpoints.target vertex)) (Endpoints.source vertex)
    (meaning.toGraph.second ≫ meaning.target) meaning.source
    (composable_read vertex base meaning) (edge_read vertex base meaning) (vertex_read vertex base meaning)
    (middle_target_read vertex base meaning) (source_read vertex base meaning)

theorem triple_first_read : (assignment vertex base meaning).evaluateArrow (Endpoints.tripleFirst vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.edge,
      InternalCategoryPresentedDiagrams.first (operations vertex base meaning endpointLaws)
        (triple vertex base meaning endpointLaws)⟩ :=
  (assignment vertex base meaning).evaluate_compose _ _ (initial_pair_read vertex base meaning endpointLaws)
    (first_read vertex base meaning)

theorem triple_middle_read : (assignment vertex base meaning).evaluateArrow (Endpoints.tripleMiddle vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.edge,
      InternalCategoryPresentedDiagrams.middle (operations vertex base meaning endpointLaws)
        (triple vertex base meaning endpointLaws)⟩ :=
  (assignment vertex base meaning).evaluate_compose _ _ (initial_pair_read vertex base meaning endpointLaws)
    (second_read vertex base meaning)

theorem composed_first_read : (assignment vertex base meaning).evaluateArrow (Endpoints.composedFirst vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.edge,
      (triple vertex base meaning endpointLaws).fst ≫ meaning.composition⟩ :=
  (assignment vertex base meaning).evaluate_compose _ _ (initial_pair_read vertex base meaning endpointLaws)
    (composition_read vertex base meaning)

theorem composed_last_read : (assignment vertex base meaning).evaluateArrow (Endpoints.composedLast vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.edge,
      InternalCategoryPresentedDiagrams.compose (operations vertex base meaning endpointLaws)
        (InternalCategoryPresentedDiagrams.middle (operations vertex base meaning endpointLaws)
          (triple vertex base meaning endpointLaws)) (triple vertex base meaning endpointLaws).snd
        (InternalCategoryPresentedDiagrams.second_matching (operations vertex base meaning endpointLaws)
          (triple vertex base meaning endpointLaws))⟩ :=
  (assignment vertex base meaning).evaluate_compose _ _
    (pair_read vertex base meaning endpointLaws _ _ _ (triple_read vertex base meaning endpointLaws) _ _ _
      (triple_middle_read vertex base meaning endpointLaws) (triple_last_read vertex base meaning endpointLaws))
    (composition_read vertex base meaning)

theorem associate_left_read : (assignment vertex base meaning).evaluateArrow (Presentation.associateLeft vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.edge,
      InternalCategoryPresentedDiagrams.associateLeft (operations vertex base meaning endpointLaws)
        (triple vertex base meaning endpointLaws)⟩ :=
  (assignment vertex base meaning).evaluate_compose _ _
    (pair_read vertex base meaning endpointLaws _ _ _ (triple_read vertex base meaning endpointLaws) _ _ _
      (composed_first_read vertex base meaning endpointLaws) (triple_last_read vertex base meaning endpointLaws))
    (composition_read vertex base meaning)

theorem associate_right_read : (assignment vertex base meaning).evaluateArrow (Presentation.associateRight vertex).code =
    some ⟨(triple vertex base meaning endpointLaws).pt,meaning.edge,
      InternalCategoryPresentedDiagrams.associateRight (operations vertex base meaning endpointLaws)
        (triple vertex base meaning endpointLaws)⟩ :=
  (assignment vertex base meaning).evaluate_compose _ _
    (pair_read vertex base meaning endpointLaws _ _ _ (triple_read vertex base meaning endpointLaws) _ _ _
      (triple_first_read vertex base meaning endpointLaws) (composed_last_read vertex base meaning endpointLaws))
    (composition_read vertex base meaning)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.EquationReadout
