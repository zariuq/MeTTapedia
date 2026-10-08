import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryGenerators
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation

/-!
# Independent evidence operations and exact endpoint admission

A target supplies an evidence object, its endpoint and unit arrows, and a
composition operation on the product equalizer of matching endpoints. The
structural parser computes the complete generator headers and the four
equation sides independently. Its endpoint realization exists exactly when
the corresponding finite arrow diagrams commute.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Meaning

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open RelativeClosedSyntax RelativeClosedSyntax.Interpretation

universe k w z

variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D] [HasFiniteLimits D]

structure Graph (vertex : D) where
  edge : D
  source : edge ⟶ vertex
  target : edge ⟶ vertex

namespace Graph

variable {vertex : D} (graph : Graph vertex)

def before : graph.edge ⊗ graph.edge ⟶ vertex := CartesianMonoidalCategory.fst _ _ ≫ graph.target
def after : graph.edge ⊗ graph.edge ⟶ vertex := CartesianMonoidalCategory.snd _ _ ≫ graph.source
def composable : D := equalizer graph.before graph.after
def first : graph.composable ⟶ graph.edge := equalizer.ι graph.before graph.after ≫ CartesianMonoidalCategory.fst _ _
def second : graph.composable ⟶ graph.edge := equalizer.ι graph.before graph.after ≫ CartesianMonoidalCategory.snd _ _

end Graph

structure Operations (vertex : D) extends Graph vertex where
  unit : vertex ⟶ edge
  composition : toGraph.composable ⟶ edge

variable {C : Type k} [Category.{k} C] (vertex : C) (base : C ⥤ D)
variable (meaning : Operations (base.obj vertex))

def assignment : Assignment C (symbols : Symbols.{k}) D where
  base := base
  object _ := meaning.edge
  arrow origin := match origin.down with
    | .source => ⟨meaning.edge, base.obj vertex, meaning.source⟩
    | .target => ⟨meaning.edge, base.obj vertex, meaning.target⟩
    | .unit => ⟨base.obj vertex, meaning.edge, meaning.unit⟩
    | .composition => ⟨meaning.toGraph.composable, meaning.edge, meaning.composition⟩

variable [MonoidalClosed D]

theorem edge_read : (assignment vertex base meaning).evaluateObject edgeCode = some meaning.edge := rfl

theorem vertex_read : (assignment vertex base meaning).evaluateObject (.base vertex) = some (base.obj vertex) := rfl

theorem before_read : (assignment vertex base meaning).evaluateArrow endpointBefore =
    some ⟨meaning.edge ⊗ meaning.edge, base.obj vertex, meaning.toGraph.before⟩ :=
  Assignment.evaluate_compose (assignment vertex base meaning) _ _
    (Assignment.evaluate_first (assignment vertex base meaning) (edge_read vertex base meaning) (edge_read vertex base meaning)) rfl

theorem after_read : (assignment vertex base meaning).evaluateArrow endpointAfter =
    some ⟨meaning.edge ⊗ meaning.edge, base.obj vertex, meaning.toGraph.after⟩ :=
  Assignment.evaluate_compose (assignment vertex base meaning) _ _
    (Assignment.evaluate_second (assignment vertex base meaning) (edge_read vertex base meaning) (edge_read vertex base meaning)) rfl

theorem composable_read : (assignment vertex base meaning).evaluateObject (composableCode vertex) =
    some meaning.toGraph.composable :=
  Assignment.evaluate_equalizer (assignment vertex base meaning) _ _
    (Assignment.evaluate_product (assignment vertex base meaning) (edge_read vertex base meaning) (edge_read vertex base meaning))
    (vertex_read vertex base meaning) (before_read vertex base meaning) (after_read vertex base meaning)

theorem first_read : (assignment vertex base meaning).evaluateArrow (first vertex).code =
    some ⟨meaning.toGraph.composable, meaning.edge, meaning.toGraph.first⟩ :=
  Assignment.evaluate_compose (assignment vertex base meaning) _ _
    (Assignment.evaluate_equalizer_arrow (assignment vertex base meaning) _ _
      (Assignment.evaluate_product (assignment vertex base meaning) (edge_read vertex base meaning) (edge_read vertex base meaning))
      (vertex_read vertex base meaning) (before_read vertex base meaning) (after_read vertex base meaning))
    (Assignment.evaluate_first (assignment vertex base meaning) (edge_read vertex base meaning) (edge_read vertex base meaning))

theorem second_read : (assignment vertex base meaning).evaluateArrow (second vertex).code =
    some ⟨meaning.toGraph.composable, meaning.edge, meaning.toGraph.second⟩ :=
  Assignment.evaluate_compose (assignment vertex base meaning) _ _
    (Assignment.evaluate_equalizer_arrow (assignment vertex base meaning) _ _
      (Assignment.evaluate_product (assignment vertex base meaning) (edge_read vertex base meaning) (edge_read vertex base meaning))
      (vertex_read vertex base meaning) (before_read vertex base meaning) (after_read vertex base meaning))
    (Assignment.evaluate_second (assignment vertex base meaning) (edge_read vertex base meaning) (edge_read vertex base meaning))

theorem realization : Realization (signature vertex) (assignment vertex base meaning) where
  source origin := by
    cases origin with
    | up origin =>
      cases origin with
      | source => exact edge_read vertex base meaning
      | target => exact edge_read vertex base meaning
      | unit => exact vertex_read vertex base meaning
      | composition => exact composable_read vertex base meaning
  target origin := by
    cases origin with
    | up origin =>
      cases origin with
      | source => exact vertex_read vertex base meaning
      | target => exact vertex_read vertex base meaning
      | unit => exact edge_read vertex base meaning
      | composition => exact edge_read vertex base meaning
  equation origin := origin.down.elim

structure EndpointLaws : Prop where
  unitSource : meaning.unit ≫ meaning.source = 𝟙 (base.obj vertex)
  unitTarget : meaning.unit ≫ meaning.target = 𝟙 (base.obj vertex)
  compositionSource : meaning.composition ≫ meaning.source = meaning.toGraph.first ≫ meaning.source
  compositionTarget : meaning.composition ≫ meaning.target = meaning.toGraph.second ≫ meaning.target

def leftValue (origin : ULift.{k} EndpointLaw) : ArrowValue D := match origin.down with
  | .unitSource => ⟨base.obj vertex, base.obj vertex, meaning.unit ≫ meaning.source⟩
  | .unitTarget => ⟨base.obj vertex, base.obj vertex, meaning.unit ≫ meaning.target⟩
  | .compositionSource => ⟨meaning.toGraph.composable, base.obj vertex, meaning.composition ≫ meaning.source⟩
  | .compositionTarget => ⟨meaning.toGraph.composable, base.obj vertex, meaning.composition ≫ meaning.target⟩

def rightValue (origin : ULift.{k} EndpointLaw) : ArrowValue D := match origin.down with
  | .unitSource => ⟨base.obj vertex, base.obj vertex, 𝟙 (base.obj vertex)⟩
  | .unitTarget => ⟨base.obj vertex, base.obj vertex, 𝟙 (base.obj vertex)⟩
  | .compositionSource => ⟨meaning.toGraph.composable, base.obj vertex, meaning.toGraph.first ≫ meaning.source⟩
  | .compositionTarget => ⟨meaning.toGraph.composable, base.obj vertex, meaning.toGraph.second ≫ meaning.target⟩

theorem left_read (origin : ULift.{k} EndpointLaw) :
    (assignment vertex base meaning).evaluateArrow (endpointDeclaration vertex origin).left.code =
      some (leftValue vertex base meaning origin) := by
  cases origin with
  | up origin =>
    cases origin <;> exact Assignment.evaluate_compose (assignment vertex base meaning) _ _ rfl rfl

theorem right_read (origin : ULift.{k} EndpointLaw) :
    (assignment vertex base meaning).evaluateArrow (endpointDeclaration vertex origin).right.code =
      some (rightValue vertex base meaning origin) := by
  cases origin with
  | up origin =>
    cases origin with
    | unitSource => exact Assignment.evaluate_identity (assignment vertex base meaning) (vertex_read vertex base meaning)
    | unitTarget => exact Assignment.evaluate_identity (assignment vertex base meaning) (vertex_read vertex base meaning)
    | compositionSource => exact Assignment.evaluate_compose (assignment vertex base meaning) _ _ (first_read vertex base meaning) rfl
    | compositionTarget => exact Assignment.evaluate_compose (assignment vertex base meaning) _ _ (second_read vertex base meaning) rfl

theorem local_admission_iff :
    EquationExtension.Satisfies (signature vertex) (endpointDeclaration vertex)
      (assignment vertex base meaning) (realization vertex base meaning) ↔ EndpointLaws vertex base meaning := by
  have diagram (origin : ULift.{k} EndpointLaw) :
      (Interpretation.functor (assignment vertex base meaning) (realization vertex base meaning)).map
          (GeneratedCategory.classOf (endpointDeclaration vertex origin).left) =
        (Interpretation.functor (assignment vertex base meaning) (realization vertex base meaning)).map
          (GeneratedCategory.classOf (endpointDeclaration vertex origin).right) ↔
      leftValue vertex base meaning origin = rightValue vertex base meaning origin := by
    have left := Interpretation.functor_complete_readout (assignment vertex base meaning)
      (realization vertex base meaning) (endpointDeclaration vertex origin).left
    have right := Interpretation.functor_complete_readout (assignment vertex base meaning)
      (realization vertex base meaning) (endpointDeclaration vertex origin).right
    have leftSame := Option.some.inj (left.symm.trans (left_read vertex base meaning origin))
    have rightSame := Option.some.inj (right.symm.trans (right_read vertex base meaning origin))
    constructor
    · intro same
      exact leftSame.symm.trans ((congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) same).trans rightSame)
    · intro same
      exact ArrowValue.arrow_injective (leftSame.trans (same.trans rightSame.symm))
  constructor
  · intro admitted
    exact ⟨ArrowValue.arrow_injective ((diagram (ULift.up EndpointLaw.unitSource)).mp (admitted _)),
      ArrowValue.arrow_injective ((diagram (ULift.up EndpointLaw.unitTarget)).mp (admitted _)),
      ArrowValue.arrow_injective ((diagram (ULift.up EndpointLaw.compositionSource)).mp (admitted _)),
      ArrowValue.arrow_injective ((diagram (ULift.up EndpointLaw.compositionTarget)).mp (admitted _))⟩
  · intro laws origin
    apply (diagram origin).mpr
    cases origin with
    | up origin =>
      cases origin with
      | unitSource => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.unitSource
      | unitTarget => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.unitTarget
      | compositionSource => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.compositionSource
      | compositionTarget => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.compositionTarget

theorem endpoint_realization_iff :
    Realization (endpointSignature vertex) (EquationExtension.extendAssignment (assignment vertex base meaning)) ↔
      EndpointLaws vertex base meaning :=
  (EquationExtension.realization_iff_satisfaction (signature vertex) (endpointDeclaration vertex)
    (assignment vertex base meaning) (realization vertex base meaning)).trans
      (local_admission_iff vertex base meaning)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Meaning
