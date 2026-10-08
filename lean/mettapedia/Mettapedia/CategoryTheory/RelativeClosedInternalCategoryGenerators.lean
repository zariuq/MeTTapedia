import Mettapedia.CategoryTheory.RelativeClosedSyntaxPresentedPullbacks
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationExtension

/-!
# Independent generators for a category of operational evidence

The vertex object is supplied by the original theory. A new evidence object
has source, target and unit operations. Composition is declared on the actual
raw matching-endpoint object, not on all pairs of evidence. The four endpoint
diagrams are independent authored equations, and their generated inclusion
retains every original base object and arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory

universe k

inductive Operation where
  | source
  | target
  | unit
  | composition

inductive EndpointLaw where
  | unitSource
  | unitTarget
  | compositionSource
  | compositionTarget

def symbols : Symbols.{k} where
  ObjectName := ULift.{k} Unit
  ArrowName := ULift.{k} Operation
  EquationName := ULift.{k} Empty

variable {C : Type k} [Category.{k} C] (vertex : C)

def edgeCode : ObjectCode C symbols := .name (ULift.up ())

def endpointBefore : ArrowCode C symbols :=
  .compose (.first edgeCode edgeCode) (.name (ULift.up Operation.target))

def endpointAfter : ArrowCode C symbols :=
  .compose (.second edgeCode edgeCode) (.name (ULift.up Operation.source))

def composableCode : ObjectCode C symbols :=
  .equalizer (.product edgeCode edgeCode) (.base vertex) endpointBefore endpointAfter

def sourceCode : Operation → ObjectCode C symbols
  | .source => edgeCode
  | .target => edgeCode
  | .unit => .base vertex
  | .composition => composableCode vertex

def targetCode : Operation → ObjectCode C symbols
  | .source => .base vertex
  | .target => .base vertex
  | .unit => edgeCode
  | .composition => edgeCode

def operationRank : ULift.{k} Operation → Nat
  | ⟨.composition⟩ => 2
  | _ => 1

def signature : Signature (C := C) (symbols := symbols) where
  objectRank _ := 0
  arrowRank := operationRank
  source origin := sourceCode vertex origin.down
  target origin := targetCode vertex origin.down
  source_before origin := by
    cases origin with
    | up origin =>
      cases origin <;> simp [sourceCode, composableCode, endpointBefore, endpointAfter,
        edgeCode, ObjectCode.before, ArrowCode.before, operationRank]
  target_before origin := by
    cases origin with
    | up origin =>
      cases origin <;> simp [targetCode, edgeCode, ObjectCode.before, operationRank]
  equationRank origin := origin.down.elim
  equationSource origin := origin.down.elim
  equationTarget origin := origin.down.elim
  left origin := origin.down.elim
  right origin := origin.down.elim
  equation_before origin := origin.down.elim

def vertexObject : Object (signature vertex) := baseObject (signature vertex) vertex

def edgeObject : Object (signature vertex) :=
  ⟨edgeCode, ⟨.objectName (signature := signature vertex) (ULift.up ())⟩⟩

def source : RawHom (edgeObject vertex) (vertexObject vertex) :=
  ⟨.name (ULift.up Operation.source),
    ⟨.arrowName (signature := signature vertex) (ULift.up Operation.source)
      (edgeObject vertex).formed.some (vertexObject vertex).formed.some⟩⟩

def target : RawHom (edgeObject vertex) (vertexObject vertex) :=
  ⟨.name (ULift.up Operation.target),
    ⟨.arrowName (signature := signature vertex) (ULift.up Operation.target)
      (edgeObject vertex).formed.some (vertexObject vertex).formed.some⟩⟩

def unit : RawHom (vertexObject vertex) (edgeObject vertex) :=
  ⟨.name (ULift.up Operation.unit),
    ⟨.arrowName (signature := signature vertex) (ULift.up Operation.unit)
      (vertexObject vertex).formed.some (edgeObject vertex).formed.some⟩⟩

def composable : Object (signature vertex) := PresentedPullback.object (target vertex) (source vertex)

def first : RawHom (composable vertex) (edgeObject vertex) :=
  PresentedPullback.first (target vertex) (source vertex)

def second : RawHom (composable vertex) (edgeObject vertex) :=
  PresentedPullback.second (target vertex) (source vertex)

def composition : RawHom (composable vertex) (edgeObject vertex) :=
  ⟨.name (ULift.up Operation.composition),
    ⟨.arrowName (signature := signature vertex) (ULift.up Operation.composition)
      (composable vertex).formed.some (edgeObject vertex).formed.some⟩⟩

def headers : HeaderFormation (signature vertex) where
  source origin := by
    cases origin with
    | up origin =>
      cases origin with
      | source => exact (edgeObject vertex).formed.some
      | target => exact (edgeObject vertex).formed.some
      | unit => exact (vertexObject vertex).formed.some
      | composition => exact (composable vertex).formed.some
  target origin := by
    cases origin with
    | up origin =>
      cases origin with
      | source => exact (vertexObject vertex).formed.some
      | target => exact (vertexObject vertex).formed.some
      | unit => exact (edgeObject vertex).formed.some
      | composition => exact (edgeObject vertex).formed.some
  left origin := origin.down.elim
  right origin := origin.down.elim

def endpointDeclaration (origin : ULift.{k} EndpointLaw) : EquationExtension.Declaration (signature vertex) :=
  match origin.down with
  | .unitSource => ⟨vertexObject vertex, vertexObject vertex,
      (unit vertex).compose (source vertex), RawHom.identity (vertexObject vertex)⟩
  | .unitTarget => ⟨vertexObject vertex, vertexObject vertex,
      (unit vertex).compose (target vertex), RawHom.identity (vertexObject vertex)⟩
  | .compositionSource => ⟨composable vertex, vertexObject vertex,
      (composition vertex).compose (source vertex), (first vertex).compose (source vertex)⟩
  | .compositionTarget => ⟨composable vertex, vertexObject vertex,
      (composition vertex).compose (target vertex), (second vertex).compose (target vertex)⟩

def endpointSignature := EquationExtension.extend (signature vertex) (endpointDeclaration vertex)

def endpointHeaders : HeaderFormation (endpointSignature vertex) :=
  EquationExtension.headers (signature vertex) (endpointDeclaration vertex) (headers vertex)

def endpointInclusion : SignatureMap (signature vertex) (endpointSignature vertex) :=
  EquationExtension.inclusion (signature vertex) (endpointDeclaration vertex)

theorem endpoint_equation (origin : ULift.{k} EndpointLaw) :
    (endpointInclusion vertex).functor.map (classOf (endpointDeclaration vertex origin).left) =
      (endpointInclusion vertex).functor.map (classOf (endpointDeclaration vertex origin).right) :=
  EquationExtension.equation_class (signature vertex) (endpointDeclaration vertex) origin

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory
