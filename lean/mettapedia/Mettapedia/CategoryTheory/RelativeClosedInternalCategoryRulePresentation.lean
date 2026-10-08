import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryNativeCategory
import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowExtension
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapComposition

/-!
# Operational evidence generators with independently authored endpoints

Each declaration supplies a complete premise object and two independently
typed program readouts. A fresh operator returns an edge from that object.
Two new, independently parallel equations prescribe its source and target.
The original operational category survives through the actual generated
inclusions. No selected-edge product, target behavior or semantic rule
satisfaction is assumed as part of the syntax construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RulePresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type k} [Category.{k} D] {symbols : Symbols.{k}}
variable {original : Signature (C := D) (symbols := symbols)}
variable (categoryMap : SignatureMap (Presentation.signature vertex) original)

structure Declaration where
  domain : Object original
  before : RawHom domain (NativeCategory.vertexObject vertex categoryMap)
  after : RawHom domain (NativeCategory.vertexObject vertex categoryMap)

variable {Index : Type k} (declarations : Index → Declaration vertex categoryMap)

def arrowDeclaration (origin : Index) : ArrowExtension.Declaration original :=
  ⟨(declarations origin).domain,NativeCategory.edgeObject vertex categoryMap⟩

def arrowSignature := ArrowExtension.extend original (arrowDeclaration vertex categoryMap declarations)

def arrowInclusion := ArrowExtension.inclusion original (arrowDeclaration vertex categoryMap declarations)

def arrowHeaders (formed : HeaderFormation original) : HeaderFormation (arrowSignature vertex categoryMap declarations) :=
  ArrowExtension.headers original (arrowDeclaration vertex categoryMap declarations) formed

def primitive (origin : Index) := ArrowExtension.generator original (arrowDeclaration vertex categoryMap declarations) origin

def domain (origin : Index) := (arrowInclusion vertex categoryMap declarations).object (declarations origin).domain

def vertices := (arrowInclusion vertex categoryMap declarations).object (NativeCategory.vertexObject vertex categoryMap)

def evidence := (arrowInclusion vertex categoryMap declarations).object (NativeCategory.edgeObject vertex categoryMap)

def source : RawHom (evidence vertex categoryMap declarations) (vertices vertex categoryMap declarations) :=
  (arrowInclusion vertex categoryMap declarations).rawArrow (NativeCategory.source vertex categoryMap)

def target : RawHom (evidence vertex categoryMap declarations) (vertices vertex categoryMap declarations) :=
  (arrowInclusion vertex categoryMap declarations).rawArrow (NativeCategory.target vertex categoryMap)

def endpointDeclaration (origin : Index × Bool) : EquationExtension.Declaration (arrowSignature vertex categoryMap declarations) :=
  match origin.2 with
  | false => ⟨domain vertex categoryMap declarations origin.1,vertices vertex categoryMap declarations,
      (primitive vertex categoryMap declarations origin.1).compose (source vertex categoryMap declarations),
      (arrowInclusion vertex categoryMap declarations).rawArrow (declarations origin.1).before⟩
  | true => ⟨domain vertex categoryMap declarations origin.1,vertices vertex categoryMap declarations,
      (primitive vertex categoryMap declarations origin.1).compose (target vertex categoryMap declarations),
      (arrowInclusion vertex categoryMap declarations).rawArrow (declarations origin.1).after⟩

def signature := EquationExtension.extend (arrowSignature vertex categoryMap declarations)
  (endpointDeclaration vertex categoryMap declarations)

def equationInclusion := EquationExtension.inclusion (arrowSignature vertex categoryMap declarations)
  (endpointDeclaration vertex categoryMap declarations)

def headers (formed : HeaderFormation original) : HeaderFormation (signature vertex categoryMap declarations) :=
  EquationExtension.headers (arrowSignature vertex categoryMap declarations)
    (endpointDeclaration vertex categoryMap declarations) (arrowHeaders vertex categoryMap declarations formed)

def ruleDomain (origin : Index) := (equationInclusion vertex categoryMap declarations).object
  (domain vertex categoryMap declarations origin)

def programs := (equationInclusion vertex categoryMap declarations).object (vertices vertex categoryMap declarations)

def edges := (equationInclusion vertex categoryMap declarations).object (evidence vertex categoryMap declarations)

def fire (origin : Index) : RawHom (ruleDomain vertex categoryMap declarations origin) (edges vertex categoryMap declarations) :=
  (equationInclusion vertex categoryMap declarations).rawArrow (primitive vertex categoryMap declarations origin)

def edgeSource : RawHom (edges vertex categoryMap declarations) (programs vertex categoryMap declarations) :=
  (equationInclusion vertex categoryMap declarations).rawArrow (source vertex categoryMap declarations)

def edgeTarget : RawHom (edges vertex categoryMap declarations) (programs vertex categoryMap declarations) :=
  (equationInclusion vertex categoryMap declarations).rawArrow (target vertex categoryMap declarations)

def before (origin : Index) : RawHom (ruleDomain vertex categoryMap declarations origin) (programs vertex categoryMap declarations) :=
  (equationInclusion vertex categoryMap declarations).rawArrow
    ((arrowInclusion vertex categoryMap declarations).rawArrow (declarations origin).before)

def after (origin : Index) : RawHom (ruleDomain vertex categoryMap declarations origin) (programs vertex categoryMap declarations) :=
  (equationInclusion vertex categoryMap declarations).rawArrow
    ((arrowInclusion vertex categoryMap declarations).rawArrow (declarations origin).after)

theorem fire_source (origin : Index) :
    classOf ((fire vertex categoryMap declarations origin).compose (edgeSource vertex categoryMap declarations)) =
      classOf (before vertex categoryMap declarations origin) :=
  EquationExtension.equation_class (arrowSignature vertex categoryMap declarations)
    (endpointDeclaration vertex categoryMap declarations) (origin,false)

theorem fire_target (origin : Index) :
    classOf ((fire vertex categoryMap declarations origin).compose (edgeTarget vertex categoryMap declarations)) =
      classOf (after vertex categoryMap declarations origin) :=
  EquationExtension.equation_class (arrowSignature vertex categoryMap declarations)
    (endpointDeclaration vertex categoryMap declarations) (origin,true)

def extendedCategoryMap := (categoryMap.compose (arrowInclusion vertex categoryMap declarations)).compose
  (equationInclusion vertex categoryMap declarations)

def category : InternalCategory (Object (signature vertex categoryMap declarations)) :=
  NativeCategory.category vertex (extendedCategoryMap vertex categoryMap declarations)

theorem programs_read : programs vertex categoryMap declarations =
    (category vertex categoryMap declarations).vertex :=
  (congrArg (equationInclusion vertex categoryMap declarations).object
    (SignatureMap.object_compose categoryMap (arrowInclusion vertex categoryMap declarations)
      ((Presentation.inclusion vertex).object (Endpoints.vertexObject vertex)))).trans
    (SignatureMap.object_compose (categoryMap.compose (arrowInclusion vertex categoryMap declarations))
      (equationInclusion vertex categoryMap declarations)
      ((Presentation.inclusion vertex).object (Endpoints.vertexObject vertex)))

theorem edges_read : edges vertex categoryMap declarations =
    (category vertex categoryMap declarations).edge :=
  (congrArg (equationInclusion vertex categoryMap declarations).object
    (SignatureMap.object_compose categoryMap (arrowInclusion vertex categoryMap declarations)
      ((Presentation.inclusion vertex).object (Endpoints.edgeObject vertex)))).trans
    (SignatureMap.object_compose (categoryMap.compose (arrowInclusion vertex categoryMap declarations))
      (equationInclusion vertex categoryMap declarations)
      ((Presentation.inclusion vertex).object (Endpoints.edgeObject vertex)))

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RulePresentation
