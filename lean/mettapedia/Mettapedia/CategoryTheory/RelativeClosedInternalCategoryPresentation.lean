import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryEndpoints
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionPreservation

/-!
# The actual finite closed presentation of operational categories

The endpoint theory admits both unit insertion arrows and both complete
three-edge associations. Their independently typed equations give the final
category presentation. Native base comparisons preserve the original
theory's finite limits and function objects; category laws do not equate
an operational edge with its source or target program.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Presentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory
open Endpoints

universe k

inductive Law where
  | leftUnit
  | rightUnit
  | associativity

variable {C : Type k} [Category.{k} C] (vertex : C)

def associateLeft : RawHom (triples vertex) (Endpoints.edgeObject vertex) :=
  (PresentedPullback.lift (Endpoints.target vertex) (Endpoints.source vertex)
    (composedFirst vertex) (tripleLast vertex) (composed_first_matching vertex)).compose
      (Endpoints.composition vertex)

def associateRight : RawHom (triples vertex) (Endpoints.edgeObject vertex) :=
  (PresentedPullback.lift (Endpoints.target vertex) (Endpoints.source vertex)
    (tripleFirst vertex) (composedLast vertex) (composed_last_matching vertex)).compose
      (Endpoints.composition vertex)

def declaration (origin : ULift.{k} Law) : EquationExtension.Declaration (endpointSignature vertex) :=
  match origin.down with
  | .leftUnit => ⟨Endpoints.edgeObject vertex, Endpoints.edgeObject vertex,
      (unitLeftPair vertex).compose (Endpoints.composition vertex), RawHom.identity (Endpoints.edgeObject vertex)⟩
  | .rightUnit => ⟨Endpoints.edgeObject vertex, Endpoints.edgeObject vertex,
      (unitRightPair vertex).compose (Endpoints.composition vertex), RawHom.identity (Endpoints.edgeObject vertex)⟩
  | .associativity => ⟨triples vertex, Endpoints.edgeObject vertex, associateLeft vertex, associateRight vertex⟩

def signature := EquationExtension.extend (endpointSignature vertex) (declaration vertex)

def headers : HeaderFormation (signature vertex) :=
  EquationExtension.headers (endpointSignature vertex) (declaration vertex) (endpointHeaders vertex)

def inclusion : SignatureMap (endpointSignature vertex) (signature vertex) :=
  EquationExtension.inclusion (endpointSignature vertex) (declaration vertex)

theorem declared_law (origin : ULift.{k} Law) :
    (inclusion vertex).functor.map (classOf (declaration vertex origin).left) =
      (inclusion vertex).functor.map (classOf (declaration vertex origin).right) :=
  EquationExtension.equation_class (endpointSignature vertex) (declaration vertex) origin

def nativeSignature [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :=
  BaseExtension.extend (signature vertex)

def nativeHeaders [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :
    HeaderFormation (nativeSignature vertex) := BaseExtension.headers (signature vertex) (headers vertex)

def nativeInclusion [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :=
  BaseExtension.originalMap (signature vertex)

def theory [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :
    Mettapedia.GSLT.Core.LambdaTheory.{k,k} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object (nativeSignature vertex))

def baseMap [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :
    Mettapedia.GSLT.Core.LambdaTheoryMap (Mettapedia.GSLT.Core.LambdaTheory.ofCategory C) (theory vertex) where
  functor := baseFunctor (nativeSignature vertex)
  preservesFiniteLimits := BaseExtension.extended_base_preservesFiniteLimits (signature vertex)
  preservesExponentials := BaseExtension.extended_base_closed (signature vertex)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Presentation
