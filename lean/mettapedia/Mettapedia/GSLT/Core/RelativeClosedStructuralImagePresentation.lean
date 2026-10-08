import Mettapedia.GSLT.Core.RelativeClosedPositionedModalPresentation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxDefinitionExtension

/-!
# Authored structural constructor images in the generated modal theory

Each structural name retains its actual source-theory argument object and
constructor arrow. Its raw defining expression is existential transport
along that arrow, using the proposition object already present in the
predicate and positioned-modal syntax. New origins remain independently
indexed even when their defining arrows agree in the theory.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImagePresentation

open _root_.CategoryTheory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory

universe k
variable (source : Theory.{k,k}) {Index : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)

structure Constructor where
  arguments : source.closed.Obj
  term : arguments ⟶ source.program

variable {Origins : Type k} (constructors : Origins → Constructor source)

def logicalInclusion := RelativeClosedPredicateLogic.equationInclusion.compose
  ((RelativeClosedPositionedModalPresentation.arrowInclusion source selected).compose
    (RelativeClosedPositionedModalPresentation.definingInclusion source selected))

def declaration (origin : Origins) :
    DefinitionExtension.Declaration (RelativeClosedPositionedModalPresentation.signature source selected) where
  source := (logicalInclusion source selected).object
    (RelativeClosedPredicateLogic.power (constructors origin).arguments)
  target := (logicalInclusion source selected).object (RelativeClosedPredicateLogic.power source.program)
  body := (logicalInclusion source selected).rawArrow
    (RelativeClosedPredicateLogic.existentialRaw (constructors origin).term)

def signature := DefinitionExtension.signature
  (RelativeClosedPositionedModalPresentation.signature source selected) (declaration source selected constructors)

def inclusion := DefinitionExtension.inclusion
  (RelativeClosedPositionedModalPresentation.signature source selected) (declaration source selected constructors)

def headers : HeaderFormation (signature source selected constructors) :=
  DefinitionExtension.headers (RelativeClosedPositionedModalPresentation.signature source selected)
    (declaration source selected constructors) (RelativeClosedPositionedModalPresentation.headers source selected)

def namedRaw (origin : Origins) := DefinitionExtension.namedRaw
  (RelativeClosedPositionedModalPresentation.signature source selected) (declaration source selected constructors) origin

def definedRaw (origin : Origins) := DefinitionExtension.definedRaw
  (RelativeClosedPositionedModalPresentation.signature source selected) (declaration source selected constructors) origin

theorem named_operation_is_constructor_image (origin : Origins) :
    classOf (namedRaw source selected constructors origin) =
      classOf (definedRaw source selected constructors origin) :=
  DefinitionExtension.named_eq_body (RelativeClosedPositionedModalPresentation.signature source selected)
    (declaration source selected constructors) origin

def nativeSignature := BaseExtension.extend (signature source selected constructors)

def nativeHeaders : HeaderFormation (nativeSignature source selected constructors) :=
  BaseExtension.headers (signature source selected constructors) (headers source selected constructors)

def nativeInclusion := BaseExtension.originalMap (signature source selected constructors)

def nativeTheory : LambdaTheory.{k,k} :=
  LambdaTheory.ofCategory (Object (nativeSignature source selected constructors))

def baseMap : LambdaTheoryMap source.closed (nativeTheory source selected constructors) where
  functor := baseFunctor (nativeSignature source selected constructors)
  preservesFiniteLimits := BaseExtension.extended_base_preservesFiniteLimits (signature source selected constructors)
  preservesExponentials := BaseExtension.extended_base_closed (signature source selected constructors)

def programTheory : Theory.{k,k} := RelativeClosedProgramReductionExtension.mappedTheory source
  (nativeTheory source selected constructors) (baseMap source selected constructors)

def programInclusion : Map source (programTheory source selected constructors) :=
  RelativeClosedProgramReductionExtension.mapping source (nativeTheory source selected constructors)
    (baseMap source selected constructors)

end Mettapedia.GSLT.Core.RelativeClosedStructuralImagePresentation
