import Mettapedia.CategoryTheory.RelativeClosedPositionedModalExpressions
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicDiagrams
import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowExtension
import Mettapedia.CategoryTheory.RelativeClosedProgramReductionExtension
import Mettapedia.GSLT.Core.PositionedRewriteModal

/-!
# Generated modalities retain actual rewrite and position declarations

Every selected generator retains an authored rule, its chosen position and
the actual pullback of complete rely instances. The empty-context possibility
generator uses the theory's actual event endpoints. Independent raw defining
equations tie these names to complete-input logical expressions. All header
and equation trees are earned by the generic arrow and equation extensions.

The final native base inclusion preserves finite limits, canonical function
objects, the designated program and the complete reduction relation. This
presentation is not yet the full modal/structural free-forgetful adjunction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open RelativeClosedPredicateLogic RelativeClosedPositionedModal
open ProgramReductionTheory AuthoredClosedTheory

universe k
variable (source : Theory.{k,k})

structure Selection where
  rule : Rule source
  position : Position rule
  assignments : source.closed.Obj
  forget : rule.parameters ⟶ assignments
  focus : assignments ⟶ position.carrier
  square : IsPullback forget (prod.lift position.relies position.focus) focus prod.snd

def Selection.frame (selected : Selection source) : PositionedRewriteModal.Frame selected.rule :=
  PositionedRewriteModal.Frame.ofPosition selected.rule selected.position selected.forget selected.focus selected.square

variable {Index : Type k} (selected : Index → Selection source)

def domain : Option Index → Object (RelativeClosedPredicateLogic.signature (C := source.closed.Obj))
  | none => RelativeClosedPredicateLogic.power source.program
  | some origin => product (RelativeClosedPredicateLogic.power (selected origin).frame.assay)
      (RelativeClosedPredicateLogic.power ((selected origin).frame.assay ⨯ source.program))

def codomain : Option Index → Object (RelativeClosedPredicateLogic.signature (C := source.closed.Obj))
  | none => RelativeClosedPredicateLogic.power source.program
  | some origin => RelativeClosedPredicateLogic.power (selected origin).frame.carrier

def expression (origin : Option Index) : RawHom (domain source selected origin) (codomain source selected origin) :=
  match origin with
  | none => possibilityRaw source.source source.target
  | some origin => modalityRaw (selected origin).frame.forget (selected origin).frame.focus
      (selected origin).frame.instantiate (selected origin).frame.outgoing

def arrowDeclaration (origin : Option Index) :
    ArrowExtension.Declaration (lawfulSignature (C := source.closed.Obj)) where
  source := equationInclusion.object (domain source selected origin)
  target := equationInclusion.object (codomain source selected origin)

def arrowSignature := ArrowExtension.extend (lawfulSignature (C := source.closed.Obj))
  (arrowDeclaration source selected)

def arrowInclusion := ArrowExtension.inclusion (lawfulSignature (C := source.closed.Obj))
  (arrowDeclaration source selected)

def primitive (origin : Option Index) :=
  ArrowExtension.generator (lawfulSignature (C := source.closed.Obj)) (arrowDeclaration source selected) origin

def definingDeclaration (origin : Option Index) : EquationExtension.Declaration (arrowSignature source selected) where
  source := (arrowInclusion source selected).object (arrowDeclaration source selected origin).source
  target := (arrowInclusion source selected).object (arrowDeclaration source selected origin).target
  left := primitive source selected origin
  right := (arrowInclusion source selected).rawArrow (equationInclusion.rawArrow (expression source selected origin))

def signature := EquationExtension.extend (arrowSignature source selected) (definingDeclaration source selected)

def definingInclusion := EquationExtension.inclusion (arrowSignature source selected) (definingDeclaration source selected)

def headers : HeaderFormation (signature source selected) :=
  EquationExtension.headers (arrowSignature source selected) (definingDeclaration source selected)
    (ArrowExtension.headers (lawfulSignature (C := source.closed.Obj)) (arrowDeclaration source selected)
      (lawfulHeaders (C := source.closed.Obj)))

def namedRaw (origin : Option Index) :=
  (definingInclusion source selected).rawArrow (primitive source selected origin)

def definedRaw (origin : Option Index) :=
  (definingInclusion source selected).rawArrow (definingDeclaration source selected origin).right

theorem named_operation_is_the_authored_expression (origin : Option Index) :
    classOf (namedRaw source selected origin) = classOf (definedRaw source selected origin) :=
  EquationExtension.equation_class (arrowSignature source selected) (definingDeclaration source selected) origin

def nativeSignature := BaseExtension.extend (signature source selected)

def nativeHeaders : HeaderFormation (nativeSignature source selected) :=
  BaseExtension.headers (signature source selected) (headers source selected)

def nativeInclusion := BaseExtension.originalMap (signature source selected)

def nativeTheory : LambdaTheory.{k,k} := LambdaTheory.ofCategory (Object (nativeSignature source selected))

def baseMap : LambdaTheoryMap source.closed (nativeTheory source selected) where
  functor := baseFunctor (nativeSignature source selected)
  preservesFiniteLimits := BaseExtension.extended_base_preservesFiniteLimits (signature source selected)
  preservesExponentials := BaseExtension.extended_base_closed (signature source selected)

def programTheory : Theory.{k,k} :=
  RelativeClosedProgramReductionExtension.mappedTheory source (nativeTheory source selected) (baseMap source selected)

def programInclusion : Map source (programTheory source selected) :=
  RelativeClosedProgramReductionExtension.mapping source (nativeTheory source selected) (baseMap source selected)

def authoredRule (origin : Index) : Rule (programTheory source selected) :=
  Rule.transport (programInclusion source selected) (selected origin).rule

def authoredPosition (origin : Index) : Position (authoredRule source selected origin) :=
  Position.transport (programInclusion source selected) (selected origin).position

theorem complete_rule_action (origin : Index) :
    (authoredRule source selected origin).action = (baseMap source selected).functor.map
      (selected origin).rule.action ≫ (programInclusion source selected).reduction := rfl

theorem complete_selected_rely (origin : Index) :
    (authoredPosition source selected origin).relies = (baseMap source selected).functor.map
      (selected origin).position.relies := rfl

theorem complete_selected_focus (origin : Index) :
    (authoredPosition source selected origin).focus = (baseMap source selected).functor.map
      (selected origin).position.focus := rfl

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalPresentation
