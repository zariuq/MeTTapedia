import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierSyntax
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationExtension

/-!
# Quantifier declarations indexed by every supplied typed generated arrow

The index retains each whole raw source, target and arrow. Existing modal,
structural and equalizer expressions are therefore eligible alongside base
arrows. The proposition name is carried through the actual inclusions rather
than replaced by a new proposition object. Each new quantifier has three
authored finite diagrams: monotonicity on the actual ordered-input equalizer,
and its adjunction unit and counit. Subsequent interpretation and iteration
must earn semantic admission and closure; this is their independent grammar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))

inductive Kind where
  | universal
  | existential

structure Operation where
  kind : Kind
  route : Route original

variable (language : PredicateSyntax original)

def arrowDeclaration (origin : Operation original) : ArrowExtension.Declaration original where
  source := language.power origin.route.source
  target := language.power origin.route.target

def arrowSignature := ArrowExtension.extend original (arrowDeclaration original language)
def arrowInclusion := ArrowExtension.inclusion original (arrowDeclaration original language)
def argumentSyntax := language.translate (arrowInclusion original language)
def mappedRoute (route : Route original) := route.translate (arrowInclusion original language)

def quantifier (kind : Kind) (route : Route original) :
    RawHom ((argumentSyntax original language).power (mappedRoute original language route).source)
      ((argumentSyntax original language).power (mappedRoute original language route).target) :=
  ArrowExtension.generator original (arrowDeclaration original language) ⟨kind, route⟩

private def parallelPair {first second : Object (arrowSignature original language)}
    (before after : RawHom first second) : EquationExtension.Declaration (arrowSignature original language) :=
  ⟨first, second, before, after⟩

def monotonicityPair (kind : Kind) (route : Route original) :
    EquationExtension.Declaration (arrowSignature original language) :=
  let input := argumentSyntax original language
  let actual := mappedRoute original language route
  let first := (input.smaller actual.source).compose (quantifier original language kind route)
  let second := (input.larger actual.source).compose (quantifier original language kind route)
  parallelPair original language (input.powerMeet actual.target second first) first

def universalUnitPair (route : Route original) : EquationExtension.Declaration (arrowSignature original language) :=
  let input := argumentSyntax original language
  let actual := mappedRoute original language route
  let complete := (input.precomposition actual).compose (quantifier original language .universal route)
  let given := RawHom.identity (input.power actual.target)
  parallelPair original language (input.powerMeet actual.target complete given) given

def universalCounitPair (route : Route original) : EquationExtension.Declaration (arrowSignature original language) :=
  let input := argumentSyntax original language
  let actual := mappedRoute original language route
  let complete := (quantifier original language .universal route).compose (input.precomposition actual)
  parallelPair original language (input.powerMeet actual.source (RawHom.identity (input.power actual.source)) complete) complete

def existentialUnitPair (route : Route original) : EquationExtension.Declaration (arrowSignature original language) :=
  let input := argumentSyntax original language
  let actual := mappedRoute original language route
  let complete := (quantifier original language .existential route).compose (input.precomposition actual)
  let given := RawHom.identity (input.power actual.source)
  parallelPair original language (input.powerMeet actual.source complete given) given

def existentialCounitPair (route : Route original) : EquationExtension.Declaration (arrowSignature original language) :=
  let input := argumentSyntax original language
  let actual := mappedRoute original language route
  let complete := (input.precomposition actual).compose (quantifier original language .existential route)
  parallelPair original language (input.powerMeet actual.target (RawHom.identity (input.power actual.target)) complete) complete

inductive Diagram where
  | universalMonotonicity
  | universalUnit
  | universalCounit
  | existentialMonotonicity
  | existentialUnit
  | existentialCounit

structure Law where
  diagram : Diagram
  route : Route original

def declaration (origin : Law original) : EquationExtension.Declaration (arrowSignature original language) :=
  match origin.diagram with
  | .universalMonotonicity => monotonicityPair original language .universal origin.route
  | .universalUnit => universalUnitPair original language origin.route
  | .universalCounit => universalCounitPair original language origin.route
  | .existentialMonotonicity => monotonicityPair original language .existential origin.route
  | .existentialUnit => existentialUnitPair original language origin.route
  | .existentialCounit => existentialCounitPair original language origin.route

def signature := EquationExtension.extend (arrowSignature original language) (declaration original language)
def equationInclusion := EquationExtension.inclusion (arrowSignature original language) (declaration original language)
def retainedSyntax := (argumentSyntax original language).translate (equationInclusion original language)

def headers (formed : HeaderFormation original) : HeaderFormation (signature original language) :=
  EquationExtension.headers (arrowSignature original language) (declaration original language)
    (ArrowExtension.headers original (arrowDeclaration original language) formed)

def named (kind : Kind) (route : Route original) :=
  (equationInclusion original language).rawArrow (quantifier original language kind route)

theorem declared_law (origin : Law original) :
    classOf ((equationInclusion original language).rawArrow (declaration original language origin).left) =
      classOf ((equationInclusion original language).rawArrow (declaration original language origin).right) :=
  EquationExtension.equation_class (arrowSignature original language) (declaration original language) origin

theorem proposition_name_is_retained : (retainedSyntax original language).proposition =
    (equationInclusion original language).object
      ((arrowInclusion original language).object language.proposition) := rfl

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier
