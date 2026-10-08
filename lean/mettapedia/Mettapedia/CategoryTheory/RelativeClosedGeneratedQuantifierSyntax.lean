import Mettapedia.CategoryTheory.RelativeClosedRawConstructions
import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowExtension

/-!
# Predicate function syntax at arbitrary generated objects and arrows

A supplied proposition object and conjunction are actual formed raw syntax,
independent of target semantic carriers. A route retains its entire typed
raw arrow, including any generated declarations in its body or endpoints.
Power inputs, precomposition and ordered-pair equalizers are constructed
from the existing raw product, evaluation and abstraction operations.
Translation retains the same proposition and conjunction declarations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory

universe k l
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))

structure PredicateSyntax where
  proposition : Object original
  conjunction : RawHom (product proposition proposition) proposition

structure Route where
  source : Object original
  target : Object original
  arrow : RawHom source target

variable {original}

def PredicateSyntax.power (language : PredicateSyntax original) (value : Object original) : Object original :=
  exponentialObject value language.proposition

def PredicateSyntax.meet {context : Object original} (language : PredicateSyntax original)
    (first second : RawHom context language.proposition) : RawHom context language.proposition :=
  (RawHom.pair first second).compose language.conjunction

def PredicateSyntax.powerConjunction (language : PredicateSyntax original) (value : Object original) :
    RawHom (product (language.power value) (language.power value)) (language.power value) :=
  let context := product (language.power value) (language.power value)
  let firstFunction := (RawHom.first context value).compose (RawHom.first (language.power value) (language.power value))
  let secondFunction := (RawHom.first context value).compose (RawHom.second (language.power value) (language.power value))
  let atFirst := (RawHom.pair firstFunction (RawHom.second context value)).compose
    (RawHom.evaluation value language.proposition)
  let atSecond := (RawHom.pair secondFunction (RawHom.second context value)).compose
    (RawHom.evaluation value language.proposition)
  RawHom.abstract (language.meet atFirst atSecond)

def PredicateSyntax.powerMeet {context : Object original} (language : PredicateSyntax original)
    (value : Object original) (first second : RawHom context (language.power value)) :
    RawHom context (language.power value) :=
  (RawHom.pair first second).compose (language.powerConjunction value)

def PredicateSyntax.precomposition (language : PredicateSyntax original) (route : Route original) :
    RawHom (language.power route.target) (language.power route.source) :=
  let input := RawHom.pair (RawHom.first (language.power route.target) route.source)
    ((RawHom.second (language.power route.target) route.source).compose route.arrow)
  RawHom.abstract (input.compose (RawHom.evaluation route.target language.proposition))

def PredicateSyntax.orderedFunctions (language : PredicateSyntax original) (value : Object original) : Object original :=
  PresentedEqualizer.object (language.powerConjunction value) (RawHom.first (language.power value) (language.power value))

def PredicateSyntax.smaller (language : PredicateSyntax original) (value : Object original) :
    RawHom (language.orderedFunctions value) (language.power value) :=
  (RawHom.inclusion (language.powerConjunction value) (RawHom.first (language.power value) (language.power value))).compose
    (RawHom.first (language.power value) (language.power value))

def PredicateSyntax.larger (language : PredicateSyntax original) (value : Object original) :
    RawHom (language.orderedFunctions value) (language.power value) :=
  (RawHom.inclusion (language.powerConjunction value) (RawHom.first (language.power value) (language.power value))).compose
    (RawHom.second (language.power value) (language.power value))

variable {E : Type l} [Category.{l} E] {nextSymbols : Symbols.{l}}
variable {next : Signature (C := E) (symbols := nextSymbols)}

def PredicateSyntax.translate (language : PredicateSyntax original) (mapping : SignatureMap original next) :
    PredicateSyntax next where
  proposition := mapping.object language.proposition
  conjunction := mapping.rawArrow language.conjunction

def Route.translate (route : Route original) (mapping : SignatureMap original next) : Route next where
  source := mapping.object route.source
  target := mapping.object route.target
  arrow := mapping.rawArrow route.arrow

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier
