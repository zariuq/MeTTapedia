import Mettapedia.GSLT.LanguageDef.TptpFofNnfShiftLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofPrenexLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Authored canonical-NNF to prenex normalization

This transformation produces the structural `TptpFofPrenex:Form` carrier.
Its recursive operations are ordinary authored rewrites:

* matrix shifting delegates variable movement to the existing term-shift
  requests;
* form shifting traverses a quantifier prefix and increments the cutoff;
* prefix combination pulls quantifiers across conjunction or disjunction; and
* prenex normalization recursively transforms canonical NNF and invokes that
  combination.

No native prenexing, substitution, or formula traversal primitive is used.
The transformation language retains the complete reusable NNF shift language
as a structural source prefix and adds the prenex target plus the four staged
operations above.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofPrenexNormalizationLanguageDef

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def ctor (label category : String) (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

def mkRule (name : String) (context : List (String × String))
    (premises : List Premise) (left right : Pattern) : RewriteRule := {
  name
  typeContext := typed context
  premises
  left
  right
}

def congruence (source target : Pattern) : Premise :=
  .congruence source target

/-! ## Shared canonical source and shift constructors -/

def indexZero : Pattern :=
  TptpFofNnfShiftLanguageDef.indexZero
def indexSucc (index : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.indexSucc index

def indexRequest (cutoff source : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.indexRequest cutoff source
def indexResult (cutoff source target : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.indexResult cutoff source target

def termRequest (cutoff source : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.termRequest cutoff source
def termResult (cutoff source target : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.termResult cutoff source target
def termsRequest (cutoff source : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.termsRequest cutoff source
def termsResult (cutoff source target : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.termsResult cutoff source target

def sourceTermVariable (index : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.termVariable index
def sourceTermFunction (function arguments : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.termFunction function arguments
def sourceTermsNil : Pattern :=
  TptpFofNnfShiftLanguageDef.termsNil
def sourceTermsCons (head tail : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.termsCons head tail

def sourceVerum : Pattern := TptpFofNnfShiftLanguageDef.verum
def sourceFalsum : Pattern := TptpFofNnfShiftLanguageDef.falsum
def sourcePositive (relation arguments : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.positive relation arguments
def sourceNegative (relation arguments : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.negative relation arguments
def sourceEqual (left right : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.equal left right
def sourceNotEqual (left right : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.notEqual left right
def sourceAnd (left right : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.and left right
def sourceOr (left right : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.or left right
def sourceAll (body : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.all body
def sourceEx (body : Pattern) : Pattern :=
  TptpFofNnfShiftLanguageDef.ex body

/-! ## Structural target constructors -/

def matrixVerum : Pattern := a "tptp-fof-prenex:matrix-verum"
def matrixFalsum : Pattern := a "tptp-fof-prenex:matrix-falsum"
def matrixPositive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-positive" [relation, arguments]
def matrixNegative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-negative" [relation, arguments]
def matrixEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-equal" [left, right]
def matrixNotEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-not-equal" [left, right]
def matrixAnd (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-and" [left, right]
def matrixOr (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-or" [left, right]

def formMatrix (body : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix" [body]
def formAll (body : Pattern) : Pattern :=
  a "tptp-fof-prenex:all" [body]
def formEx (body : Pattern) : Pattern :=
  a "tptp-fof-prenex:ex" [body]

/-! ## Operation constructors -/

def connectiveAnd : Pattern := a "tptp-fof-prenex-normalize:and"
def connectiveOr : Pattern := a "tptp-fof-prenex-normalize:or"

def matrixShiftRequest (cutoff source : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:matrix-shift-request" [cutoff, source]
def matrixShiftResult (cutoff source target : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:matrix-shift-result"
    [cutoff, source, target]

def formShiftRequest (cutoff source : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:form-shift-request" [cutoff, source]
def formShiftResult (cutoff source target : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:form-shift-result"
    [cutoff, source, target]

def combineRequest (connective left right : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:combine-request"
    [connective, left, right]
def combineResult (connective left right target : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:combine-result"
    [connective, left, right, target]

def prenexRequest (source : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:request" [source]
def prenexResult (source target : Pattern) : Pattern :=
  a "tptp-fof-prenex-normalize:result" [source, target]

/-! ## Authored rewrite rows -/

def matrixShiftRewrites : List RewriteRule := [
  mkRule "tptp-fof-prenex-normalize:shift-matrix-verum"
    [("cutoff", "TptpResolvedFof:Index")] []
    (matrixShiftRequest (v "cutoff") matrixVerum)
    (matrixShiftResult (v "cutoff") matrixVerum matrixVerum),
  mkRule "tptp-fof-prenex-normalize:shift-matrix-falsum"
    [("cutoff", "TptpResolvedFof:Index")] []
    (matrixShiftRequest (v "cutoff") matrixFalsum)
    (matrixShiftResult (v "cutoff") matrixFalsum matrixFalsum),
  mkRule "tptp-fof-prenex-normalize:shift-matrix-positive"
    [("cutoff", "TptpResolvedFof:Index"),
     ("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpResolvedFof:Terms")]
    [congruence
      (termsRequest (v "cutoff") (v "arguments"))
      (termsResult (v "cutoff") (v "arguments") (v "targetArguments"))]
    (matrixShiftRequest (v "cutoff")
      (matrixPositive (v "relation") (v "arguments")))
    (matrixShiftResult (v "cutoff")
      (matrixPositive (v "relation") (v "arguments"))
      (matrixPositive (v "relation") (v "targetArguments"))),
  mkRule "tptp-fof-prenex-normalize:shift-matrix-negative"
    [("cutoff", "TptpResolvedFof:Index"),
     ("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpResolvedFof:Terms")]
    [congruence
      (termsRequest (v "cutoff") (v "arguments"))
      (termsResult (v "cutoff") (v "arguments") (v "targetArguments"))]
    (matrixShiftRequest (v "cutoff")
      (matrixNegative (v "relation") (v "arguments")))
    (matrixShiftResult (v "cutoff")
      (matrixNegative (v "relation") (v "arguments"))
      (matrixNegative (v "relation") (v "targetArguments"))),
  mkRule "tptp-fof-prenex-normalize:shift-matrix-equal"
    [("cutoff", "TptpResolvedFof:Index"),
     ("left", "TptpResolvedFof:Term"),
     ("right", "TptpResolvedFof:Term"),
     ("targetLeft", "TptpResolvedFof:Term"),
     ("targetRight", "TptpResolvedFof:Term")]
    [congruence
      (termRequest (v "cutoff") (v "left"))
      (termResult (v "cutoff") (v "left") (v "targetLeft")),
     congruence
      (termRequest (v "cutoff") (v "right"))
      (termResult (v "cutoff") (v "right") (v "targetRight"))]
    (matrixShiftRequest (v "cutoff")
      (matrixEqual (v "left") (v "right")))
    (matrixShiftResult (v "cutoff")
      (matrixEqual (v "left") (v "right"))
      (matrixEqual (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-prenex-normalize:shift-matrix-not-equal"
    [("cutoff", "TptpResolvedFof:Index"),
     ("left", "TptpResolvedFof:Term"),
     ("right", "TptpResolvedFof:Term"),
     ("targetLeft", "TptpResolvedFof:Term"),
     ("targetRight", "TptpResolvedFof:Term")]
    [congruence
      (termRequest (v "cutoff") (v "left"))
      (termResult (v "cutoff") (v "left") (v "targetLeft")),
     congruence
      (termRequest (v "cutoff") (v "right"))
      (termResult (v "cutoff") (v "right") (v "targetRight"))]
    (matrixShiftRequest (v "cutoff")
      (matrixNotEqual (v "left") (v "right")))
    (matrixShiftResult (v "cutoff")
      (matrixNotEqual (v "left") (v "right"))
      (matrixNotEqual (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-prenex-normalize:shift-matrix-and"
    [("cutoff", "TptpResolvedFof:Index"),
     ("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix"),
     ("targetLeft", "TptpFofPrenex:Matrix"),
     ("targetRight", "TptpFofPrenex:Matrix")]
    [congruence
      (matrixShiftRequest (v "cutoff") (v "left"))
      (matrixShiftResult (v "cutoff") (v "left") (v "targetLeft")),
     congruence
      (matrixShiftRequest (v "cutoff") (v "right"))
      (matrixShiftResult (v "cutoff") (v "right") (v "targetRight"))]
    (matrixShiftRequest (v "cutoff")
      (matrixAnd (v "left") (v "right")))
    (matrixShiftResult (v "cutoff")
      (matrixAnd (v "left") (v "right"))
      (matrixAnd (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-prenex-normalize:shift-matrix-or"
    [("cutoff", "TptpResolvedFof:Index"),
     ("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix"),
     ("targetLeft", "TptpFofPrenex:Matrix"),
     ("targetRight", "TptpFofPrenex:Matrix")]
    [congruence
      (matrixShiftRequest (v "cutoff") (v "left"))
      (matrixShiftResult (v "cutoff") (v "left") (v "targetLeft")),
     congruence
      (matrixShiftRequest (v "cutoff") (v "right"))
      (matrixShiftResult (v "cutoff") (v "right") (v "targetRight"))]
    (matrixShiftRequest (v "cutoff")
      (matrixOr (v "left") (v "right")))
    (matrixShiftResult (v "cutoff")
      (matrixOr (v "left") (v "right"))
      (matrixOr (v "targetLeft") (v "targetRight")))
]

def formShiftRewrites : List RewriteRule := [
  mkRule "tptp-fof-prenex-normalize:shift-form-matrix"
    [("cutoff", "TptpResolvedFof:Index"),
     ("body", "TptpFofPrenex:Matrix"),
     ("targetBody", "TptpFofPrenex:Matrix")]
    [congruence
      (matrixShiftRequest (v "cutoff") (v "body"))
      (matrixShiftResult (v "cutoff") (v "body") (v "targetBody"))]
    (formShiftRequest (v "cutoff") (formMatrix (v "body")))
    (formShiftResult (v "cutoff") (formMatrix (v "body"))
      (formMatrix (v "targetBody"))),
  mkRule "tptp-fof-prenex-normalize:shift-form-all"
    [("cutoff", "TptpResolvedFof:Index"),
     ("body", "TptpFofPrenex:Form"),
     ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (formShiftRequest (indexSucc (v "cutoff")) (v "body"))
      (formShiftResult (indexSucc (v "cutoff")) (v "body")
        (v "targetBody"))]
    (formShiftRequest (v "cutoff") (formAll (v "body")))
    (formShiftResult (v "cutoff") (formAll (v "body"))
      (formAll (v "targetBody"))),
  mkRule "tptp-fof-prenex-normalize:shift-form-ex"
    [("cutoff", "TptpResolvedFof:Index"),
     ("body", "TptpFofPrenex:Form"),
     ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (formShiftRequest (indexSucc (v "cutoff")) (v "body"))
      (formShiftResult (indexSucc (v "cutoff")) (v "body")
        (v "targetBody"))]
    (formShiftRequest (v "cutoff") (formEx (v "body")))
    (formShiftResult (v "cutoff") (formEx (v "body"))
      (formEx (v "targetBody")))
]

def combineRewrites : List RewriteRule := [
  mkRule "tptp-fof-prenex-normalize:combine-left-all"
    [("connective", "TptpFofPrenexNormalize:Connective"),
     ("leftBody", "TptpFofPrenex:Form"),
     ("right", "TptpFofPrenex:Form"),
     ("shiftedRight", "TptpFofPrenex:Form"),
     ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (formShiftRequest indexZero (v "right"))
      (formShiftResult indexZero (v "right") (v "shiftedRight")),
     congruence
      (combineRequest (v "connective") (v "leftBody") (v "shiftedRight"))
      (combineResult (v "connective") (v "leftBody") (v "shiftedRight")
        (v "targetBody"))]
    (combineRequest (v "connective") (formAll (v "leftBody")) (v "right"))
    (combineResult (v "connective") (formAll (v "leftBody")) (v "right")
      (formAll (v "targetBody"))),
  mkRule "tptp-fof-prenex-normalize:combine-left-ex"
    [("connective", "TptpFofPrenexNormalize:Connective"),
     ("leftBody", "TptpFofPrenex:Form"),
     ("right", "TptpFofPrenex:Form"),
     ("shiftedRight", "TptpFofPrenex:Form"),
     ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (formShiftRequest indexZero (v "right"))
      (formShiftResult indexZero (v "right") (v "shiftedRight")),
     congruence
      (combineRequest (v "connective") (v "leftBody") (v "shiftedRight"))
      (combineResult (v "connective") (v "leftBody") (v "shiftedRight")
        (v "targetBody"))]
    (combineRequest (v "connective") (formEx (v "leftBody")) (v "right"))
    (combineResult (v "connective") (formEx (v "leftBody")) (v "right")
      (formEx (v "targetBody"))),
  mkRule "tptp-fof-prenex-normalize:combine-right-all"
    [("connective", "TptpFofPrenexNormalize:Connective"),
     ("leftBody", "TptpFofPrenex:Matrix"),
     ("rightBody", "TptpFofPrenex:Form"),
     ("shiftedLeft", "TptpFofPrenex:Form"),
     ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (formShiftRequest indexZero (formMatrix (v "leftBody")))
      (formShiftResult indexZero (formMatrix (v "leftBody"))
        (v "shiftedLeft")),
     congruence
      (combineRequest (v "connective") (v "shiftedLeft") (v "rightBody"))
      (combineResult (v "connective") (v "shiftedLeft") (v "rightBody")
        (v "targetBody"))]
    (combineRequest (v "connective") (formMatrix (v "leftBody"))
      (formAll (v "rightBody")))
    (combineResult (v "connective") (formMatrix (v "leftBody"))
      (formAll (v "rightBody")) (formAll (v "targetBody"))),
  mkRule "tptp-fof-prenex-normalize:combine-right-ex"
    [("connective", "TptpFofPrenexNormalize:Connective"),
     ("leftBody", "TptpFofPrenex:Matrix"),
     ("rightBody", "TptpFofPrenex:Form"),
     ("shiftedLeft", "TptpFofPrenex:Form"),
     ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (formShiftRequest indexZero (formMatrix (v "leftBody")))
      (formShiftResult indexZero (formMatrix (v "leftBody"))
        (v "shiftedLeft")),
     congruence
      (combineRequest (v "connective") (v "shiftedLeft") (v "rightBody"))
      (combineResult (v "connective") (v "shiftedLeft") (v "rightBody")
        (v "targetBody"))]
    (combineRequest (v "connective") (formMatrix (v "leftBody"))
      (formEx (v "rightBody")))
    (combineResult (v "connective") (formMatrix (v "leftBody"))
      (formEx (v "rightBody")) (formEx (v "targetBody"))),
  mkRule "tptp-fof-prenex-normalize:combine-matrices-and"
    [("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix")] []
    (combineRequest connectiveAnd (formMatrix (v "left"))
      (formMatrix (v "right")))
    (combineResult connectiveAnd (formMatrix (v "left"))
      (formMatrix (v "right"))
      (formMatrix (matrixAnd (v "left") (v "right")))),
  mkRule "tptp-fof-prenex-normalize:combine-matrices-or"
    [("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix")] []
    (combineRequest connectiveOr (formMatrix (v "left"))
      (formMatrix (v "right")))
    (combineResult connectiveOr (formMatrix (v "left"))
      (formMatrix (v "right"))
      (formMatrix (matrixOr (v "left") (v "right"))))
]

def prenexRewrites : List RewriteRule := [
  mkRule "tptp-fof-prenex-normalize:verum" [] []
    (prenexRequest sourceVerum)
    (prenexResult sourceVerum (formMatrix matrixVerum)),
  mkRule "tptp-fof-prenex-normalize:falsum" [] []
    (prenexRequest sourceFalsum)
    (prenexResult sourceFalsum (formMatrix matrixFalsum)),
  mkRule "tptp-fof-prenex-normalize:positive"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")] []
    (prenexRequest (sourcePositive (v "relation") (v "arguments")))
    (prenexResult (sourcePositive (v "relation") (v "arguments"))
      (formMatrix (matrixPositive (v "relation") (v "arguments")))),
  mkRule "tptp-fof-prenex-normalize:negative"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")] []
    (prenexRequest (sourceNegative (v "relation") (v "arguments")))
    (prenexResult (sourceNegative (v "relation") (v "arguments"))
      (formMatrix (matrixNegative (v "relation") (v "arguments")))),
  mkRule "tptp-fof-prenex-normalize:equal"
    [("left", "TptpResolvedFof:Term"),
     ("right", "TptpResolvedFof:Term")] []
    (prenexRequest (sourceEqual (v "left") (v "right")))
    (prenexResult (sourceEqual (v "left") (v "right"))
      (formMatrix (matrixEqual (v "left") (v "right")))),
  mkRule "tptp-fof-prenex-normalize:not-equal"
    [("left", "TptpResolvedFof:Term"),
     ("right", "TptpResolvedFof:Term")] []
    (prenexRequest (sourceNotEqual (v "left") (v "right")))
    (prenexResult (sourceNotEqual (v "left") (v "right"))
      (formMatrix (matrixNotEqual (v "left") (v "right")))),
  mkRule "tptp-fof-prenex-normalize:and"
    [("left", "NNFFormula"), ("right", "NNFFormula"),
     ("leftTarget", "TptpFofPrenex:Form"),
     ("rightTarget", "TptpFofPrenex:Form"),
     ("target", "TptpFofPrenex:Form")]
    [congruence
      (prenexRequest (v "left"))
      (prenexResult (v "left") (v "leftTarget")),
     congruence
      (prenexRequest (v "right"))
      (prenexResult (v "right") (v "rightTarget")),
     congruence
      (combineRequest connectiveAnd (v "leftTarget") (v "rightTarget"))
      (combineResult connectiveAnd (v "leftTarget") (v "rightTarget")
        (v "target"))]
    (prenexRequest (sourceAnd (v "left") (v "right")))
    (prenexResult (sourceAnd (v "left") (v "right")) (v "target")),
  mkRule "tptp-fof-prenex-normalize:or"
    [("left", "NNFFormula"), ("right", "NNFFormula"),
     ("leftTarget", "TptpFofPrenex:Form"),
     ("rightTarget", "TptpFofPrenex:Form"),
     ("target", "TptpFofPrenex:Form")]
    [congruence
      (prenexRequest (v "left"))
      (prenexResult (v "left") (v "leftTarget")),
     congruence
      (prenexRequest (v "right"))
      (prenexResult (v "right") (v "rightTarget")),
     congruence
      (combineRequest connectiveOr (v "leftTarget") (v "rightTarget"))
      (combineResult connectiveOr (v "leftTarget") (v "rightTarget")
        (v "target"))]
    (prenexRequest (sourceOr (v "left") (v "right")))
    (prenexResult (sourceOr (v "left") (v "right")) (v "target")),
  mkRule "tptp-fof-prenex-normalize:all"
    [("body", "NNFFormula"), ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (prenexRequest (v "body"))
      (prenexResult (v "body") (v "targetBody"))]
    (prenexRequest (sourceAll (v "body")))
    (prenexResult (sourceAll (v "body")) (formAll (v "targetBody"))),
  mkRule "tptp-fof-prenex-normalize:ex"
    [("body", "NNFFormula"), ("targetBody", "TptpFofPrenex:Form")]
    [congruence
      (prenexRequest (v "body"))
      (prenexResult (v "body") (v "targetBody"))]
    (prenexRequest (sourceEx (v "body")))
    (prenexResult (sourceEx (v "body")) (formEx (v "targetBody")))
]

def authoredRewrites : List RewriteRule :=
  matrixShiftRewrites ++ formShiftRewrites ++ combineRewrites ++ prenexRewrites

def connectiveTerms : List GrammarRule := [
  ctor "tptp-fof-prenex-normalize:and"
    "TptpFofPrenexNormalize:Connective" [],
  ctor "tptp-fof-prenex-normalize:or"
    "TptpFofPrenexNormalize:Connective" []
]

def operationTerms : List GrammarRule := [
  ctor "tptp-fof-prenex-normalize:matrix-shift-request"
    "TptpFofPrenexNormalize:MatrixShiftResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpFofPrenex:Matrix")] (some .rewrite),
  ctor "tptp-fof-prenex-normalize:matrix-shift-result"
    "TptpFofPrenexNormalize:MatrixShiftResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpFofPrenex:Matrix"),
     ("target", "TptpFofPrenex:Matrix")],
  ctor "tptp-fof-prenex-normalize:form-shift-request"
    "TptpFofPrenexNormalize:FormShiftResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpFofPrenex:Form")] (some .rewrite),
  ctor "tptp-fof-prenex-normalize:form-shift-result"
    "TptpFofPrenexNormalize:FormShiftResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpFofPrenex:Form"),
     ("target", "TptpFofPrenex:Form")],
  ctor "tptp-fof-prenex-normalize:combine-request"
    "TptpFofPrenexNormalize:CombineResult"
    [("connective", "TptpFofPrenexNormalize:Connective"),
     ("left", "TptpFofPrenex:Form"),
     ("right", "TptpFofPrenex:Form")] (some .rewrite),
  ctor "tptp-fof-prenex-normalize:combine-result"
    "TptpFofPrenexNormalize:CombineResult"
    [("connective", "TptpFofPrenexNormalize:Connective"),
     ("left", "TptpFofPrenex:Form"),
     ("right", "TptpFofPrenex:Form"),
     ("target", "TptpFofPrenex:Form")],
  ctor "tptp-fof-prenex-normalize:request"
    "TptpFofPrenexNormalize:Result"
    [("source", "NNFFormula")] (some .rewrite),
  ctor "tptp-fof-prenex-normalize:result"
    "TptpFofPrenexNormalize:Result"
    [("source", "NNFFormula"), ("target", "TptpFofPrenex:Form")]
]

def language : LanguageDef := {
  name := "TptpFofPrenexNormalization"
  types := TptpFofNnfShiftLanguageDef.language.types ++ [
    ("TptpFofPrenex:Matrix" : TypeDecl),
    ("TptpFofPrenex:Form" : TypeDecl),
    ("TptpFofPrenexNormalize:Connective" : TypeDecl),
    ("TptpFofPrenexNormalize:MatrixShiftResult" : TypeDecl),
    ("TptpFofPrenexNormalize:FormShiftResult" : TypeDecl),
    ("TptpFofPrenexNormalize:CombineResult" : TypeDecl),
    ("TptpFofPrenexNormalize:Result" : TypeDecl)]
  terms := TptpFofNnfShiftLanguageDef.language.terms ++
    TptpFofPrenexLanguageDef.matrixTerms ++
    TptpFofPrenexLanguageDef.prenexTerms ++
    connectiveTerms ++ operationTerms
  equations := []
  rewrites := TptpFofNnfShiftLanguageDef.rewrites ++ authoredRewrites
}

theorem authored_rewrite_count : authoredRewrites.length = 27 := by
  decide +kernel

theorem rewrite_count : language.rewrites.length = 45 := by
  decide +kernel

@[simp] theorem language_rewrites :
    language.rewrites = TptpFofNnfShiftLanguageDef.rewrites ++
      authoredRewrites := rfl

@[simp] private theorem language_typeNames : language.typeNames = [
    "String", "TptpFofSymbol:FunctionHead",
    "TptpFofSymbol:PredicateHead", "TptpResolvedFof:Index", "TptpResolvedFof:Term",
    "TptpResolvedFof:Terms", "TptpResolvedFof:Formula", "NNFFormula",
    "TptpFofNnfShift:IndexResult", "TptpFofNnfShift:TermResult",
    "TptpFofNnfShift:TermsResult", "TptpFofNnfShift:FormulaResult",
    "TptpFofPrenex:Matrix", "TptpFofPrenex:Form",
    "TptpFofPrenexNormalize:Connective",
    "TptpFofPrenexNormalize:MatrixShiftResult",
    "TptpFofPrenexNormalize:FormShiftResult",
    "TptpFofPrenexNormalize:CombineResult",
    "TptpFofPrenexNormalize:Result"] := by
  rfl

@[simp] private theorem language_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures language = [
      ("tptp-fof-symbol:function-plain", 1),
      ("tptp-fof-symbol:function-defined", 1),
      ("tptp-fof-symbol:function-system", 1),
      ("tptp-fof-symbol:function-integer", 1),
      ("tptp-fof-symbol:function-rational", 1),
      ("tptp-fof-symbol:function-real", 1),
      ("tptp-fof-symbol:function-distinct-object", 1),
      ("tptp-fof-symbol:predicate-plain", 1),
      ("tptp-fof-symbol:predicate-defined", 1),
      ("tptp-fof-symbol:predicate-system", 1),
      ("tptp-fof-resolved:index-zero", 0),
      ("tptp-fof-resolved:index-succ", 1),
      ("tptp-fof-resolved:term-variable", 1),
      ("tptp-fof-resolved:term-function", 2),
      ("tptp-fof-resolved:terms-nil", 0),
      ("tptp-fof-resolved:terms-cons", 2),
      ("tptp-fof-resolved:verum", 0),
      ("tptp-fof-resolved:falsum", 0),
      ("tptp-fof-resolved:predicate", 2),
      ("tptp-fof-resolved:equal", 2),
      ("tptp-fof-resolved:not", 1),
      ("tptp-fof-resolved:and", 2),
      ("tptp-fof-resolved:or", 2),
      ("tptp-fof-resolved:iff", 2),
      ("tptp-fof-resolved:implies", 2),
      ("tptp-fof-resolved:reverse-implies", 2),
      ("tptp-fof-resolved:xor", 2),
      ("tptp-fof-resolved:nor", 2),
      ("tptp-fof-resolved:nand", 2),
      ("tptp-fof-resolved:all", 1),
      ("tptp-fof-resolved:ex", 1),
      ("tptp-fof-nnf:verum", 0),
      ("tptp-fof-nnf:falsum", 0),
      ("tptp-fof-nnf:positive", 2),
      ("tptp-fof-nnf:negative", 2),
      ("tptp-fof-nnf:equal", 2),
      ("tptp-fof-nnf:not-equal", 2),
      ("tptp-fof-nnf:and", 2),
      ("tptp-fof-nnf:or", 2),
      ("tptp-fof-nnf:all", 1),
      ("tptp-fof-nnf:ex", 1),
      ("tptp-fof-nnf-shift:index-request", 2),
      ("tptp-fof-nnf-shift:index-result", 3),
      ("tptp-fof-nnf-shift:term-request", 2),
      ("tptp-fof-nnf-shift:term-result", 3),
      ("tptp-fof-nnf-shift:terms-request", 2),
      ("tptp-fof-nnf-shift:terms-result", 3),
      ("tptp-fof-nnf-shift:formula-request", 2),
      ("tptp-fof-nnf-shift:formula-result", 3),
      ("tptp-fof-prenex:matrix-verum", 0),
      ("tptp-fof-prenex:matrix-falsum", 0),
      ("tptp-fof-prenex:matrix-positive", 2),
      ("tptp-fof-prenex:matrix-negative", 2),
      ("tptp-fof-prenex:matrix-equal", 2),
      ("tptp-fof-prenex:matrix-not-equal", 2),
      ("tptp-fof-prenex:matrix-and", 2),
      ("tptp-fof-prenex:matrix-or", 2),
      ("tptp-fof-prenex:matrix", 1),
      ("tptp-fof-prenex:all", 1),
      ("tptp-fof-prenex:ex", 1),
      ("tptp-fof-prenex-normalize:and", 0),
      ("tptp-fof-prenex-normalize:or", 0),
      ("tptp-fof-prenex-normalize:matrix-shift-request", 2),
      ("tptp-fof-prenex-normalize:matrix-shift-result", 3),
      ("tptp-fof-prenex-normalize:form-shift-request", 2),
      ("tptp-fof-prenex-normalize:form-shift-result", 3),
      ("tptp-fof-prenex-normalize:combine-request", 3),
      ("tptp-fof-prenex-normalize:combine-result", 4),
      ("tptp-fof-prenex-normalize:request", 1),
      ("tptp-fof-prenex-normalize:result", 2)] := by
  rfl

@[simp] private theorem language_constructorLabels :
    RewriteValidationCertificate.constructorLabels language = [
      "tptp-fof-symbol:function-plain",
      "tptp-fof-symbol:function-defined",
      "tptp-fof-symbol:function-system",
      "tptp-fof-symbol:function-integer",
      "tptp-fof-symbol:function-rational",
      "tptp-fof-symbol:function-real",
      "tptp-fof-symbol:function-distinct-object",
      "tptp-fof-symbol:predicate-plain",
      "tptp-fof-symbol:predicate-defined",
      "tptp-fof-symbol:predicate-system",
      "tptp-fof-resolved:index-zero", "tptp-fof-resolved:index-succ",
      "tptp-fof-resolved:term-variable", "tptp-fof-resolved:term-function",
      "tptp-fof-resolved:terms-nil", "tptp-fof-resolved:terms-cons",
      "tptp-fof-resolved:verum", "tptp-fof-resolved:falsum",
      "tptp-fof-resolved:predicate", "tptp-fof-resolved:equal",
      "tptp-fof-resolved:not", "tptp-fof-resolved:and",
      "tptp-fof-resolved:or", "tptp-fof-resolved:iff",
      "tptp-fof-resolved:implies", "tptp-fof-resolved:reverse-implies",
      "tptp-fof-resolved:xor", "tptp-fof-resolved:nor",
      "tptp-fof-resolved:nand", "tptp-fof-resolved:all",
      "tptp-fof-resolved:ex", "tptp-fof-nnf:verum",
      "tptp-fof-nnf:falsum", "tptp-fof-nnf:positive",
      "tptp-fof-nnf:negative", "tptp-fof-nnf:equal",
      "tptp-fof-nnf:not-equal", "tptp-fof-nnf:and",
      "tptp-fof-nnf:or", "tptp-fof-nnf:all", "tptp-fof-nnf:ex",
      "tptp-fof-nnf-shift:index-request",
      "tptp-fof-nnf-shift:index-result",
      "tptp-fof-nnf-shift:term-request",
      "tptp-fof-nnf-shift:term-result",
      "tptp-fof-nnf-shift:terms-request",
      "tptp-fof-nnf-shift:terms-result",
      "tptp-fof-nnf-shift:formula-request",
      "tptp-fof-nnf-shift:formula-result",
      "tptp-fof-prenex:matrix-verum", "tptp-fof-prenex:matrix-falsum",
      "tptp-fof-prenex:matrix-positive", "tptp-fof-prenex:matrix-negative",
      "tptp-fof-prenex:matrix-equal", "tptp-fof-prenex:matrix-not-equal",
      "tptp-fof-prenex:matrix-and", "tptp-fof-prenex:matrix-or",
      "tptp-fof-prenex:matrix", "tptp-fof-prenex:all",
      "tptp-fof-prenex:ex", "tptp-fof-prenex-normalize:and",
      "tptp-fof-prenex-normalize:or",
      "tptp-fof-prenex-normalize:matrix-shift-request",
      "tptp-fof-prenex-normalize:matrix-shift-result",
      "tptp-fof-prenex-normalize:form-shift-request",
      "tptp-fof-prenex-normalize:form-shift-result",
      "tptp-fof-prenex-normalize:combine-request",
      "tptp-fof-prenex-normalize:combine-result",
      "tptp-fof-prenex-normalize:request",
      "tptp-fof-prenex-normalize:result"] := by
  rfl

local macro "certify_authored_row" : tactic =>
  `(tactic|
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      language_typeNames, language_constructorSignatures,
      language_constructorLabels, typed, mkRule, congruence,
      authoredRewrites, matrixShiftRewrites, formShiftRewrites,
      combineRewrites, prenexRewrites, indexZero, indexSucc,
      termRequest, termResult, termsRequest, termsResult,
      sourceVerum, sourceFalsum, sourcePositive, sourceNegative,
      sourceEqual, sourceNotEqual, sourceAnd, sourceOr, sourceAll, sourceEx,
      matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
      matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
      formMatrix, formAll, formEx, connectiveAnd, connectiveOr,
      matrixShiftRequest, matrixShiftResult, formShiftRequest,
      formShiftResult, combineRequest, combineResult, prenexRequest,
      prenexResult,
      TptpFofNnfShiftLanguageDef.indexRequest,
      TptpFofNnfShiftLanguageDef.indexResult,
      TptpFofNnfShiftLanguageDef.termRequest,
      TptpFofNnfShiftLanguageDef.termResult,
      TptpFofNnfShiftLanguageDef.termsRequest,
      TptpFofNnfShiftLanguageDef.termsResult,
      TptpFofNnfShiftLanguageDef.formulaRequest,
      TptpFofNnfShiftLanguageDef.formulaResult,
      TptpFofNnfShiftLanguageDef.indexZero,
      TptpFofNnfShiftLanguageDef.indexSucc,
      TptpFofNnfShiftLanguageDef.termVariable,
      TptpFofNnfShiftLanguageDef.termFunction,
      TptpFofNnfShiftLanguageDef.termsNil,
      TptpFofNnfShiftLanguageDef.termsCons,
      TptpFofNnfShiftLanguageDef.verum,
      TptpFofNnfShiftLanguageDef.falsum,
      TptpFofNnfShiftLanguageDef.positive,
      TptpFofNnfShiftLanguageDef.negative,
      TptpFofNnfShiftLanguageDef.equal,
      TptpFofNnfShiftLanguageDef.notEqual,
      TptpFofNnfShiftLanguageDef.and,
      TptpFofNnfShiftLanguageDef.or,
      TptpFofNnfShiftLanguageDef.all,
      TptpFofNnfShiftLanguageDef.ex,
      TptpFofNnfShiftLanguageDef.a, TptpFofNnfShiftLanguageDef.v,
      a, v, LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])

local macro "certify_source_row" : tactic =>
  `(tactic|
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      language_typeNames, language_constructorSignatures,
      language_constructorLabels,
      TptpFofNnfShiftLanguageDef.rewrites,
      TptpFofNnfShiftLanguageDef.typed, TptpFofNnfShiftLanguageDef.mkRule,
      TptpFofNnfShiftLanguageDef.congruence,
      TptpFofNnfShiftLanguageDef.indexRequest,
      TptpFofNnfShiftLanguageDef.indexResult,
      TptpFofNnfShiftLanguageDef.termRequest,
      TptpFofNnfShiftLanguageDef.termResult,
      TptpFofNnfShiftLanguageDef.termsRequest,
      TptpFofNnfShiftLanguageDef.termsResult,
      TptpFofNnfShiftLanguageDef.formulaRequest,
      TptpFofNnfShiftLanguageDef.formulaResult,
      TptpFofNnfShiftLanguageDef.indexZero,
      TptpFofNnfShiftLanguageDef.indexSucc,
      TptpFofNnfShiftLanguageDef.termVariable,
      TptpFofNnfShiftLanguageDef.termFunction,
      TptpFofNnfShiftLanguageDef.termsNil,
      TptpFofNnfShiftLanguageDef.termsCons,
      TptpFofNnfShiftLanguageDef.verum,
      TptpFofNnfShiftLanguageDef.falsum,
      TptpFofNnfShiftLanguageDef.positive,
      TptpFofNnfShiftLanguageDef.negative,
      TptpFofNnfShiftLanguageDef.equal,
      TptpFofNnfShiftLanguageDef.notEqual,
      TptpFofNnfShiftLanguageDef.and,
      TptpFofNnfShiftLanguageDef.or,
      TptpFofNnfShiftLanguageDef.all,
      TptpFofNnfShiftLanguageDef.ex,
      TptpFofNnfShiftLanguageDef.a, TptpFofNnfShiftLanguageDef.v,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  decide +kernel

private theorem source00_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[0] = true := by certify_source_row
private theorem source01_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[1] = true := by certify_source_row
private theorem source02_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[2] = true := by certify_source_row
private theorem source03_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[3] = true := by certify_source_row
private theorem source04_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[4] = true := by certify_source_row
private theorem source05_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[5] = true := by certify_source_row
private theorem source06_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[6] = true := by certify_source_row
private theorem source07_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[7] = true := by certify_source_row
private theorem source08_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[8] = true := by certify_source_row
private theorem source09_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[9] = true := by certify_source_row
private theorem source10_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[10] = true := by certify_source_row
private theorem source11_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[11] = true := by certify_source_row
private theorem source12_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[12] = true := by certify_source_row
private theorem source13_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[13] = true := by certify_source_row
private theorem source14_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[14] = true := by certify_source_row
private theorem source15_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[15] = true := by certify_source_row
private theorem source16_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[16] = true := by certify_source_row
private theorem source17_checked :
    RewriteValidationCertificate.check language
      TptpFofNnfShiftLanguageDef.rewrites[17] = true := by certify_source_row

private theorem authored00_checked :
    RewriteValidationCertificate.check language authoredRewrites[0] = true := by
  certify_authored_row
private theorem authored01_checked :
    RewriteValidationCertificate.check language authoredRewrites[1] = true := by
  certify_authored_row
private theorem authored02_checked :
    RewriteValidationCertificate.check language authoredRewrites[2] = true := by
  certify_authored_row
private theorem authored03_checked :
    RewriteValidationCertificate.check language authoredRewrites[3] = true := by
  certify_authored_row
private theorem authored04_checked :
    RewriteValidationCertificate.check language authoredRewrites[4] = true := by
  certify_authored_row
private theorem authored05_checked :
    RewriteValidationCertificate.check language authoredRewrites[5] = true := by
  certify_authored_row
private theorem authored06_checked :
    RewriteValidationCertificate.check language authoredRewrites[6] = true := by
  certify_authored_row
private theorem authored07_checked :
    RewriteValidationCertificate.check language authoredRewrites[7] = true := by
  certify_authored_row
private theorem authored08_checked :
    RewriteValidationCertificate.check language authoredRewrites[8] = true := by
  certify_authored_row
private theorem authored09_checked :
    RewriteValidationCertificate.check language authoredRewrites[9] = true := by
  certify_authored_row
private theorem authored10_checked :
    RewriteValidationCertificate.check language authoredRewrites[10] = true := by
  certify_authored_row
private theorem authored11_checked :
    RewriteValidationCertificate.check language authoredRewrites[11] = true := by
  certify_authored_row
private theorem authored12_checked :
    RewriteValidationCertificate.check language authoredRewrites[12] = true := by
  certify_authored_row
private theorem authored13_checked :
    RewriteValidationCertificate.check language authoredRewrites[13] = true := by
  certify_authored_row
private theorem authored14_checked :
    RewriteValidationCertificate.check language authoredRewrites[14] = true := by
  certify_authored_row
private theorem authored15_checked :
    RewriteValidationCertificate.check language authoredRewrites[15] = true := by
  certify_authored_row
private theorem authored16_checked :
    RewriteValidationCertificate.check language authoredRewrites[16] = true := by
  certify_authored_row
private theorem authored17_checked :
    RewriteValidationCertificate.check language authoredRewrites[17] = true := by
  certify_authored_row
private theorem authored18_checked :
    RewriteValidationCertificate.check language authoredRewrites[18] = true := by
  certify_authored_row
private theorem authored19_checked :
    RewriteValidationCertificate.check language authoredRewrites[19] = true := by
  certify_authored_row
private theorem authored20_checked :
    RewriteValidationCertificate.check language authoredRewrites[20] = true := by
  certify_authored_row
private theorem authored21_checked :
    RewriteValidationCertificate.check language authoredRewrites[21] = true := by
  certify_authored_row
private theorem authored22_checked :
    RewriteValidationCertificate.check language authoredRewrites[22] = true := by
  certify_authored_row
private theorem authored23_checked :
    RewriteValidationCertificate.check language authoredRewrites[23] = true := by
  certify_authored_row
private theorem authored24_checked :
    RewriteValidationCertificate.check language authoredRewrites[24] = true := by
  certify_authored_row
private theorem authored25_checked :
    RewriteValidationCertificate.check language authoredRewrites[25] = true := by
  certify_authored_row
private theorem authored26_checked :
    RewriteValidationCertificate.check language authoredRewrites[26] = true := by
  certify_authored_row

private theorem every_rewrite_checked (rewrite : RewriteRule)
    (membership : rewrite ∈ language.rewrites) :
    RewriteValidationCertificate.check language rewrite = true := by
  simp only [language_rewrites, List.mem_append] at membership
  rcases membership with sourceMembership | authoredMembership
  · simp only [TptpFofNnfShiftLanguageDef.rewrites, List.mem_cons,
      List.not_mem_nil, or_false] at sourceMembership
    rcases sourceMembership with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
       rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source00_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source01_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source02_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source03_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source04_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source05_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source06_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source07_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source08_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source09_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source10_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source11_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source12_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source13_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source14_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source15_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source16_checked
    · simpa [TptpFofNnfShiftLanguageDef.rewrites] using source17_checked
  · simp only [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
      combineRewrites, prenexRewrites, List.mem_append] at authoredMembership
    rcases authoredMembership with matrixOrFormOrCombine | prenexMembership
    · rcases matrixOrFormOrCombine with matrixOrForm | combineMembership
      · rcases matrixOrForm with matrixMembership | formMembership
        · simp only [List.mem_cons,
            List.not_mem_nil, or_false] at matrixMembership
          rcases matrixMembership with
            (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · simpa [authoredRewrites, matrixShiftRewrites] using authored00_checked
          · simpa [authoredRewrites, matrixShiftRewrites] using authored01_checked
          · simpa [authoredRewrites, matrixShiftRewrites] using authored02_checked
          · simpa [authoredRewrites, matrixShiftRewrites] using authored03_checked
          · simpa [authoredRewrites, matrixShiftRewrites] using authored04_checked
          · simpa [authoredRewrites, matrixShiftRewrites] using authored05_checked
          · simpa [authoredRewrites, matrixShiftRewrites] using authored06_checked
          · simpa [authoredRewrites, matrixShiftRewrites] using authored07_checked
        · simp only [List.mem_cons,
            List.not_mem_nil, or_false] at formMembership
          rcases formMembership with (rfl | rfl | rfl)
          · simpa [authoredRewrites, matrixShiftRewrites,
              formShiftRewrites] using authored08_checked
          · simpa [authoredRewrites, matrixShiftRewrites,
              formShiftRewrites] using authored09_checked
          · simpa [authoredRewrites, matrixShiftRewrites,
              formShiftRewrites] using authored10_checked
      · simp only [List.mem_cons,
          List.not_mem_nil, or_false] at combineMembership
        rcases combineMembership with (rfl | rfl | rfl | rfl | rfl | rfl)
        · simpa [authoredRewrites, matrixShiftRewrites,
            formShiftRewrites, combineRewrites] using authored11_checked
        · simpa [authoredRewrites, matrixShiftRewrites,
            formShiftRewrites, combineRewrites] using authored12_checked
        · simpa [authoredRewrites, matrixShiftRewrites,
            formShiftRewrites, combineRewrites] using authored13_checked
        · simpa [authoredRewrites, matrixShiftRewrites,
            formShiftRewrites, combineRewrites] using authored14_checked
        · simpa [authoredRewrites, matrixShiftRewrites,
            formShiftRewrites, combineRewrites] using authored15_checked
        · simpa [authoredRewrites, matrixShiftRewrites,
            formShiftRewrites, combineRewrites] using authored16_checked
    · simp only [List.mem_cons,
        List.not_mem_nil, or_false] at prenexMembership
      rcases prenexMembership with
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored17_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored18_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored19_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored20_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored21_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored22_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored23_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored24_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored25_checked
      · simpa [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites] using authored26_checked

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
    constructorLabels_nodup
  exact every_rewrite_checked rewrite membership

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def shiftInclusion :
    StructuralMorphism TptpFofNnfShiftLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _
      (List.mem_append_left _
        (List.mem_append_left _
          (List.mem_append_left _ membership)))
  mapsEquations declaration membership := by
    change declaration ∈ ([] : List Equation) at membership
    simp at membership
  mapsRewrites declaration membership := by
    rw [mapRewriteRule_id]
    exact List.mem_append_left _ membership

def targetInclusion :
    StructuralMorphism TptpFofPrenexLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    change List.Mem declaration (TptpFofNnfLanguageDef.language.types ++
      [("TptpFofPrenex:Matrix" : TypeDecl),
       ("TptpFofPrenex:Form" : TypeDecl)]) at membership
    change List.Mem declaration (TptpFofNnfShiftLanguageDef.language.types ++ [
      ("TptpFofPrenex:Matrix" : TypeDecl),
      ("TptpFofPrenex:Form" : TypeDecl),
      ("TptpFofPrenexNormalize:Connective" : TypeDecl),
      ("TptpFofPrenexNormalize:MatrixShiftResult" : TypeDecl),
      ("TptpFofPrenexNormalize:FormShiftResult" : TypeDecl),
      ("TptpFofPrenexNormalize:CombineResult" : TypeDecl),
      ("TptpFofPrenexNormalize:Result" : TypeDecl)])
    rcases List.mem_append.mp membership with source | target
    · apply List.mem_append_left
      change List.Mem declaration (TptpFofNnfLanguageDef.language.types ++ [
        ("TptpFofNnfShift:IndexResult" : TypeDecl),
        ("TptpFofNnfShift:TermResult" : TypeDecl),
        ("TptpFofNnfShift:TermsResult" : TypeDecl),
        ("TptpFofNnfShift:FormulaResult" : TypeDecl)])
      exact List.mem_append_left _ source
    · apply List.mem_append_right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at target ⊢
      aesop
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    change declaration ∈ TptpFofNnfLanguageDef.language.terms ++
      TptpFofPrenexLanguageDef.matrixTerms ++
      TptpFofPrenexLanguageDef.prenexTerms at membership
    change declaration ∈ TptpFofNnfShiftLanguageDef.language.terms ++
      TptpFofPrenexLanguageDef.matrixTerms ++
      TptpFofPrenexLanguageDef.prenexTerms ++
      connectiveTerms ++ operationTerms
    simp only [TptpFofNnfShiftLanguageDef.language,
      List.mem_append] at membership ⊢
    aesop
  mapsEquations declaration membership := by
    change declaration ∈ ([] : List Equation) at membership
    simp at membership
  mapsRewrites declaration membership := by
    change declaration ∈ ([] : List RewriteRule) at membership
    simp at membership

/-! ## Exact authored root steps -/

theorem authored_silent_on_index_request
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (cutoff source : Pattern) :
    authoredRewrites.flatMap (fun rule =>
      applyRuleUsing base language recursiveStep rule
        (indexRequest cutoff source)) = [] := by
  simp [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
    combineRewrites, prenexRewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic, mkRule, indexRequest,
    TptpFofNnfShiftLanguageDef.indexRequest,
    TptpFofNnfShiftLanguageDef.a, matrixShiftRequest,
    formShiftRequest, combineRequest, prenexRequest, a, v,
    matchPattern]

theorem authored_silent_on_term_request
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (cutoff source : Pattern) :
    authoredRewrites.flatMap (fun rule =>
      applyRuleUsing base language recursiveStep rule
        (termRequest cutoff source)) = [] := by
  simp [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
    combineRewrites, prenexRewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic, mkRule, termRequest,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.a, matrixShiftRequest,
    formShiftRequest, combineRequest, prenexRequest, a, v,
    matchPattern]

theorem authored_silent_on_terms_request
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (cutoff source : Pattern) :
    authoredRewrites.flatMap (fun rule =>
      applyRuleUsing base language recursiveStep rule
        (termsRequest cutoff source)) = [] := by
  simp [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
    combineRewrites, prenexRewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic, mkRule, termsRequest,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.a, matrixShiftRequest,
    formShiftRequest, combineRequest, prenexRequest, a, v,
    matchPattern]

local macro "embedded_shift_rules" : tactic =>
  `(tactic|
    simp [indexZero, indexSucc, indexRequest, indexResult,
      termRequest, termResult, termsRequest, termsResult,
      sourceTermVariable, sourceTermFunction, sourceTermsNil,
      sourceTermsCons, TptpFofNnfShiftLanguageDef.rewrites, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      TptpFofNnfShiftLanguageDef.mkRule,
      TptpFofNnfShiftLanguageDef.congruence,
      TptpFofNnfShiftLanguageDef.indexRequest,
      TptpFofNnfShiftLanguageDef.indexResult,
      TptpFofNnfShiftLanguageDef.termRequest,
      TptpFofNnfShiftLanguageDef.termResult,
      TptpFofNnfShiftLanguageDef.termsRequest,
      TptpFofNnfShiftLanguageDef.termsResult,
      TptpFofNnfShiftLanguageDef.formulaRequest,
      TptpFofNnfShiftLanguageDef.formulaResult,
      TptpFofNnfShiftLanguageDef.indexZero,
      TptpFofNnfShiftLanguageDef.indexSucc,
      TptpFofNnfShiftLanguageDef.termVariable,
      TptpFofNnfShiftLanguageDef.termFunction,
      TptpFofNnfShiftLanguageDef.termsNil,
      TptpFofNnfShiftLanguageDef.termsCons,
      TptpFofNnfShiftLanguageDef.verum,
      TptpFofNnfShiftLanguageDef.falsum,
      TptpFofNnfShiftLanguageDef.positive,
      TptpFofNnfShiftLanguageDef.negative,
      TptpFofNnfShiftLanguageDef.equal,
      TptpFofNnfShiftLanguageDef.notEqual,
      TptpFofNnfShiftLanguageDef.and,
      TptpFofNnfShiftLanguageDef.or,
      TptpFofNnfShiftLanguageDef.all,
      TptpFofNnfShiftLanguageDef.ex,
      TptpFofNnfShiftLanguageDef.a,
      TptpFofNnfShiftLanguageDef.v,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

local syntax "embedded_shift_rules_using " term,* : tactic
local macro_rules
  | `(tactic| embedded_shift_rules_using $_proofs:term,*) =>
      `(tactic|
        simp only [indexZero, indexSucc, indexRequest, indexResult,
          termRequest, termResult, termsRequest, termsResult,
          sourceTermVariable, sourceTermFunction, sourceTermsNil,
          sourceTermsCons] at * <;>
        simp only [TptpFofNnfShiftLanguageDef.indexRequest,
          TptpFofNnfShiftLanguageDef.indexResult,
          TptpFofNnfShiftLanguageDef.termRequest,
          TptpFofNnfShiftLanguageDef.termResult,
          TptpFofNnfShiftLanguageDef.termsRequest,
          TptpFofNnfShiftLanguageDef.termsResult,
          TptpFofNnfShiftLanguageDef.indexZero,
          TptpFofNnfShiftLanguageDef.indexSucc,
          TptpFofNnfShiftLanguageDef.termVariable,
          TptpFofNnfShiftLanguageDef.termFunction,
          TptpFofNnfShiftLanguageDef.termsNil,
          TptpFofNnfShiftLanguageDef.termsCons,
          TptpFofNnfShiftLanguageDef.a] at * <;>
        simp [*, TptpFofNnfShiftLanguageDef.rewrites, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
          TptpFofNnfShiftLanguageDef.mkRule,
          TptpFofNnfShiftLanguageDef.congruence,
          TptpFofNnfShiftLanguageDef.indexRequest,
          TptpFofNnfShiftLanguageDef.indexResult,
          TptpFofNnfShiftLanguageDef.termRequest,
          TptpFofNnfShiftLanguageDef.termResult,
          TptpFofNnfShiftLanguageDef.termsRequest,
          TptpFofNnfShiftLanguageDef.termsResult,
          TptpFofNnfShiftLanguageDef.formulaRequest,
          TptpFofNnfShiftLanguageDef.formulaResult,
          TptpFofNnfShiftLanguageDef.indexZero,
          TptpFofNnfShiftLanguageDef.indexSucc,
          TptpFofNnfShiftLanguageDef.termVariable,
          TptpFofNnfShiftLanguageDef.termFunction,
          TptpFofNnfShiftLanguageDef.termsNil,
          TptpFofNnfShiftLanguageDef.termsCons,
          TptpFofNnfShiftLanguageDef.verum,
          TptpFofNnfShiftLanguageDef.falsum,
          TptpFofNnfShiftLanguageDef.positive,
          TptpFofNnfShiftLanguageDef.negative,
          TptpFofNnfShiftLanguageDef.equal,
          TptpFofNnfShiftLanguageDef.notEqual,
          TptpFofNnfShiftLanguageDef.and,
          TptpFofNnfShiftLanguageDef.or,
          TptpFofNnfShiftLanguageDef.all,
          TptpFofNnfShiftLanguageDef.ex,
          TptpFofNnfShiftLanguageDef.a,
          TptpFofNnfShiftLanguageDef.v,
          matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
          applyBindings])

local macro "prenex_root" : tactic =>
  `(tactic|
    simp [rewriteAt, language_rewrites, authoredRewrites,
      matrixShiftRewrites, formShiftRewrites, combineRewrites,
      prenexRewrites, TptpFofNnfShiftLanguageDef.rewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
      premiseStepUsing, mkRule, congruence,
      matrixShiftRequest, matrixShiftResult, formShiftRequest,
      formShiftResult, combineRequest, combineResult, prenexRequest,
      prenexResult, connectiveAnd, connectiveOr,
      matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
      matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
      formMatrix, formAll, formEx,
      indexZero, indexSucc, indexRequest, indexResult,
      termRequest, termResult, termsRequest, termsResult,
      sourceTermVariable, sourceTermFunction, sourceTermsNil,
      sourceTermsCons, sourceVerum, sourceFalsum, sourcePositive,
      sourceNegative, sourceEqual, sourceNotEqual, sourceAnd, sourceOr,
      sourceAll, sourceEx, TptpFofNnfShiftLanguageDef.indexRequest,
      TptpFofNnfShiftLanguageDef.indexResult,
      TptpFofNnfShiftLanguageDef.termRequest,
      TptpFofNnfShiftLanguageDef.termResult,
      TptpFofNnfShiftLanguageDef.termsRequest,
      TptpFofNnfShiftLanguageDef.termsResult,
      TptpFofNnfShiftLanguageDef.formulaRequest,
      TptpFofNnfShiftLanguageDef.formulaResult,
      TptpFofNnfShiftLanguageDef.indexZero,
      TptpFofNnfShiftLanguageDef.indexSucc,
      TptpFofNnfShiftLanguageDef.termVariable,
      TptpFofNnfShiftLanguageDef.termFunction,
      TptpFofNnfShiftLanguageDef.termsNil,
      TptpFofNnfShiftLanguageDef.termsCons,
      TptpFofNnfShiftLanguageDef.verum,
      TptpFofNnfShiftLanguageDef.falsum,
      TptpFofNnfShiftLanguageDef.positive,
      TptpFofNnfShiftLanguageDef.negative,
      TptpFofNnfShiftLanguageDef.equal,
      TptpFofNnfShiftLanguageDef.notEqual,
      TptpFofNnfShiftLanguageDef.and,
      TptpFofNnfShiftLanguageDef.or,
      TptpFofNnfShiftLanguageDef.all,
      TptpFofNnfShiftLanguageDef.ex,
      TptpFofNnfShiftLanguageDef.mkRule,
      TptpFofNnfShiftLanguageDef.congruence,
      TptpFofNnfShiftLanguageDef.v,
      TptpFofNnfShiftLanguageDef.a,
      a, v, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local syntax "prenex_root_using " term,* : tactic
local macro_rules
  | `(tactic| prenex_root_using $_proofs:term,*) =>
      `(tactic|
        simp only [indexZero, indexSucc, indexRequest, indexResult,
          termRequest, termResult, termsRequest, termsResult,
          sourceTermVariable, sourceTermFunction, sourceTermsNil,
          sourceTermsCons, matrixShiftRequest, matrixShiftResult,
          formShiftRequest, formShiftResult, combineRequest, combineResult,
          prenexRequest, prenexResult, connectiveAnd, connectiveOr,
          matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
          matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
          formMatrix, formAll, formEx, sourceVerum, sourceFalsum,
          sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
          sourceAnd, sourceOr, sourceAll, sourceEx, a] at * <;>
        simp only [TptpFofNnfShiftLanguageDef.indexRequest,
          TptpFofNnfShiftLanguageDef.indexResult,
          TptpFofNnfShiftLanguageDef.termRequest,
          TptpFofNnfShiftLanguageDef.termResult,
          TptpFofNnfShiftLanguageDef.termsRequest,
          TptpFofNnfShiftLanguageDef.termsResult,
          TptpFofNnfShiftLanguageDef.formulaRequest,
          TptpFofNnfShiftLanguageDef.formulaResult,
          TptpFofNnfShiftLanguageDef.indexZero,
          TptpFofNnfShiftLanguageDef.indexSucc,
          TptpFofNnfShiftLanguageDef.termVariable,
          TptpFofNnfShiftLanguageDef.termFunction,
          TptpFofNnfShiftLanguageDef.termsNil,
          TptpFofNnfShiftLanguageDef.termsCons,
          TptpFofNnfShiftLanguageDef.verum,
          TptpFofNnfShiftLanguageDef.falsum,
          TptpFofNnfShiftLanguageDef.positive,
          TptpFofNnfShiftLanguageDef.negative,
          TptpFofNnfShiftLanguageDef.equal,
          TptpFofNnfShiftLanguageDef.notEqual,
          TptpFofNnfShiftLanguageDef.and,
          TptpFofNnfShiftLanguageDef.or,
          TptpFofNnfShiftLanguageDef.all,
          TptpFofNnfShiftLanguageDef.ex,
          TptpFofNnfShiftLanguageDef.a] at * <;>
        simp [*, rewriteAt, language_rewrites, authoredRewrites,
          matrixShiftRewrites, formShiftRewrites, combineRewrites,
          prenexRewrites, TptpFofNnfShiftLanguageDef.rewrites,
          applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
          premiseStepUsing, mkRule, congruence,
          TptpFofNnfShiftLanguageDef.mkRule,
          TptpFofNnfShiftLanguageDef.congruence,
          TptpFofNnfShiftLanguageDef.indexRequest,
          TptpFofNnfShiftLanguageDef.indexResult,
          TptpFofNnfShiftLanguageDef.termRequest,
          TptpFofNnfShiftLanguageDef.termResult,
          TptpFofNnfShiftLanguageDef.termsRequest,
          TptpFofNnfShiftLanguageDef.termsResult,
          TptpFofNnfShiftLanguageDef.formulaRequest,
          TptpFofNnfShiftLanguageDef.formulaResult,
          TptpFofNnfShiftLanguageDef.indexZero,
          TptpFofNnfShiftLanguageDef.indexSucc,
          TptpFofNnfShiftLanguageDef.termVariable,
          TptpFofNnfShiftLanguageDef.termFunction,
          TptpFofNnfShiftLanguageDef.termsNil,
          TptpFofNnfShiftLanguageDef.termsCons,
          TptpFofNnfShiftLanguageDef.verum,
          TptpFofNnfShiftLanguageDef.falsum,
          TptpFofNnfShiftLanguageDef.positive,
          TptpFofNnfShiftLanguageDef.negative,
          TptpFofNnfShiftLanguageDef.equal,
          TptpFofNnfShiftLanguageDef.notEqual,
          TptpFofNnfShiftLanguageDef.and,
          TptpFofNnfShiftLanguageDef.or,
          TptpFofNnfShiftLanguageDef.all,
          TptpFofNnfShiftLanguageDef.ex,
          TptpFofNnfShiftLanguageDef.mkRule,
          TptpFofNnfShiftLanguageDef.congruence,
          TptpFofNnfShiftLanguageDef.v,
          TptpFofNnfShiftLanguageDef.a,
          matrixShiftRequest, matrixShiftResult, formShiftRequest,
          formShiftResult, combineRequest, combineResult, prenexRequest,
          prenexResult, connectiveAnd, connectiveOr,
          matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
          matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
          formMatrix, formAll, formEx, indexZero, indexSucc,
          indexRequest, indexResult, termRequest, termResult, termsRequest,
          termsResult, sourceTermVariable, sourceTermFunction,
          sourceTermsNil, sourceTermsCons, sourceVerum, sourceFalsum,
          sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
          sourceAnd, sourceOr, sourceAll, sourceEx, a, v,
          matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
          applyBindings])

theorem embedded_index_zero_at_zero_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest indexZero indexZero) =
      [indexResult indexZero indexZero (indexSucc indexZero)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_index_request, List.append_nil]
  embedded_shift_rules

theorem embedded_index_succ_at_zero_exact (fuel : Nat) (index : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest indexZero (indexSucc index)) =
      [indexResult indexZero (indexSucc index)
        (indexSucc (indexSucc index))] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_index_request, List.append_nil]
  embedded_shift_rules

theorem embedded_index_zero_under_binder_exact (fuel : Nat)
    (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest (indexSucc cutoff) indexZero) =
      [indexResult (indexSucc cutoff) indexZero indexZero] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_index_request, List.append_nil]
  embedded_shift_rules

theorem embedded_index_succ_under_binder_exact (fuel : Nat)
    (cutoff index target : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (indexRequest cutoff index) = [indexResult cutoff index target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest (indexSucc cutoff) (indexSucc index)) =
      [indexResult (indexSucc cutoff) (indexSucc index)
        (indexSucc target)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_index_request, List.append_nil]
  embedded_shift_rules_using exact

theorem embedded_term_variable_exact (fuel : Nat)
    (cutoff index target : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (indexRequest cutoff index) = [indexResult cutoff index target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termRequest cutoff (sourceTermVariable index)) =
      [termResult cutoff (sourceTermVariable index)
        (sourceTermVariable target)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_term_request, List.append_nil]
  embedded_shift_rules_using exact

theorem embedded_term_function_exact (fuel : Nat)
    (cutoff function arguments targetArguments : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsRequest cutoff arguments) =
        [termsResult cutoff arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termRequest cutoff (sourceTermFunction function arguments)) =
      [termResult cutoff (sourceTermFunction function arguments)
        (sourceTermFunction function targetArguments)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_term_request, List.append_nil]
  embedded_shift_rules_using exact

theorem embedded_terms_nil_exact (fuel : Nat) (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termsRequest cutoff sourceTermsNil) =
      [termsResult cutoff sourceTermsNil sourceTermsNil] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_terms_request, List.append_nil]
  embedded_shift_rules

theorem embedded_terms_cons_exact (fuel : Nat)
    (cutoff head tail targetHead targetTail : Pattern)
    (headExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff head) = [termResult cutoff head targetHead])
    (tailExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsRequest cutoff tail) = [termsResult cutoff tail targetTail]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termsRequest cutoff (sourceTermsCons head tail)) =
      [termsResult cutoff (sourceTermsCons head tail)
        (sourceTermsCons targetHead targetTail)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [authored_silent_on_terms_request, List.append_nil]
  embedded_shift_rules_using headExact, tailExact

/-- The reusable cutoff-shift derivation remains exact after adjoining the
prenex operations.  Formula-level shift is intentionally excluded here: the
prenex machine only imports index, term, and term-list shifting. -/
theorem embedded_shift_rewriteAt_exact
    {sort : TptpFofNnfShiftLanguageDef.SubjectSort}
    {cutoff source target : Pattern}
    (derivation : TptpFofNnfShiftLanguageDef.ShiftDerivation
      sort cutoff source target)
    (notFormula : sort ≠ .formula)
    (fuel : Nat) (enough : derivation.height <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (sort.request cutoff source) =
      [sort.result cutoff source target] := by
  induction derivation generalizing fuel with
  | indexZeroAtZero =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            indexRequest, indexResult, indexZero, indexSucc] using
            embedded_index_zero_at_zero_exact fuel
  | indexSuccAtZero index =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            indexRequest, indexResult, indexZero, indexSucc] using
            embedded_index_succ_at_zero_exact fuel index
  | indexZeroUnderBinder cutoff =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            indexRequest, indexResult, indexZero, indexSucc] using
            embedded_index_zero_under_binder_exact fuel cutoff
  | indexSuccUnderBinder prior inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          have priorEnough : prior.height <= fuel := by
            simpa [TptpFofNnfShiftLanguageDef.ShiftDerivation.height,
              Nat.succ_eq_add_one] using enough
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            indexRequest, indexResult, indexZero, indexSucc] using
            embedded_index_succ_under_binder_exact fuel _ _ _
              (inductionHypothesis (by decide) fuel priorEnough)
  | termVariable indexShift inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : indexShift.height <= fuel := by
            simpa [TptpFofNnfShiftLanguageDef.ShiftDerivation.height,
              Nat.succ_eq_add_one] using enough
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            indexRequest, indexResult, termRequest, termResult,
            sourceTermVariable] using
            embedded_term_variable_exact fuel _ _ _
              (inductionHypothesis (by decide) fuel childEnough)
  | termFunction argumentsShift inductionHypothesis =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : argumentsShift.height <= fuel := by
            simpa [TptpFofNnfShiftLanguageDef.ShiftDerivation.height,
              Nat.succ_eq_add_one] using enough
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            termsRequest, termsResult, termRequest, termResult,
            sourceTermFunction] using
            embedded_term_function_exact fuel _ _ _ _
              (inductionHypothesis (by decide) fuel childEnough)
  | termsNil cutoff =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            termsRequest, termsResult, sourceTermsNil] using
            embedded_terms_nil_exact fuel cutoff
  | termsCons headShift tailShift headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [TptpFofNnfShiftLanguageDef.ShiftDerivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max headShift.height tailShift.height <= fuel := by
            simpa [TptpFofNnfShiftLanguageDef.ShiftDerivation.height,
              Nat.succ_eq_add_one] using enough
          have headEnough : headShift.height <= fuel :=
            le_trans (Nat.le_max_left _ _) maximumEnough
          have tailEnough : tailShift.height <= fuel :=
            le_trans (Nat.le_max_right _ _) maximumEnough
          simpa [TptpFofNnfShiftLanguageDef.SubjectSort.request,
            TptpFofNnfShiftLanguageDef.SubjectSort.result,
            termRequest, termResult, termsRequest, termsResult,
            sourceTermsCons] using
            embedded_terms_cons_exact fuel _ _ _ _ _
              (headHypothesis (by decide) fuel headEnough)
              (tailHypothesis (by decide) fuel tailEnough)
  | formulaVerum => exact (notFormula rfl).elim
  | formulaFalsum => exact (notFormula rfl).elim
  | formulaPositive => exact (notFormula rfl).elim
  | formulaNegative => exact (notFormula rfl).elim
  | formulaEqual => exact (notFormula rfl).elim
  | formulaNotEqual => exact (notFormula rfl).elim
  | formulaAnd => exact (notFormula rfl).elim
  | formulaOr => exact (notFormula rfl).elim
  | formulaAll => exact (notFormula rfl).elim
  | formulaEx => exact (notFormula rfl).elim

theorem shift_silent_on_matrix_shift_request
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (cutoff source : Pattern) :
    TptpFofNnfShiftLanguageDef.rewrites.flatMap (fun rule =>
      applyRuleUsing base language recursiveStep rule
        (matrixShiftRequest cutoff source)) = [] := by
  simp [TptpFofNnfShiftLanguageDef.rewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic,
    TptpFofNnfShiftLanguageDef.mkRule,
    TptpFofNnfShiftLanguageDef.indexRequest,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.formulaRequest,
    TptpFofNnfShiftLanguageDef.a, matrixShiftRequest, a,
    matchPattern]

theorem shift_silent_on_form_shift_request
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (cutoff source : Pattern) :
    TptpFofNnfShiftLanguageDef.rewrites.flatMap (fun rule =>
      applyRuleUsing base language recursiveStep rule
        (formShiftRequest cutoff source)) = [] := by
  simp [TptpFofNnfShiftLanguageDef.rewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic,
    TptpFofNnfShiftLanguageDef.mkRule,
    TptpFofNnfShiftLanguageDef.indexRequest,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.formulaRequest,
    TptpFofNnfShiftLanguageDef.a, formShiftRequest, a,
    matchPattern]

theorem shift_silent_on_combine_request
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (connective left right : Pattern) :
    TptpFofNnfShiftLanguageDef.rewrites.flatMap (fun rule =>
      applyRuleUsing base language recursiveStep rule
        (combineRequest connective left right)) = [] := by
  simp [TptpFofNnfShiftLanguageDef.rewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic,
    TptpFofNnfShiftLanguageDef.mkRule,
    TptpFofNnfShiftLanguageDef.indexRequest,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.formulaRequest,
    TptpFofNnfShiftLanguageDef.a, combineRequest, a,
    matchPattern]

theorem shift_silent_on_prenex_request
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (source : Pattern) :
    TptpFofNnfShiftLanguageDef.rewrites.flatMap (fun rule =>
      applyRuleUsing base language recursiveStep rule
        (prenexRequest source)) = [] := by
  simp [TptpFofNnfShiftLanguageDef.rewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic,
    TptpFofNnfShiftLanguageDef.mkRule,
    TptpFofNnfShiftLanguageDef.indexRequest,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.formulaRequest,
    TptpFofNnfShiftLanguageDef.a, prenexRequest, a,
    matchPattern]

local macro "authored_prenex_rules" : tactic =>
  `(tactic|
    simp [authoredRewrites, matrixShiftRewrites, formShiftRewrites,
      combineRewrites, prenexRewrites, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      mkRule, congruence, indexZero, indexSucc, termRequest, termResult,
      termsRequest, termsResult, matrixShiftRequest, matrixShiftResult,
      formShiftRequest, formShiftResult, combineRequest, combineResult,
      prenexRequest, prenexResult, connectiveAnd, connectiveOr,
      matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
      matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
      formMatrix, formAll, formEx, sourceVerum, sourceFalsum,
      sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
      sourceAnd, sourceOr, sourceAll, sourceEx,
      TptpFofNnfShiftLanguageDef.termRequest,
      TptpFofNnfShiftLanguageDef.termResult,
      TptpFofNnfShiftLanguageDef.termsRequest,
      TptpFofNnfShiftLanguageDef.termsResult,
      TptpFofNnfShiftLanguageDef.indexZero,
      TptpFofNnfShiftLanguageDef.indexSucc,
      TptpFofNnfShiftLanguageDef.verum,
      TptpFofNnfShiftLanguageDef.falsum,
      TptpFofNnfShiftLanguageDef.positive,
      TptpFofNnfShiftLanguageDef.negative,
      TptpFofNnfShiftLanguageDef.equal,
      TptpFofNnfShiftLanguageDef.notEqual,
      TptpFofNnfShiftLanguageDef.and,
      TptpFofNnfShiftLanguageDef.or,
      TptpFofNnfShiftLanguageDef.all,
      TptpFofNnfShiftLanguageDef.ex,
      TptpFofNnfShiftLanguageDef.a,
      a, v, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local syntax "authored_prenex_rules_using " term,* : tactic
local macro_rules
  | `(tactic| authored_prenex_rules_using $_proofs:term,*) =>
      `(tactic|
        simp only [indexZero, indexSucc, termRequest, termResult,
          termsRequest, termsResult, matrixShiftRequest, matrixShiftResult,
          formShiftRequest, formShiftResult, combineRequest, combineResult,
          prenexRequest, prenexResult, connectiveAnd, connectiveOr,
          matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
          matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
          formMatrix, formAll, formEx, sourceVerum, sourceFalsum,
          sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
          sourceAnd, sourceOr, sourceAll, sourceEx, a] at * <;>
        (try simp only [TptpFofNnfShiftLanguageDef.termRequest,
          TptpFofNnfShiftLanguageDef.termResult,
          TptpFofNnfShiftLanguageDef.termsRequest,
          TptpFofNnfShiftLanguageDef.termsResult,
          TptpFofNnfShiftLanguageDef.indexZero,
          TptpFofNnfShiftLanguageDef.indexSucc,
          TptpFofNnfShiftLanguageDef.verum,
          TptpFofNnfShiftLanguageDef.falsum,
          TptpFofNnfShiftLanguageDef.positive,
          TptpFofNnfShiftLanguageDef.negative,
          TptpFofNnfShiftLanguageDef.equal,
          TptpFofNnfShiftLanguageDef.notEqual,
          TptpFofNnfShiftLanguageDef.and,
          TptpFofNnfShiftLanguageDef.or,
          TptpFofNnfShiftLanguageDef.all,
          TptpFofNnfShiftLanguageDef.ex,
          TptpFofNnfShiftLanguageDef.a] at *) <;>
        simp [*, authoredRewrites, matrixShiftRewrites, formShiftRewrites,
          combineRewrites, prenexRewrites, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
          mkRule, congruence, indexZero, indexSucc, termRequest, termResult,
          termsRequest, termsResult, matrixShiftRequest, matrixShiftResult,
          formShiftRequest, formShiftResult, combineRequest, combineResult,
          prenexRequest, prenexResult, connectiveAnd, connectiveOr,
          matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
          matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
          formMatrix, formAll, formEx, sourceVerum, sourceFalsum,
          sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
          sourceAnd, sourceOr, sourceAll, sourceEx,
          TptpFofNnfShiftLanguageDef.termRequest,
          TptpFofNnfShiftLanguageDef.termResult,
          TptpFofNnfShiftLanguageDef.termsRequest,
          TptpFofNnfShiftLanguageDef.termsResult,
          TptpFofNnfShiftLanguageDef.indexZero,
          TptpFofNnfShiftLanguageDef.indexSucc,
          TptpFofNnfShiftLanguageDef.verum,
          TptpFofNnfShiftLanguageDef.falsum,
          TptpFofNnfShiftLanguageDef.positive,
          TptpFofNnfShiftLanguageDef.negative,
          TptpFofNnfShiftLanguageDef.equal,
          TptpFofNnfShiftLanguageDef.notEqual,
          TptpFofNnfShiftLanguageDef.and,
          TptpFofNnfShiftLanguageDef.or,
          TptpFofNnfShiftLanguageDef.all,
          TptpFofNnfShiftLanguageDef.ex,
          TptpFofNnfShiftLanguageDef.a,
          a, v, matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings])

theorem matrix_shift_verum_exact (fuel : Nat) (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff matrixVerum) =
      [matrixShiftResult cutoff matrixVerum matrixVerum] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  authored_prenex_rules

theorem matrix_shift_falsum_exact (fuel : Nat) (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff matrixFalsum) =
      [matrixShiftResult cutoff matrixFalsum matrixFalsum] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  authored_prenex_rules

theorem matrix_shift_positive_exact (fuel : Nat)
    (cutoff relation arguments targetArguments : Pattern)
    (argumentsExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          (termsRequest cutoff arguments) =
        [termsResult cutoff arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff (matrixPositive relation arguments)) =
      [matrixShiftResult cutoff (matrixPositive relation arguments)
        (matrixPositive relation targetArguments)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  prenex_root_using argumentsExact

theorem matrix_shift_negative_exact (fuel : Nat)
    (cutoff relation arguments targetArguments : Pattern)
    (argumentsExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
          (termsRequest cutoff arguments) =
        [termsResult cutoff arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff (matrixNegative relation arguments)) =
      [matrixShiftResult cutoff (matrixNegative relation arguments)
        (matrixNegative relation targetArguments)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  prenex_root_using argumentsExact

theorem matrix_shift_equal_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff left) = [termResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff right) = [termResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff (matrixEqual left right)) =
      [matrixShiftResult cutoff (matrixEqual left right)
        (matrixEqual targetLeft targetRight)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  prenex_root_using leftExact, rightExact

theorem matrix_shift_not_equal_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff left) = [termResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff right) = [termResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff (matrixNotEqual left right)) =
      [matrixShiftResult cutoff (matrixNotEqual left right)
        (matrixNotEqual targetLeft targetRight)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  prenex_root_using leftExact, rightExact

theorem matrix_shift_and_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (matrixShiftRequest cutoff left) =
        [matrixShiftResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (matrixShiftRequest cutoff right) =
        [matrixShiftResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff (matrixAnd left right)) =
      [matrixShiftResult cutoff (matrixAnd left right)
        (matrixAnd targetLeft targetRight)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  simp only [matrixShiftRequest, matrixShiftResult, matrixAnd, a] at leftExact rightExact ⊢
  simp [leftExact, rightExact, authoredRewrites, matrixShiftRewrites,
    formShiftRewrites, combineRewrites, prenexRewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    mkRule, congruence, indexZero, indexSucc, termRequest, termResult,
    termsRequest, termsResult, matrixShiftRequest, matrixShiftResult,
    formShiftRequest, formShiftResult, combineRequest, combineResult,
    prenexRequest, prenexResult, connectiveAnd, connectiveOr,
    matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
    matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
    formMatrix, formAll, formEx, sourceVerum, sourceFalsum,
    sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
    sourceAnd, sourceOr, sourceAll, sourceEx,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.termResult,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.termsResult,
    TptpFofNnfShiftLanguageDef.indexZero,
    TptpFofNnfShiftLanguageDef.indexSucc,
    TptpFofNnfShiftLanguageDef.verum,
    TptpFofNnfShiftLanguageDef.falsum,
    TptpFofNnfShiftLanguageDef.positive,
    TptpFofNnfShiftLanguageDef.negative,
    TptpFofNnfShiftLanguageDef.equal,
    TptpFofNnfShiftLanguageDef.notEqual,
    TptpFofNnfShiftLanguageDef.and,
    TptpFofNnfShiftLanguageDef.or,
    TptpFofNnfShiftLanguageDef.all,
    TptpFofNnfShiftLanguageDef.ex,
    TptpFofNnfShiftLanguageDef.a,
    a, v, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

theorem matrix_shift_or_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (matrixShiftRequest cutoff left) =
        [matrixShiftResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (matrixShiftRequest cutoff right) =
        [matrixShiftResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (matrixShiftRequest cutoff (matrixOr left right)) =
      [matrixShiftResult cutoff (matrixOr left right)
        (matrixOr targetLeft targetRight)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_matrix_shift_request, List.nil_append]
  simp only [matrixShiftRequest, matrixShiftResult, matrixOr, a] at leftExact rightExact ⊢
  simp [leftExact, rightExact, authoredRewrites, matrixShiftRewrites,
    formShiftRewrites, combineRewrites, prenexRewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    mkRule, congruence, indexZero, indexSucc, termRequest, termResult,
    termsRequest, termsResult, matrixShiftRequest, matrixShiftResult,
    formShiftRequest, formShiftResult, combineRequest, combineResult,
    prenexRequest, prenexResult, connectiveAnd, connectiveOr,
    matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
    matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
    formMatrix, formAll, formEx, sourceVerum, sourceFalsum,
    sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
    sourceAnd, sourceOr, sourceAll, sourceEx,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.termResult,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.termsResult,
    TptpFofNnfShiftLanguageDef.indexZero,
    TptpFofNnfShiftLanguageDef.indexSucc,
    TptpFofNnfShiftLanguageDef.verum,
    TptpFofNnfShiftLanguageDef.falsum,
    TptpFofNnfShiftLanguageDef.positive,
    TptpFofNnfShiftLanguageDef.negative,
    TptpFofNnfShiftLanguageDef.equal,
    TptpFofNnfShiftLanguageDef.notEqual,
    TptpFofNnfShiftLanguageDef.and,
    TptpFofNnfShiftLanguageDef.or,
    TptpFofNnfShiftLanguageDef.all,
    TptpFofNnfShiftLanguageDef.ex,
    TptpFofNnfShiftLanguageDef.a,
    a, v, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

theorem form_shift_matrix_exact (fuel : Nat)
    (cutoff body targetBody : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (matrixShiftRequest cutoff body) =
        [matrixShiftResult cutoff body targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formShiftRequest cutoff (formMatrix body)) =
      [formShiftResult cutoff (formMatrix body) (formMatrix targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_form_shift_request, List.nil_append]
  simp only [matrixShiftRequest, matrixShiftResult, formShiftRequest,
    formShiftResult, formMatrix, a] at bodyExact ⊢
  simp [bodyExact, authoredRewrites, matrixShiftRewrites,
    formShiftRewrites, combineRewrites, prenexRewrites, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    mkRule, congruence, indexZero, indexSucc, termRequest, termResult,
    termsRequest, termsResult, matrixShiftRequest, matrixShiftResult,
    formShiftRequest, formShiftResult, combineRequest, combineResult,
    prenexRequest, prenexResult, connectiveAnd, connectiveOr,
    matrixVerum, matrixFalsum, matrixPositive, matrixNegative,
    matrixEqual, matrixNotEqual, matrixAnd, matrixOr,
    formMatrix, formAll, formEx, sourceVerum, sourceFalsum,
    sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
    sourceAnd, sourceOr, sourceAll, sourceEx,
    TptpFofNnfShiftLanguageDef.termRequest,
    TptpFofNnfShiftLanguageDef.termResult,
    TptpFofNnfShiftLanguageDef.termsRequest,
    TptpFofNnfShiftLanguageDef.termsResult,
    TptpFofNnfShiftLanguageDef.indexZero,
    TptpFofNnfShiftLanguageDef.indexSucc,
    TptpFofNnfShiftLanguageDef.verum,
    TptpFofNnfShiftLanguageDef.falsum,
    TptpFofNnfShiftLanguageDef.positive,
    TptpFofNnfShiftLanguageDef.negative,
    TptpFofNnfShiftLanguageDef.equal,
    TptpFofNnfShiftLanguageDef.notEqual,
    TptpFofNnfShiftLanguageDef.and,
    TptpFofNnfShiftLanguageDef.or,
    TptpFofNnfShiftLanguageDef.all,
    TptpFofNnfShiftLanguageDef.ex,
    TptpFofNnfShiftLanguageDef.a,
    a, v, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

theorem form_shift_all_exact (fuel : Nat)
    (cutoff body targetBody : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formShiftRequest (indexSucc cutoff) body) =
        [formShiftResult (indexSucc cutoff) body targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formShiftRequest cutoff (formAll body)) =
      [formShiftResult cutoff (formAll body) (formAll targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_form_shift_request, List.nil_append]
  prenex_root_using bodyExact

theorem form_shift_ex_exact (fuel : Nat)
    (cutoff body targetBody : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formShiftRequest (indexSucc cutoff) body) =
        [formShiftResult (indexSucc cutoff) body targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formShiftRequest cutoff (formEx body)) =
      [formShiftResult cutoff (formEx body) (formEx targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_form_shift_request, List.nil_append]
  prenex_root_using bodyExact

theorem combine_left_all_exact (fuel : Nat)
    (connective leftBody right shiftedRight targetBody : Pattern)
    (shiftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formShiftRequest indexZero right) =
        [formShiftResult indexZero right shiftedRight])
    (combineExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (combineRequest connective leftBody shiftedRight) =
        [combineResult connective leftBody shiftedRight targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (combineRequest connective (formAll leftBody) right) =
      [combineResult connective (formAll leftBody) right
        (formAll targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_combine_request, List.nil_append]
  prenex_root_using shiftExact, combineExact

theorem combine_left_ex_exact (fuel : Nat)
    (connective leftBody right shiftedRight targetBody : Pattern)
    (shiftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formShiftRequest indexZero right) =
        [formShiftResult indexZero right shiftedRight])
    (combineExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (combineRequest connective leftBody shiftedRight) =
        [combineResult connective leftBody shiftedRight targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (combineRequest connective (formEx leftBody) right) =
      [combineResult connective (formEx leftBody) right
        (formEx targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_combine_request, List.nil_append]
  prenex_root_using shiftExact, combineExact

theorem combine_right_all_exact (fuel : Nat)
    (connective leftBody rightBody shiftedLeft targetBody : Pattern)
    (shiftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formShiftRequest indexZero (formMatrix leftBody)) =
        [formShiftResult indexZero (formMatrix leftBody) shiftedLeft])
    (combineExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (combineRequest connective shiftedLeft rightBody) =
        [combineResult connective shiftedLeft rightBody targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (combineRequest connective (formMatrix leftBody)
          (formAll rightBody)) =
      [combineResult connective (formMatrix leftBody) (formAll rightBody)
        (formAll targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_combine_request, List.nil_append]
  prenex_root_using shiftExact, combineExact

theorem combine_right_ex_exact (fuel : Nat)
    (connective leftBody rightBody shiftedLeft targetBody : Pattern)
    (shiftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formShiftRequest indexZero (formMatrix leftBody)) =
        [formShiftResult indexZero (formMatrix leftBody) shiftedLeft])
    (combineExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (combineRequest connective shiftedLeft rightBody) =
        [combineResult connective shiftedLeft rightBody targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (combineRequest connective (formMatrix leftBody)
          (formEx rightBody)) =
      [combineResult connective (formMatrix leftBody) (formEx rightBody)
        (formEx targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_combine_request, List.nil_append]
  prenex_root_using shiftExact, combineExact

theorem combine_matrices_and_exact (fuel : Nat)
    (left right : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (combineRequest connectiveAnd (formMatrix left) (formMatrix right)) =
      [combineResult connectiveAnd (formMatrix left) (formMatrix right)
        (formMatrix (matrixAnd left right))] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_combine_request, List.nil_append]
  authored_prenex_rules

theorem combine_matrices_or_exact (fuel : Nat)
    (left right : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (combineRequest connectiveOr (formMatrix left) (formMatrix right)) =
      [combineResult connectiveOr (formMatrix left) (formMatrix right)
        (formMatrix (matrixOr left right))] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_combine_request, List.nil_append]
  authored_prenex_rules

theorem prenex_verum_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest sourceVerum) =
      [prenexResult sourceVerum (formMatrix matrixVerum)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  authored_prenex_rules

theorem prenex_falsum_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest sourceFalsum) =
      [prenexResult sourceFalsum (formMatrix matrixFalsum)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  authored_prenex_rules

theorem prenex_positive_exact (fuel : Nat)
    (relation arguments : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourcePositive relation arguments)) =
      [prenexResult (sourcePositive relation arguments)
        (formMatrix (matrixPositive relation arguments))] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  authored_prenex_rules

theorem prenex_negative_exact (fuel : Nat)
    (relation arguments : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourceNegative relation arguments)) =
      [prenexResult (sourceNegative relation arguments)
        (formMatrix (matrixNegative relation arguments))] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  authored_prenex_rules

theorem prenex_equal_exact (fuel : Nat) (left right : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourceEqual left right)) =
      [prenexResult (sourceEqual left right)
        (formMatrix (matrixEqual left right))] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  authored_prenex_rules

theorem prenex_not_equal_exact (fuel : Nat) (left right : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourceNotEqual left right)) =
      [prenexResult (sourceNotEqual left right)
        (formMatrix (matrixNotEqual left right))] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  authored_prenex_rules

theorem prenex_and_exact (fuel : Nat)
    (left right leftTarget rightTarget target : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (prenexRequest left) = [prenexResult left leftTarget])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (prenexRequest right) = [prenexResult right rightTarget])
    (combineExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (combineRequest connectiveAnd leftTarget rightTarget) =
        [combineResult connectiveAnd leftTarget rightTarget target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourceAnd left right)) =
      [prenexResult (sourceAnd left right) target] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  prenex_root_using leftExact, rightExact, combineExact

theorem prenex_or_exact (fuel : Nat)
    (left right leftTarget rightTarget target : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (prenexRequest left) = [prenexResult left leftTarget])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (prenexRequest right) = [prenexResult right rightTarget])
    (combineExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (combineRequest connectiveOr leftTarget rightTarget) =
        [combineResult connectiveOr leftTarget rightTarget target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourceOr left right)) =
      [prenexResult (sourceOr left right) target] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  prenex_root_using leftExact, rightExact, combineExact

theorem prenex_all_exact (fuel : Nat) (body targetBody : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (prenexRequest body) = [prenexResult body targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourceAll body)) =
      [prenexResult (sourceAll body) (formAll targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  prenex_root_using bodyExact

theorem prenex_ex_exact (fuel : Nat) (body targetBody : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (prenexRequest body) = [prenexResult body targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (prenexRequest (sourceEx body)) =
      [prenexResult (sourceEx body) (formEx targetBody)] := by
  simp only [rewriteAt, language_rewrites, List.flatMap_append]
  rw [shift_silent_on_prenex_request, List.nil_append]
  prenex_root_using bodyExact

/-! ## Independent structural derivations -/

/-- A syntax-directed derivation independent of the rewrite interpreter.
Each constructor corresponds to one authored row; the embedded constructor
imports only the index/term/term-list fragment of the already independent
cutoff-shift derivation. -/
inductive Derivation : Pattern → Pattern → Type
  | embeddedShift
      {sort : TptpFofNnfShiftLanguageDef.SubjectSort}
      {cutoff source target : Pattern}
      (shift : TptpFofNnfShiftLanguageDef.ShiftDerivation
        sort cutoff source target)
      (notFormula : sort ≠ .formula) :
      Derivation (sort.request cutoff source) (sort.result cutoff source target)
  | matrixVerum (cutoff : Pattern) :
      Derivation (matrixShiftRequest cutoff matrixVerum)
        (matrixShiftResult cutoff matrixVerum matrixVerum)
  | matrixFalsum (cutoff : Pattern) :
      Derivation (matrixShiftRequest cutoff matrixFalsum)
        (matrixShiftResult cutoff matrixFalsum matrixFalsum)
  | matrixPositive {cutoff relation arguments targetArguments : Pattern}
      (argumentsShift : Derivation (termsRequest cutoff arguments)
        (termsResult cutoff arguments targetArguments)) :
      Derivation (matrixShiftRequest cutoff (matrixPositive relation arguments))
        (matrixShiftResult cutoff (matrixPositive relation arguments)
          (matrixPositive relation targetArguments))
  | matrixNegative {cutoff relation arguments targetArguments : Pattern}
      (argumentsShift : Derivation (termsRequest cutoff arguments)
        (termsResult cutoff arguments targetArguments)) :
      Derivation (matrixShiftRequest cutoff (matrixNegative relation arguments))
        (matrixShiftResult cutoff (matrixNegative relation arguments)
          (matrixNegative relation targetArguments))
  | matrixEqual {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : Derivation (termRequest cutoff left)
        (termResult cutoff left targetLeft))
      (rightShift : Derivation (termRequest cutoff right)
        (termResult cutoff right targetRight)) :
      Derivation (matrixShiftRequest cutoff (matrixEqual left right))
        (matrixShiftResult cutoff (matrixEqual left right)
          (matrixEqual targetLeft targetRight))
  | matrixNotEqual {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : Derivation (termRequest cutoff left)
        (termResult cutoff left targetLeft))
      (rightShift : Derivation (termRequest cutoff right)
        (termResult cutoff right targetRight)) :
      Derivation (matrixShiftRequest cutoff (matrixNotEqual left right))
        (matrixShiftResult cutoff (matrixNotEqual left right)
          (matrixNotEqual targetLeft targetRight))
  | matrixAnd {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : Derivation (matrixShiftRequest cutoff left)
        (matrixShiftResult cutoff left targetLeft))
      (rightShift : Derivation (matrixShiftRequest cutoff right)
        (matrixShiftResult cutoff right targetRight)) :
      Derivation (matrixShiftRequest cutoff (matrixAnd left right))
        (matrixShiftResult cutoff (matrixAnd left right)
          (matrixAnd targetLeft targetRight))
  | matrixOr {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : Derivation (matrixShiftRequest cutoff left)
        (matrixShiftResult cutoff left targetLeft))
      (rightShift : Derivation (matrixShiftRequest cutoff right)
        (matrixShiftResult cutoff right targetRight)) :
      Derivation (matrixShiftRequest cutoff (matrixOr left right))
        (matrixShiftResult cutoff (matrixOr left right)
          (matrixOr targetLeft targetRight))
  | formMatrix {cutoff body targetBody : Pattern}
      (bodyShift : Derivation (matrixShiftRequest cutoff body)
        (matrixShiftResult cutoff body targetBody)) :
      Derivation (formShiftRequest cutoff (formMatrix body))
        (formShiftResult cutoff (formMatrix body) (formMatrix targetBody))
  | formAll {cutoff body targetBody : Pattern}
      (bodyShift : Derivation (formShiftRequest (indexSucc cutoff) body)
        (formShiftResult (indexSucc cutoff) body targetBody)) :
      Derivation (formShiftRequest cutoff (formAll body))
        (formShiftResult cutoff (formAll body) (formAll targetBody))
  | formEx {cutoff body targetBody : Pattern}
      (bodyShift : Derivation (formShiftRequest (indexSucc cutoff) body)
        (formShiftResult (indexSucc cutoff) body targetBody)) :
      Derivation (formShiftRequest cutoff (formEx body))
        (formShiftResult cutoff (formEx body) (formEx targetBody))
  | combineLeftAll {connective leftBody right shiftedRight targetBody : Pattern}
      (rightShift : Derivation (formShiftRequest indexZero right)
        (formShiftResult indexZero right shiftedRight))
      (bodyCombine : Derivation
        (combineRequest connective leftBody shiftedRight)
        (combineResult connective leftBody shiftedRight targetBody)) :
      Derivation (combineRequest connective (formAll leftBody) right)
        (combineResult connective (formAll leftBody) right
          (formAll targetBody))
  | combineLeftEx {connective leftBody right shiftedRight targetBody : Pattern}
      (rightShift : Derivation (formShiftRequest indexZero right)
        (formShiftResult indexZero right shiftedRight))
      (bodyCombine : Derivation
        (combineRequest connective leftBody shiftedRight)
        (combineResult connective leftBody shiftedRight targetBody)) :
      Derivation (combineRequest connective (formEx leftBody) right)
        (combineResult connective (formEx leftBody) right
          (formEx targetBody))
  | combineRightAll
      {connective leftBody rightBody shiftedLeft targetBody : Pattern}
      (leftShift : Derivation
        (formShiftRequest indexZero (formMatrix leftBody))
        (formShiftResult indexZero (formMatrix leftBody) shiftedLeft))
      (bodyCombine : Derivation
        (combineRequest connective shiftedLeft rightBody)
        (combineResult connective shiftedLeft rightBody targetBody)) :
      Derivation (combineRequest connective (formMatrix leftBody)
          (formAll rightBody))
        (combineResult connective (formMatrix leftBody) (formAll rightBody)
          (formAll targetBody))
  | combineRightEx
      {connective leftBody rightBody shiftedLeft targetBody : Pattern}
      (leftShift : Derivation
        (formShiftRequest indexZero (formMatrix leftBody))
        (formShiftResult indexZero (formMatrix leftBody) shiftedLeft))
      (bodyCombine : Derivation
        (combineRequest connective shiftedLeft rightBody)
        (combineResult connective shiftedLeft rightBody targetBody)) :
      Derivation (combineRequest connective (formMatrix leftBody)
          (formEx rightBody))
        (combineResult connective (formMatrix leftBody) (formEx rightBody)
          (formEx targetBody))
  | combineMatricesAnd (left right : Pattern) :
      Derivation (combineRequest connectiveAnd (formMatrix left)
          (formMatrix right))
        (combineResult connectiveAnd (formMatrix left) (formMatrix right)
          (formMatrix (matrixAnd left right)))
  | combineMatricesOr (left right : Pattern) :
      Derivation (combineRequest connectiveOr (formMatrix left)
          (formMatrix right))
        (combineResult connectiveOr (formMatrix left) (formMatrix right)
          (formMatrix (matrixOr left right)))
  | prenexVerum :
      Derivation (prenexRequest sourceVerum)
        (prenexResult sourceVerum (formMatrix matrixVerum))
  | prenexFalsum :
      Derivation (prenexRequest sourceFalsum)
        (prenexResult sourceFalsum (formMatrix matrixFalsum))
  | prenexPositive (relation arguments : Pattern) :
      Derivation (prenexRequest (sourcePositive relation arguments))
        (prenexResult (sourcePositive relation arguments)
          (formMatrix (matrixPositive relation arguments)))
  | prenexNegative (relation arguments : Pattern) :
      Derivation (prenexRequest (sourceNegative relation arguments))
        (prenexResult (sourceNegative relation arguments)
          (formMatrix (matrixNegative relation arguments)))
  | prenexEqual (left right : Pattern) :
      Derivation (prenexRequest (sourceEqual left right))
        (prenexResult (sourceEqual left right)
          (formMatrix (matrixEqual left right)))
  | prenexNotEqual (left right : Pattern) :
      Derivation (prenexRequest (sourceNotEqual left right))
        (prenexResult (sourceNotEqual left right)
          (formMatrix (matrixNotEqual left right)))
  | prenexAnd {left right leftTarget rightTarget target : Pattern}
      (leftPrenex : Derivation (prenexRequest left)
        (prenexResult left leftTarget))
      (rightPrenex : Derivation (prenexRequest right)
        (prenexResult right rightTarget))
      (combined : Derivation (combineRequest connectiveAnd leftTarget rightTarget)
        (combineResult connectiveAnd leftTarget rightTarget target)) :
      Derivation (prenexRequest (sourceAnd left right))
        (prenexResult (sourceAnd left right) target)
  | prenexOr {left right leftTarget rightTarget target : Pattern}
      (leftPrenex : Derivation (prenexRequest left)
        (prenexResult left leftTarget))
      (rightPrenex : Derivation (prenexRequest right)
        (prenexResult right rightTarget))
      (combined : Derivation (combineRequest connectiveOr leftTarget rightTarget)
        (combineResult connectiveOr leftTarget rightTarget target)) :
      Derivation (prenexRequest (sourceOr left right))
        (prenexResult (sourceOr left right) target)
  | prenexAll {body targetBody : Pattern}
      (bodyPrenex : Derivation (prenexRequest body)
        (prenexResult body targetBody)) :
      Derivation (prenexRequest (sourceAll body))
        (prenexResult (sourceAll body) (formAll targetBody))
  | prenexEx {body targetBody : Pattern}
      (bodyPrenex : Derivation (prenexRequest body)
        (prenexResult body targetBody)) :
      Derivation (prenexRequest (sourceEx body))
        (prenexResult (sourceEx body) (formEx targetBody))

def Derivation.height : {source target : Pattern} →
    Derivation source target → Nat
  | _, _, .embeddedShift shift _ => shift.height
  | _, _, .matrixVerum _ | _, _, .matrixFalsum _ => 1
  | _, _, .matrixPositive child | _, _, .matrixNegative child =>
      child.height + 1
  | _, _, .matrixEqual left right | _, _, .matrixNotEqual left right |
      _, _, .matrixAnd left right | _, _, .matrixOr left right =>
      max left.height right.height + 1
  | _, _, .formMatrix child | _, _, .formAll child | _, _, .formEx child =>
      child.height + 1
  | _, _, .combineLeftAll shift combine |
      _, _, .combineLeftEx shift combine |
      _, _, .combineRightAll shift combine |
      _, _, .combineRightEx shift combine =>
      max shift.height combine.height + 1
  | _, _, .combineMatricesAnd _ _ | _, _, .combineMatricesOr _ _ => 1
  | _, _, .prenexVerum | _, _, .prenexFalsum => 1
  | _, _, .prenexPositive _ _ | _, _, .prenexNegative _ _ |
      _, _, .prenexEqual _ _ | _, _, .prenexNotEqual _ _ => 1
  | _, _, .prenexAnd left right combined |
      _, _, .prenexOr left right combined =>
      max (max left.height right.height) combined.height + 1
  | _, _, .prenexAll child | _, _, .prenexEx child => child.height + 1

/-- Every independent structural derivation is interpreted as exactly one
authored reduct.  The equality preserves both result multiplicity and order. -/
theorem Derivation.rewriteAt_exact {source target : Pattern}
    (derivation : Derivation source target)
    (fuel : Nat) (enough : derivation.height <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel source =
      [target] := by
  induction derivation generalizing fuel with
  | embeddedShift shift notFormula =>
      exact embedded_shift_rewriteAt_exact shift notFormula fuel enough
  | matrixVerum cutoff =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using matrix_shift_verum_exact fuel cutoff
  | matrixFalsum cutoff =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using matrix_shift_falsum_exact fuel cutoff
  | matrixPositive child inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : child.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact matrix_shift_positive_exact fuel _ _ _ _
            (inductionHypothesis fuel childEnough)
  | matrixNegative child inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : child.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact matrix_shift_negative_exact fuel _ _ _ _
            (inductionHypothesis fuel childEnough)
  | matrixEqual left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact matrix_shift_equal_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | matrixNotEqual left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact matrix_shift_not_equal_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | matrixAnd left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact matrix_shift_and_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | matrixOr left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact matrix_shift_or_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | formMatrix child inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : child.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact form_shift_matrix_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | formAll child inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : child.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact form_shift_all_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | formEx child inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : child.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact form_shift_ex_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | combineLeftAll shift combine shiftHypothesis combineHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max shift.height combine.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact combine_left_all_exact fuel _ _ _ _ _
            (shiftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (combineHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | combineLeftEx shift combine shiftHypothesis combineHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max shift.height combine.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact combine_left_ex_exact fuel _ _ _ _ _
            (shiftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (combineHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | combineRightAll shift combine shiftHypothesis combineHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max shift.height combine.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact combine_right_all_exact fuel _ _ _ _ _
            (shiftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (combineHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | combineRightEx shift combine shiftHypothesis combineHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough : max shift.height combine.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact combine_right_ex_exact fuel _ _ _ _ _
            (shiftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (combineHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | combineMatricesAnd left right =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using combine_matrices_and_exact fuel left right
  | combineMatricesOr left right =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using combine_matrices_or_exact fuel left right
  | prenexVerum =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using prenex_verum_exact fuel
  | prenexFalsum =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using prenex_falsum_exact fuel
  | prenexPositive relation arguments =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using prenex_positive_exact fuel relation arguments
  | prenexNegative relation arguments =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using prenex_negative_exact fuel relation arguments
  | prenexEqual left right =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using prenex_equal_exact fuel left right
  | prenexNotEqual left right =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => simpa using prenex_not_equal_exact fuel left right
  | prenexAnd left right combined leftHypothesis rightHypothesis combineHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max (max left.height right.height) combined.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height <= fuel :=
            le_trans (Nat.le_max_left _ _)
              (le_trans (Nat.le_max_left _ _) maximumEnough)
          have rightEnough : right.height <= fuel :=
            le_trans (Nat.le_max_right _ _)
              (le_trans (Nat.le_max_left _ _) maximumEnough)
          have combineEnough : combined.height <= fuel :=
            le_trans (Nat.le_max_right _ _) maximumEnough
          exact prenex_and_exact fuel _ _ _ _ _
            (leftHypothesis fuel leftEnough)
            (rightHypothesis fuel rightEnough)
            (combineHypothesis fuel combineEnough)
  | prenexOr left right combined leftHypothesis rightHypothesis combineHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max (max left.height right.height) combined.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height <= fuel :=
            le_trans (Nat.le_max_left _ _)
              (le_trans (Nat.le_max_left _ _) maximumEnough)
          have rightEnough : right.height <= fuel :=
            le_trans (Nat.le_max_right _ _)
              (le_trans (Nat.le_max_left _ _) maximumEnough)
          have combineEnough : combined.height <= fuel :=
            le_trans (Nat.le_max_right _ _) maximumEnough
          exact prenex_or_exact fuel _ _ _ _ _
            (leftHypothesis fuel leftEnough)
            (rightHypothesis fuel rightEnough)
            (combineHypothesis fuel combineEnough)
  | prenexAll child inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : child.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact prenex_all_exact fuel _ _
            (inductionHypothesis fuel childEnough)
  | prenexEx child inductionHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : child.height <= fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          exact prenex_ex_exact fuel _ _
            (inductionHypothesis fuel childEnough)

theorem Derivation.no_invention {source target candidate : Pattern}
    (derivation : Derivation source target)
    (fuel : Nat) (enough : derivation.height <= fuel)
    (membership : candidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel source) :
    candidate = target := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

/-! ## Canonical semantic derivations -/

abbrev Formula (depth : Nat) :=
  TptpFofPrenexSemantics.Formula depth

/-- The structural result computed by matrix shifting, defined without the
rewrite interpreter. -/
noncomputable def matrixShiftTarget (cutoff : Nat) :
    {depth : Nat} → (formula : Formula depth) →
      TptpFofPrenexSemantics.QuantifierFree formula → Pattern
  | _, .verum, _ => matrixVerum
  | _, .falsum, _ => matrixFalsum
  | _, .rel (.predicate predicate) arguments, _ =>
      matrixPositive
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (TptpFofNnfShiftLanguageDef.shiftedTermsPattern cutoff
          (List.ofFn arguments))
  | _, .rel .equality arguments, _ =>
      matrixEqual
        (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 0))
        (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 1))
  | _, .nrel (.predicate predicate) arguments, _ =>
      matrixNegative
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (TptpFofNnfShiftLanguageDef.shiftedTermsPattern cutoff
          (List.ofFn arguments))
  | _, .nrel .equality arguments, _ =>
      matrixNotEqual
        (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 0))
        (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 1))
  | _, .and left right, quantifierFree =>
      matrixAnd
        (matrixShiftTarget cutoff left quantifierFree.1)
        (matrixShiftTarget cutoff right quantifierFree.2)
  | _, .or left right, quantifierFree =>
      matrixOr
        (matrixShiftTarget cutoff left quantifierFree.1)
        (matrixShiftTarget cutoff right quantifierFree.2)
  | _, .all _, impossible => False.elim impossible
  | _, .ex _, impossible => False.elim impossible

/-- Canonical structural derivation for matrix shifting. -/
noncomputable def matrixShiftDerivation (cutoff : Nat) :
    {depth : Nat} → (formula : Formula depth) →
      (quantifierFree : TptpFofPrenexSemantics.QuantifierFree formula) →
      Derivation
        (matrixShiftRequest
          (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
          (TptpFofPrenexLanguageDef.encodeMatrix formula quantifierFree))
        (matrixShiftResult
          (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
          (TptpFofPrenexLanguageDef.encodeMatrix formula quantifierFree)
          (matrixShiftTarget cutoff formula quantifierFree))
  | _, .verum, _ => .matrixVerum _
  | _, .falsum, _ => .matrixFalsum _
  | _, .rel (.predicate predicate) arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixShiftTarget,
        TptpFofPrenexLanguageDef.matrixPositive,
        TptpFofPrenexLanguageDef.a,
        matrixPositive, a,
        TptpFofNnfShiftLanguageDef.sourceTermsPattern_exact] using
        Derivation.matrixPositive
          (Derivation.embeddedShift
            (TptpFofNnfShiftLanguageDef.termsDerivation cutoff
              (List.ofFn arguments)) (by decide))
  | _, .rel .equality arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixShiftTarget,
        TptpFofPrenexLanguageDef.matrixEqual,
        TptpFofPrenexLanguageDef.a,
        matrixEqual, a,
        TptpFofNnfShiftLanguageDef.sourceTermPattern_exact] using
        Derivation.matrixEqual
          (Derivation.embeddedShift
            (TptpFofNnfShiftLanguageDef.termDerivation cutoff (arguments 0))
            (by decide))
          (Derivation.embeddedShift
            (TptpFofNnfShiftLanguageDef.termDerivation cutoff (arguments 1))
            (by decide))
  | _, .nrel (.predicate predicate) arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixShiftTarget,
        TptpFofPrenexLanguageDef.matrixNegative,
        TptpFofPrenexLanguageDef.a,
        matrixNegative, a,
        TptpFofNnfShiftLanguageDef.sourceTermsPattern_exact] using
        Derivation.matrixNegative
          (Derivation.embeddedShift
            (TptpFofNnfShiftLanguageDef.termsDerivation cutoff
              (List.ofFn arguments)) (by decide))
  | _, .nrel .equality arguments, _ => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixShiftTarget,
        TptpFofPrenexLanguageDef.matrixNotEqual,
        TptpFofPrenexLanguageDef.a,
        matrixNotEqual, a,
        TptpFofNnfShiftLanguageDef.sourceTermPattern_exact] using
        Derivation.matrixNotEqual
          (Derivation.embeddedShift
            (TptpFofNnfShiftLanguageDef.termDerivation cutoff (arguments 0))
            (by decide))
          (Derivation.embeddedShift
            (TptpFofNnfShiftLanguageDef.termDerivation cutoff (arguments 1))
            (by decide))
  | _, .and left right, quantifierFree => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixShiftTarget,
        TptpFofPrenexLanguageDef.matrixAnd,
        TptpFofPrenexLanguageDef.a, matrixAnd, a] using
        Derivation.matrixAnd
          (matrixShiftDerivation cutoff left quantifierFree.1)
          (matrixShiftDerivation cutoff right quantifierFree.2)
  | _, .or left right, quantifierFree => by
      simpa [TptpFofPrenexLanguageDef.encodeMatrix, matrixShiftTarget,
        TptpFofPrenexLanguageDef.matrixOr,
        TptpFofPrenexLanguageDef.a, matrixOr, a] using
        Derivation.matrixOr
          (matrixShiftDerivation cutoff left quantifierFree.1)
          (matrixShiftDerivation cutoff right quantifierFree.2)
  | _, .all _, impossible => False.elim impossible
  | _, .ex _, impossible => False.elim impossible

@[simp] theorem encodeMatrix_positive {depth arity : Nat}
    (predicate : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth)
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (.rel (.predicate predicate) arguments)) :
    TptpFofPrenexLanguageDef.encodeMatrix
        (.rel (.predicate predicate) arguments) quantifierFree =
      TptpFofPrenexLanguageDef.matrixPositive
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeMatrix_verum {depth : Nat}
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (show Formula depth from .verum)) :
    TptpFofPrenexLanguageDef.encodeMatrix .verum quantifierFree =
      TptpFofPrenexLanguageDef.matrixVerum := by
  rfl

@[simp] theorem encodeMatrix_falsum {depth : Nat}
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (show Formula depth from .falsum)) :
    TptpFofPrenexLanguageDef.encodeMatrix .falsum quantifierFree =
      TptpFofPrenexLanguageDef.matrixFalsum := by
  rfl

@[simp] theorem encodeMatrix_equal {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth)
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (.rel .equality arguments)) :
    TptpFofPrenexLanguageDef.encodeMatrix (.rel .equality arguments)
        quantifierFree =
      TptpFofPrenexLanguageDef.matrixEqual
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeMatrix_negative {depth arity : Nat}
    (predicate : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth)
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (.nrel (.predicate predicate) arguments)) :
    TptpFofPrenexLanguageDef.encodeMatrix
        (.nrel (.predicate predicate) arguments) quantifierFree =
      TptpFofPrenexLanguageDef.matrixNegative
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeMatrix_notEqual {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth)
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (.nrel .equality arguments)) :
    TptpFofPrenexLanguageDef.encodeMatrix (.nrel .equality arguments)
        quantifierFree =
      TptpFofPrenexLanguageDef.matrixNotEqual
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeMatrix_and {depth : Nat}
    (left right : Formula depth)
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (.and left right)) :
    TptpFofPrenexLanguageDef.encodeMatrix (.and left right)
        quantifierFree =
      TptpFofPrenexLanguageDef.matrixAnd
        (TptpFofPrenexLanguageDef.encodeMatrix left quantifierFree.1)
        (TptpFofPrenexLanguageDef.encodeMatrix right quantifierFree.2) := by
  rfl

@[simp] theorem encodeMatrix_or {depth : Nat}
    (left right : Formula depth)
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree
      (.or left right)) :
    TptpFofPrenexLanguageDef.encodeMatrix (.or left right)
        quantifierFree =
      TptpFofPrenexLanguageDef.matrixOr
        (TptpFofPrenexLanguageDef.encodeMatrix left quantifierFree.1)
        (TptpFofPrenexLanguageDef.encodeMatrix right quantifierFree.2) := by
  rfl

/-- The structural matrix target is exactly the independently defined
binder-safe shift of the semantic matrix. -/
theorem matrixShiftTarget_exact :
    (base cutoff : Nat) ->
    (formula : Formula (base + cutoff)) ->
    (quantifierFree : TptpFofPrenexSemantics.QuantifierFree formula) ->
    matrixShiftTarget cutoff formula quantifierFree =
      TptpFofPrenexLanguageDef.encodeMatrix
        (TptpFofNnfShiftLanguageDef.protectedShift base cutoff ▹ formula)
        (TptpFofPrenexSemantics.quantifierFree_rew
          (TptpFofNnfShiftLanguageDef.protectedShift base cutoff)
          quantifierFree)
  | _, _, .verum, _ => rfl
  | _, _, .falsum, _ => rfl
  | base, cutoff, .rel (.predicate predicate) arguments, _ => by
      change matrixPositive
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofNnfShiftLanguageDef.shiftedTermsPattern cutoff
            (List.ofFn arguments)) =
        TptpFofPrenexLanguageDef.encodeMatrix
          (.rel (.predicate predicate)
            (fun index =>
              TptpFofNnfShiftLanguageDef.protectedShift base cutoff
                (arguments index))) _
      rw [TptpFofNnfShiftLanguageDef.shiftedTermsPattern_exact base cutoff]
      simp [List.map_ofFn, Function.comp_def, matrixPositive, a,
        TptpFofPrenexLanguageDef.matrixPositive,
        TptpFofPrenexLanguageDef.a]
  | base, cutoff, .rel .equality arguments, _ => by
      change matrixEqual
          (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 0))
          (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 1)) =
        TptpFofPrenexLanguageDef.encodeMatrix
          (.rel .equality
            (fun index =>
              TptpFofNnfShiftLanguageDef.protectedShift base cutoff
                (arguments index))) _
      rw [TptpFofNnfShiftLanguageDef.shiftedTermPattern_exact base cutoff,
        TptpFofNnfShiftLanguageDef.shiftedTermPattern_exact base cutoff]
      simp [matrixEqual, a,
        TptpFofPrenexLanguageDef.matrixEqual,
        TptpFofPrenexLanguageDef.a]
  | base, cutoff, .nrel (.predicate predicate) arguments, _ => by
      change matrixNegative
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofNnfShiftLanguageDef.shiftedTermsPattern cutoff
            (List.ofFn arguments)) =
        TptpFofPrenexLanguageDef.encodeMatrix
          (.nrel (.predicate predicate)
            (fun index =>
              TptpFofNnfShiftLanguageDef.protectedShift base cutoff
                (arguments index))) _
      rw [TptpFofNnfShiftLanguageDef.shiftedTermsPattern_exact base cutoff]
      simp [List.map_ofFn, Function.comp_def, matrixNegative, a,
        TptpFofPrenexLanguageDef.matrixNegative,
        TptpFofPrenexLanguageDef.a]
  | base, cutoff, .nrel .equality arguments, _ => by
      change matrixNotEqual
          (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 0))
          (TptpFofNnfShiftLanguageDef.shiftedTermPattern cutoff (arguments 1)) =
        TptpFofPrenexLanguageDef.encodeMatrix
          (.nrel .equality
            (fun index =>
              TptpFofNnfShiftLanguageDef.protectedShift base cutoff
                (arguments index))) _
      rw [TptpFofNnfShiftLanguageDef.shiftedTermPattern_exact base cutoff,
        TptpFofNnfShiftLanguageDef.shiftedTermPattern_exact base cutoff]
      simp [matrixNotEqual, a,
        TptpFofPrenexLanguageDef.matrixNotEqual,
        TptpFofPrenexLanguageDef.a]
  | base, cutoff, .and left right, quantifierFree => by
      change matrixAnd
          (matrixShiftTarget cutoff left quantifierFree.1)
          (matrixShiftTarget cutoff right quantifierFree.2) =
        TptpFofPrenexLanguageDef.encodeMatrix
          (.and
            (TptpFofNnfShiftLanguageDef.protectedShift base cutoff ▹ left)
            (TptpFofNnfShiftLanguageDef.protectedShift base cutoff ▹ right)) _
      rw [matrixShiftTarget_exact base cutoff left quantifierFree.1,
        matrixShiftTarget_exact base cutoff right quantifierFree.2]
      simp [matrixAnd, a,
        TptpFofPrenexLanguageDef.matrixAnd,
        TptpFofPrenexLanguageDef.a]
  | base, cutoff, .or left right, quantifierFree => by
      change matrixOr
          (matrixShiftTarget cutoff left quantifierFree.1)
          (matrixShiftTarget cutoff right quantifierFree.2) =
        TptpFofPrenexLanguageDef.encodeMatrix
          (.or
            (TptpFofNnfShiftLanguageDef.protectedShift base cutoff ▹ left)
            (TptpFofNnfShiftLanguageDef.protectedShift base cutoff ▹ right)) _
      rw [matrixShiftTarget_exact base cutoff left quantifierFree.1,
        matrixShiftTarget_exact base cutoff right quantifierFree.2]
      simp [matrixOr, a,
        TptpFofPrenexLanguageDef.matrixOr,
        TptpFofPrenexLanguageDef.a]
  | _, _, .all _, impossible => False.elim impossible
  | _, _, .ex _, impossible => False.elim impossible

/-- Canonical structural result of shifting every matrix beneath a prenex
prefix.  The cutoff grows when the traversal crosses a binder. -/
noncomputable def formShiftTarget (cutoff : Nat) :
    {depth : Nat} -> TptpFofPrenexSemantics.PrenexForm depth -> Pattern
  | _, .matrix formula quantifierFree =>
      formMatrix (matrixShiftTarget cutoff formula quantifierFree)
  | _, .all body => formAll (formShiftTarget (cutoff + 1) body)
  | _, .ex body => formEx (formShiftTarget (cutoff + 1) body)

/-- Canonical authored derivation for shifting a complete prenex form. -/
noncomputable def formShiftDerivation (cutoff : Nat) :
    {depth : Nat} -> (form : TptpFofPrenexSemantics.PrenexForm depth) ->
    Derivation
      (formShiftRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
        (TptpFofPrenexLanguageDef.encodePrenex form))
      (formShiftResult
        (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
        (TptpFofPrenexLanguageDef.encodePrenex form)
        (formShiftTarget cutoff form))
  | _, .matrix formula quantifierFree => by
      simpa [TptpFofPrenexLanguageDef.encodePrenex, formShiftTarget,
        TptpFofPrenexLanguageDef.matrix, TptpFofPrenexLanguageDef.a,
        formMatrix, a] using
        Derivation.formMatrix
          (matrixShiftDerivation cutoff formula quantifierFree)
  | _, .all body => by
      simpa [TptpFofPrenexLanguageDef.encodePrenex, formShiftTarget,
        TptpFofNnfShiftLanguageDef.encodeNatIndex_succ,
        TptpFofPrenexLanguageDef.all, TptpFofPrenexLanguageDef.a,
        formAll, a] using
        Derivation.formAll (formShiftDerivation (cutoff + 1) body)
  | _, .ex body => by
      simpa [TptpFofPrenexLanguageDef.encodePrenex, formShiftTarget,
        TptpFofNnfShiftLanguageDef.encodeNatIndex_succ,
        TptpFofPrenexLanguageDef.ex, TptpFofPrenexLanguageDef.a,
        formEx, a] using
        Derivation.formEx (formShiftDerivation (cutoff + 1) body)

/-- Form shifting agrees exactly with the independent semantic rewriting of a
prenex object. -/
theorem formShiftTarget_exact :
    (base cutoff : Nat) ->
    (form : TptpFofPrenexSemantics.PrenexForm (base + cutoff)) ->
    formShiftTarget cutoff form =
      TptpFofPrenexLanguageDef.encodePrenex
        (form.rew
          (TptpFofNnfShiftLanguageDef.protectedShift base cutoff))
  | base, cutoff, .matrix formula quantifierFree => by
      rw [formShiftTarget,
        matrixShiftTarget_exact base cutoff formula quantifierFree]
      simp [TptpFofPrenexSemantics.PrenexForm.rew,
        TptpFofPrenexLanguageDef.encodePrenex,
        formMatrix, a, TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.a]
  | base, cutoff, .all body => by
      rw [formShiftTarget,
        formShiftTarget_exact base (cutoff + 1) body]
      simp [TptpFofPrenexSemantics.PrenexForm.rew,
        TptpFofNnfShiftLanguageDef.protectedShift_q,
        TptpFofPrenexLanguageDef.encodePrenex,
        formAll, a, TptpFofPrenexLanguageDef.all,
        TptpFofPrenexLanguageDef.a]
  | base, cutoff, .ex body => by
      rw [formShiftTarget,
        formShiftTarget_exact base (cutoff + 1) body]
      simp [TptpFofPrenexSemantics.PrenexForm.rew,
        TptpFofNnfShiftLanguageDef.protectedShift_q,
        TptpFofPrenexLanguageDef.encodePrenex,
        formEx, a, TptpFofPrenexLanguageDef.ex,
        TptpFofPrenexLanguageDef.a]

/-- Canonical wire constructor for the semantic Boolean connective. -/
def connectivePattern : TptpFofPrenexSemantics.Connective -> Pattern
  | .and => connectiveAnd
  | .or => connectiveOr

/-- Structural target produced by the authored prefix-combination rows.  This
definition follows the prefix shape but does not call the semantic `combine`
function whose agreement is proved below. -/
noncomputable def combineTarget {depth : Nat}
    (connective : TptpFofPrenexSemantics.Connective)
    (left right : TptpFofPrenexSemantics.PrenexForm depth) : Pattern :=
  match left, right with
  | .all leftBody, right =>
      formAll (combineTarget connective leftBody
        (right.rew LO.FirstOrder.Rew.bShift))
  | .ex leftBody, right =>
      formEx (combineTarget connective leftBody
        (right.rew LO.FirstOrder.Rew.bShift))
  | left@(.matrix _ _), .all rightBody =>
      formAll (combineTarget connective
        (left.rew LO.FirstOrder.Rew.bShift) rightBody)
  | left@(.matrix _ _), .ex rightBody =>
      formEx (combineTarget connective
        (left.rew LO.FirstOrder.Rew.bShift) rightBody)
  | .matrix leftFormula leftQf, .matrix rightFormula rightQf =>
      formMatrix <| match connective with
        | .and => matrixAnd
            (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf)
            (TptpFofPrenexLanguageDef.encodeMatrix rightFormula rightQf)
        | .or => matrixOr
            (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf)
            (TptpFofPrenexLanguageDef.encodeMatrix rightFormula rightQf)
termination_by left.quantifierCount + right.quantifierCount
decreasing_by
  all_goals
    simp [TptpFofPrenexSemantics.PrenexForm.quantifierCount,
      TptpFofPrenexSemantics.PrenexForm.rew_quantifierCount_exact, *]

/-- The structural combination target is exactly the independently defined
semantic prefix combination. -/
theorem combineTarget_exact {depth : Nat}
    (connective : TptpFofPrenexSemantics.Connective) :
    (left right : TptpFofPrenexSemantics.PrenexForm depth) ->
    combineTarget connective left right =
      TptpFofPrenexLanguageDef.encodePrenex
        (TptpFofPrenexSemantics.combine connective left right)
  | .all leftBody, right => by
      rw [combineTarget, TptpFofPrenexSemantics.combine,
        combineTarget_exact connective leftBody
          (right.rew LO.FirstOrder.Rew.bShift)]
      simp [TptpFofPrenexLanguageDef.encodePrenex,
        formAll, a, TptpFofPrenexLanguageDef.all,
        TptpFofPrenexLanguageDef.a]
  | .ex leftBody, right => by
      rw [combineTarget, TptpFofPrenexSemantics.combine,
        combineTarget_exact connective leftBody
          (right.rew LO.FirstOrder.Rew.bShift)]
      simp [TptpFofPrenexLanguageDef.encodePrenex,
        formEx, a, TptpFofPrenexLanguageDef.ex,
        TptpFofPrenexLanguageDef.a]
  | .matrix leftFormula leftQf, .all rightBody => by
      rw [combineTarget, TptpFofPrenexSemantics.combine,
        combineTarget_exact connective
          ((TptpFofPrenexSemantics.PrenexForm.matrix
            leftFormula leftQf).rew LO.FirstOrder.Rew.bShift) rightBody]
      simp [TptpFofPrenexLanguageDef.encodePrenex,
        formAll, a, TptpFofPrenexLanguageDef.all,
        TptpFofPrenexLanguageDef.a]
  | .matrix leftFormula leftQf, .ex rightBody => by
      rw [combineTarget, TptpFofPrenexSemantics.combine,
        combineTarget_exact connective
          ((TptpFofPrenexSemantics.PrenexForm.matrix
            leftFormula leftQf).rew LO.FirstOrder.Rew.bShift) rightBody]
      simp [TptpFofPrenexLanguageDef.encodePrenex,
        formEx, a, TptpFofPrenexLanguageDef.ex,
        TptpFofPrenexLanguageDef.a]
  | .matrix leftFormula leftQf, .matrix rightFormula rightQf => by
      cases connective <;>
        simp [combineTarget, TptpFofPrenexSemantics.combine,
          TptpFofPrenexSemantics.Connective.apply,
          TptpFofPrenexLanguageDef.encodePrenex,
          formMatrix, matrixAnd, matrixOr, a,
          TptpFofPrenexLanguageDef.matrix,
          TptpFofPrenexLanguageDef.matrixAnd,
          TptpFofPrenexLanguageDef.matrixOr,
          TptpFofPrenexLanguageDef.a]
termination_by left right => left.quantifierCount + right.quantifierCount
decreasing_by
  all_goals
    simp [TptpFofPrenexSemantics.PrenexForm.quantifierCount,
      TptpFofPrenexSemantics.PrenexForm.rew_quantifierCount_exact, *]

/-- The zero-cutoff form shift is the authored witness for the standard
one-binder lift used by prefix combination. -/
noncomputable def formShiftDerivation_bShift {depth : Nat}
    (form : TptpFofPrenexSemantics.PrenexForm depth) :
    Derivation
      (formShiftRequest indexZero
        (TptpFofPrenexLanguageDef.encodePrenex form))
      (formShiftResult indexZero
        (TptpFofPrenexLanguageDef.encodePrenex form)
        (TptpFofPrenexLanguageDef.encodePrenex
          (form.rew LO.FirstOrder.Rew.bShift))) := by
  have exactTarget := formShiftTarget_exact depth 0 form
  rw [TptpFofNnfShiftLanguageDef.protectedShift_zero] at exactTarget
  simpa [TptpFofNnfShiftLanguageDef.encodeNatIndex_zero,
    exactTarget, indexZero] using formShiftDerivation 0 form

/-- Canonical authored derivation for combining two prenex prefixes. -/
noncomputable def combineDerivation {depth : Nat}
    (connective : TptpFofPrenexSemantics.Connective) :
    (left right : TptpFofPrenexSemantics.PrenexForm depth) ->
    Derivation
      (combineRequest (connectivePattern connective)
        (TptpFofPrenexLanguageDef.encodePrenex left)
        (TptpFofPrenexLanguageDef.encodePrenex right))
      (combineResult (connectivePattern connective)
        (TptpFofPrenexLanguageDef.encodePrenex left)
        (TptpFofPrenexLanguageDef.encodePrenex right)
        (combineTarget connective left right))
  | .all leftBody, right => by
      simpa [combineTarget, TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.all, TptpFofPrenexLanguageDef.a,
        formAll, a] using
        Derivation.combineLeftAll
          (formShiftDerivation_bShift right)
          (combineDerivation connective leftBody
            (right.rew LO.FirstOrder.Rew.bShift))
  | .ex leftBody, right => by
      simpa [combineTarget, TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.ex, TptpFofPrenexLanguageDef.a,
        formEx, a] using
        Derivation.combineLeftEx
          (formShiftDerivation_bShift right)
          (combineDerivation connective leftBody
            (right.rew LO.FirstOrder.Rew.bShift))
  | .matrix leftFormula leftQf, .all rightBody => by
      let left : TptpFofPrenexSemantics.PrenexForm depth :=
        .matrix leftFormula leftQf
      have leftShift : Derivation
          (formShiftRequest indexZero
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf)))
          (formShiftResult indexZero
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf))
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix
                (LO.FirstOrder.Rew.bShift ▹ leftFormula)
                (TptpFofPrenexSemantics.quantifierFree_rew
                  LO.FirstOrder.Rew.bShift leftQf)))) := by
        simpa [left, TptpFofPrenexSemantics.PrenexForm.rew,
          TptpFofPrenexLanguageDef.encodePrenex,
          TptpFofPrenexLanguageDef.matrix,
          TptpFofPrenexLanguageDef.a, formMatrix, a] using
          formShiftDerivation_bShift left
      have bodyCombine : Derivation
          (combineRequest (connectivePattern connective)
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix
                (LO.FirstOrder.Rew.bShift ▹ leftFormula)
                (TptpFofPrenexSemantics.quantifierFree_rew
                  LO.FirstOrder.Rew.bShift leftQf)))
            (TptpFofPrenexLanguageDef.encodePrenex rightBody))
          (combineResult (connectivePattern connective)
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix
                (LO.FirstOrder.Rew.bShift ▹ leftFormula)
                (TptpFofPrenexSemantics.quantifierFree_rew
                  LO.FirstOrder.Rew.bShift leftQf)))
            (TptpFofPrenexLanguageDef.encodePrenex rightBody)
            (combineTarget connective
              (left.rew LO.FirstOrder.Rew.bShift) rightBody)) := by
        simpa [left, TptpFofPrenexSemantics.PrenexForm.rew,
          TptpFofPrenexLanguageDef.encodePrenex,
          TptpFofPrenexLanguageDef.matrix,
          TptpFofPrenexLanguageDef.a, formMatrix, a] using
          combineDerivation connective
            (left.rew LO.FirstOrder.Rew.bShift) rightBody
      simpa [left, combineTarget,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.all, TptpFofPrenexLanguageDef.a,
        formMatrix, formAll, a] using
        Derivation.combineRightAll leftShift bodyCombine
  | .matrix leftFormula leftQf, .ex rightBody => by
      let left : TptpFofPrenexSemantics.PrenexForm depth :=
        .matrix leftFormula leftQf
      have leftShift : Derivation
          (formShiftRequest indexZero
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf)))
          (formShiftResult indexZero
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf))
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix
                (LO.FirstOrder.Rew.bShift ▹ leftFormula)
                (TptpFofPrenexSemantics.quantifierFree_rew
                  LO.FirstOrder.Rew.bShift leftQf)))) := by
        simpa [left, TptpFofPrenexSemantics.PrenexForm.rew,
          TptpFofPrenexLanguageDef.encodePrenex,
          TptpFofPrenexLanguageDef.matrix,
          TptpFofPrenexLanguageDef.a, formMatrix, a] using
          formShiftDerivation_bShift left
      have bodyCombine : Derivation
          (combineRequest (connectivePattern connective)
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix
                (LO.FirstOrder.Rew.bShift ▹ leftFormula)
                (TptpFofPrenexSemantics.quantifierFree_rew
                  LO.FirstOrder.Rew.bShift leftQf)))
            (TptpFofPrenexLanguageDef.encodePrenex rightBody))
          (combineResult (connectivePattern connective)
            (formMatrix
              (TptpFofPrenexLanguageDef.encodeMatrix
                (LO.FirstOrder.Rew.bShift ▹ leftFormula)
                (TptpFofPrenexSemantics.quantifierFree_rew
                  LO.FirstOrder.Rew.bShift leftQf)))
            (TptpFofPrenexLanguageDef.encodePrenex rightBody)
            (combineTarget connective
              (left.rew LO.FirstOrder.Rew.bShift) rightBody)) := by
        simpa [left, TptpFofPrenexSemantics.PrenexForm.rew,
          TptpFofPrenexLanguageDef.encodePrenex,
          TptpFofPrenexLanguageDef.matrix,
          TptpFofPrenexLanguageDef.a, formMatrix, a] using
          combineDerivation connective
            (left.rew LO.FirstOrder.Rew.bShift) rightBody
      simpa [left, combineTarget,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.ex, TptpFofPrenexLanguageDef.a,
        formMatrix, formEx, a] using
        Derivation.combineRightEx leftShift bodyCombine
  | .matrix leftFormula leftQf, .matrix rightFormula rightQf => by
      cases connective with
      | and =>
          simpa [connectivePattern, combineTarget,
            TptpFofPrenexLanguageDef.encodePrenex,
            TptpFofPrenexLanguageDef.matrix,
            TptpFofPrenexLanguageDef.a, formMatrix,
            matrixAnd, a] using
            Derivation.combineMatricesAnd
              (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf)
              (TptpFofPrenexLanguageDef.encodeMatrix rightFormula rightQf)
      | or =>
          simpa [connectivePattern, combineTarget,
            TptpFofPrenexLanguageDef.encodePrenex,
            TptpFofPrenexLanguageDef.matrix,
            TptpFofPrenexLanguageDef.a, formMatrix,
            matrixOr, a] using
            Derivation.combineMatricesOr
              (TptpFofPrenexLanguageDef.encodeMatrix leftFormula leftQf)
              (TptpFofPrenexLanguageDef.encodeMatrix rightFormula rightQf)
termination_by left right => left.quantifierCount + right.quantifierCount
decreasing_by
  all_goals
    simp [TptpFofPrenexSemantics.PrenexForm.quantifierCount,
      TptpFofPrenexSemantics.PrenexForm.rew_quantifierCount_exact, *]

/-- Syntax-directed authored derivation from every canonical NNF formula to
the result of the independently defined total prenex normalizer. -/
noncomputable def prenexDerivation : {depth : Nat} ->
    (formula : Formula depth) ->
    Derivation
      (prenexRequest (TptpFofNnfLanguageDef.encodeFormula formula))
      (prenexResult (TptpFofNnfLanguageDef.encodeFormula formula)
        (TptpFofPrenexLanguageDef.encodePrenex
          (TptpFofPrenexSemantics.prenex formula)))
  | _, .verum => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.matrixVerum,
        TptpFofPrenexLanguageDef.a,
        sourceVerum, formMatrix, matrixVerum, a] using
        Derivation.prenexVerum
  | _, .falsum => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.matrixFalsum,
        TptpFofPrenexLanguageDef.a,
        sourceFalsum, formMatrix, matrixFalsum, a] using
        Derivation.prenexFalsum
  | _, .rel (.predicate predicate) arguments => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.matrixPositive,
        TptpFofPrenexLanguageDef.a,
        sourcePositive, formMatrix, matrixPositive, a] using
        Derivation.prenexPositive
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments))
  | _, .rel .equality arguments => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.matrixEqual,
        TptpFofPrenexLanguageDef.a,
        sourceEqual, formMatrix, matrixEqual, a] using
        Derivation.prenexEqual
          (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
          (TptpResolvedFofLanguageDef.encodeTerm (arguments 1))
  | _, .nrel (.predicate predicate) arguments => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.matrixNegative,
        TptpFofPrenexLanguageDef.a,
        sourceNegative, formMatrix, matrixNegative, a] using
        Derivation.prenexNegative
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments))
  | _, .nrel .equality arguments => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.matrix,
        TptpFofPrenexLanguageDef.matrixNotEqual,
        TptpFofPrenexLanguageDef.a,
        sourceNotEqual, formMatrix, matrixNotEqual, a] using
        Derivation.prenexNotEqual
          (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
          (TptpResolvedFofLanguageDef.encodeTerm (arguments 1))
  | _, .and left right => by
      have combinedExact := combineTarget_exact
        TptpFofPrenexSemantics.Connective.and
        (TptpFofPrenexSemantics.prenex left)
        (TptpFofPrenexSemantics.prenex right)
      simpa [TptpFofPrenexSemantics.prenex, connectivePattern, sourceAnd,
        combinedExact] using
        Derivation.prenexAnd
          (prenexDerivation left)
          (prenexDerivation right)
          (combineDerivation TptpFofPrenexSemantics.Connective.and
            (TptpFofPrenexSemantics.prenex left)
            (TptpFofPrenexSemantics.prenex right))
  | _, .or left right => by
      have combinedExact := combineTarget_exact
        TptpFofPrenexSemantics.Connective.or
        (TptpFofPrenexSemantics.prenex left)
        (TptpFofPrenexSemantics.prenex right)
      simpa [TptpFofPrenexSemantics.prenex, connectivePattern, sourceOr,
        combinedExact] using
        Derivation.prenexOr
          (prenexDerivation left)
          (prenexDerivation right)
          (combineDerivation TptpFofPrenexSemantics.Connective.or
            (TptpFofPrenexSemantics.prenex left)
            (TptpFofPrenexSemantics.prenex right))
  | _, .all body => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.all, TptpFofPrenexLanguageDef.a,
        sourceAll, formAll, a] using
        Derivation.prenexAll (prenexDerivation body)
  | _, .ex body => by
      simpa [TptpFofPrenexSemantics.prenex,
        TptpFofPrenexLanguageDef.encodePrenex,
        TptpFofPrenexLanguageDef.ex, TptpFofPrenexLanguageDef.a,
        sourceEx, formEx, a] using
        Derivation.prenexEx (prenexDerivation body)

/-- Every canonical NNF formula is normalized by the authored LanguageDef to
exactly the independent semantic prenex result. -/
theorem prenex_rewriteAt_exact {depth : Nat} (formula : Formula depth)
    (fuel : Nat) (enough : (prenexDerivation formula).height <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (prenexRequest (TptpFofNnfLanguageDef.encodeFormula formula)) =
      [prenexResult (TptpFofNnfLanguageDef.encodeFormula formula)
        (TptpFofPrenexLanguageDef.encodePrenex
          (TptpFofPrenexSemantics.prenex formula))] :=
  (prenexDerivation formula).rewriteAt_exact fuel enough

/-- The operational normalizer cannot emit any result other than the
independently specified semantic prenex form. -/
theorem prenex_no_invention {depth : Nat} (formula : Formula depth)
    (fuel : Nat) (candidate : Pattern)
    (membership : candidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (prenexRequest (TptpFofNnfLanguageDef.encodeFormula formula)))
    (enough : (prenexDerivation formula).height <= fuel) :
    candidate = prenexResult
      (TptpFofNnfLanguageDef.encodeFormula formula)
      (TptpFofPrenexLanguageDef.encodePrenex
        (TptpFofPrenexSemantics.prenex formula)) := by
  rw [prenex_rewriteAt_exact formula fuel enough] at membership
  simpa using membership

#print axioms language_validate
#print axioms shiftInclusion
#print axioms targetInclusion
#print axioms embedded_index_zero_at_zero_exact
#print axioms matrixShiftTarget_exact
#print axioms formShiftTarget_exact
#print axioms combineTarget_exact
#print axioms prenex_rewriteAt_exact
#print axioms prenex_no_invention

end Mettapedia.GSLT.LanguageDef.TptpFofPrenexNormalizationLanguageDef
