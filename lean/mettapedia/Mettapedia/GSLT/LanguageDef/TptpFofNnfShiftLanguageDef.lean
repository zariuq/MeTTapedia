import Mettapedia.GSLT.LanguageDef.TptpFofNnfLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-!
# Capture-avoiding shift for canonical TPTP FOF NNF

This authored transformation inserts one ambient de Bruijn variable after an
explicit number of protected binders.  The cutoff is a structural natural
number; terms, term lists, and formulas are traversed by ordinary congruence
premises.  Quantifier rules increment the cutoff before traversing their body.

The language is intentionally reusable.  Prenex conversion uses it when a
quantifier crosses a Boolean connective, while later binder-sensitive stages
can use the same operation without acquiring a native shifting primitive.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofNnfShiftLanguageDef

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

def indexZero : Pattern := a "tptp-fof-resolved:index-zero"
def indexSucc (index : Pattern) : Pattern :=
  a "tptp-fof-resolved:index-succ" [index]

def termVariable (index : Pattern) : Pattern :=
  a "tptp-fof-resolved:term-variable" [index]
def termFunction (function arguments : Pattern) : Pattern :=
  a "tptp-fof-resolved:term-function" [function, arguments]
def termsNil : Pattern := a "tptp-fof-resolved:terms-nil"
def termsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-resolved:terms-cons" [head, tail]

def verum : Pattern := a "tptp-fof-nnf:verum"
def falsum : Pattern := a "tptp-fof-nnf:falsum"
def positive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-nnf:positive" [relation, arguments]
def negative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-nnf:negative" [relation, arguments]
def equal (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:equal" [left, right]
def notEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:not-equal" [left, right]
def and (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:and" [left, right]
def or (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:or" [left, right]
def all (body : Pattern) : Pattern := a "tptp-fof-nnf:all" [body]
def ex (body : Pattern) : Pattern := a "tptp-fof-nnf:ex" [body]

def indexRequest (cutoff source : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:index-request" [cutoff, source]
def indexResult (cutoff source target : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:index-result" [cutoff, source, target]

def termRequest (cutoff source : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:term-request" [cutoff, source]
def termResult (cutoff source target : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:term-result" [cutoff, source, target]

def termsRequest (cutoff source : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:terms-request" [cutoff, source]
def termsResult (cutoff source target : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:terms-result" [cutoff, source, target]

def formulaRequest (cutoff source : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:formula-request" [cutoff, source]
def formulaResult (cutoff source target : Pattern) : Pattern :=
  a "tptp-fof-nnf-shift:formula-result" [cutoff, source, target]

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

def rewrites : List RewriteRule := [
  mkRule "tptp-fof-nnf-shift:index-zero-at-zero" [] []
    (indexRequest indexZero indexZero)
    (indexResult indexZero indexZero (indexSucc indexZero)),
  mkRule "tptp-fof-nnf-shift:index-succ-at-zero"
    [("index", "TptpResolvedFof:Index")] []
    (indexRequest indexZero (indexSucc (v "index")))
    (indexResult indexZero (indexSucc (v "index"))
      (indexSucc (indexSucc (v "index")))),
  mkRule "tptp-fof-nnf-shift:index-zero-under-binder"
    [("cutoff", "TptpResolvedFof:Index")] []
    (indexRequest (indexSucc (v "cutoff")) indexZero)
    (indexResult (indexSucc (v "cutoff")) indexZero indexZero),
  mkRule "tptp-fof-nnf-shift:index-succ-under-binder"
    [("cutoff", "TptpResolvedFof:Index"),
     ("index", "TptpResolvedFof:Index"),
     ("target", "TptpResolvedFof:Index")]
    [congruence
      (indexRequest (v "cutoff") (v "index"))
      (indexResult (v "cutoff") (v "index") (v "target"))]
    (indexRequest (indexSucc (v "cutoff")) (indexSucc (v "index")))
    (indexResult (indexSucc (v "cutoff")) (indexSucc (v "index"))
      (indexSucc (v "target"))),

  mkRule "tptp-fof-nnf-shift:term-variable"
    [("cutoff", "TptpResolvedFof:Index"),
     ("index", "TptpResolvedFof:Index"),
     ("targetIndex", "TptpResolvedFof:Index")]
    [congruence
      (indexRequest (v "cutoff") (v "index"))
      (indexResult (v "cutoff") (v "index") (v "targetIndex"))]
    (termRequest (v "cutoff") (termVariable (v "index")))
    (termResult (v "cutoff") (termVariable (v "index"))
      (termVariable (v "targetIndex"))),
  mkRule "tptp-fof-nnf-shift:term-function"
    [("cutoff", "TptpResolvedFof:Index"),
     ("function", "TptpFofSymbol:FunctionHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpResolvedFof:Terms")]
    [congruence
      (termsRequest (v "cutoff") (v "arguments"))
      (termsResult (v "cutoff") (v "arguments") (v "targetArguments"))]
    (termRequest (v "cutoff")
      (termFunction (v "function") (v "arguments")))
    (termResult (v "cutoff")
      (termFunction (v "function") (v "arguments"))
      (termFunction (v "function") (v "targetArguments"))),

  mkRule "tptp-fof-nnf-shift:terms-nil"
    [("cutoff", "TptpResolvedFof:Index")] []
    (termsRequest (v "cutoff") termsNil)
    (termsResult (v "cutoff") termsNil termsNil),
  mkRule "tptp-fof-nnf-shift:terms-cons"
    [("cutoff", "TptpResolvedFof:Index"),
     ("head", "TptpResolvedFof:Term"),
     ("tail", "TptpResolvedFof:Terms"),
     ("targetHead", "TptpResolvedFof:Term"),
     ("targetTail", "TptpResolvedFof:Terms")]
    [congruence
      (termRequest (v "cutoff") (v "head"))
      (termResult (v "cutoff") (v "head") (v "targetHead")),
     congruence
      (termsRequest (v "cutoff") (v "tail"))
      (termsResult (v "cutoff") (v "tail") (v "targetTail"))]
    (termsRequest (v "cutoff") (termsCons (v "head") (v "tail")))
    (termsResult (v "cutoff") (termsCons (v "head") (v "tail"))
      (termsCons (v "targetHead") (v "targetTail"))),

  mkRule "tptp-fof-nnf-shift:verum"
    [("cutoff", "TptpResolvedFof:Index")] []
    (formulaRequest (v "cutoff") verum)
    (formulaResult (v "cutoff") verum verum),
  mkRule "tptp-fof-nnf-shift:falsum"
    [("cutoff", "TptpResolvedFof:Index")] []
    (formulaRequest (v "cutoff") falsum)
    (formulaResult (v "cutoff") falsum falsum),
  mkRule "tptp-fof-nnf-shift:positive"
    [("cutoff", "TptpResolvedFof:Index"),
     ("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpResolvedFof:Terms")]
    [congruence
      (termsRequest (v "cutoff") (v "arguments"))
      (termsResult (v "cutoff") (v "arguments") (v "targetArguments"))]
    (formulaRequest (v "cutoff")
      (positive (v "relation") (v "arguments")))
    (formulaResult (v "cutoff")
      (positive (v "relation") (v "arguments"))
      (positive (v "relation") (v "targetArguments"))),
  mkRule "tptp-fof-nnf-shift:negative"
    [("cutoff", "TptpResolvedFof:Index"),
     ("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpResolvedFof:Terms")]
    [congruence
      (termsRequest (v "cutoff") (v "arguments"))
      (termsResult (v "cutoff") (v "arguments") (v "targetArguments"))]
    (formulaRequest (v "cutoff")
      (negative (v "relation") (v "arguments")))
    (formulaResult (v "cutoff")
      (negative (v "relation") (v "arguments"))
      (negative (v "relation") (v "targetArguments"))),
  mkRule "tptp-fof-nnf-shift:equal"
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
    (formulaRequest (v "cutoff") (equal (v "left") (v "right")))
    (formulaResult (v "cutoff") (equal (v "left") (v "right"))
      (equal (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-nnf-shift:not-equal"
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
    (formulaRequest (v "cutoff") (notEqual (v "left") (v "right")))
    (formulaResult (v "cutoff") (notEqual (v "left") (v "right"))
      (notEqual (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-nnf-shift:and"
    [("cutoff", "TptpResolvedFof:Index"), ("left", "NNFFormula"),
     ("right", "NNFFormula"), ("targetLeft", "NNFFormula"),
     ("targetRight", "NNFFormula")]
    [congruence
      (formulaRequest (v "cutoff") (v "left"))
      (formulaResult (v "cutoff") (v "left") (v "targetLeft")),
     congruence
      (formulaRequest (v "cutoff") (v "right"))
      (formulaResult (v "cutoff") (v "right") (v "targetRight"))]
    (formulaRequest (v "cutoff") (and (v "left") (v "right")))
    (formulaResult (v "cutoff") (and (v "left") (v "right"))
      (and (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-nnf-shift:or"
    [("cutoff", "TptpResolvedFof:Index"), ("left", "NNFFormula"),
     ("right", "NNFFormula"), ("targetLeft", "NNFFormula"),
     ("targetRight", "NNFFormula")]
    [congruence
      (formulaRequest (v "cutoff") (v "left"))
      (formulaResult (v "cutoff") (v "left") (v "targetLeft")),
     congruence
      (formulaRequest (v "cutoff") (v "right"))
      (formulaResult (v "cutoff") (v "right") (v "targetRight"))]
    (formulaRequest (v "cutoff") (or (v "left") (v "right")))
    (formulaResult (v "cutoff") (or (v "left") (v "right"))
      (or (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-nnf-shift:all"
    [("cutoff", "TptpResolvedFof:Index"), ("body", "NNFFormula"),
     ("targetBody", "NNFFormula")]
    [congruence
      (formulaRequest (indexSucc (v "cutoff")) (v "body"))
      (formulaResult (indexSucc (v "cutoff")) (v "body")
        (v "targetBody"))]
    (formulaRequest (v "cutoff") (all (v "body")))
    (formulaResult (v "cutoff") (all (v "body"))
      (all (v "targetBody"))),
  mkRule "tptp-fof-nnf-shift:ex"
    [("cutoff", "TptpResolvedFof:Index"), ("body", "NNFFormula"),
     ("targetBody", "NNFFormula")]
    [congruence
      (formulaRequest (indexSucc (v "cutoff")) (v "body"))
      (formulaResult (indexSucc (v "cutoff")) (v "body")
        (v "targetBody"))]
    (formulaRequest (v "cutoff") (ex (v "body")))
    (formulaResult (v "cutoff") (ex (v "body"))
      (ex (v "targetBody")))
]

def operationTerms : List GrammarRule := [
  ctor "tptp-fof-nnf-shift:index-request" "TptpFofNnfShift:IndexResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpResolvedFof:Index")] (some .rewrite),
  ctor "tptp-fof-nnf-shift:index-result" "TptpFofNnfShift:IndexResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpResolvedFof:Index"),
     ("target", "TptpResolvedFof:Index")],
  ctor "tptp-fof-nnf-shift:term-request" "TptpFofNnfShift:TermResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpResolvedFof:Term")] (some .rewrite),
  ctor "tptp-fof-nnf-shift:term-result" "TptpFofNnfShift:TermResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpResolvedFof:Term"),
     ("target", "TptpResolvedFof:Term")],
  ctor "tptp-fof-nnf-shift:terms-request" "TptpFofNnfShift:TermsResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpResolvedFof:Terms")] (some .rewrite),
  ctor "tptp-fof-nnf-shift:terms-result" "TptpFofNnfShift:TermsResult"
    [("cutoff", "TptpResolvedFof:Index"),
     ("source", "TptpResolvedFof:Terms"),
     ("target", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-nnf-shift:formula-request" "TptpFofNnfShift:FormulaResult"
    [("cutoff", "TptpResolvedFof:Index"), ("source", "NNFFormula")]
    (some .rewrite),
  ctor "tptp-fof-nnf-shift:formula-result" "TptpFofNnfShift:FormulaResult"
    [("cutoff", "TptpResolvedFof:Index"), ("source", "NNFFormula"),
     ("target", "NNFFormula")]
]

def language : LanguageDef := {
  name := "TptpFofNnfShift"
  types := TptpFofNnfLanguageDef.language.types ++ [
    ("TptpFofNnfShift:IndexResult" : TypeDecl),
    ("TptpFofNnfShift:TermResult" : TypeDecl),
    ("TptpFofNnfShift:TermsResult" : TypeDecl),
    ("TptpFofNnfShift:FormulaResult" : TypeDecl)]
  terms := TptpFofNnfLanguageDef.language.terms ++ operationTerms
  equations := []
  rewrites
}

theorem rewrite_count : rewrites.length = 18 := by decide

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

@[simp] private theorem language_typeNames : language.typeNames = [
    "String", "TptpFofSymbol:FunctionHead",
    "TptpFofSymbol:PredicateHead", "TptpResolvedFof:Index",
    "TptpResolvedFof:Term",
    "TptpResolvedFof:Terms", "TptpResolvedFof:Formula", "NNFFormula",
    "TptpFofNnfShift:IndexResult", "TptpFofNnfShift:TermResult",
    "TptpFofNnfShift:TermsResult", "TptpFofNnfShift:FormulaResult"] := by
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
      ("tptp-fof-nnf-shift:formula-result", 3)] := by
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
      "tptp-fof-nnf-shift:formula-result"] := by
  rfl

local macro "certify_shift_row" : tactic =>
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
      rewrites, language_typeNames, language_constructorSignatures,
      language_constructorLabels, typed, mkRule, congruence, indexRequest,
      indexResult, termRequest, termResult, termsRequest, termsResult,
      formulaRequest, formulaResult, indexZero, indexSucc, termVariable,
      termFunction, termsNil, termsCons, verum, falsum, positive, negative,
      equal, notEqual, and, or, all, ex, a, v,
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

private theorem rewrite00_checked :
    RewriteValidationCertificate.check language rewrites[0] = true := by
  certify_shift_row
private theorem rewrite01_checked :
    RewriteValidationCertificate.check language rewrites[1] = true := by
  certify_shift_row
private theorem rewrite02_checked :
    RewriteValidationCertificate.check language rewrites[2] = true := by
  certify_shift_row
private theorem rewrite03_checked :
    RewriteValidationCertificate.check language rewrites[3] = true := by
  certify_shift_row
private theorem rewrite04_checked :
    RewriteValidationCertificate.check language rewrites[4] = true := by
  certify_shift_row
private theorem rewrite05_checked :
    RewriteValidationCertificate.check language rewrites[5] = true := by
  certify_shift_row
private theorem rewrite06_checked :
    RewriteValidationCertificate.check language rewrites[6] = true := by
  certify_shift_row
private theorem rewrite07_checked :
    RewriteValidationCertificate.check language rewrites[7] = true := by
  certify_shift_row
private theorem rewrite08_checked :
    RewriteValidationCertificate.check language rewrites[8] = true := by
  certify_shift_row
private theorem rewrite09_checked :
    RewriteValidationCertificate.check language rewrites[9] = true := by
  certify_shift_row
private theorem rewrite10_checked :
    RewriteValidationCertificate.check language rewrites[10] = true := by
  certify_shift_row
private theorem rewrite11_checked :
    RewriteValidationCertificate.check language rewrites[11] = true := by
  certify_shift_row
private theorem rewrite12_checked :
    RewriteValidationCertificate.check language rewrites[12] = true := by
  certify_shift_row
private theorem rewrite13_checked :
    RewriteValidationCertificate.check language rewrites[13] = true := by
  certify_shift_row
private theorem rewrite14_checked :
    RewriteValidationCertificate.check language rewrites[14] = true := by
  certify_shift_row
private theorem rewrite15_checked :
    RewriteValidationCertificate.check language rewrites[15] = true := by
  certify_shift_row
private theorem rewrite16_checked :
    RewriteValidationCertificate.check language rewrites[16] = true := by
  certify_shift_row
private theorem rewrite17_checked :
    RewriteValidationCertificate.check language rewrites[17] = true := by
  certify_shift_row

private theorem every_rewrite_checked (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.check language rewrite = true := by
  simp only [rewrites, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · simpa [rewrites] using rewrite00_checked
  · simpa [rewrites] using rewrite01_checked
  · simpa [rewrites] using rewrite02_checked
  · simpa [rewrites] using rewrite03_checked
  · simpa [rewrites] using rewrite04_checked
  · simpa [rewrites] using rewrite05_checked
  · simpa [rewrites] using rewrite06_checked
  · simpa [rewrites] using rewrite07_checked
  · simpa [rewrites] using rewrite08_checked
  · simpa [rewrites] using rewrite09_checked
  · simpa [rewrites] using rewrite10_checked
  · simpa [rewrites] using rewrite11_checked
  · simpa [rewrites] using rewrite12_checked
  · simpa [rewrites] using rewrite13_checked
  · simpa [rewrites] using rewrite14_checked
  · simpa [rewrites] using rewrite15_checked
  · simpa [rewrites] using rewrite16_checked
  · simpa [rewrites] using rewrite17_checked

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
    constructorLabels_nodup
  exact every_rewrite_checked rewrite membership

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def sourceInclusion :
    StructuralMorphism TptpFofNnfLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈ TptpFofNnfLanguageDef.language.equations at membership
    simp [TptpFofNnfLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈ TptpFofNnfLanguageDef.language.rewrites at membership
    simp [TptpFofNnfLanguageDef.no_rewrites] at membership

/-! ## Exact root rules -/

local macro "shift_root" : tactic =>
  `(tactic|
    simp [rewriteAt, language_rewrites, rewrites, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      mkRule, congruence, indexRequest, indexResult, termRequest, termResult,
      termsRequest, termsResult, formulaRequest, formulaResult, indexZero,
      indexSucc, termVariable, termFunction, termsNil, termsCons, verum,
      falsum, positive, negative, equal, notEqual, and, or, all, ex, a, v,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings])

local syntax "shift_root_using " term,* : tactic
local macro_rules
  | `(tactic| shift_root_using $_proofs:term,*) =>
      `(tactic|
        simp only [indexRequest, indexResult, termRequest, termResult,
          termsRequest, termsResult, formulaRequest, formulaResult,
          indexZero, indexSucc, termVariable, termFunction, termsNil,
          termsCons, verum, falsum, positive, negative, equal, notEqual,
          and, or, all, ex, a] at * <;>
        simp [*, rewriteAt, language_rewrites, rewrites, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
          mkRule, congruence, indexRequest, indexResult, termRequest,
          termResult, termsRequest, termsResult, formulaRequest,
          formulaResult, indexZero, indexSucc, termVariable, termFunction,
          termsNil, termsCons, verum, falsum, positive, negative, equal,
          notEqual, and, or, all, ex, a, v, matchPattern, matchArgs,
          mergeBindings, applyBindingsForRule, applyBindings])

theorem index_zero_at_zero_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest indexZero indexZero) =
      [indexResult indexZero indexZero (indexSucc indexZero)] := by
  shift_root

theorem index_succ_at_zero_exact (fuel : Nat) (index : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest indexZero (indexSucc index)) =
      [indexResult indexZero (indexSucc index)
        (indexSucc (indexSucc index))] := by
  shift_root

theorem index_zero_under_binder_exact (fuel : Nat) (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest (indexSucc cutoff) indexZero) =
      [indexResult (indexSucc cutoff) indexZero indexZero] := by
  shift_root

theorem index_succ_under_binder_exact (fuel : Nat)
    (cutoff index target : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (indexRequest cutoff index) = [indexResult cutoff index target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (indexRequest (indexSucc cutoff) (indexSucc index)) =
      [indexResult (indexSucc cutoff) (indexSucc index)
        (indexSucc target)] := by
  shift_root_using exact

theorem term_variable_exact (fuel : Nat) (cutoff index target : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (indexRequest cutoff index) = [indexResult cutoff index target]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termRequest cutoff (termVariable index)) =
      [termResult cutoff (termVariable index) (termVariable target)] := by
  shift_root_using exact

theorem term_function_exact (fuel : Nat)
    (cutoff function arguments targetArguments : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsRequest cutoff arguments) =
        [termsResult cutoff arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termRequest cutoff (termFunction function arguments)) =
      [termResult cutoff (termFunction function arguments)
        (termFunction function targetArguments)] := by
  shift_root_using exact

theorem terms_nil_exact (fuel : Nat) (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termsRequest cutoff termsNil) =
      [termsResult cutoff termsNil termsNil] := by
  shift_root

theorem terms_cons_exact (fuel : Nat)
    (cutoff head tail targetHead targetTail : Pattern)
    (headExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff head) = [termResult cutoff head targetHead])
    (tailExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsRequest cutoff tail) = [termsResult cutoff tail targetTail]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (termsRequest cutoff (termsCons head tail)) =
      [termsResult cutoff (termsCons head tail)
        (termsCons targetHead targetTail)] := by
  shift_root_using headExact, tailExact

theorem verum_exact (fuel : Nat) (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff verum) =
      [formulaResult cutoff verum verum] := by
  shift_root

theorem falsum_exact (fuel : Nat) (cutoff : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff falsum) =
      [formulaResult cutoff falsum falsum] := by
  shift_root

theorem positive_exact (fuel : Nat)
    (cutoff relation arguments targetArguments : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsRequest cutoff arguments) =
        [termsResult cutoff arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (positive relation arguments)) =
      [formulaResult cutoff (positive relation arguments)
        (positive relation targetArguments)] := by
  shift_root_using exact

theorem negative_exact (fuel : Nat)
    (cutoff relation arguments targetArguments : Pattern)
    (exact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termsRequest cutoff arguments) =
        [termsResult cutoff arguments targetArguments]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (negative relation arguments)) =
      [formulaResult cutoff (negative relation arguments)
        (negative relation targetArguments)] := by
  shift_root_using exact

theorem equal_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff left) = [termResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff right) = [termResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (equal left right)) =
      [formulaResult cutoff (equal left right)
        (equal targetLeft targetRight)] := by
  shift_root_using leftExact, rightExact

theorem notEqual_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff left) = [termResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (termRequest cutoff right) = [termResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (notEqual left right)) =
      [formulaResult cutoff (notEqual left right)
        (notEqual targetLeft targetRight)] := by
  shift_root_using leftExact, rightExact

theorem and_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formulaRequest cutoff left) =
        [formulaResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formulaRequest cutoff right) =
        [formulaResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (and left right)) =
      [formulaResult cutoff (and left right) (and targetLeft targetRight)] := by
  shift_root_using leftExact, rightExact

theorem or_exact (fuel : Nat)
    (cutoff left right targetLeft targetRight : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formulaRequest cutoff left) =
        [formulaResult cutoff left targetLeft])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formulaRequest cutoff right) =
        [formulaResult cutoff right targetRight]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (or left right)) =
      [formulaResult cutoff (or left right) (or targetLeft targetRight)] := by
  shift_root_using leftExact, rightExact

theorem all_exact (fuel : Nat) (cutoff body targetBody : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formulaRequest (indexSucc cutoff) body) =
        [formulaResult (indexSucc cutoff) body targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (all body)) =
      [formulaResult cutoff (all body) (all targetBody)] := by
  shift_root_using bodyExact

theorem ex_exact (fuel : Nat) (cutoff body targetBody : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (formulaRequest (indexSucc cutoff) body) =
        [formulaResult (indexSucc cutoff) body targetBody]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (formulaRequest cutoff (ex body)) =
      [formulaResult cutoff (ex body) (ex targetBody)] := by
  shift_root_using bodyExact

/-! ## Independent structural shift derivations -/

inductive SubjectSort
  | index
  | term
  | terms
  | formula
  deriving DecidableEq, Repr

def SubjectSort.request : SubjectSort -> Pattern -> Pattern -> Pattern
  | .index => indexRequest
  | .term => termRequest
  | .terms => termsRequest
  | .formula => formulaRequest

def SubjectSort.result :
    SubjectSort -> Pattern -> Pattern -> Pattern -> Pattern
  | .index => indexResult
  | .term => termResult
  | .terms => termsResult
  | .formula => formulaResult

/-- A derivation of one capture-avoiding insertion on the structural
representation.  This relation is independent of the rewrite engine and
mirrors the mathematical recursion on cutoff and syntax. -/
inductive ShiftDerivation :
    SubjectSort -> Pattern -> Pattern -> Pattern -> Type
  | indexZeroAtZero :
      ShiftDerivation .index indexZero indexZero (indexSucc indexZero)
  | indexSuccAtZero (index : Pattern) :
      ShiftDerivation .index indexZero (indexSucc index)
        (indexSucc (indexSucc index))
  | indexZeroUnderBinder (cutoff : Pattern) :
      ShiftDerivation .index (indexSucc cutoff) indexZero indexZero
  | indexSuccUnderBinder {cutoff index target : Pattern}
      (prior : ShiftDerivation .index cutoff index target) :
      ShiftDerivation .index (indexSucc cutoff) (indexSucc index)
        (indexSucc target)
  | termVariable {cutoff index target : Pattern}
      (indexShift : ShiftDerivation .index cutoff index target) :
      ShiftDerivation .term cutoff (termVariable index)
        (termVariable target)
  | termFunction {cutoff function arguments targetArguments : Pattern}
      (argumentsShift :
        ShiftDerivation .terms cutoff arguments targetArguments) :
      ShiftDerivation .term cutoff (termFunction function arguments)
        (termFunction function targetArguments)
  | termsNil (cutoff : Pattern) :
      ShiftDerivation .terms cutoff termsNil termsNil
  | termsCons {cutoff head tail targetHead targetTail : Pattern}
      (headShift : ShiftDerivation .term cutoff head targetHead)
      (tailShift : ShiftDerivation .terms cutoff tail targetTail) :
      ShiftDerivation .terms cutoff (termsCons head tail)
        (termsCons targetHead targetTail)
  | formulaVerum (cutoff : Pattern) :
      ShiftDerivation .formula cutoff verum verum
  | formulaFalsum (cutoff : Pattern) :
      ShiftDerivation .formula cutoff falsum falsum
  | formulaPositive {cutoff relation arguments targetArguments : Pattern}
      (argumentsShift :
        ShiftDerivation .terms cutoff arguments targetArguments) :
      ShiftDerivation .formula cutoff (positive relation arguments)
        (positive relation targetArguments)
  | formulaNegative {cutoff relation arguments targetArguments : Pattern}
      (argumentsShift :
        ShiftDerivation .terms cutoff arguments targetArguments) :
      ShiftDerivation .formula cutoff (negative relation arguments)
        (negative relation targetArguments)
  | formulaEqual {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : ShiftDerivation .term cutoff left targetLeft)
      (rightShift : ShiftDerivation .term cutoff right targetRight) :
      ShiftDerivation .formula cutoff (equal left right)
        (equal targetLeft targetRight)
  | formulaNotEqual {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : ShiftDerivation .term cutoff left targetLeft)
      (rightShift : ShiftDerivation .term cutoff right targetRight) :
      ShiftDerivation .formula cutoff (notEqual left right)
        (notEqual targetLeft targetRight)
  | formulaAnd {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : ShiftDerivation .formula cutoff left targetLeft)
      (rightShift : ShiftDerivation .formula cutoff right targetRight) :
      ShiftDerivation .formula cutoff (and left right)
        (and targetLeft targetRight)
  | formulaOr {cutoff left right targetLeft targetRight : Pattern}
      (leftShift : ShiftDerivation .formula cutoff left targetLeft)
      (rightShift : ShiftDerivation .formula cutoff right targetRight) :
      ShiftDerivation .formula cutoff (or left right)
        (or targetLeft targetRight)
  | formulaAll {cutoff body targetBody : Pattern}
      (bodyShift : ShiftDerivation .formula (indexSucc cutoff) body targetBody) :
      ShiftDerivation .formula cutoff (all body) (all targetBody)
  | formulaEx {cutoff body targetBody : Pattern}
      (bodyShift : ShiftDerivation .formula (indexSucc cutoff) body targetBody) :
      ShiftDerivation .formula cutoff (ex body) (ex targetBody)

def ShiftDerivation.height :
    {sort : SubjectSort} -> {cutoff source target : Pattern} ->
      ShiftDerivation sort cutoff source target -> Nat
  | _, _, _, _, .indexZeroAtZero => 1
  | _, _, _, _, .indexSuccAtZero _ => 1
  | _, _, _, _, .indexZeroUnderBinder _ => 1
  | _, _, _, _, .indexSuccUnderBinder prior => prior.height + 1
  | _, _, _, _, .termVariable indexShift => indexShift.height + 1
  | _, _, _, _, .termFunction argumentsShift => argumentsShift.height + 1
  | _, _, _, _, .termsNil _ => 1
  | _, _, _, _, .termsCons headShift tailShift =>
      max headShift.height tailShift.height + 1
  | _, _, _, _, .formulaVerum _ => 1
  | _, _, _, _, .formulaFalsum _ => 1
  | _, _, _, _, .formulaPositive argumentsShift => argumentsShift.height + 1
  | _, _, _, _, .formulaNegative argumentsShift => argumentsShift.height + 1
  | _, _, _, _, .formulaEqual leftShift rightShift =>
      max leftShift.height rightShift.height + 1
  | _, _, _, _, .formulaNotEqual leftShift rightShift =>
      max leftShift.height rightShift.height + 1
  | _, _, _, _, .formulaAnd leftShift rightShift =>
      max leftShift.height rightShift.height + 1
  | _, _, _, _, .formulaOr leftShift rightShift =>
      max leftShift.height rightShift.height + 1
  | _, _, _, _, .formulaAll bodyShift => bodyShift.height + 1
  | _, _, _, _, .formulaEx bodyShift => bodyShift.height + 1

/-! ## Canonical derivations and semantic insertion -/

def shiftIndexValue : Nat -> Nat -> Nat
  | 0, index => index + 1
  | _ + 1, 0 => 0
  | cutoff + 1, index + 1 => shiftIndexValue cutoff index + 1

theorem shiftIndexValue_lt (base cutoff index : Nat)
    (bound : index < base + cutoff) :
    shiftIndexValue cutoff index < (base + 1) + cutoff := by
  induction cutoff generalizing index with
  | zero => simpa [shiftIndexValue] using bound
  | succ cutoff inductionHypothesis =>
      cases index with
      | zero => simp [shiftIndexValue]
      | succ index =>
          simp only [shiftIndexValue]
          have prior := inductionHypothesis index (by omega)
          omega

def shiftFin (base cutoff : Nat) (index : Fin (base + cutoff)) :
    Fin ((base + 1) + cutoff) :=
  ⟨shiftIndexValue cutoff index.val,
    shiftIndexValue_lt base cutoff index.val index.isLt⟩

@[simp] theorem shiftFin_zero (base cutoff : Nat) :
    shiftFin base (cutoff + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem shiftFin_succ (base cutoff : Nat)
    (index : Fin (base + cutoff)) :
    shiftFin base (cutoff + 1) index.succ =
      (shiftFin base cutoff index).succ := by
  apply Fin.ext
  rfl

def protectedShift (base cutoff : Nat) :
    LO.FirstOrder.Rew
      TptpFofNormalizationSemantics.language Empty (base + cutoff)
      Empty ((base + 1) + cutoff) :=
  LO.FirstOrder.Rew.map (shiftFin base cutoff) id

theorem protectedShift_q (base cutoff : Nat) :
    (protectedShift base cutoff).q = protectedShift base (cutoff + 1) := by
  apply LO.FirstOrder.Rew.ext
  · intro index
    refine Fin.cases ?_ (fun prior => ?_) index
    · simp [protectedShift]
    · simp [protectedShift]
  · intro impossible
    exact nomatch impossible

@[simp] theorem encodeNatIndex_zero :
    TptpResolvedFofLanguageDef.encodeNatIndex 0 = indexZero := by
  rfl

@[simp] theorem encodeNatIndex_succ (index : Nat) :
    TptpResolvedFofLanguageDef.encodeNatIndex (index + 1) =
      indexSucc (TptpResolvedFofLanguageDef.encodeNatIndex index) := by
  rfl

@[simp] theorem encodeTermPatterns_nil :
    TptpResolvedFofLanguageDef.encodeTermPatterns [] = termsNil := by
  rfl

@[simp] theorem encodeTermPatterns_cons (head : Pattern)
    (tail : List Pattern) :
    TptpResolvedFofLanguageDef.encodeTermPatterns (head :: tail) =
      termsCons head (TptpResolvedFofLanguageDef.encodeTermPatterns tail) := by
  rfl

@[simp] theorem encodeTerm_bvar {depth : Nat} (index : Fin depth) :
    TptpResolvedFofLanguageDef.encodeTerm
        (show TptpFofNormalizationSemantics.Term depth from .bvar index) =
      termVariable
        (TptpResolvedFofLanguageDef.encodeNatIndex index.val) := by
  rfl

@[simp] theorem encodeTerm_func {depth arity : Nat}
    (function : TptpFofNormalizationSemantics.FunctionSymbol arity)
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth) :
    TptpResolvedFofLanguageDef.encodeTerm (.func function arguments) =
      termFunction
        (TptpFofSymbolLanguageDef.encodeFunctionHead
          ⟨function.kind, function.name⟩)
        (TptpResolvedFofLanguageDef.encodeTermPatterns
          (List.ofFn fun index =>
            TptpResolvedFofLanguageDef.encodeTerm (arguments index))) := by
  rfl

def indexDerivation : (cutoff index : Nat) ->
    ShiftDerivation .index
      (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
      (TptpResolvedFofLanguageDef.encodeNatIndex index)
      (TptpResolvedFofLanguageDef.encodeNatIndex
        (shiftIndexValue cutoff index))
  | 0, 0 => .indexZeroAtZero
  | 0, index + 1 => .indexSuccAtZero
      (TptpResolvedFofLanguageDef.encodeNatIndex index)
  | cutoff + 1, 0 => .indexZeroUnderBinder
      (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
  | cutoff + 1, index + 1 =>
      .indexSuccUnderBinder (indexDerivation cutoff index)

def encodePatternList : List Pattern -> Pattern
  | [] => termsNil
  | head :: tail => termsCons head (encodePatternList tail)

noncomputable def sourceTermPattern {depth : Nat}
    (term : TptpFofNormalizationSemantics.Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => termVariable <|
      TptpResolvedFofLanguageDef.encodeNatIndex index.val)
    (fun impossible => nomatch impossible)
    (fun {arity} (function :
        TptpFofNormalizationSemantics.FunctionSymbol arity)
        _ encodedArguments =>
      termFunction
        (TptpFofSymbolLanguageDef.encodeFunctionHead
          ⟨function.kind, function.name⟩)
        (encodePatternList (List.ofFn encodedArguments)))
    term

noncomputable def sourceTermsPattern {depth : Nat}
    (terms : List (TptpFofNormalizationSemantics.Term depth)) : Pattern :=
  encodePatternList (terms.map sourceTermPattern)

noncomputable def shiftedTermPattern (cutoff : Nat) {depth : Nat}
    (term : TptpFofNormalizationSemantics.Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => termVariable <|
      TptpResolvedFofLanguageDef.encodeNatIndex
        (shiftIndexValue cutoff index.val))
    (fun impossible => nomatch impossible)
    (fun {arity} (function :
        TptpFofNormalizationSemantics.FunctionSymbol arity)
        _ shiftedArguments =>
      termFunction
        (TptpFofSymbolLanguageDef.encodeFunctionHead
          ⟨function.kind, function.name⟩)
        (encodePatternList (List.ofFn shiftedArguments)))
    term

noncomputable def shiftedTermsPattern (cutoff : Nat) {depth : Nat}
    (terms : List (TptpFofNormalizationSemantics.Term depth)) : Pattern :=
  encodePatternList (terms.map (shiftedTermPattern cutoff))

noncomputable def vectorTermsDerivation (cutoff : Nat) {depth : Nat} :
    {arity : Nat} ->
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth) ->
    ((index : Fin arity) ->
      ShiftDerivation .term
        (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
        (sourceTermPattern (arguments index))
        (shiftedTermPattern cutoff (arguments index))) ->
    ShiftDerivation .terms
      (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
      (encodePatternList
        (List.ofFn fun index =>
          sourceTermPattern (arguments index)))
      (encodePatternList
        (List.ofFn fun index => shiftedTermPattern cutoff (arguments index)))
  | 0, _, _ => by
      simpa [List.ofFn_zero, encodePatternList] using
        ShiftDerivation.termsNil
          (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
  | arity + 1, arguments, children => by
      simpa [List.ofFn_succ, encodePatternList] using
        ShiftDerivation.termsCons (children 0)
          (vectorTermsDerivation cutoff
            (fun index => arguments index.succ)
            (fun index => children index.succ))

noncomputable def termDerivation (cutoff : Nat) {depth : Nat}
    (term : TptpFofNormalizationSemantics.Term depth) :
      ShiftDerivation .term
        (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
        (sourceTermPattern term)
        (shiftedTermPattern cutoff term) :=
  LO.FirstOrder.Semiterm.rec
    (motive := fun term =>
      ShiftDerivation .term
        (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
        (sourceTermPattern term)
        (shiftedTermPattern cutoff term))
    (fun index => by
      simpa [sourceTermPattern, shiftedTermPattern] using
        ShiftDerivation.termVariable
          (indexDerivation cutoff index.val))
    (fun impossible => nomatch impossible)
    (fun {arity} function arguments children => by
      simpa [sourceTermPattern, shiftedTermPattern] using
        ShiftDerivation.termFunction
          (vectorTermsDerivation cutoff arguments children))
    term

noncomputable def termsDerivation (cutoff : Nat) {depth : Nat} :
    (terms : List (TptpFofNormalizationSemantics.Term depth)) ->
    ShiftDerivation .terms
      (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
      (sourceTermsPattern terms)
      (shiftedTermsPattern cutoff terms)
  | [] => by
      simpa [sourceTermsPattern, shiftedTermsPattern, encodePatternList] using
        ShiftDerivation.termsNil
          (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
  | head :: tail => by
      simpa [sourceTermsPattern, shiftedTermsPattern, encodePatternList] using
        ShiftDerivation.termsCons (termDerivation cutoff head)
          (termsDerivation cutoff tail)

noncomputable def sourceFormulaPattern {depth : Nat} :
    LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth -> Pattern
  | .verum => verum
  | .falsum => falsum
  | .rel (.predicate predicate) arguments =>
      positive (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨predicate.kind, predicate.name⟩)
        (sourceTermsPattern (List.ofFn arguments))
  | .rel .equality arguments =>
      equal (sourceTermPattern (arguments 0))
        (sourceTermPattern (arguments 1))
  | .nrel (.predicate predicate) arguments =>
      negative (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨predicate.kind, predicate.name⟩)
        (sourceTermsPattern (List.ofFn arguments))
  | .nrel .equality arguments =>
      notEqual (sourceTermPattern (arguments 0))
        (sourceTermPattern (arguments 1))
  | .and left right =>
      and (sourceFormulaPattern left) (sourceFormulaPattern right)
  | .or left right =>
      or (sourceFormulaPattern left) (sourceFormulaPattern right)
  | .all body => all (sourceFormulaPattern body)
  | .ex body => ex (sourceFormulaPattern body)

noncomputable def shiftedFormulaPattern (cutoff : Nat) {depth : Nat} :
    LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth -> Pattern
  | .verum => verum
  | .falsum => falsum
  | .rel (.predicate predicate) arguments =>
      positive (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨predicate.kind, predicate.name⟩)
        (shiftedTermsPattern cutoff (List.ofFn arguments))
  | .rel .equality arguments =>
      equal (shiftedTermPattern cutoff (arguments 0))
        (shiftedTermPattern cutoff (arguments 1))
  | .nrel (.predicate predicate) arguments =>
      negative (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨predicate.kind, predicate.name⟩)
        (shiftedTermsPattern cutoff (List.ofFn arguments))
  | .nrel .equality arguments =>
      notEqual (shiftedTermPattern cutoff (arguments 0))
        (shiftedTermPattern cutoff (arguments 1))
  | .and left right =>
      and (shiftedFormulaPattern cutoff left)
        (shiftedFormulaPattern cutoff right)
  | .or left right =>
      or (shiftedFormulaPattern cutoff left)
        (shiftedFormulaPattern cutoff right)
  | .all body => all (shiftedFormulaPattern (cutoff + 1) body)
  | .ex body => ex (shiftedFormulaPattern (cutoff + 1) body)

noncomputable def formulaDerivation (cutoff : Nat) {depth : Nat} :
    (formula : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth) ->
    ShiftDerivation .formula
      (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
      (sourceFormulaPattern formula)
      (shiftedFormulaPattern cutoff formula)
  | .verum => .formulaVerum _
  | .falsum => .formulaFalsum _
  | .rel (.predicate _) arguments =>
      .formulaPositive (termsDerivation cutoff (List.ofFn arguments))
  | .rel .equality arguments =>
      .formulaEqual (termDerivation cutoff (arguments 0))
        (termDerivation cutoff (arguments 1))
  | .nrel (.predicate _) arguments =>
      .formulaNegative (termsDerivation cutoff (List.ofFn arguments))
  | .nrel .equality arguments =>
      .formulaNotEqual (termDerivation cutoff (arguments 0))
        (termDerivation cutoff (arguments 1))
  | .and left right =>
      .formulaAnd (formulaDerivation cutoff left)
        (formulaDerivation cutoff right)
  | .or left right =>
      .formulaOr (formulaDerivation cutoff left)
        (formulaDerivation cutoff right)
  | .all body => by
      simpa [sourceFormulaPattern, shiftedFormulaPattern] using
        ShiftDerivation.formulaAll
        (formulaDerivation (cutoff + 1) body)
  | .ex body => by
      simpa [sourceFormulaPattern, shiftedFormulaPattern] using
        ShiftDerivation.formulaEx
        (formulaDerivation (cutoff + 1) body)

theorem encodePatternList_exact (patterns : List Pattern) :
    encodePatternList patterns =
      TptpResolvedFofLanguageDef.encodeTermPatterns patterns := by
  induction patterns with
  | nil => simp [encodePatternList]
  | cons head tail inductionHypothesis =>
      simp [encodePatternList, inductionHypothesis]

theorem sourceTermPattern_exact {depth : Nat}
    (term : TptpFofNormalizationSemantics.Term depth) :
    sourceTermPattern term = TptpResolvedFofLanguageDef.encodeTerm term := by
  induction term with
  | bvar index => rfl
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      simp only [sourceTermPattern, encodeTerm_func]
      rw [encodePatternList_exact]
      congr 2
      exact List.ofFn_inj.mpr (funext inductionHypothesis)

theorem sourceTermsPattern_exact {depth : Nat}
    (terms : List (TptpFofNormalizationSemantics.Term depth)) :
    sourceTermsPattern terms = TptpResolvedFofLanguageDef.encodeTerms terms := by
  unfold sourceTermsPattern TptpResolvedFofLanguageDef.encodeTerms
  rw [encodePatternList_exact]
  congr 1
  apply List.map_congr_left
  intro term membership
  exact sourceTermPattern_exact term

theorem shiftedTermPattern_exact (base cutoff : Nat)
    (term : TptpFofNormalizationSemantics.Term (base + cutoff)) :
    shiftedTermPattern cutoff term =
      TptpResolvedFofLanguageDef.encodeTerm
        (protectedShift base cutoff term) := by
  induction term with
  | bvar index =>
      simp [shiftedTermPattern, protectedShift,
        LO.FirstOrder.Rew.map_bvar, shiftFin, encodeTerm_bvar]
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      rw [LO.FirstOrder.Rew.func]
      simp only [shiftedTermPattern, encodeTerm_func]
      rw [encodePatternList_exact]
      congr 2
      exact List.ofFn_inj.mpr (funext inductionHypothesis)

theorem shiftedTermsPattern_exact (base cutoff : Nat)
    (terms : List
      (TptpFofNormalizationSemantics.Term (base + cutoff))) :
    shiftedTermsPattern cutoff terms =
      TptpResolvedFofLanguageDef.encodeTerms
        (terms.map (protectedShift base cutoff)) := by
  unfold shiftedTermsPattern TptpResolvedFofLanguageDef.encodeTerms
  rw [encodePatternList_exact, List.map_map]
  congr 1
  apply List.map_congr_left
  intro term membership
  exact shiftedTermPattern_exact base cutoff term

@[simp] theorem encodeFormula_verum {depth : Nat} :
    TptpFofNnfLanguageDef.encodeFormula
        (show LO.FirstOrder.Semiformula
          TptpFofNormalizationSemantics.language Empty depth from .verum) =
      verum := by
  rfl

@[simp] theorem encodeFormula_falsum {depth : Nat} :
    TptpFofNnfLanguageDef.encodeFormula
        (show LO.FirstOrder.Semiformula
          TptpFofNormalizationSemantics.language Empty depth from .falsum) =
      falsum := by
  rfl

@[simp] theorem encodeFormula_positive {depth arity : Nat}
    (predicate : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity ->
      TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula
        (.rel (.predicate predicate) arguments) =
      positive (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨predicate.kind, predicate.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeFormula_negative {depth arity : Nat}
    (predicate : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity ->
      TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula
        (.nrel (.predicate predicate) arguments) =
      negative (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨predicate.kind, predicate.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeFormula_equal {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula (.rel .equality arguments) =
      equal (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeFormula_notEqual {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula (.nrel .equality arguments) =
      notEqual (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeFormula_and {depth : Nat}
    (left right : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth) :
    TptpFofNnfLanguageDef.encodeFormula (.and left right) =
      and (TptpFofNnfLanguageDef.encodeFormula left)
        (TptpFofNnfLanguageDef.encodeFormula right) := by
  rfl

@[simp] theorem encodeFormula_or {depth : Nat}
    (left right : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth) :
    TptpFofNnfLanguageDef.encodeFormula (.or left right) =
      or (TptpFofNnfLanguageDef.encodeFormula left)
        (TptpFofNnfLanguageDef.encodeFormula right) := by
  rfl

@[simp] theorem encodeFormula_all {depth : Nat}
    (body : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty (depth + 1)) :
    TptpFofNnfLanguageDef.encodeFormula (.all body) =
      all (TptpFofNnfLanguageDef.encodeFormula body) := by
  rfl

@[simp] theorem encodeFormula_ex {depth : Nat}
    (body : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty (depth + 1)) :
    TptpFofNnfLanguageDef.encodeFormula (.ex body) =
      ex (TptpFofNnfLanguageDef.encodeFormula body) := by
  rfl

theorem sourceFormulaPattern_exact {depth : Nat}
    (formula : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth) :
    sourceFormulaPattern formula =
      TptpFofNnfLanguageDef.encodeFormula formula := by
  induction formula with
  | verum => rfl
  | falsum => rfl
  | rel relation arguments =>
      cases relation with
      | predicate predicate =>
          simp only [sourceFormulaPattern]
          rw [sourceTermsPattern_exact]
          simp
      | equality =>
          simp only [sourceFormulaPattern]
          rw [sourceTermPattern_exact, sourceTermPattern_exact]
          simp
  | nrel relation arguments =>
      cases relation with
      | predicate predicate =>
          simp only [sourceFormulaPattern]
          rw [sourceTermsPattern_exact]
          simp
      | equality =>
          simp only [sourceFormulaPattern]
          rw [sourceTermPattern_exact, sourceTermPattern_exact]
          simp
  | and left right leftHypothesis rightHypothesis =>
      simp [sourceFormulaPattern, leftHypothesis, rightHypothesis]
  | or left right leftHypothesis rightHypothesis =>
      simp [sourceFormulaPattern, leftHypothesis, rightHypothesis]
  | all body inductionHypothesis =>
      simp [sourceFormulaPattern, inductionHypothesis]
  | ex body inductionHypothesis =>
      simp [sourceFormulaPattern, inductionHypothesis]

theorem shiftedFormulaPattern_exact :
    (base cutoff : Nat) ->
    (formula : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty (base + cutoff)) ->
    shiftedFormulaPattern cutoff formula =
      TptpFofNnfLanguageDef.encodeFormula
        (protectedShift base cutoff ▹ formula)
  | _, _, .verum => rfl
  | _, _, .falsum => rfl
  | base, cutoff, .rel (.predicate predicate) arguments => by
      change positive _ (shiftedTermsPattern cutoff (List.ofFn arguments)) =
        TptpFofNnfLanguageDef.encodeFormula
          (.rel (.predicate predicate)
            (fun index => protectedShift base cutoff (arguments index)))
      rw [shiftedTermsPattern_exact base cutoff]
      simp only [List.map_ofFn, encodeFormula_positive, Function.comp_def]
  | base, cutoff, .rel .equality arguments => by
      change equal (shiftedTermPattern cutoff (arguments 0))
          (shiftedTermPattern cutoff (arguments 1)) =
        TptpFofNnfLanguageDef.encodeFormula
          (.rel .equality
            (fun index => protectedShift base cutoff (arguments index)))
      rw [shiftedTermPattern_exact base cutoff,
        shiftedTermPattern_exact base cutoff, encodeFormula_equal]
  | base, cutoff, .nrel (.predicate predicate) arguments => by
      change negative _ (shiftedTermsPattern cutoff (List.ofFn arguments)) =
        TptpFofNnfLanguageDef.encodeFormula
          (.nrel (.predicate predicate)
            (fun index => protectedShift base cutoff (arguments index)))
      rw [shiftedTermsPattern_exact base cutoff]
      simp only [List.map_ofFn, encodeFormula_negative, Function.comp_def]
  | base, cutoff, .nrel .equality arguments => by
      change notEqual (shiftedTermPattern cutoff (arguments 0))
          (shiftedTermPattern cutoff (arguments 1)) =
        TptpFofNnfLanguageDef.encodeFormula
          (.nrel .equality
            (fun index => protectedShift base cutoff (arguments index)))
      rw [shiftedTermPattern_exact base cutoff,
        shiftedTermPattern_exact base cutoff, encodeFormula_notEqual]
  | base, cutoff, .and left right => by
      change and (shiftedFormulaPattern cutoff left)
          (shiftedFormulaPattern cutoff right) =
        TptpFofNnfLanguageDef.encodeFormula
          (.and (protectedShift base cutoff ▹ left)
            (protectedShift base cutoff ▹ right))
      rw [shiftedFormulaPattern_exact base cutoff left,
        shiftedFormulaPattern_exact base cutoff right, encodeFormula_and]
  | base, cutoff, .or left right => by
      change or (shiftedFormulaPattern cutoff left)
          (shiftedFormulaPattern cutoff right) =
        TptpFofNnfLanguageDef.encodeFormula
          (.or (protectedShift base cutoff ▹ left)
            (protectedShift base cutoff ▹ right))
      rw [shiftedFormulaPattern_exact base cutoff left,
        shiftedFormulaPattern_exact base cutoff right, encodeFormula_or]
  | base, cutoff, .all body => by
      change all (shiftedFormulaPattern (cutoff + 1) body) =
        TptpFofNnfLanguageDef.encodeFormula
          (.all ((protectedShift base cutoff).q ▹ body))
      rw [protectedShift_q, encodeFormula_all,
        shiftedFormulaPattern_exact base (cutoff + 1) body]
  | base, cutoff, .ex body => by
      change ex (shiftedFormulaPattern (cutoff + 1) body) =
        TptpFofNnfLanguageDef.encodeFormula
          (.ex ((protectedShift base cutoff).q ▹ body))
      rw [protectedShift_q, encodeFormula_ex,
        shiftedFormulaPattern_exact base (cutoff + 1) body]

theorem protectedShift_zero (base : Nat) :
    protectedShift base 0 =
      (LO.FirstOrder.Rew.bShift (L := TptpFofNormalizationSemantics.language)
        (ξ := Empty) (n := base)) := by
  apply LO.FirstOrder.Rew.ext
  · intro index
    rw [protectedShift, LO.FirstOrder.Rew.map_bvar,
      LO.FirstOrder.Rew.bShift_bvar]
    congr 1
  · intro impossible
    exact nomatch impossible

/-- Every independently derived shift is executed by the authored LanguageDef
as exactly one result, with no duplicate or invented reduct. -/
theorem ShiftDerivation.rewriteAt_exact
    {sort : SubjectSort} {cutoff source target : Pattern}
    (derivation : ShiftDerivation sort cutoff source target)
    (fuel : Nat) (enough : derivation.height <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (sort.request cutoff source) =
      [sort.result cutoff source target] := by
  induction derivation generalizing fuel with
  | indexZeroAtZero =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [SubjectSort.request, SubjectSort.result] using
            index_zero_at_zero_exact fuel
  | indexSuccAtZero index =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [SubjectSort.request, SubjectSort.result] using
            index_succ_at_zero_exact fuel index
  | indexZeroUnderBinder cutoff =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [SubjectSort.request, SubjectSort.result] using
            index_zero_under_binder_exact fuel cutoff
  | indexSuccUnderBinder prior inductionHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have priorEnough : prior.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            index_succ_under_binder_exact fuel _ _ _
            (inductionHypothesis fuel priorEnough)
  | termVariable indexShift inductionHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : indexShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            term_variable_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | termFunction argumentsShift inductionHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : argumentsShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            term_function_exact fuel _ _ _ _
            (inductionHypothesis fuel childEnough)
  | termsNil cutoff =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [SubjectSort.request, SubjectSort.result] using
            terms_nil_exact fuel cutoff
  | termsCons headShift tailShift headHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max headShift.height tailShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          have headEnough : headShift.height <= fuel :=
            le_trans (Nat.le_max_left _ _) maximumEnough
          have tailEnough : tailShift.height <= fuel :=
            le_trans (Nat.le_max_right _ _) maximumEnough
          simpa [SubjectSort.request, SubjectSort.result] using
            terms_cons_exact fuel _ _ _ _ _
            (headHypothesis fuel headEnough) (tailHypothesis fuel tailEnough)
  | formulaVerum cutoff =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [SubjectSort.request, SubjectSort.result] using
            verum_exact fuel cutoff
  | formulaFalsum cutoff =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          simpa [SubjectSort.request, SubjectSort.result] using
            falsum_exact fuel cutoff
  | formulaPositive argumentsShift inductionHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : argumentsShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            positive_exact fuel _ _ _ _
            (inductionHypothesis fuel childEnough)
  | formulaNegative argumentsShift inductionHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : argumentsShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            negative_exact fuel _ _ _ _
            (inductionHypothesis fuel childEnough)
  | formulaEqual leftShift rightShift leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max leftShift.height rightShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            equal_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | formulaNotEqual leftShift rightShift leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max leftShift.height rightShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            notEqual_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | formulaAnd leftShift rightShift leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max leftShift.height rightShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            and_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | formulaOr leftShift rightShift leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max leftShift.height rightShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            or_exact fuel _ _ _ _ _
            (leftHypothesis fuel
              (le_trans (Nat.le_max_left _ _) maximumEnough))
            (rightHypothesis fuel
              (le_trans (Nat.le_max_right _ _) maximumEnough))
  | formulaAll bodyShift inductionHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : bodyShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            all_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)
  | formulaEx bodyShift inductionHypothesis =>
      cases fuel with
      | zero => simp [ShiftDerivation.height] at enough
      | succ fuel =>
          have childEnough : bodyShift.height <= fuel := by
            simpa [ShiftDerivation.height, Nat.succ_eq_add_one] using enough
          simpa [SubjectSort.request, SubjectSort.result] using
            ex_exact fuel _ _ _
            (inductionHypothesis fuel childEnough)

theorem ShiftDerivation.no_invention
    {sort : SubjectSort} {cutoff source target candidate : Pattern}
    (derivation : ShiftDerivation sort cutoff source target)
    (fuel : Nat) (enough : derivation.height <= fuel)
    (membership : candidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (sort.request cutoff source)) :
    candidate = sort.result cutoff source target := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

/-- On canonical semantic input, the authored LanguageDef computes exactly
the independently defined cutoff insertion. -/
theorem rewriteAt_protectedShift_exact (base cutoff : Nat)
    (formula : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty (base + cutoff)) :
    let derivation := formulaDerivation cutoff formula
    rewriteAt (engineBasePremises RelationEnv.empty) language
        derivation.height
        (formulaRequest
          (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
          (TptpFofNnfLanguageDef.encodeFormula formula)) =
      [formulaResult
        (TptpResolvedFofLanguageDef.encodeNatIndex cutoff)
        (TptpFofNnfLanguageDef.encodeFormula formula)
        (TptpFofNnfLanguageDef.encodeFormula
          (protectedShift base cutoff ▹ formula))] := by
  dsimp only
  have execution :=
    ShiftDerivation.rewriteAt_exact
      (formulaDerivation cutoff formula)
      (formulaDerivation cutoff formula).height (le_refl _)
  simpa only [SubjectSort.request, SubjectSort.result,
    sourceFormulaPattern_exact formula,
    shiftedFormulaPattern_exact base cutoff formula] using execution

/-- The specialization used by prenex conversion inserts one new ambient
binder and is exactly the library's semantic `bShift`. -/
theorem rewriteAt_bShift_exact (depth : Nat)
    (formula : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth) :
    let derivation := formulaDerivation 0 formula
    rewriteAt (engineBasePremises RelationEnv.empty) language
        derivation.height
        (formulaRequest
          (TptpResolvedFofLanguageDef.encodeNatIndex 0)
          (TptpFofNnfLanguageDef.encodeFormula formula)) =
      [formulaResult
        (TptpResolvedFofLanguageDef.encodeNatIndex 0)
        (TptpFofNnfLanguageDef.encodeFormula formula)
        (TptpFofNnfLanguageDef.encodeFormula
          (LO.FirstOrder.Rew.bShift ▹ formula))] := by
  simpa [protectedShift_zero] using
    rewriteAt_protectedShift_exact depth 0 formula

theorem rewriteAt_bShift_no_invention (depth : Nat)
    (formula : LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth)
    (candidate : Pattern)
    (membership : candidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language
        (formulaDerivation 0 formula).height
        (formulaRequest
          (TptpResolvedFofLanguageDef.encodeNatIndex 0)
          (TptpFofNnfLanguageDef.encodeFormula formula))) :
    candidate =
      formulaResult
        (TptpResolvedFofLanguageDef.encodeNatIndex 0)
        (TptpFofNnfLanguageDef.encodeFormula formula)
        (TptpFofNnfLanguageDef.encodeFormula
          (LO.FirstOrder.Rew.bShift ▹ formula)) := by
  rw [rewriteAt_bShift_exact depth formula] at membership
  simpa using membership

namespace Canary

def source : LO.FirstOrder.Semiformula
    TptpFofNormalizationSemantics.language Empty 1 :=
  .all <| .rel .equality (fun
    | 0 => .bvar 0
    | 1 => .bvar 1)

def target : LO.FirstOrder.Semiformula
    TptpFofNormalizationSemantics.language Empty 2 :=
  .all <| .rel .equality (fun
    | 0 => .bvar 0
    | 1 => .bvar 2)

theorem bound_index_stays_and_free_index_moves :
    LO.FirstOrder.Rew.bShift ▹ source = target := by
  change LO.FirstOrder.Semiformula.rewAux LO.FirstOrder.Rew.bShift source = target
  simp only [source, target, LO.FirstOrder.Semiformula.rewAux]
  congr 2
  funext index
  fin_cases index
  · simp
  · change LO.FirstOrder.Rew.bShift.q
        (.bvar (Fin.succ 0)) = .bvar (Fin.succ (Fin.succ 0))
    rw [LO.FirstOrder.Rew.q_bvar_succ,
      LO.FirstOrder.Rew.bShift_bvar,
      LO.FirstOrder.Rew.bShift_bvar]

theorem execution_is_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (formulaDerivation 0 source).height
        (formulaRequest
          (TptpResolvedFofLanguageDef.encodeNatIndex 0)
          (TptpFofNnfLanguageDef.encodeFormula source)) =
      [formulaResult
        (TptpResolvedFofLanguageDef.encodeNatIndex 0)
        (TptpFofNnfLanguageDef.encodeFormula source)
        (TptpFofNnfLanguageDef.encodeFormula target)] := by
  rw [rewriteAt_bShift_exact, bound_index_stays_and_free_index_moves]

end Canary

#print axioms language_validate
#print axioms sourceInclusion
#print axioms index_zero_at_zero_exact
#print axioms index_succ_under_binder_exact
#print axioms term_function_exact
#print axioms terms_cons_exact
#print axioms and_exact
#print axioms all_exact
#print axioms ShiftDerivation.rewriteAt_exact
#print axioms ShiftDerivation.no_invention
#print axioms protectedShift_q
#print axioms shiftedFormulaPattern_exact
#print axioms rewriteAt_protectedShift_exact
#print axioms rewriteAt_bShift_exact
#print axioms rewriteAt_bShift_no_invention
#print axioms Canary.bound_index_stays_and_free_index_moves
#print axioms Canary.execution_is_exact

end Mettapedia.GSLT.LanguageDef.TptpFofNnfShiftLanguageDef
