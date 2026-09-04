import Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermAgreement
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Authored evidence-bearing FOF Skolemization

This LanguageDef translates canonical prenex FOF into the disjoint Skolem
signature.  Existential binders allocate generated symbols from an explicit
frontier and record each introduced identity and arity in the result.  The
formula traversal consumes only the independently verified term substrate;
it contains no native allocation, substitution, or proof-search operation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

open Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermLanguageDef
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def ctor (label category : String) (parameters : List (String × String)) :
    GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
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

def matrixRequest (environment source : Pattern) : Pattern :=
  a "tptp-fof-skolemize:matrix-request" [environment, source]

def matrixResult (environment source target : Pattern) : Pattern :=
  a "tptp-fof-skolemize:matrix-result" [environment, source, target]

def formRequest (environment targetDepth frontier source : Pattern) : Pattern :=
  a "tptp-fof-skolemize:form-request"
    [environment, targetDepth, frontier, source]

def formResult (environment targetDepth frontier source target next
    introduced : Pattern) : Pattern :=
  a "tptp-fof-skolemize:form-result"
    [environment, targetDepth, frontier, source, target, next, introduced]

def operationTerms : List GrammarRule := [
  ctor "tptp-fof-skolemize:matrix-request"
    "TptpFofSkolemize:MatrixResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("source", "TptpFofPrenex:Matrix")],
  ctor "tptp-fof-skolemize:matrix-result"
    "TptpFofSkolemize:MatrixResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("source", "TptpFofPrenex:Matrix"),
     ("target", "TptpFofSkolem:Formula")],
  ctor "tptp-fof-skolemize:form-request"
    "TptpFofSkolemize:FormResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("targetDepth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("source", "TptpFofPrenex:Form")],
  ctor "tptp-fof-skolemize:form-result"
    "TptpFofSkolemize:FormResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("targetDepth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("source", "TptpFofPrenex:Form"),
     ("target", "TptpFofSkolem:Formula"),
     ("next", "TptpResolvedFof:Index"),
     ("introduced", "TptpFofSkolem:IntroducedList")]
]

def matrixRewrites : List RewriteRule := [
  mkRule "tptp-fof-skolemize:matrix-verum"
    [("environment", "TptpFofSkolemTerm:Env")] []
    (matrixRequest (v "environment")
      TptpFofPrenexLanguageDef.matrixVerum)
    (matrixResult (v "environment")
      TptpFofPrenexLanguageDef.matrixVerum TptpFofSkolemLanguageDef.verum),
  mkRule "tptp-fof-skolemize:matrix-falsum"
    [("environment", "TptpFofSkolemTerm:Env")] []
    (matrixRequest (v "environment")
      TptpFofPrenexLanguageDef.matrixFalsum)
    (matrixResult (v "environment")
      TptpFofPrenexLanguageDef.matrixFalsum TptpFofSkolemLanguageDef.falsum),
  mkRule "tptp-fof-skolemize:matrix-positive"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpFofSkolem:Terms")]
    [congruence
      (translateTermsRequest (v "environment") (v "arguments"))
      (translateTermsResult (v "environment") (v "arguments")
        (v "targetArguments"))]
    (matrixRequest (v "environment")
      (TptpFofPrenexLanguageDef.matrixPositive
        (v "relation") (v "arguments")))
    (matrixResult (v "environment")
      (TptpFofPrenexLanguageDef.matrixPositive
        (v "relation") (v "arguments"))
      (TptpFofSkolemLanguageDef.positive
        (v "relation") (v "targetArguments"))),
  mkRule "tptp-fof-skolemize:matrix-negative"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpFofSkolem:Terms")]
    [congruence
      (translateTermsRequest (v "environment") (v "arguments"))
      (translateTermsResult (v "environment") (v "arguments")
        (v "targetArguments"))]
    (matrixRequest (v "environment")
      (TptpFofPrenexLanguageDef.matrixNegative
        (v "relation") (v "arguments")))
    (matrixResult (v "environment")
      (TptpFofPrenexLanguageDef.matrixNegative
        (v "relation") (v "arguments"))
      (TptpFofSkolemLanguageDef.negative
        (v "relation") (v "targetArguments"))),
  mkRule "tptp-fof-skolemize:matrix-equal"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term"),
     ("targetLeft", "TptpFofSkolem:Term"),
     ("targetRight", "TptpFofSkolem:Term")]
    [congruence (translateTermRequest (v "environment") (v "left"))
      (translateTermResult (v "environment") (v "left") (v "targetLeft")),
     congruence (translateTermRequest (v "environment") (v "right"))
      (translateTermResult (v "environment") (v "right") (v "targetRight"))]
    (matrixRequest (v "environment")
      (TptpFofPrenexLanguageDef.matrixEqual (v "left") (v "right")))
    (matrixResult (v "environment")
      (TptpFofPrenexLanguageDef.matrixEqual (v "left") (v "right"))
      (TptpFofSkolemLanguageDef.equal (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-skolemize:matrix-not-equal"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term"),
     ("targetLeft", "TptpFofSkolem:Term"),
     ("targetRight", "TptpFofSkolem:Term")]
    [congruence (translateTermRequest (v "environment") (v "left"))
      (translateTermResult (v "environment") (v "left") (v "targetLeft")),
     congruence (translateTermRequest (v "environment") (v "right"))
      (translateTermResult (v "environment") (v "right") (v "targetRight"))]
    (matrixRequest (v "environment")
      (TptpFofPrenexLanguageDef.matrixNotEqual (v "left") (v "right")))
    (matrixResult (v "environment")
      (TptpFofPrenexLanguageDef.matrixNotEqual (v "left") (v "right"))
      (TptpFofSkolemLanguageDef.notEqual
        (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-skolemize:matrix-and"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix"),
     ("targetLeft", "TptpFofSkolem:Formula"),
     ("targetRight", "TptpFofSkolem:Formula")]
    [congruence (matrixRequest (v "environment") (v "left"))
      (matrixResult (v "environment") (v "left") (v "targetLeft")),
     congruence (matrixRequest (v "environment") (v "right"))
      (matrixResult (v "environment") (v "right") (v "targetRight"))]
    (matrixRequest (v "environment")
      (TptpFofPrenexLanguageDef.matrixAnd (v "left") (v "right")))
    (matrixResult (v "environment")
      (TptpFofPrenexLanguageDef.matrixAnd (v "left") (v "right"))
      (TptpFofSkolemLanguageDef.and (v "targetLeft") (v "targetRight"))),
  mkRule "tptp-fof-skolemize:matrix-or"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix"),
     ("targetLeft", "TptpFofSkolem:Formula"),
     ("targetRight", "TptpFofSkolem:Formula")]
    [congruence (matrixRequest (v "environment") (v "left"))
      (matrixResult (v "environment") (v "left") (v "targetLeft")),
     congruence (matrixRequest (v "environment") (v "right"))
      (matrixResult (v "environment") (v "right") (v "targetRight"))]
    (matrixRequest (v "environment")
      (TptpFofPrenexLanguageDef.matrixOr (v "left") (v "right")))
    (matrixResult (v "environment")
      (TptpFofPrenexLanguageDef.matrixOr (v "left") (v "right"))
      (TptpFofSkolemLanguageDef.or (v "targetLeft") (v "targetRight")))
]

def formRewrites : List RewriteRule := [
  mkRule "tptp-fof-skolemize:form-matrix"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("targetDepth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("matrix", "TptpFofPrenex:Matrix"),
     ("target", "TptpFofSkolem:Formula")]
    [congruence (matrixRequest (v "environment") (v "matrix"))
      (matrixResult (v "environment") (v "matrix") (v "target"))]
    (formRequest (v "environment") (v "targetDepth") (v "frontier")
      (TptpFofPrenexLanguageDef.matrix (v "matrix")))
    (formResult (v "environment") (v "targetDepth") (v "frontier")
      (TptpFofPrenexLanguageDef.matrix (v "matrix")) (v "target")
      (v "frontier") TptpFofSkolemLanguageDef.introducedNil),
  mkRule "tptp-fof-skolemize:form-all"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("shiftedEnvironment", "TptpFofSkolemTerm:Env"),
     ("targetDepth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("body", "TptpFofPrenex:Form"),
     ("target", "TptpFofSkolem:Formula"),
     ("next", "TptpResolvedFof:Index"),
     ("introduced", "TptpFofSkolem:IntroducedList")]
    [congruence (envShiftRequest (v "environment"))
      (envShiftResult (v "environment") (v "shiftedEnvironment")),
     congruence
      (formRequest
        (envCons (targetTermVariable indexZero) (v "shiftedEnvironment"))
        (indexSucc (v "targetDepth")) (v "frontier") (v "body"))
      (formResult
        (envCons (targetTermVariable indexZero) (v "shiftedEnvironment"))
        (indexSucc (v "targetDepth")) (v "frontier") (v "body")
        (v "target") (v "next") (v "introduced"))]
    (formRequest (v "environment") (v "targetDepth") (v "frontier")
      (TptpFofPrenexLanguageDef.all (v "body")))
    (formResult (v "environment") (v "targetDepth") (v "frontier")
      (TptpFofPrenexLanguageDef.all (v "body"))
      (TptpFofSkolemLanguageDef.all (v "target"))
      (v "next") (v "introduced")),
  mkRule "tptp-fof-skolemize:form-ex"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("targetDepth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms"),
     ("body", "TptpFofPrenex:Form"),
     ("target", "TptpFofSkolem:Formula"),
     ("next", "TptpResolvedFof:Index"),
     ("introduced", "TptpFofSkolem:IntroducedList")]
    [congruence (variablesRequest (v "targetDepth"))
      (variablesResult (v "targetDepth") (v "arguments")),
     congruence
      (formRequest
        (envCons (targetTermGenerated (v "frontier") (v "arguments"))
          (v "environment"))
        (v "targetDepth") (indexSucc (v "frontier")) (v "body"))
      (formResult
        (envCons (targetTermGenerated (v "frontier") (v "arguments"))
          (v "environment"))
        (v "targetDepth") (indexSucc (v "frontier")) (v "body")
        (v "target") (v "next") (v "introduced"))]
    (formRequest (v "environment") (v "targetDepth") (v "frontier")
      (TptpFofPrenexLanguageDef.ex (v "body")))
    (formResult (v "environment") (v "targetDepth") (v "frontier")
      (TptpFofPrenexLanguageDef.ex (v "body"))
      (v "target") (v "next")
      (TptpFofSkolemLanguageDef.introducedCons
        (TptpFofSkolemLanguageDef.introducedSymbol
          (v "frontier") (v "targetDepth"))
        (v "introduced")))
]

def rewrites : List RewriteRule := matrixRewrites ++ formRewrites

theorem rewrite_count : rewrites.length = 11 := by decide

def language : LanguageDef := {
  name := "TptpFofSkolemization"
  types := TptpFofSkolemTermLanguageDef.language.types ++ [
    ("TptpFofSkolemize:MatrixResult" : TypeDecl),
    ("TptpFofSkolemize:FormResult" : TypeDecl)]
  terms := TptpFofSkolemTermLanguageDef.language.terms ++ operationTerms
  equations := []
  rewrites := TptpFofSkolemTermLanguageDef.rewrites ++ rewrites
}

@[simp] theorem language_rewrites :
    language.rewrites = TptpFofSkolemTermLanguageDef.rewrites ++ rewrites := rfl

@[simp] theorem language_typeNames : language.typeNames =
    TptpFofSkolemTermLanguageDef.language.typeNames ++ [
      "TptpFofSkolemize:MatrixResult", "TptpFofSkolemize:FormResult"] := by
  simp only [language, LanguageDef.typeNames, List.map_append]
  rfl

@[simp] theorem language_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofSkolemTermLanguageDef.language ++ [
      ("tptp-fof-skolemize:matrix-request", 2),
      ("tptp-fof-skolemize:matrix-result", 3),
      ("tptp-fof-skolemize:form-request", 4),
      ("tptp-fof-skolemize:form-result", 7)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    operationTerms, ctor]

@[simp] theorem language_constructorLabels :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofSkolemTermLanguageDef.language ++ [
      "tptp-fof-skolemize:matrix-request",
      "tptp-fof-skolemize:matrix-result",
      "tptp-fof-skolemize:form-request",
      "tptp-fof-skolemize:form-result"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    operationTerms, ctor]

local macro "certify_skolemization_row" : tactic =>
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
      rewrites, matrixRewrites, formRewrites,
      language_typeNames,
      language_constructorSignatures, language_constructorLabels,
      TptpFofSkolemTermLanguageDef.language_typeNames,
      TptpFofSkolemTermLanguageDef.language_constructorSignatures,
      TptpFofSkolemTermLanguageDef.language_constructorLabels,
      TptpFofSkolemTermLanguageDef.a,
      TptpFofSkolemTermLanguageDef.v,
      TptpFofSkolemTermLanguageDef.typed,
      TptpFofSkolemTermLanguageDef.mkRule,
      TptpFofSkolemTermLanguageDef.congruence,
      TptpFofSkolemTermLanguageDef.indexZero,
      TptpFofSkolemTermLanguageDef.indexSucc,
      TptpFofSkolemTermLanguageDef.sourceTermVariable,
      TptpFofSkolemTermLanguageDef.sourceTermFunction,
      TptpFofSkolemTermLanguageDef.sourceTermsNil,
      TptpFofSkolemTermLanguageDef.sourceTermsCons,
      TptpFofSkolemTermLanguageDef.targetTermVariable,
      TptpFofSkolemTermLanguageDef.targetTermOriginal,
      TptpFofSkolemTermLanguageDef.targetTermGenerated,
      TptpFofSkolemTermLanguageDef.targetTermsNil,
      TptpFofSkolemTermLanguageDef.targetTermsCons,
      TptpFofSkolemTermLanguageDef.envNil,
      TptpFofSkolemTermLanguageDef.envCons,
      TptpFofSkolemTermLanguageDef.termShiftRequest,
      TptpFofSkolemTermLanguageDef.termShiftResult,
      TptpFofSkolemTermLanguageDef.termsShiftRequest,
      TptpFofSkolemTermLanguageDef.termsShiftResult,
      TptpFofSkolemTermLanguageDef.envShiftRequest,
      TptpFofSkolemTermLanguageDef.envShiftResult,
      TptpFofSkolemTermLanguageDef.variablesRequest,
      TptpFofSkolemTermLanguageDef.variablesResult,
      TptpFofSkolemTermLanguageDef.lookupRequest,
      TptpFofSkolemTermLanguageDef.lookupResult,
      TptpFofSkolemTermLanguageDef.translateTermRequest,
      TptpFofSkolemTermLanguageDef.translateTermResult,
      TptpFofSkolemTermLanguageDef.translateTermsRequest,
      TptpFofSkolemTermLanguageDef.translateTermsResult,
      TptpFofPrenexLanguageDef.a, TptpFofSkolemLanguageDef.a,
      typed, mkRule, congruence, matrixRequest, matrixResult, formRequest,
      formResult, termShiftRequest, termShiftResult, termsShiftRequest,
      termsShiftResult, envShiftRequest, envShiftResult, variablesRequest,
      variablesResult, translateTermRequest, translateTermResult,
      translateTermsRequest, translateTermsResult, indexZero, indexSucc,
      sourceTermVariable, sourceTermFunction, sourceTermsNil,
      sourceTermsCons, targetTermVariable, targetTermOriginal,
      targetTermGenerated, targetTermsNil, targetTermsCons, envNil, envCons,
      a, v,
      TptpFofPrenexLanguageDef.matrixVerum,
      TptpFofPrenexLanguageDef.matrixFalsum,
      TptpFofPrenexLanguageDef.matrixPositive,
      TptpFofPrenexLanguageDef.matrixNegative,
      TptpFofPrenexLanguageDef.matrixEqual,
      TptpFofPrenexLanguageDef.matrixNotEqual,
      TptpFofPrenexLanguageDef.matrixAnd,
      TptpFofPrenexLanguageDef.matrixOr,
      TptpFofPrenexLanguageDef.matrix,
      TptpFofPrenexLanguageDef.all, TptpFofPrenexLanguageDef.ex,
      TptpFofSkolemLanguageDef.verum, TptpFofSkolemLanguageDef.falsum,
      TptpFofSkolemLanguageDef.positive,
      TptpFofSkolemLanguageDef.negative,
      TptpFofSkolemLanguageDef.equal,
      TptpFofSkolemLanguageDef.notEqual,
      TptpFofSkolemLanguageDef.and, TptpFofSkolemLanguageDef.or,
      TptpFofSkolemLanguageDef.all,
      TptpFofSkolemLanguageDef.introducedSymbol,
      TptpFofSkolemLanguageDef.introducedNil,
      TptpFofSkolemLanguageDef.introducedCons,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by decide +kernel

private theorem rewrite00_checked :
    RewriteValidationCertificate.check language rewrites[0] = true := by
  certify_skolemization_row
private theorem rewrite01_checked :
    RewriteValidationCertificate.check language rewrites[1] = true := by
  certify_skolemization_row
private theorem rewrite02_checked :
    RewriteValidationCertificate.check language rewrites[2] = true := by
  certify_skolemization_row
private theorem rewrite03_checked :
    RewriteValidationCertificate.check language rewrites[3] = true := by
  certify_skolemization_row
set_option maxHeartbeats 800000 in
private theorem rewrite04_checked :
    RewriteValidationCertificate.check language rewrites[4] = true := by
  certify_skolemization_row
set_option maxHeartbeats 800000 in
private theorem rewrite05_checked :
    RewriteValidationCertificate.check language rewrites[5] = true := by
  certify_skolemization_row
private theorem rewrite06_contextTypes_checked :
    RewriteValidationCertificate.contextTypesCheck language rewrites[6] = true := by
  certify_skolemization_row
private theorem rewrite06_leftDeclared_checked :
    RewriteValidationCertificate.patternDeclaredCheck language rewrites[6].left = true := by
  certify_skolemization_row
private theorem rewrite06_rightDeclared_checked :
    RewriteValidationCertificate.patternDeclaredCheck language rewrites[6].right = true := by
  certify_skolemization_row
private theorem rewrite06_premisesDeclared_checked :
    RewriteValidationCertificate.premisesDeclaredCheck language rewrites[6] = true := by
  certify_skolemization_row
private theorem rewrite06_scoped_checked :
    RewriteValidationCertificate.allPatternsScopedCheck rewrites[6] = true := by
  certify_skolemization_row
private theorem rewrite06_fvars_checked :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language rewrites[6] = true := by
  certify_skolemization_row
private theorem rewrite06_binders_checked :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language rewrites[6] = true := by
  certify_skolemization_row
private theorem rewrite06_contextNames_checked :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language rewrites[6] = true := by
  certify_skolemization_row
private theorem rewrite06_rightBound_checked :
    RewriteValidationCertificate.rightBoundCheck rewrites[6] = true := by
  certify_skolemization_row
private theorem rewrite06_checked :
    RewriteValidationCertificate.check language rewrites[6] = true := by
  simp only [RewriteValidationCertificate.check, Bool.and_eq_true]
  exact ⟨rewrite06_contextTypes_checked, rewrite06_leftDeclared_checked,
    rewrite06_rightDeclared_checked, rewrite06_premisesDeclared_checked,
    rewrite06_scoped_checked, rewrite06_fvars_checked,
    rewrite06_binders_checked, rewrite06_contextNames_checked,
    rewrite06_rightBound_checked⟩

private theorem rewrite07_contextTypes_checked :
    RewriteValidationCertificate.contextTypesCheck language rewrites[7] = true := by
  certify_skolemization_row
private theorem rewrite07_leftDeclared_checked :
    RewriteValidationCertificate.patternDeclaredCheck language rewrites[7].left = true := by
  certify_skolemization_row
private theorem rewrite07_rightDeclared_checked :
    RewriteValidationCertificate.patternDeclaredCheck language rewrites[7].right = true := by
  certify_skolemization_row
private theorem rewrite07_premisesDeclared_checked :
    RewriteValidationCertificate.premisesDeclaredCheck language rewrites[7] = true := by
  certify_skolemization_row
private theorem rewrite07_scoped_checked :
    RewriteValidationCertificate.allPatternsScopedCheck rewrites[7] = true := by
  certify_skolemization_row
private theorem rewrite07_fvars_checked :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language rewrites[7] = true := by
  certify_skolemization_row
private theorem rewrite07_binders_checked :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language rewrites[7] = true := by
  certify_skolemization_row
private theorem rewrite07_contextNames_checked :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language rewrites[7] = true := by
  certify_skolemization_row
private theorem rewrite07_rightBound_checked :
    RewriteValidationCertificate.rightBoundCheck rewrites[7] = true := by
  certify_skolemization_row
private theorem rewrite07_checked :
    RewriteValidationCertificate.check language rewrites[7] = true := by
  simp only [RewriteValidationCertificate.check, Bool.and_eq_true]
  exact ⟨rewrite07_contextTypes_checked, rewrite07_leftDeclared_checked,
    rewrite07_rightDeclared_checked, rewrite07_premisesDeclared_checked,
    rewrite07_scoped_checked, rewrite07_fvars_checked,
    rewrite07_binders_checked, rewrite07_contextNames_checked,
    rewrite07_rightBound_checked⟩

private theorem rewrite08_contextTypes_checked :
    RewriteValidationCertificate.contextTypesCheck language rewrites[8] = true := by
  certify_skolemization_row
private theorem rewrite08_leftDeclared_checked :
    RewriteValidationCertificate.patternDeclaredCheck language rewrites[8].left = true := by
  certify_skolemization_row
private theorem rewrite08_rightDeclared_checked :
    RewriteValidationCertificate.patternDeclaredCheck language rewrites[8].right = true := by
  certify_skolemization_row
private theorem rewrite08_premisesDeclared_checked :
    RewriteValidationCertificate.premisesDeclaredCheck language rewrites[8] = true := by
  certify_skolemization_row
private theorem rewrite08_scoped_checked :
    RewriteValidationCertificate.allPatternsScopedCheck rewrites[8] = true := by
  certify_skolemization_row
private theorem rewrite08_fvars_checked :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language rewrites[8] = true := by
  certify_skolemization_row
private theorem rewrite08_binders_checked :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language rewrites[8] = true := by
  certify_skolemization_row
private theorem rewrite08_contextNames_checked :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language rewrites[8] = true := by
  certify_skolemization_row
private theorem rewrite08_rightBound_checked :
    RewriteValidationCertificate.rightBoundCheck rewrites[8] = true := by
  certify_skolemization_row
private theorem rewrite08_checked :
    RewriteValidationCertificate.check language rewrites[8] = true := by
  simp only [RewriteValidationCertificate.check, Bool.and_eq_true]
  exact ⟨rewrite08_contextTypes_checked, rewrite08_leftDeclared_checked,
    rewrite08_rightDeclared_checked, rewrite08_premisesDeclared_checked,
    rewrite08_scoped_checked, rewrite08_fvars_checked,
    rewrite08_binders_checked, rewrite08_contextNames_checked,
    rewrite08_rightBound_checked⟩
set_option maxHeartbeats 800000 in
private theorem rewrite09_checked :
    RewriteValidationCertificate.check language rewrites[9] = true := by
  certify_skolemization_row
set_option maxHeartbeats 800000 in
private theorem rewrite10_checked :
    RewriteValidationCertificate.check language rewrites[10] = true := by
  certify_skolemization_row

private theorem every_authored_rewrite_checked (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.check language rewrite = true := by
  rw [rewrites] at membership
  rcases List.mem_append.mp membership with matrixMembership | formMembership
  · simp only [matrixRewrites, List.mem_cons, List.not_mem_nil,
      or_false] at matrixMembership
    rcases matrixMembership with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite00_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite01_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite02_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite03_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite04_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite05_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite06_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite07_checked
  · simp only [formRewrites, List.mem_cons, List.not_mem_nil,
      or_false] at formMembership
    rcases formMembership with (rfl | rfl | rfl)
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite08_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite09_checked
    · simpa [rewrites, matrixRewrites, formRewrites] using rewrite10_checked

private theorem inherited_schema_avoids_added (rewrite : RewriteRule)
    (membership : rewrite ∈ TptpFofSkolemTermLanguageDef.rewrites) :
    ∀ name ∈ schemaNames rewrite,
      name ∉ ["tptp-fof-skolemize:matrix-request",
        "tptp-fof-skolemize:matrix-result",
        "tptp-fof-skolemize:form-request",
        "tptp-fof-skolemize:form-result"] := by
  simp only [TptpFofSkolemTermLanguageDef.rewrites, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl)
  all_goals
    simp [schemaNames, TptpFofSkolemTermLanguageDef.translateTermsConsRule,
      TptpFofSkolemTermLanguageDef.mkRule,
      TptpFofSkolemTermLanguageDef.congruence,
      TptpFofSkolemTermLanguageDef.a,
      TptpFofSkolemTermLanguageDef.v,
      TptpFofSkolemTermLanguageDef.indexZero,
      TptpFofSkolemTermLanguageDef.indexSucc,
      TptpFofSkolemTermLanguageDef.sourceTermVariable,
      TptpFofSkolemTermLanguageDef.sourceTermFunction,
      TptpFofSkolemTermLanguageDef.sourceTermsNil,
      TptpFofSkolemTermLanguageDef.sourceTermsCons,
      TptpFofSkolemTermLanguageDef.targetTermVariable,
      TptpFofSkolemTermLanguageDef.targetTermOriginal,
      TptpFofSkolemTermLanguageDef.targetTermGenerated,
      TptpFofSkolemTermLanguageDef.targetTermsNil,
      TptpFofSkolemTermLanguageDef.targetTermsCons,
      TptpFofSkolemTermLanguageDef.envNil,
      TptpFofSkolemTermLanguageDef.envCons,
      TptpFofSkolemTermLanguageDef.termShiftRequest,
      TptpFofSkolemTermLanguageDef.termShiftResult,
      TptpFofSkolemTermLanguageDef.termsShiftRequest,
      TptpFofSkolemTermLanguageDef.termsShiftResult,
      TptpFofSkolemTermLanguageDef.envShiftRequest,
      TptpFofSkolemTermLanguageDef.envShiftResult,
      TptpFofSkolemTermLanguageDef.variablesRequest,
      TptpFofSkolemTermLanguageDef.variablesResult,
      TptpFofSkolemTermLanguageDef.lookupRequest,
      TptpFofSkolemTermLanguageDef.lookupResult,
      TptpFofSkolemTermLanguageDef.translateTermRequest,
      TptpFofSkolemTermLanguageDef.translateTermResult,
      TptpFofSkolemTermLanguageDef.translateTermsRequest,
      TptpFofSkolemTermLanguageDef.translateTermsResult,
      TptpFofSkolemTermLanguageDef.typed,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premiseFvarNames, LanguageDef.premisePatterns,
      LanguageDef.premiseForAllParams, Pattern.freeFvarNames] <;> aesop

private def inheritedExtendsFor (rewrite : RewriteRule)
    (membership : rewrite ∈ TptpFofSkolemTermLanguageDef.rewrites) :
    ExtendsFor TptpFofSkolemTermLanguageDef.language language rewrite where
  addedTypes := ["TptpFofSkolemize:MatrixResult",
    "TptpFofSkolemize:FormResult"]
  addedSignatures := [
    ("tptp-fof-skolemize:matrix-request", 2),
    ("tptp-fof-skolemize:matrix-result", 3),
    ("tptp-fof-skolemize:form-request", 4),
    ("tptp-fof-skolemize:form-result", 7)]
  addedLabels := ["tptp-fof-skolemize:matrix-request",
    "tptp-fof-skolemize:matrix-result",
    "tptp-fof-skolemize:form-request",
    "tptp-fof-skolemize:form-result"]
  typeNames := language_typeNames
  signatures := language_constructorSignatures
  labels := language_constructorLabels
  avoidsSchema := inherited_schema_avoids_added rewrite membership

private theorem inherited_rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ TptpFofSkolemTermLanguageDef.rewrites) :
    RewriteValidationCertificate.Certificate language rewrite :=
  RewriteValidationCertificateExtension.Certificate.extend
    (TptpFofSkolemTermLanguageDef.transition_certificate rewrite
      (by simpa only [TptpFofSkolemTermLanguageDef.language_rewrites] using membership))
    (inheritedExtendsFor rewrite membership)

private theorem every_rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ language.rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  rw [language_rewrites] at membership
  rcases List.mem_append.mp membership with inherited | authored
  · exact inherited_rewrite_certificate rewrite inherited
  · exact RewriteValidationCertificate.certificate_of_check
      (every_authored_rewrite_checked rewrite authored)

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  exact RewriteValidationCertificate.validateRewrite_eq_nil
    constructorLabels_nodup (every_rewrite_certificate rewrite membership)

/-- Reusable structural certificate for every authored Skolemization row.
Later disjoint signature extensions can transport this evidence without
rechecking the complete source presentation. -/
theorem transition_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ language.rewrites) :
    RewriteValidationCertificate.Certificate language rewrite :=
  every_rewrite_certificate rewrite membership

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def sourceInclusion :
    StructuralMorphism TptpFofSkolemTermLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈ ([] : List Equation) at membership
    simp at membership
  mapsRewrites declaration membership := by
    rw [mapRewriteRule_id]
    exact List.mem_append_left _ membership

/-- The complete authored Skolemization presentation belongs to the canonical
LanguageDef wire fragment. -/
theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact language_supported

/-- Canonical object-language wire for the authored Skolemization
transformation. -/
def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms language_validate
#print axioms transition_certificate
#print axioms sourceInclusion
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef
