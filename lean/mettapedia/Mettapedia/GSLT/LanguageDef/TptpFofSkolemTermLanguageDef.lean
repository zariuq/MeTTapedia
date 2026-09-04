import Mettapedia.GSLT.LanguageDef.TptpFofSkolemLanguageDef
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT

/-!
# Authored term substrate for FOF Skolemization

This LanguageDef implements the binder-sensitive term work required by
Skolemization: one-binder shifting in the target signature, finite environment
shifting and lookup, construction of the in-scope universal-variable vector,
and translation of source terms into the disjoint Skolem signature.

The rows are calculus-neutral support for the later prenex traversal.  They do
not allocate fresh symbols or decide a proof-search strategy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
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

/-! ## Shared source and target constructors -/

def indexZero : Pattern := a "tptp-fof-resolved:index-zero"
def indexSucc (index : Pattern) : Pattern :=
  a "tptp-fof-resolved:index-succ" [index]

def sourceTermVariable (index : Pattern) : Pattern :=
  a "tptp-fof-resolved:term-variable" [index]
def sourceTermFunction (function arguments : Pattern) : Pattern :=
  a "tptp-fof-resolved:term-function" [function, arguments]
def sourceTermsNil : Pattern := a "tptp-fof-resolved:terms-nil"
def sourceTermsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-resolved:terms-cons" [head, tail]

def targetTermVariable (index : Pattern) : Pattern :=
  a "tptp-fof-skolem:term-variable" [index]
def targetTermOriginal (function arguments : Pattern) : Pattern :=
  a "tptp-fof-skolem:term-original" [function, arguments]
def targetTermGenerated (id arguments : Pattern) : Pattern :=
  a "tptp-fof-skolem:term-generated" [id, arguments]
def targetTermsNil : Pattern := a "tptp-fof-skolem:terms-nil"
def targetTermsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-skolem:terms-cons" [head, tail]

def envNil : Pattern := a "tptp-fof-skolem-term:env-nil"
def envCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:env-cons" [head, tail]

/-! ## Operation constructors -/

def termShiftRequest (source : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:term-shift-request" [source]
def termShiftResult (source target : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:term-shift-result" [source, target]
def termsShiftRequest (source : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:terms-shift-request" [source]
def termsShiftResult (source target : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:terms-shift-result" [source, target]
def envShiftRequest (source : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:env-shift-request" [source]
def envShiftResult (source target : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:env-shift-result" [source, target]
def variablesRequest (depth : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:variables-request" [depth]
def variablesResult (depth target : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:variables-result" [depth, target]
def lookupRequest (environment index : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:lookup-request" [environment, index]
def lookupResult (environment index target : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:lookup-result" [environment, index, target]
def translateTermRequest (environment source : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:translate-term-request" [environment, source]
def translateTermResult (environment source target : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:translate-term-result"
    [environment, source, target]
def translateTermsRequest (environment source : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:translate-terms-request" [environment, source]
def translateTermsResult (environment source target : Pattern) : Pattern :=
  a "tptp-fof-skolem-term:translate-terms-result"
    [environment, source, target]

def operationTerms : List GrammarRule := [
  ctor "tptp-fof-skolem-term:env-nil" "TptpFofSkolemTerm:Env" [],
  ctor "tptp-fof-skolem-term:env-cons" "TptpFofSkolemTerm:Env"
    [("head", "TptpFofSkolem:Term"), ("tail", "TptpFofSkolemTerm:Env")],
  ctor "tptp-fof-skolem-term:term-shift-request"
    "TptpFofSkolemTerm:TermShiftResult"
    [("source", "TptpFofSkolem:Term")],
  ctor "tptp-fof-skolem-term:term-shift-result"
    "TptpFofSkolemTerm:TermShiftResult"
    [("source", "TptpFofSkolem:Term"),
     ("target", "TptpFofSkolem:Term")],
  ctor "tptp-fof-skolem-term:terms-shift-request"
    "TptpFofSkolemTerm:TermsShiftResult"
    [("source", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem-term:terms-shift-result"
    "TptpFofSkolemTerm:TermsShiftResult"
    [("source", "TptpFofSkolem:Terms"),
     ("target", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem-term:env-shift-request"
    "TptpFofSkolemTerm:EnvShiftResult"
    [("source", "TptpFofSkolemTerm:Env")],
  ctor "tptp-fof-skolem-term:env-shift-result"
    "TptpFofSkolemTerm:EnvShiftResult"
    [("source", "TptpFofSkolemTerm:Env"),
     ("target", "TptpFofSkolemTerm:Env")],
  ctor "tptp-fof-skolem-term:variables-request"
    "TptpFofSkolemTerm:VariablesResult"
    [("depth", "TptpResolvedFof:Index")],
  ctor "tptp-fof-skolem-term:variables-result"
    "TptpFofSkolemTerm:VariablesResult"
    [("depth", "TptpResolvedFof:Index"),
     ("target", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem-term:lookup-request"
    "TptpFofSkolemTerm:LookupResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("index", "TptpResolvedFof:Index")],
  ctor "tptp-fof-skolem-term:lookup-result"
    "TptpFofSkolemTerm:LookupResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("index", "TptpResolvedFof:Index"),
     ("target", "TptpFofSkolem:Term")],
  ctor "tptp-fof-skolem-term:translate-term-request"
    "TptpFofSkolemTerm:TranslateTermResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("source", "TptpResolvedFof:Term")],
  ctor "tptp-fof-skolem-term:translate-term-result"
    "TptpFofSkolemTerm:TranslateTermResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("source", "TptpResolvedFof:Term"),
     ("target", "TptpFofSkolem:Term")],
  ctor "tptp-fof-skolem-term:translate-terms-request"
    "TptpFofSkolemTerm:TranslateTermsResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("source", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-skolem-term:translate-terms-result"
    "TptpFofSkolemTerm:TranslateTermsResult"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("source", "TptpResolvedFof:Terms"),
     ("target", "TptpFofSkolem:Terms")]
]

/-! ## Authored rows -/

def translateTermsConsRule : RewriteRule :=
  mkRule "tptp-fof-skolem-term:translate-terms-cons"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("head", "TptpResolvedFof:Term"), ("tail", "TptpResolvedFof:Terms"),
     ("targetHead", "TptpFofSkolem:Term"),
     ("targetTail", "TptpFofSkolem:Terms")]
    [congruence
      (translateTermRequest (v "environment") (v "head"))
      (translateTermResult (v "environment") (v "head") (v "targetHead")),
     congruence
      (translateTermsRequest (v "environment") (v "tail"))
      (translateTermsResult (v "environment") (v "tail") (v "targetTail"))]
    (translateTermsRequest (v "environment")
      (sourceTermsCons (v "head") (v "tail")))
    (translateTermsResult (v "environment")
      (sourceTermsCons (v "head") (v "tail"))
      (targetTermsCons (v "targetHead") (v "targetTail")))

def rewrites : List RewriteRule := [
  mkRule "tptp-fof-skolem-term:shift-variable"
    [("index", "TptpResolvedFof:Index")] []
    (termShiftRequest (targetTermVariable (v "index")))
    (termShiftResult (targetTermVariable (v "index"))
      (targetTermVariable (indexSucc (v "index")))),
  mkRule "tptp-fof-skolem-term:shift-original"
    [("function", "TptpFofSymbol:FunctionHead"),
     ("arguments", "TptpFofSkolem:Terms"),
     ("targetArguments", "TptpFofSkolem:Terms")]
    [congruence
      (termsShiftRequest (v "arguments"))
      (termsShiftResult (v "arguments") (v "targetArguments"))]
    (termShiftRequest (targetTermOriginal (v "function") (v "arguments")))
    (termShiftResult
      (targetTermOriginal (v "function") (v "arguments"))
      (targetTermOriginal (v "function") (v "targetArguments"))),
  mkRule "tptp-fof-skolem-term:shift-generated"
    [("id", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms"),
     ("targetArguments", "TptpFofSkolem:Terms")]
    [congruence
      (termsShiftRequest (v "arguments"))
      (termsShiftResult (v "arguments") (v "targetArguments"))]
    (termShiftRequest (targetTermGenerated (v "id") (v "arguments")))
    (termShiftResult
      (targetTermGenerated (v "id") (v "arguments"))
      (targetTermGenerated (v "id") (v "targetArguments"))),
  mkRule "tptp-fof-skolem-term:shift-terms-nil" [] []
    (termsShiftRequest targetTermsNil)
    (termsShiftResult targetTermsNil targetTermsNil),
  mkRule "tptp-fof-skolem-term:shift-terms-cons"
    [("head", "TptpFofSkolem:Term"), ("tail", "TptpFofSkolem:Terms"),
     ("targetHead", "TptpFofSkolem:Term"),
     ("targetTail", "TptpFofSkolem:Terms")]
    [congruence
      (termShiftRequest (v "head"))
      (termShiftResult (v "head") (v "targetHead")),
     congruence
      (termsShiftRequest (v "tail"))
      (termsShiftResult (v "tail") (v "targetTail"))]
    (termsShiftRequest (targetTermsCons (v "head") (v "tail")))
    (termsShiftResult
      (targetTermsCons (v "head") (v "tail"))
      (targetTermsCons (v "targetHead") (v "targetTail"))),

  mkRule "tptp-fof-skolem-term:shift-env-nil" [] []
    (envShiftRequest envNil)
    (envShiftResult envNil envNil),
  mkRule "tptp-fof-skolem-term:shift-env-cons"
    [("head", "TptpFofSkolem:Term"), ("tail", "TptpFofSkolemTerm:Env"),
     ("targetHead", "TptpFofSkolem:Term"),
     ("targetTail", "TptpFofSkolemTerm:Env")]
    [congruence
      (termShiftRequest (v "head"))
      (termShiftResult (v "head") (v "targetHead")),
     congruence
      (envShiftRequest (v "tail"))
      (envShiftResult (v "tail") (v "targetTail"))]
    (envShiftRequest (envCons (v "head") (v "tail")))
    (envShiftResult (envCons (v "head") (v "tail"))
      (envCons (v "targetHead") (v "targetTail"))),

  mkRule "tptp-fof-skolem-term:variables-zero" [] []
    (variablesRequest indexZero)
    (variablesResult indexZero targetTermsNil),
  mkRule "tptp-fof-skolem-term:variables-succ"
    [("depth", "TptpResolvedFof:Index"),
     ("prior", "TptpFofSkolem:Terms"),
     ("shifted", "TptpFofSkolem:Terms")]
    [congruence (variablesRequest (v "depth"))
      (variablesResult (v "depth") (v "prior")),
     congruence (termsShiftRequest (v "prior"))
      (termsShiftResult (v "prior") (v "shifted"))]
    (variablesRequest (indexSucc (v "depth")))
    (variablesResult (indexSucc (v "depth"))
      (targetTermsCons (targetTermVariable indexZero) (v "shifted"))),

  mkRule "tptp-fof-skolem-term:lookup-zero"
    [("head", "TptpFofSkolem:Term"), ("tail", "TptpFofSkolemTerm:Env")] []
    (lookupRequest (envCons (v "head") (v "tail")) indexZero)
    (lookupResult (envCons (v "head") (v "tail")) indexZero (v "head")),
  mkRule "tptp-fof-skolem-term:lookup-succ"
    [("head", "TptpFofSkolem:Term"), ("tail", "TptpFofSkolemTerm:Env"),
     ("index", "TptpResolvedFof:Index"),
     ("target", "TptpFofSkolem:Term")]
    [congruence (lookupRequest (v "tail") (v "index"))
      (lookupResult (v "tail") (v "index") (v "target"))]
    (lookupRequest (envCons (v "head") (v "tail"))
      (indexSucc (v "index")))
    (lookupResult (envCons (v "head") (v "tail"))
      (indexSucc (v "index")) (v "target")),

  mkRule "tptp-fof-skolem-term:translate-variable"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("index", "TptpResolvedFof:Index"),
     ("target", "TptpFofSkolem:Term")]
    [congruence (lookupRequest (v "environment") (v "index"))
      (lookupResult (v "environment") (v "index") (v "target"))]
    (translateTermRequest (v "environment")
      (sourceTermVariable (v "index")))
    (translateTermResult (v "environment")
      (sourceTermVariable (v "index")) (v "target")),
  mkRule "tptp-fof-skolem-term:translate-function"
    [("environment", "TptpFofSkolemTerm:Env"),
     ("function", "TptpFofSymbol:FunctionHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("targetArguments", "TptpFofSkolem:Terms")]
    [congruence
      (translateTermsRequest (v "environment") (v "arguments"))
      (translateTermsResult (v "environment") (v "arguments")
        (v "targetArguments"))]
    (translateTermRequest (v "environment")
      (sourceTermFunction (v "function") (v "arguments")))
    (translateTermResult (v "environment")
      (sourceTermFunction (v "function") (v "arguments"))
      (targetTermOriginal (v "function") (v "targetArguments"))),
  mkRule "tptp-fof-skolem-term:translate-terms-nil"
    [("environment", "TptpFofSkolemTerm:Env")] []
    (translateTermsRequest (v "environment") sourceTermsNil)
    (translateTermsResult (v "environment") sourceTermsNil targetTermsNil),
  translateTermsConsRule
]

theorem rewrite_count : rewrites.length = 15 := by decide

@[simp] theorem rewrite14_exact : rewrites[14] = translateTermsConsRule := by
  rfl

def language : LanguageDef := {
  name := "TptpFofSkolemTerm"
  types := TptpFofSkolemLanguageDef.language.types ++ [
    ("TptpFofSkolemTerm:Env" : TypeDecl),
    ("TptpFofSkolemTerm:TermShiftResult" : TypeDecl),
    ("TptpFofSkolemTerm:TermsShiftResult" : TypeDecl),
    ("TptpFofSkolemTerm:EnvShiftResult" : TypeDecl),
    ("TptpFofSkolemTerm:VariablesResult" : TypeDecl),
    ("TptpFofSkolemTerm:LookupResult" : TypeDecl),
    ("TptpFofSkolemTerm:TranslateTermResult" : TypeDecl),
    ("TptpFofSkolemTerm:TranslateTermsResult" : TypeDecl)]
  terms := TptpFofSkolemLanguageDef.language.terms ++ operationTerms
  equations := []
  rewrites := rewrites
}

@[simp] theorem language_typeNames :
    language.typeNames = [
      "String", "TptpFofSymbol:FunctionHead",
      "TptpFofSymbol:PredicateHead", "TptpResolvedFof:Index",
      "TptpResolvedFof:Term",
      "TptpResolvedFof:Terms", "TptpResolvedFof:Formula", "NNFFormula",
      "TptpFofPrenex:Matrix", "TptpFofPrenex:Form",
      "TptpFofSkolem:Term", "TptpFofSkolem:Terms",
      "TptpFofSkolem:Formula", "TptpFofSkolem:IntroducedSymbol",
      "TptpFofSkolem:IntroducedList", "TptpFofSkolem:Output",
      "TptpFofSkolemTerm:Env", "TptpFofSkolemTerm:TermShiftResult",
      "TptpFofSkolemTerm:TermsShiftResult",
      "TptpFofSkolemTerm:EnvShiftResult",
      "TptpFofSkolemTerm:VariablesResult",
      "TptpFofSkolemTerm:LookupResult",
      "TptpFofSkolemTerm:TranslateTermResult",
      "TptpFofSkolemTerm:TranslateTermsResult"] := by
  rfl

@[simp] theorem language_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofSkolemLanguageDef.language ++ [
      ("tptp-fof-skolem-term:env-nil", 0),
      ("tptp-fof-skolem-term:env-cons", 2),
      ("tptp-fof-skolem-term:term-shift-request", 1),
      ("tptp-fof-skolem-term:term-shift-result", 2),
      ("tptp-fof-skolem-term:terms-shift-request", 1),
      ("tptp-fof-skolem-term:terms-shift-result", 2),
      ("tptp-fof-skolem-term:env-shift-request", 1),
      ("tptp-fof-skolem-term:env-shift-result", 2),
      ("tptp-fof-skolem-term:variables-request", 1),
      ("tptp-fof-skolem-term:variables-result", 2),
      ("tptp-fof-skolem-term:lookup-request", 2),
      ("tptp-fof-skolem-term:lookup-result", 3),
      ("tptp-fof-skolem-term:translate-term-request", 2),
      ("tptp-fof-skolem-term:translate-term-result", 3),
      ("tptp-fof-skolem-term:translate-terms-request", 2),
      ("tptp-fof-skolem-term:translate-terms-result", 3)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    operationTerms, ctor]

@[simp] theorem language_constructorLabels :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofSkolemLanguageDef.language ++ [
      "tptp-fof-skolem-term:env-nil",
      "tptp-fof-skolem-term:env-cons",
      "tptp-fof-skolem-term:term-shift-request",
      "tptp-fof-skolem-term:term-shift-result",
      "tptp-fof-skolem-term:terms-shift-request",
      "tptp-fof-skolem-term:terms-shift-result",
      "tptp-fof-skolem-term:env-shift-request",
      "tptp-fof-skolem-term:env-shift-result",
      "tptp-fof-skolem-term:variables-request",
      "tptp-fof-skolem-term:variables-result",
      "tptp-fof-skolem-term:lookup-request",
      "tptp-fof-skolem-term:lookup-result",
      "tptp-fof-skolem-term:translate-term-request",
      "tptp-fof-skolem-term:translate-term-result",
      "tptp-fof-skolem-term:translate-terms-request",
      "tptp-fof-skolem-term:translate-terms-result"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    operationTerms, ctor]

local macro "certify_skolem_term_row" : tactic =>
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
      language_constructorLabels, typed, mkRule, congruence,
      translateTermsConsRule,
      TptpFofSkolemLanguageDef.typeNames_exact,
      TptpFofSkolemLanguageDef.constructorSignatures_exact,
      TptpFofSkolemLanguageDef.constructorLabels_exact,
      indexZero, indexSucc, sourceTermVariable, sourceTermFunction,
      sourceTermsNil, sourceTermsCons, targetTermVariable,
      targetTermOriginal, targetTermGenerated, targetTermsNil,
      targetTermsCons, envNil, envCons, termShiftRequest, termShiftResult,
      termsShiftRequest, termsShiftResult, envShiftRequest,
      envShiftResult, variablesRequest, variablesResult, lookupRequest,
      lookupResult, translateTermRequest, translateTermResult,
      translateTermsRequest, translateTermsResult, a, v,
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
  certify_skolem_term_row
private theorem rewrite01_checked :
    RewriteValidationCertificate.check language rewrites[1] = true := by
  certify_skolem_term_row
private theorem rewrite02_checked :
    RewriteValidationCertificate.check language rewrites[2] = true := by
  certify_skolem_term_row
private theorem rewrite03_checked :
    RewriteValidationCertificate.check language rewrites[3] = true := by
  certify_skolem_term_row
private theorem rewrite04_checked :
    RewriteValidationCertificate.check language rewrites[4] = true := by
  certify_skolem_term_row
private theorem rewrite05_checked :
    RewriteValidationCertificate.check language rewrites[5] = true := by
  certify_skolem_term_row
private theorem rewrite06_checked :
    RewriteValidationCertificate.check language rewrites[6] = true := by
  certify_skolem_term_row
private theorem rewrite07_checked :
    RewriteValidationCertificate.check language rewrites[7] = true := by
  certify_skolem_term_row
private theorem rewrite08_checked :
    RewriteValidationCertificate.check language rewrites[8] = true := by
  certify_skolem_term_row
private theorem rewrite09_checked :
    RewriteValidationCertificate.check language rewrites[9] = true := by
  certify_skolem_term_row
private theorem rewrite10_checked :
    RewriteValidationCertificate.check language rewrites[10] = true := by
  certify_skolem_term_row
private theorem rewrite11_checked :
    RewriteValidationCertificate.check language rewrites[11] = true := by
  certify_skolem_term_row
private theorem rewrite12_checked :
    RewriteValidationCertificate.check language rewrites[12] = true := by
  certify_skolem_term_row
private theorem rewrite13_checked :
    RewriteValidationCertificate.check language rewrites[13] = true := by
  certify_skolem_term_row
private theorem rewrite14_checked :
    RewriteValidationCertificate.check language rewrites[14] = true := by
  rw [rewrite14_exact]
  have contextTypes :
      RewriteValidationCertificate.contextTypesCheck language
          translateTermsConsRule = true := by
    certify_skolem_term_row
  have leftDeclared :
      RewriteValidationCertificate.patternDeclaredCheck language
          translateTermsConsRule.left = true := by
    certify_skolem_term_row
  have rightDeclared :
      RewriteValidationCertificate.patternDeclaredCheck language
          translateTermsConsRule.right = true := by
    certify_skolem_term_row
  have premisesDeclared :
      RewriteValidationCertificate.premisesDeclaredCheck language
          translateTermsConsRule = true := by
    certify_skolem_term_row
  have allPatternsScoped :
      RewriteValidationCertificate.allPatternsScopedCheck
          translateTermsConsRule = true := by
    certify_skolem_term_row
  have fvarsAvoidConstructors :
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck language
          translateTermsConsRule = true := by
    unfold RewriteValidationCertificate.fvarsAvoidConstructorsCheck
    generalize labelsEq :
      RewriteValidationCertificate.constructorLabels language = labels
    simp [translateTermsConsRule, mkRule, congruence,
      translateTermRequest, translateTermResult, translateTermsRequest,
      translateTermsResult, sourceTermsCons, targetTermsCons, a, v,
      LanguageDef.patternFvarNames, LanguageDef.premiseFvarNames,
      Pattern.freeFvarNames]
    rw [← labelsEq, language_constructorLabels]
    decide +kernel
  have bindersAvoidConstructors :
      RewriteValidationCertificate.bindersAvoidConstructorsCheck language
          translateTermsConsRule = true := by
    unfold RewriteValidationCertificate.bindersAvoidConstructorsCheck
    generalize labelsEq :
      RewriteValidationCertificate.constructorLabels language = labels
    simp [translateTermsConsRule, mkRule, congruence,
      translateTermRequest, translateTermResult, translateTermsRequest,
      translateTermsResult, sourceTermsCons, targetTermsCons, a, v,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseForAllParams]
  have contextAvoidsConstructors :
      RewriteValidationCertificate.contextAvoidsConstructorsCheck language
          translateTermsConsRule = true := by
    certify_skolem_term_row
  have rightBound :
      RewriteValidationCertificate.rightBoundCheck
          translateTermsConsRule = true := by
    certify_skolem_term_row
  simp only [RewriteValidationCertificate.check, Bool.and_eq_true]
  exact ⟨contextTypes, leftDeclared, rightDeclared, premisesDeclared,
    allPatternsScoped, fvarsAvoidConstructors, bindersAvoidConstructors,
    contextAvoidsConstructors, rightBound⟩

private theorem every_rewrite_checked (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.check language rewrite = true := by
  simp only [rewrites, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl)
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

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
    constructorLabels_nodup
  exact every_rewrite_checked rewrite membership

/-- Reusable structural certificate for every authored Skolem-term row.
Signature extensions transport this evidence instead of re-running the
complete Boolean validator over unchanged rows. -/
theorem transition_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ language.rewrites) :
    RewriteValidationCertificate.Certificate language rewrite :=
  RewriteValidationCertificate.certificate_of_check
    (every_rewrite_checked rewrite membership)

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def targetInclusion :
    StructuralMorphism TptpFofSkolemLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈ TptpFofSkolemLanguageDef.language.equations at membership
    simp [TptpFofSkolemLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈ TptpFofSkolemLanguageDef.language.rewrites at membership
    simp [TptpFofSkolemLanguageDef.no_rewrites] at membership

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

#print axioms language_validate
#print axioms transition_certificate
#print axioms targetInclusion

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermLanguageDef
