import Mettapedia.GSLT.LanguageDef.TptpFofAlphaExplicitNnfLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Authored NNF-to-alpha-explicit TPTP presentation transform

This GSLT adds deterministic binder identities to canonical binder-resolved
NNF.  It is an optional presentation refinement for TPTP/TSTP interchange,
not the internal clausification representation.

The recursive state is explicit in the authored terms.  Binary nodes thread
the fresh frontier from the left subtree into the right subtree; quantifiers
allocate exactly the current frontier.  Generic contextual execution supplies
all recursion.  No native naming primitive or TPTP-specific evaluator is
used.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofNnfToAlphaExplicitLanguageDef

open LO FirstOrder
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

def sourceVerum : Pattern := a "tptp-fof-nnf:verum"
def sourceFalsum : Pattern := a "tptp-fof-nnf:falsum"
def sourcePositive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-nnf:positive" [relation, arguments]
def sourceNegative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-nnf:negative" [relation, arguments]
def sourceEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:equal" [left, right]
def sourceNotEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:not-equal" [left, right]
def sourceAnd (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:and" [left, right]
def sourceOr (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:or" [left, right]
def sourceAll (body : Pattern) : Pattern := a "tptp-fof-nnf:all" [body]
def sourceEx (body : Pattern) : Pattern := a "tptp-fof-nnf:ex" [body]

def binderSucc (binder : Pattern) : Pattern :=
  a "tptp-fof-alpha:binder-succ" [binder]

def targetVerum : Pattern := a "tptp-fof-alpha:verum"
def targetFalsum : Pattern := a "tptp-fof-alpha:falsum"
def targetPositive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-alpha:positive" [relation, arguments]
def targetNegative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-alpha:negative" [relation, arguments]
def targetEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-alpha:equal" [left, right]
def targetNotEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-alpha:not-equal" [left, right]
def targetAnd (left right : Pattern) : Pattern :=
  a "tptp-fof-alpha:and" [left, right]
def targetOr (left right : Pattern) : Pattern :=
  a "tptp-fof-alpha:or" [left, right]
def targetAll (binder body : Pattern) : Pattern :=
  a "tptp-fof-alpha:all" [binder, body]
def targetEx (binder body : Pattern) : Pattern :=
  a "tptp-fof-alpha:ex" [binder, body]

def request (source next : Pattern) : Pattern :=
  a "tptp-fof-alpha-label:request" [source, next]

def result (source first target next : Pattern) : Pattern :=
  a "tptp-fof-alpha-label:result" [source, first, target, next]

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

def leafRule (name : String) (source target : Pattern) : RewriteRule :=
  mkRule name [("next", "TptpFofAlpha:BinderId")] []
    (request source (v "next"))
    (result source (v "next") target (v "next"))

def binaryRule (name : String)
    (source target : Pattern -> Pattern -> Pattern) : RewriteRule :=
  mkRule name [
      ("left", "NNFFormula"), ("right", "NNFFormula"),
      ("first", "TptpFofAlpha:BinderId"),
      ("middle", "TptpFofAlpha:BinderId"),
      ("next", "TptpFofAlpha:BinderId"),
      ("leftTarget", "TptpFofAlpha:Formula"),
      ("rightTarget", "TptpFofAlpha:Formula")]
    [congruence
        (request (v "left") (v "first"))
        (result (v "left") (v "first") (v "leftTarget") (v "middle")),
     congruence
        (request (v "right") (v "middle"))
        (result (v "right") (v "middle") (v "rightTarget") (v "next"))]
    (request (source (v "left") (v "right")) (v "first"))
    (result (source (v "left") (v "right")) (v "first")
      (target (v "leftTarget") (v "rightTarget")) (v "next"))

def quantifierRule (name : String)
    (source : Pattern -> Pattern) (target : Pattern -> Pattern -> Pattern) :
    RewriteRule :=
  mkRule name [
      ("body", "NNFFormula"),
      ("first", "TptpFofAlpha:BinderId"),
      ("next", "TptpFofAlpha:BinderId"),
      ("bodyTarget", "TptpFofAlpha:Formula")]
    [congruence
      (request (v "body") (binderSucc (v "first")))
      (result (v "body") (binderSucc (v "first"))
        (v "bodyTarget") (v "next"))]
    (request (source (v "body")) (v "first"))
    (result (source (v "body")) (v "first")
      (target (v "first") (v "bodyTarget")) (v "next"))

def rewrites : List RewriteRule := [
  leafRule "tptp-fof-alpha-label:verum" sourceVerum targetVerum,
  leafRule "tptp-fof-alpha-label:falsum" sourceFalsum targetFalsum,
  mkRule "tptp-fof-alpha-label:positive"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("next", "TptpFofAlpha:BinderId")] []
    (request (sourcePositive (v "relation") (v "arguments")) (v "next"))
    (result (sourcePositive (v "relation") (v "arguments")) (v "next")
      (targetPositive (v "relation") (v "arguments")) (v "next")),
  mkRule "tptp-fof-alpha-label:negative"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms"),
     ("next", "TptpFofAlpha:BinderId")] []
    (request (sourceNegative (v "relation") (v "arguments")) (v "next"))
    (result (sourceNegative (v "relation") (v "arguments")) (v "next")
      (targetNegative (v "relation") (v "arguments")) (v "next")),
  mkRule "tptp-fof-alpha-label:equal"
    [("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term"),
     ("next", "TptpFofAlpha:BinderId")] []
    (request (sourceEqual (v "left") (v "right")) (v "next"))
    (result (sourceEqual (v "left") (v "right")) (v "next")
      (targetEqual (v "left") (v "right")) (v "next")),
  mkRule "tptp-fof-alpha-label:not-equal"
    [("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term"),
     ("next", "TptpFofAlpha:BinderId")] []
    (request (sourceNotEqual (v "left") (v "right")) (v "next"))
    (result (sourceNotEqual (v "left") (v "right")) (v "next")
      (targetNotEqual (v "left") (v "right")) (v "next")),
  binaryRule "tptp-fof-alpha-label:and" sourceAnd targetAnd,
  binaryRule "tptp-fof-alpha-label:or" sourceOr targetOr,
  quantifierRule "tptp-fof-alpha-label:all" sourceAll targetAll,
  quantifierRule "tptp-fof-alpha-label:ex" sourceEx targetEx
]

def transformTerms : List GrammarRule := [
  ctor "tptp-fof-alpha-label:request" "TptpFofAlpha:LabelingResult"
    [("source", "NNFFormula"), ("next", "TptpFofAlpha:BinderId")]
    (some .rewrite),
  ctor "tptp-fof-alpha-label:result" "TptpFofAlpha:LabelingResult"
    [("source", "NNFFormula"), ("first", "TptpFofAlpha:BinderId"),
     ("target", "TptpFofAlpha:Formula"),
     ("next", "TptpFofAlpha:BinderId")]
]

def language : LanguageDef := {
  name := "TptpFofNnfToAlphaExplicit"
  types := TptpFofAlphaExplicitNnfLanguageDef.language.types ++
    [("TptpFofAlpha:LabelingResult" : TypeDecl)]
  terms := TptpFofAlphaExplicitNnfLanguageDef.language.terms ++ transformTerms
  equations := []
  rewrites
}

theorem target_types_are_exact_prefix :
    language.types = TptpFofAlphaExplicitNnfLanguageDef.language.types ++
      [("TptpFofAlpha:LabelingResult" : TypeDecl)] := by
  rfl

theorem target_terms_are_exact_prefix :
    language.terms = TptpFofAlphaExplicitNnfLanguageDef.language.terms ++
      transformTerms := by
  rfl

theorem rewrite_count : rewrites.length = 10 := by
  decide

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

@[simp] private theorem language_typeNames : language.typeNames =
    ["String", "TptpFofSymbol:FunctionHead",
      "TptpFofSymbol:PredicateHead", "TptpResolvedFof:Index",
      "TptpResolvedFof:Term",
      "TptpResolvedFof:Terms", "TptpResolvedFof:Formula", "NNFFormula",
      "TptpFofAlpha:BinderId", "TptpFofAlpha:Formula",
      "TptpFofAlpha:LabelingResult"] := by
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
      ("tptp-fof-alpha:binder-zero", 0),
      ("tptp-fof-alpha:binder-succ", 1),
      ("tptp-fof-alpha:verum", 0),
      ("tptp-fof-alpha:falsum", 0),
      ("tptp-fof-alpha:positive", 2),
      ("tptp-fof-alpha:negative", 2),
      ("tptp-fof-alpha:equal", 2),
      ("tptp-fof-alpha:not-equal", 2),
      ("tptp-fof-alpha:and", 2),
      ("tptp-fof-alpha:or", 2),
      ("tptp-fof-alpha:all", 2),
      ("tptp-fof-alpha:ex", 2),
      ("tptp-fof-alpha-label:request", 2),
      ("tptp-fof-alpha-label:result", 4)] := by
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
      "tptp-fof-resolved:index-zero",
      "tptp-fof-resolved:index-succ",
      "tptp-fof-resolved:term-variable",
      "tptp-fof-resolved:term-function",
      "tptp-fof-resolved:terms-nil",
      "tptp-fof-resolved:terms-cons",
      "tptp-fof-resolved:verum",
      "tptp-fof-resolved:falsum",
      "tptp-fof-resolved:predicate",
      "tptp-fof-resolved:equal",
      "tptp-fof-resolved:not",
      "tptp-fof-resolved:and",
      "tptp-fof-resolved:or",
      "tptp-fof-resolved:iff",
      "tptp-fof-resolved:implies",
      "tptp-fof-resolved:reverse-implies",
      "tptp-fof-resolved:xor",
      "tptp-fof-resolved:nor",
      "tptp-fof-resolved:nand",
      "tptp-fof-resolved:all",
      "tptp-fof-resolved:ex",
      "tptp-fof-nnf:verum",
      "tptp-fof-nnf:falsum",
      "tptp-fof-nnf:positive",
      "tptp-fof-nnf:negative",
      "tptp-fof-nnf:equal",
      "tptp-fof-nnf:not-equal",
      "tptp-fof-nnf:and",
      "tptp-fof-nnf:or",
      "tptp-fof-nnf:all",
      "tptp-fof-nnf:ex",
      "tptp-fof-alpha:binder-zero",
      "tptp-fof-alpha:binder-succ",
      "tptp-fof-alpha:verum",
      "tptp-fof-alpha:falsum",
      "tptp-fof-alpha:positive",
      "tptp-fof-alpha:negative",
      "tptp-fof-alpha:equal",
      "tptp-fof-alpha:not-equal",
      "tptp-fof-alpha:and",
      "tptp-fof-alpha:or",
      "tptp-fof-alpha:all",
      "tptp-fof-alpha:ex",
      "tptp-fof-alpha-label:request",
      "tptp-fof-alpha-label:result"] := by
  rfl

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  decide +kernel

local macro "certify_label_row" : tactic =>
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
      typed, leafRule, binaryRule, quantifierRule, mkRule, congruence,
      request, result, binderSucc, sourceVerum, sourceFalsum,
      sourcePositive, sourceNegative, sourceEqual, sourceNotEqual,
      sourceAnd, sourceOr, sourceAll, sourceEx, targetVerum, targetFalsum,
      targetPositive, targetNegative, targetEqual, targetNotEqual,
      targetAnd, targetOr, targetAll, targetEx, a, v,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])

private theorem verumRule_checked :
    RewriteValidationCertificate.check language
      (leafRule "tptp-fof-alpha-label:verum" sourceVerum targetVerum) =
        true := by
  certify_label_row

private theorem falsumRule_checked :
    RewriteValidationCertificate.check language
      (leafRule "tptp-fof-alpha-label:falsum" sourceFalsum targetFalsum) =
        true := by
  certify_label_row

private theorem positiveRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-alpha-label:positive"
        [("relation", "TptpFofSymbol:PredicateHead"),
         ("arguments", "TptpResolvedFof:Terms"),
         ("next", "TptpFofAlpha:BinderId")] []
        (request (sourcePositive (v "relation") (v "arguments")) (v "next"))
        (result (sourcePositive (v "relation") (v "arguments")) (v "next")
          (targetPositive (v "relation") (v "arguments")) (v "next"))) =
        true := by
  certify_label_row

private theorem negativeRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-alpha-label:negative"
        [("relation", "TptpFofSymbol:PredicateHead"),
         ("arguments", "TptpResolvedFof:Terms"),
         ("next", "TptpFofAlpha:BinderId")] []
        (request (sourceNegative (v "relation") (v "arguments")) (v "next"))
        (result (sourceNegative (v "relation") (v "arguments")) (v "next")
          (targetNegative (v "relation") (v "arguments")) (v "next"))) =
        true := by
  certify_label_row

private theorem equalRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-alpha-label:equal"
        [("left", "TptpResolvedFof:Term"),
         ("right", "TptpResolvedFof:Term"),
         ("next", "TptpFofAlpha:BinderId")] []
        (request (sourceEqual (v "left") (v "right")) (v "next"))
        (result (sourceEqual (v "left") (v "right")) (v "next")
          (targetEqual (v "left") (v "right")) (v "next"))) = true := by
  certify_label_row

private theorem notEqualRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-alpha-label:not-equal"
        [("left", "TptpResolvedFof:Term"),
         ("right", "TptpResolvedFof:Term"),
         ("next", "TptpFofAlpha:BinderId")] []
        (request (sourceNotEqual (v "left") (v "right")) (v "next"))
        (result (sourceNotEqual (v "left") (v "right")) (v "next")
          (targetNotEqual (v "left") (v "right")) (v "next"))) = true := by
  certify_label_row

private theorem andRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-alpha-label:and" sourceAnd targetAnd) = true := by
  certify_label_row

private theorem orRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-alpha-label:or" sourceOr targetOr) = true := by
  certify_label_row

private theorem allRule_checked :
    RewriteValidationCertificate.check language
      (quantifierRule "tptp-fof-alpha-label:all" sourceAll targetAll) =
        true := by
  certify_label_row

private theorem exRule_checked :
    RewriteValidationCertificate.check language
      (quantifierRule "tptp-fof-alpha-label:ex" sourceEx targetEx) = true := by
  certify_label_row

local macro "validate_label_row" : tactic =>
  `(tactic|
    apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup <;>
    first
    | exact verumRule_checked
    | exact falsumRule_checked
    | exact positiveRule_checked
    | exact negativeRule_checked
    | exact equalRule_checked
    | exact notEqualRule_checked
    | exact andRule_checked
    | exact orRule_checked
    | exact allRule_checked
    | exact exRule_checked)

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  simp only [language_rewrites, rewrites, List.mem_cons, List.not_mem_nil,
    or_false] at membership
  rcases membership with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    validate_label_row

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def targetInclusion :
    StructuralMorphism TptpFofAlphaExplicitNnfLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈ TptpFofAlphaExplicitNnfLanguageDef.language.equations at membership
    simp [TptpFofAlphaExplicitNnfLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈ TptpFofAlphaExplicitNnfLanguageDef.language.rewrites at membership
    simp [TptpFofAlphaExplicitNnfLanguageDef.no_rewrites] at membership

def sourceInclusion :
    StructuralMorphism TptpFofNnfLanguageDef.validated validated :=
  StructuralMorphism.comp TptpFofAlphaExplicitNnfLanguageDef.nnfInclusion
    targetInclusion

/-! ## Exact root execution -/

local macro "label_root" : tactic =>
  `(tactic|
    simp [rewriteAt, language_rewrites, rewrites, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      leafRule, binaryRule, quantifierRule, mkRule, congruence, request,
      result, binderSucc, sourceVerum, sourceFalsum, sourcePositive,
      sourceNegative, sourceEqual, sourceNotEqual, sourceAnd, sourceOr,
      sourceAll, sourceEx, targetVerum, targetFalsum, targetPositive,
      targetNegative, targetEqual, targetNotEqual, targetAnd, targetOr,
      targetAll, targetEx, a, v, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local syntax "label_root_using " term,* : tactic
local macro_rules
  | `(tactic| label_root_using $_proofs:term,*) =>
      `(tactic|
        simp only [request, result, binderSucc, a] at * <;>
        simp [*, rewriteAt, language_rewrites, rewrites, applyRuleUsing,
          matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
          leafRule, binaryRule, quantifierRule, mkRule, congruence, request,
          result, binderSucc, sourceVerum, sourceFalsum, sourcePositive,
          sourceNegative, sourceEqual, sourceNotEqual, sourceAnd, sourceOr,
          sourceAll, sourceEx, targetVerum, targetFalsum, targetPositive,
          targetNegative, targetEqual, targetNotEqual, targetAnd, targetOr,
          targetAll, targetEx, a, v, matchPattern, matchArgs, mergeBindings,
          applyBindingsForRule, applyBindings])

theorem verum_rewriteAt_exact (fuel : Nat) (next : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request sourceVerum next) =
      [result sourceVerum next targetVerum next] := by
  label_root

theorem falsum_rewriteAt_exact (fuel : Nat) (next : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request sourceFalsum next) =
      [result sourceFalsum next targetFalsum next] := by
  label_root

theorem positive_rewriteAt_exact (fuel : Nat)
    (relation arguments next : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourcePositive relation arguments) next) =
      [result (sourcePositive relation arguments) next
        (targetPositive relation arguments) next] := by
  label_root

theorem negative_rewriteAt_exact (fuel : Nat)
    (relation arguments next : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourceNegative relation arguments) next) =
      [result (sourceNegative relation arguments) next
        (targetNegative relation arguments) next] := by
  label_root

theorem equal_rewriteAt_exact (fuel : Nat) (left right next : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourceEqual left right) next) =
      [result (sourceEqual left right) next (targetEqual left right) next] := by
  label_root

theorem notEqual_rewriteAt_exact (fuel : Nat)
    (left right next : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourceNotEqual left right) next) =
      [result (sourceNotEqual left right) next
        (targetNotEqual left right) next] := by
  label_root

theorem and_rewriteAt_exact (fuel : Nat)
    (left right first middle next leftTarget rightTarget : Pattern)
    (leftExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request left first) = [result left first leftTarget middle])
    (rightExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request right middle) = [result right middle rightTarget next]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourceAnd left right) first) =
      [result (sourceAnd left right) first
        (targetAnd leftTarget rightTarget) next] := by
  label_root_using leftExact, rightExact

theorem or_rewriteAt_exact (fuel : Nat)
    (left right first middle next leftTarget rightTarget : Pattern)
    (leftExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request left first) = [result left first leftTarget middle])
    (rightExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request right middle) = [result right middle rightTarget next]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourceOr left right) first) =
      [result (sourceOr left right) first
        (targetOr leftTarget rightTarget) next] := by
  label_root_using leftExact, rightExact

theorem all_rewriteAt_exact (fuel : Nat)
    (body first next bodyTarget : Pattern)
    (bodyExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request body (binderSucc first)) =
          [result body (binderSucc first) bodyTarget next]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourceAll body) first) =
      [result (sourceAll body) first (targetAll first bodyTarget) next] := by
  label_root_using bodyExact

theorem ex_rewriteAt_exact (fuel : Nat)
    (body first next bodyTarget : Pattern)
    (bodyExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request body (binderSucc first)) =
          [result body (binderSucc first) bodyTarget next]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (sourceEx body) first) =
      [result (sourceEx body) first (targetEx first bodyTarget) next] := by
  label_root_using bodyExact

/-! ## Exact agreement with the independent alpha labeller -/

abbrev NnfFormula (depth : Nat) :=
  TptpFofAlphaExplicitNnf.NnfFormula depth

abbrev AlphaFormula (depth : Nat) :=
  TptpFofAlphaExplicitNnf.Formula depth

@[simp] theorem encodeSource_verum {depth : Nat} :
    TptpFofNnfLanguageDef.encodeFormula
        (show NnfFormula depth from .verum) = sourceVerum := by
  rfl

@[simp] theorem encodeSource_falsum {depth : Nat} :
    TptpFofNnfLanguageDef.encodeFormula
        (show NnfFormula depth from .falsum) = sourceFalsum := by
  rfl

@[simp] theorem encodeSource_positive {depth arity : Nat}
    (symbol : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula (.rel (.predicate symbol) arguments) =
      sourcePositive (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨symbol.kind, symbol.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeSource_negative {depth arity : Nat}
    (symbol : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula (.nrel (.predicate symbol) arguments) =
      sourceNegative (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨symbol.kind, symbol.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeSource_equal {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula (.rel (.equality) arguments) =
      sourceEqual (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeSource_notEqual {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofNnfLanguageDef.encodeFormula (.nrel (.equality) arguments) =
      sourceNotEqual (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeSource_and {depth : Nat} (left right : NnfFormula depth) :
    TptpFofNnfLanguageDef.encodeFormula (.and left right) =
      sourceAnd (TptpFofNnfLanguageDef.encodeFormula left)
        (TptpFofNnfLanguageDef.encodeFormula right) := by
  rfl

@[simp] theorem encodeSource_or {depth : Nat} (left right : NnfFormula depth) :
    TptpFofNnfLanguageDef.encodeFormula (.or left right) =
      sourceOr (TptpFofNnfLanguageDef.encodeFormula left)
        (TptpFofNnfLanguageDef.encodeFormula right) := by
  rfl

@[simp] theorem encodeSource_all {depth : Nat} (body : NnfFormula (depth + 1)) :
    TptpFofNnfLanguageDef.encodeFormula (.all body) =
      sourceAll (TptpFofNnfLanguageDef.encodeFormula body) := by
  rfl

@[simp] theorem encodeSource_ex {depth : Nat} (body : NnfFormula (depth + 1)) :
    TptpFofNnfLanguageDef.encodeFormula (.ex body) =
      sourceEx (TptpFofNnfLanguageDef.encodeFormula body) := by
  rfl

@[simp] theorem encodeTarget_verum {depth : Nat} :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
        (show AlphaFormula depth from .verum) = targetVerum := by
  rfl

@[simp] theorem encodeTarget_falsum {depth : Nat} :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
        (show AlphaFormula depth from .falsum) = targetFalsum := by
  rfl

@[simp] theorem encodeTarget_positive {depth arity : Nat}
    (symbol : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
        (.rel (.predicate symbol) arguments) =
      targetPositive (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨symbol.kind, symbol.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeTarget_negative {depth arity : Nat}
    (symbol : TptpFofNormalizationSemantics.PredicateSymbol arity)
    (arguments : Fin arity -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
        (.nrel (.predicate symbol) arguments) =
      targetNegative (TptpFofSymbolLanguageDef.encodePredicateHead
          ⟨symbol.kind, symbol.name⟩)
        (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)) := by
  rfl

@[simp] theorem encodeTarget_equal {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula (.rel (.equality) arguments) =
      targetEqual (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeTarget_notEqual {depth : Nat}
    (arguments : Fin 2 -> TptpFofNormalizationSemantics.Term depth) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
        (.nrel (.equality) arguments) =
      targetNotEqual (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
        (TptpResolvedFofLanguageDef.encodeTerm (arguments 1)) := by
  rfl

@[simp] theorem encodeTarget_and {depth : Nat}
    (left right : AlphaFormula depth) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula (.and left right) =
      targetAnd (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula left)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula right) := by
  rfl

@[simp] theorem encodeTarget_or {depth : Nat}
    (left right : AlphaFormula depth) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula (.or left right) =
      targetOr (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula left)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula right) := by
  rfl

@[simp] theorem encodeTarget_all {depth : Nat} (binder : Nat)
    (body : AlphaFormula (depth + 1)) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula (.all binder body) =
      targetAll (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId binder)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula body) := by
  rfl

@[simp] theorem encodeTarget_ex {depth : Nat} (binder : Nat)
    (body : AlphaFormula (depth + 1)) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeFormula (.ex binder body) =
      targetEx (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId binder)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula body) := by
  rfl

def formulaHeight {depth : Nat} :
    TptpFofAlphaExplicitNnf.NnfFormula depth -> Nat
  | .verum | .falsum | .rel _ _ | .nrel _ _ => 1
  | .and left right | .or left right =>
      max (formulaHeight left) (formulaHeight right) + 1
  | .all body | .ex body => formulaHeight body + 1

@[simp] theorem encodeBinderId_add_one (binder : Nat) :
    TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId (binder + 1) =
      binderSucc
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId binder) := by
  rfl

/-- The authored transformation has exactly the independent labeller's one
result.  The equality preserves the source, the initial frontier, the complete
alpha-explicit target, and the final frontier; consequently it also excludes
duplicate or invented results. -/
theorem rewriteAt_labelFrom_exact {depth : Nat}
    (source : TptpFofAlphaExplicitNnf.NnfFormula depth)
    (first fuel : Nat) (enough : formulaHeight source <= fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request (TptpFofNnfLanguageDef.encodeFormula source)
          (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)) =
      [result (TptpFofNnfLanguageDef.encodeFormula source)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
          (TptpFofAlphaExplicitNnf.labelFrom source first).1)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
          (TptpFofAlphaExplicitNnf.labelFrom source first).2)] := by
  induction source generalizing first fuel with
  | verum =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
            Nat.succ_eq_add_one] using
            verum_rewriteAt_exact fuel
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
  | falsum =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
            Nat.succ_eq_add_one] using
            falsum_rewriteAt_exact fuel
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
  | rel relation arguments =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          cases relation with
          | predicate predicate =>
              simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
                Nat.succ_eq_add_one] using
                positive_rewriteAt_exact fuel
                  (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
                  (TptpResolvedFofLanguageDef.encodeTerms
                    (List.ofFn arguments))
                  (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
          | equality =>
              simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
                Nat.succ_eq_add_one] using
                equal_rewriteAt_exact fuel
                  (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
                  (TptpResolvedFofLanguageDef.encodeTerm (arguments 1))
                  (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
  | nrel relation arguments =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          cases relation with
          | predicate predicate =>
              simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
                Nat.succ_eq_add_one] using
                negative_rewriteAt_exact fuel
                  (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
                  (TptpResolvedFofLanguageDef.encodeTerms
                    (List.ofFn arguments))
                  (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
          | equality =>
              simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
                Nat.succ_eq_add_one] using
                notEqual_rewriteAt_exact fuel
                  (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
                  (TptpResolvedFofLanguageDef.encodeTerm (arguments 1))
                  (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
  | and left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          have maximumEnough :
              max (formulaHeight left) (formulaHeight right) <= fuel := by
            simpa [formulaHeight, Nat.succ_eq_add_one] using enough
          have leftEnough : formulaHeight left <= fuel :=
            le_trans (Nat.le_max_left _ _) maximumEnough
          have rightEnough : formulaHeight right <= fuel :=
            le_trans (Nat.le_max_right _ _) maximumEnough
          have leftExact := leftHypothesis first fuel leftEnough
          have rightExact := rightHypothesis
            (TptpFofAlphaExplicitNnf.labelFrom left first).2 fuel rightEnough
          simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
            Nat.succ_eq_add_one] using
            and_rewriteAt_exact fuel
              (TptpFofNnfLanguageDef.encodeFormula left)
              (TptpFofNnfLanguageDef.encodeFormula right)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
                (TptpFofAlphaExplicitNnf.labelFrom left first).2)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
                (TptpFofAlphaExplicitNnf.labelFrom right
                  (TptpFofAlphaExplicitNnf.labelFrom left first).2).2)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
                (TptpFofAlphaExplicitNnf.labelFrom left first).1)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
                (TptpFofAlphaExplicitNnf.labelFrom right
                  (TptpFofAlphaExplicitNnf.labelFrom left first).2).1)
              leftExact rightExact
  | or left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          have maximumEnough :
              max (formulaHeight left) (formulaHeight right) <= fuel := by
            simpa [formulaHeight, Nat.succ_eq_add_one] using enough
          have leftEnough : formulaHeight left <= fuel :=
            le_trans (Nat.le_max_left _ _) maximumEnough
          have rightEnough : formulaHeight right <= fuel :=
            le_trans (Nat.le_max_right _ _) maximumEnough
          have leftExact := leftHypothesis first fuel leftEnough
          have rightExact := rightHypothesis
            (TptpFofAlphaExplicitNnf.labelFrom left first).2 fuel rightEnough
          simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
            Nat.succ_eq_add_one] using
            or_rewriteAt_exact fuel
              (TptpFofNnfLanguageDef.encodeFormula left)
              (TptpFofNnfLanguageDef.encodeFormula right)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
                (TptpFofAlphaExplicitNnf.labelFrom left first).2)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
                (TptpFofAlphaExplicitNnf.labelFrom right
                  (TptpFofAlphaExplicitNnf.labelFrom left first).2).2)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
                (TptpFofAlphaExplicitNnf.labelFrom left first).1)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
                (TptpFofAlphaExplicitNnf.labelFrom right
                  (TptpFofAlphaExplicitNnf.labelFrom left first).2).1)
              leftExact rightExact
  | all body bodyHypothesis =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          have bodyEnough : formulaHeight body <= fuel := by
            simpa [formulaHeight, Nat.succ_eq_add_one] using enough
          have bodyExact := bodyHypothesis (first + 1) fuel bodyEnough
          simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
            Nat.succ_eq_add_one] using
            all_rewriteAt_exact fuel
              (TptpFofNnfLanguageDef.encodeFormula body)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
                (TptpFofAlphaExplicitNnf.labelFrom body (first + 1)).2)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
                (TptpFofAlphaExplicitNnf.labelFrom body (first + 1)).1)
              bodyExact
  | ex body bodyHypothesis =>
      cases fuel with
      | zero => simp [formulaHeight] at enough
      | succ fuel =>
          have bodyEnough : formulaHeight body <= fuel := by
            simpa [formulaHeight, Nat.succ_eq_add_one] using enough
          have bodyExact := bodyHypothesis (first + 1) fuel bodyEnough
          simpa [formulaHeight, TptpFofAlphaExplicitNnf.labelFrom,
            Nat.succ_eq_add_one] using
            ex_rewriteAt_exact fuel
              (TptpFofNnfLanguageDef.encodeFormula body)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
                (TptpFofAlphaExplicitNnf.labelFrom body (first + 1)).2)
              (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
                (TptpFofAlphaExplicitNnf.labelFrom body (first + 1)).1)
              bodyExact

theorem rewriteAt_label_exact {depth : Nat}
    (source : NnfFormula depth) :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (formulaHeight source)
        (request (TptpFofNnfLanguageDef.encodeFormula source)
          (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0)) =
      [result (TptpFofNnfLanguageDef.encodeFormula source)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
          (TptpFofAlphaExplicitNnf.label source))
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
          (TptpFofAlphaExplicitNnf.labelFrom source 0).2)] := by
  simpa [TptpFofAlphaExplicitNnf.label] using
    rewriteAt_labelFrom_exact source 0 (formulaHeight source) (le_refl _)

theorem generated_target_erases_exact {depth : Nat}
    (source : NnfFormula depth) (first : Nat) :
    TptpFofAlphaExplicitNnf.erase
        (TptpFofAlphaExplicitNnf.labelFrom source first).1 = source := by
  exact TptpFofAlphaExplicitNnf.labelFrom_erase_exact source first

theorem generated_binder_ids_exact {depth : Nat}
    (source : NnfFormula depth) (first : Nat) :
    TptpFofAlphaExplicitNnf.binderIds
        (TptpFofAlphaExplicitNnf.labelFrom source first).1 =
      List.range' first
        (TptpFofAlphaExplicitNnf.quantifierCount source) := by
  exact TptpFofAlphaExplicitNnf.labelFrom_binderIds_exact source first

theorem generated_binder_ids_nodup {depth : Nat}
    (source : NnfFormula depth) (first : Nat) :
    (TptpFofAlphaExplicitNnf.binderIds
      (TptpFofAlphaExplicitNnf.labelFrom source first).1).Nodup := by
  rw [generated_binder_ids_exact]
  exact List.nodup_range'

/-- Exact singleton execution gives the strongest local no-invention result:
every observed reduct is the source-preserving independently computed result. -/
theorem rewriteAt_no_invention {depth : Nat}
    (source : NnfFormula depth) (first fuel : Nat)
    (enough : formulaHeight source <= fuel) (candidate : Pattern)
    (membership : candidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request (TptpFofNnfLanguageDef.encodeFormula source)
          (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first))) :
    candidate =
      result (TptpFofNnfLanguageDef.encodeFormula source)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId first)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
          (TptpFofAlphaExplicitNnf.labelFrom source first).1)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId
          (TptpFofAlphaExplicitNnf.labelFrom source first).2) := by
  rw [rewriteAt_labelFrom_exact source first fuel enough] at membership
  simpa using membership

namespace Canary

theorem nested_execution_is_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (formulaHeight TptpFofAlphaExplicitNnf.Canary.nestedSource)
        (request
          (TptpFofNnfLanguageDef.encodeFormula
            TptpFofAlphaExplicitNnf.Canary.nestedSource)
          (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0)) =
      [result
        (TptpFofNnfLanguageDef.encodeFormula
          TptpFofAlphaExplicitNnf.Canary.nestedSource)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0)
        (TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
          (TptpFofAlphaExplicitNnf.label
            TptpFofAlphaExplicitNnf.Canary.nestedSource))
        (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 2)] := by
  have frontierExact :
      (TptpFofAlphaExplicitNnf.labelFrom
        TptpFofAlphaExplicitNnf.Canary.nestedSource 0).2 = 2 := by
    rw [TptpFofAlphaExplicitNnf.labelFrom_next_exact]
    decide +kernel
  rw [rewriteAt_label_exact, frontierExact]

/-- A compound-negation spelling is outside the canonical NNF source carrier
and has no accidental alpha-labelling behavior. -/
theorem compound_negation_has_no_result (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (request (a "tptp-fof-nnf:not" [sourceVerum])
          (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0)) = [] := by
  label_root

end Canary

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact language_supported

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms language_validate
#print axioms targetInclusion
#print axioms sourceInclusion
#print axioms rewriteAt_labelFrom_exact
#print axioms rewriteAt_label_exact
#print axioms generated_target_erases_exact
#print axioms generated_binder_ids_exact
#print axioms generated_binder_ids_nodup
#print axioms rewriteAt_no_invention
#print axioms Canary.nested_execution_is_exact
#print axioms Canary.compound_negation_has_no_result
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofNnfToAlphaExplicitLanguageDef
