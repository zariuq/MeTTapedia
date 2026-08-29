import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# An authored GSLT for binder-resolved FOF normalization

This presentation is the executable normalization arrow used by the TPTP
clausification pipeline.  Its source carrier is already binder-resolved:
bound-variable indices are data inside `Term`, not source spellings.  The
preceding elaboration stage is responsible for admitting only indices in
scope.  Normalization itself is total on the raw carrier and does not inspect
terms, symbol names, or indices.

Every recursive call is an authored `Premise.congruence`.  The generic
MeTTaIL contextual engine therefore supplies the recursion; there is no
TPTP-specific evaluator or native connective dispatch.  The target carrier
has only signed atoms, conjunction, disjunction, and quantifiers, so NNF is a
structural property of the target language rather than a post-hoc checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

def sourceVerum : Pattern := a "tptp-fof-resolved:verum"
def sourceFalsum : Pattern := a "tptp-fof-resolved:falsum"
def sourcePredicate (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-resolved:predicate" [relation, arguments]
def sourceEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:equal" [left, right]
def sourceNot (body : Pattern) : Pattern :=
  a "tptp-fof-resolved:not" [body]
def sourceAnd (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:and" [left, right]
def sourceOr (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:or" [left, right]
def sourceIff (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:iff" [left, right]
def sourceImplies (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:implies" [left, right]
def sourceReverseImplies (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:reverse-implies" [left, right]
def sourceXor (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:xor" [left, right]
def sourceNor (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:nor" [left, right]
def sourceNand (left right : Pattern) : Pattern :=
  a "tptp-fof-resolved:nand" [left, right]
def sourceAll (body : Pattern) : Pattern :=
  a "tptp-fof-resolved:all" [body]
def sourceEx (body : Pattern) : Pattern :=
  a "tptp-fof-resolved:ex" [body]

def targetVerum : Pattern := a "tptp-fof-nnf:verum"
def targetFalsum : Pattern := a "tptp-fof-nnf:falsum"
def targetPositive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-nnf:positive" [relation, arguments]
def targetNegative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-nnf:negative" [relation, arguments]
def targetEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:equal" [left, right]
def targetNotEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:not-equal" [left, right]
def targetAnd (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:and" [left, right]
def targetOr (left right : Pattern) : Pattern :=
  a "tptp-fof-nnf:or" [left, right]
def targetAll (body : Pattern) : Pattern :=
  a "tptp-fof-nnf:all" [body]
def targetEx (body : Pattern) : Pattern :=
  a "tptp-fof-nnf:ex" [body]

def positive (formula : Pattern) : Pattern :=
  a "tptp-fof-normalize:positive" [formula]
def negative (formula : Pattern) : Pattern :=
  a "tptp-fof-normalize:negative" [formula]

def request (polarity : Bool) (formula : Pattern) : Pattern :=
  if polarity then positive formula else negative formula

def mkRule (name : String) (context : List (String × String))
    (premises : List Premise) (left right : Pattern) : RewriteRule := {
  name := name
  typeContext := typed context
  premises := premises
  left := left
  right := right
}

def congruence (source target : Pattern) : Premise :=
  .congruence source target

def leafRules : List RewriteRule := [
  mkRule "tptp-fof-normalize:positive-verum" [] []
    (positive sourceVerum) targetVerum,
  mkRule "tptp-fof-normalize:negative-verum" [] []
    (negative sourceVerum) targetFalsum,
  mkRule "tptp-fof-normalize:positive-falsum" [] []
    (positive sourceFalsum) targetFalsum,
  mkRule "tptp-fof-normalize:negative-falsum" [] []
    (negative sourceFalsum) targetVerum,
  mkRule "tptp-fof-normalize:positive-predicate"
    [("relation", "String"), ("arguments", "Terms")] []
    (positive (sourcePredicate (v "relation") (v "arguments")))
    (targetPositive (v "relation") (v "arguments")),
  mkRule "tptp-fof-normalize:negative-predicate"
    [("relation", "String"), ("arguments", "Terms")] []
    (negative (sourcePredicate (v "relation") (v "arguments")))
    (targetNegative (v "relation") (v "arguments")),
  mkRule "tptp-fof-normalize:positive-equal"
    [("left", "Term"), ("right", "Term")] []
    (positive (sourceEqual (v "left") (v "right")))
    (targetEqual (v "left") (v "right")),
  mkRule "tptp-fof-normalize:negative-equal"
    [("left", "Term"), ("right", "Term")] []
    (negative (sourceEqual (v "left") (v "right")))
    (targetNotEqual (v "left") (v "right"))
]

def unaryRules : List RewriteRule := [
  mkRule "tptp-fof-normalize:positive-not"
    [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
    [congruence (negative (v "body")) (v "bodyResult")]
    (positive (sourceNot (v "body"))) (v "bodyResult"),
  mkRule "tptp-fof-normalize:negative-not"
    [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
    [congruence (positive (v "body")) (v "bodyResult")]
    (negative (sourceNot (v "body"))) (v "bodyResult"),
  mkRule "tptp-fof-normalize:positive-all"
    [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
    [congruence (positive (v "body")) (v "bodyResult")]
    (positive (sourceAll (v "body"))) (targetAll (v "bodyResult")),
  mkRule "tptp-fof-normalize:negative-all"
    [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
    [congruence (negative (v "body")) (v "bodyResult")]
    (negative (sourceAll (v "body"))) (targetEx (v "bodyResult")),
  mkRule "tptp-fof-normalize:positive-ex"
    [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
    [congruence (positive (v "body")) (v "bodyResult")]
    (positive (sourceEx (v "body"))) (targetEx (v "bodyResult")),
  mkRule "tptp-fof-normalize:negative-ex"
    [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
    [congruence (negative (v "body")) (v "bodyResult")]
    (negative (sourceEx (v "body"))) (targetAll (v "bodyResult"))
]

def binaryRule (name : String) (polarity : Bool)
    (source : Pattern -> Pattern -> Pattern)
    (leftPolarity rightPolarity : Bool)
    (target : Pattern -> Pattern -> Pattern) : RewriteRule :=
  mkRule name
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula"),
     ("leftResult", "NNFFormula"), ("rightResult", "NNFFormula")]
    [congruence (request leftPolarity (v "left")) (v "leftResult"),
     congruence (request rightPolarity (v "right")) (v "rightResult")]
    (request polarity (source (v "left") (v "right")))
    (target (v "leftResult") (v "rightResult"))

def fourWayRule (name : String) (polarity : Bool)
    (source : Pattern -> Pattern -> Pattern)
    (target : Pattern -> Pattern -> Pattern -> Pattern -> Pattern) :
    RewriteRule :=
  mkRule name
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula"),
     ("leftPositive", "NNFFormula"), ("leftNegative", "NNFFormula"),
     ("rightPositive", "NNFFormula"), ("rightNegative", "NNFFormula")]
    [congruence (positive (v "left")) (v "leftPositive"),
     congruence (negative (v "left")) (v "leftNegative"),
     congruence (positive (v "right")) (v "rightPositive"),
     congruence (negative (v "right")) (v "rightNegative")]
    (request polarity (source (v "left") (v "right")))
    (target (v "leftPositive") (v "leftNegative")
      (v "rightPositive") (v "rightNegative"))

def binaryRules : List RewriteRule := [
  binaryRule "tptp-fof-normalize:positive-and" true sourceAnd true true targetAnd,
  binaryRule "tptp-fof-normalize:negative-and" false sourceAnd false false targetOr,
  binaryRule "tptp-fof-normalize:positive-or" true sourceOr true true targetOr,
  binaryRule "tptp-fof-normalize:negative-or" false sourceOr false false targetAnd,
  binaryRule "tptp-fof-normalize:positive-implies" true sourceImplies false true targetOr,
  binaryRule "tptp-fof-normalize:negative-implies" false sourceImplies true false targetAnd,
  binaryRule "tptp-fof-normalize:positive-reverse-implies" true
    sourceReverseImplies true false (fun left right => targetOr right left),
  binaryRule "tptp-fof-normalize:negative-reverse-implies" false
    sourceReverseImplies false true (fun left right => targetAnd right left),
  binaryRule "tptp-fof-normalize:positive-nor" true sourceNor false false targetAnd,
  binaryRule "tptp-fof-normalize:negative-nor" false sourceNor true true targetOr,
  binaryRule "tptp-fof-normalize:positive-nand" true sourceNand false false targetOr,
  binaryRule "tptp-fof-normalize:negative-nand" false sourceNand true true targetAnd,
  fourWayRule "tptp-fof-normalize:positive-iff" true sourceIff
    (fun leftPositive leftNegative rightPositive rightNegative =>
      targetAnd (targetOr leftNegative rightPositive)
        (targetOr rightNegative leftPositive)),
  fourWayRule "tptp-fof-normalize:negative-iff" false sourceIff
    (fun leftPositive leftNegative rightPositive rightNegative =>
      targetOr (targetAnd leftPositive rightNegative)
        (targetAnd rightPositive leftNegative)),
  fourWayRule "tptp-fof-normalize:positive-xor" true sourceXor
    (fun leftPositive leftNegative rightPositive rightNegative =>
      targetOr (targetAnd leftPositive rightNegative)
        (targetAnd leftNegative rightPositive)),
  fourWayRule "tptp-fof-normalize:negative-xor" false sourceXor
    (fun leftPositive leftNegative rightPositive rightNegative =>
      targetAnd (targetOr leftNegative rightPositive)
        (targetOr rightNegative leftPositive))
]

def rewrites : List RewriteRule := leafRules ++ unaryRules ++ binaryRules

def terms : List GrammarRule := [
  ctor "tptp-fof-resolved:term-variable" "Term" [("index", "Integer")],
  ctor "tptp-fof-resolved:term-function" "Term"
    [("function", "String"), ("arguments", "Terms")],
  ctor "tptp-fof-resolved:terms-nil" "Terms" [],
  ctor "tptp-fof-resolved:terms-cons" "Terms"
    [("head", "Term"), ("tail", "Terms")],
  ctor "tptp-fof-resolved:verum" "ResolvedFormula" [],
  ctor "tptp-fof-resolved:falsum" "ResolvedFormula" [],
  ctor "tptp-fof-resolved:predicate" "ResolvedFormula"
    [("relation", "String"), ("arguments", "Terms")],
  ctor "tptp-fof-resolved:equal" "ResolvedFormula"
    [("left", "Term"), ("right", "Term")],
  ctor "tptp-fof-resolved:not" "ResolvedFormula" [("body", "ResolvedFormula")],
  ctor "tptp-fof-resolved:and" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:or" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:iff" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:implies" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:reverse-implies" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:xor" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:nor" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:nand" "ResolvedFormula"
    [("left", "ResolvedFormula"), ("right", "ResolvedFormula")],
  ctor "tptp-fof-resolved:all" "ResolvedFormula" [("body", "ResolvedFormula")],
  ctor "tptp-fof-resolved:ex" "ResolvedFormula" [("body", "ResolvedFormula")],
  ctor "tptp-fof-nnf:verum" "NNFFormula" [],
  ctor "tptp-fof-nnf:falsum" "NNFFormula" [],
  ctor "tptp-fof-nnf:positive" "NNFFormula"
    [("relation", "String"), ("arguments", "Terms")],
  ctor "tptp-fof-nnf:negative" "NNFFormula"
    [("relation", "String"), ("arguments", "Terms")],
  ctor "tptp-fof-nnf:equal" "NNFFormula"
    [("left", "Term"), ("right", "Term")],
  ctor "tptp-fof-nnf:not-equal" "NNFFormula"
    [("left", "Term"), ("right", "Term")],
  ctor "tptp-fof-nnf:and" "NNFFormula"
    [("left", "NNFFormula"), ("right", "NNFFormula")],
  ctor "tptp-fof-nnf:or" "NNFFormula"
    [("left", "NNFFormula"), ("right", "NNFFormula")],
  ctor "tptp-fof-nnf:all" "NNFFormula" [("body", "NNFFormula")],
  ctor "tptp-fof-nnf:ex" "NNFFormula" [("body", "NNFFormula")],
  ctor "tptp-fof-normalize:positive" "NNFFormula"
    [("formula", "ResolvedFormula")] (some .rewrite),
  ctor "tptp-fof-normalize:negative" "NNFFormula"
    [("formula", "ResolvedFormula")] (some .rewrite)
]

def language : LanguageDef := {
  name := "TPTPFOFNormalization"
  types := [
    { name := "Integer", carrier := .builtinInt },
    { name := "String", carrier := .builtinString },
    "Term", "Terms", "ResolvedFormula", "NNFFormula"]
  terms := terms
  equations := []
  rewrites := rewrites
}

theorem rewrite_count : rewrites.length = 30 := by
  decide

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

@[simp] private theorem language_typeNames : language.typeNames =
    ["Integer", "String", "Term", "Terms", "ResolvedFormula", "NNFFormula"] :=
  rfl

@[simp] private theorem language_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures language = [
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
      ("tptp-fof-normalize:positive", 1),
      ("tptp-fof-normalize:negative", 1)] := by
  rfl

@[simp] private theorem language_constructorLabels :
    RewriteValidationCertificate.constructorLabels language = [
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
      "tptp-fof-normalize:positive",
      "tptp-fof-normalize:negative"] := by
  rfl

local macro "certify_normalization_row" : tactic =>
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
      typed, binaryRule, fourWayRule, mkRule, congruence, request,
      positive, negative,
      sourceVerum, sourceFalsum, sourcePredicate, sourceEqual, sourceNot,
      sourceAnd, sourceOr, sourceIff, sourceImplies, sourceReverseImplies,
      sourceXor, sourceNor, sourceNand, sourceAll, sourceEx, targetVerum,
      targetFalsum, targetPositive, targetNegative, targetEqual,
      targetNotEqual, targetAnd, targetOr, targetAll, targetEx, a, v,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  decide

private theorem positiveVerumRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:positive-verum" [] []
        (positive sourceVerum) targetVerum) = true := by
  certify_normalization_row

private theorem negativeVerumRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:negative-verum" [] []
        (negative sourceVerum) targetFalsum) = true := by
  certify_normalization_row

private theorem positiveFalsumRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:positive-falsum" [] []
        (positive sourceFalsum) targetFalsum) = true := by
  certify_normalization_row

private theorem negativeFalsumRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:negative-falsum" [] []
        (negative sourceFalsum) targetVerum) = true := by
  certify_normalization_row

private theorem positivePredicateRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:positive-predicate"
        [("relation", "String"), ("arguments", "Terms")] []
        (positive (sourcePredicate (v "relation") (v "arguments")))
        (targetPositive (v "relation") (v "arguments"))) = true := by
  certify_normalization_row

private theorem negativePredicateRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:negative-predicate"
        [("relation", "String"), ("arguments", "Terms")] []
        (negative (sourcePredicate (v "relation") (v "arguments")))
        (targetNegative (v "relation") (v "arguments"))) = true := by
  certify_normalization_row

private theorem positiveEqualRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:positive-equal"
        [("left", "Term"), ("right", "Term")] []
        (positive (sourceEqual (v "left") (v "right")))
        (targetEqual (v "left") (v "right"))) = true := by
  certify_normalization_row

private theorem negativeEqualRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:negative-equal"
        [("left", "Term"), ("right", "Term")] []
        (negative (sourceEqual (v "left") (v "right")))
        (targetNotEqual (v "left") (v "right"))) = true := by
  certify_normalization_row

private theorem positiveNotRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:positive-not"
        [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
        [congruence (negative (v "body")) (v "bodyResult")]
        (positive (sourceNot (v "body"))) (v "bodyResult")) = true := by
  certify_normalization_row

private theorem negativeNotRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:negative-not"
        [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
        [congruence (positive (v "body")) (v "bodyResult")]
        (negative (sourceNot (v "body"))) (v "bodyResult")) = true := by
  certify_normalization_row

private theorem positiveAllRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:positive-all"
        [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
        [congruence (positive (v "body")) (v "bodyResult")]
        (positive (sourceAll (v "body")))
        (targetAll (v "bodyResult"))) = true := by
  certify_normalization_row

private theorem negativeAllRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:negative-all"
        [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
        [congruence (negative (v "body")) (v "bodyResult")]
        (negative (sourceAll (v "body")))
        (targetEx (v "bodyResult"))) = true := by
  certify_normalization_row

private theorem positiveExRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:positive-ex"
        [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
        [congruence (positive (v "body")) (v "bodyResult")]
        (positive (sourceEx (v "body")))
        (targetEx (v "bodyResult"))) = true := by
  certify_normalization_row

private theorem negativeExRule_checked :
    RewriteValidationCertificate.check language
      (mkRule "tptp-fof-normalize:negative-ex"
        [("body", "ResolvedFormula"), ("bodyResult", "NNFFormula")]
        [congruence (negative (v "body")) (v "bodyResult")]
        (negative (sourceEx (v "body")))
        (targetAll (v "bodyResult"))) = true := by
  certify_normalization_row

private theorem positiveAndRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:positive-and" true
        sourceAnd true true targetAnd) = true := by
  certify_normalization_row

private theorem negativeAndRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:negative-and" false
        sourceAnd false false targetOr) = true := by
  certify_normalization_row

private theorem positiveOrRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:positive-or" true
        sourceOr true true targetOr) = true := by
  certify_normalization_row

private theorem negativeOrRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:negative-or" false
        sourceOr false false targetAnd) = true := by
  certify_normalization_row

private theorem positiveImpliesRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:positive-implies" true
        sourceImplies false true targetOr) = true := by
  certify_normalization_row

private theorem negativeImpliesRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:negative-implies" false
        sourceImplies true false targetAnd) = true := by
  certify_normalization_row

private theorem positiveReverseImpliesRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:positive-reverse-implies" true
        sourceReverseImplies true false
        (fun left right => targetOr right left)) = true := by
  certify_normalization_row

private theorem negativeReverseImpliesRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:negative-reverse-implies" false
        sourceReverseImplies false true
        (fun left right => targetAnd right left)) = true := by
  certify_normalization_row

private theorem positiveNorRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:positive-nor" true
        sourceNor false false targetAnd) = true := by
  certify_normalization_row

private theorem negativeNorRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:negative-nor" false
        sourceNor true true targetOr) = true := by
  certify_normalization_row

private theorem positiveNandRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:positive-nand" true
        sourceNand false false targetOr) = true := by
  certify_normalization_row

private theorem negativeNandRule_checked :
    RewriteValidationCertificate.check language
      (binaryRule "tptp-fof-normalize:negative-nand" false
        sourceNand true true targetAnd) = true := by
  certify_normalization_row

private theorem positiveIffRule_checked :
    RewriteValidationCertificate.check language
      (fourWayRule "tptp-fof-normalize:positive-iff" true sourceIff
        (fun leftPositive leftNegative rightPositive rightNegative =>
          targetAnd (targetOr leftNegative rightPositive)
            (targetOr rightNegative leftPositive))) = true := by
  certify_normalization_row

private theorem negativeIffRule_checked :
    RewriteValidationCertificate.check language
      (fourWayRule "tptp-fof-normalize:negative-iff" false sourceIff
        (fun leftPositive leftNegative rightPositive rightNegative =>
          targetOr (targetAnd leftPositive rightNegative)
            (targetAnd rightPositive leftNegative))) = true := by
  certify_normalization_row

private theorem positiveXorRule_checked :
    RewriteValidationCertificate.check language
      (fourWayRule "tptp-fof-normalize:positive-xor" true sourceXor
        (fun leftPositive leftNegative rightPositive rightNegative =>
          targetOr (targetAnd leftPositive rightNegative)
            (targetAnd leftNegative rightPositive))) = true := by
  certify_normalization_row

private theorem negativeXorRule_checked :
    RewriteValidationCertificate.check language
      (fourWayRule "tptp-fof-normalize:negative-xor" false sourceXor
        (fun leftPositive leftNegative rightPositive rightNegative =>
          targetAnd (targetOr leftNegative rightPositive)
            (targetOr rightNegative leftPositive))) = true := by
  certify_normalization_row

local macro "validate_normalization_row" : tactic =>
  `(tactic|
    apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup <;>
    first
    | exact positiveVerumRule_checked
    | exact negativeVerumRule_checked
    | exact positiveFalsumRule_checked
    | exact negativeFalsumRule_checked
    | exact positivePredicateRule_checked
    | exact negativePredicateRule_checked
    | exact positiveEqualRule_checked
    | exact negativeEqualRule_checked
    | exact positiveNotRule_checked
    | exact negativeNotRule_checked
    | exact positiveAllRule_checked
    | exact negativeAllRule_checked
    | exact positiveExRule_checked
    | exact negativeExRule_checked
    | exact positiveAndRule_checked
    | exact negativeAndRule_checked
    | exact positiveOrRule_checked
    | exact negativeOrRule_checked
    | exact positiveImpliesRule_checked
    | exact negativeImpliesRule_checked
    | exact positiveReverseImpliesRule_checked
    | exact negativeReverseImpliesRule_checked
    | exact positiveNorRule_checked
    | exact negativeNorRule_checked
    | exact positiveNandRule_checked
    | exact negativeNandRule_checked
    | exact positiveIffRule_checked
    | exact negativeIffRule_checked
    | exact positiveXorRule_checked
    | exact negativeXorRule_checked)

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide
  intro rewrite membership
  simp only [language_rewrites, rewrites, leafRules, unaryRules, binaryRules,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with earlier | binary
  · rcases earlier with leaf | unary
    · rcases leaf with
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        validate_normalization_row
    · rcases unary with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        validate_normalization_row
  · rcases binary with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
       rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      validate_normalization_row

def validated : ValidatedLanguageDef where
  language := language
  valid := language_validate

local macro "normalize_root" : tactic =>
  `(tactic|
    simp [rewriteAt, language_rewrites, rewrites, leafRules, unaryRules,
      binaryRules, applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing, binaryRule, fourWayRule, mkRule,
      congruence, positive, negative, request, sourceVerum, sourceFalsum,
      sourcePredicate, sourceEqual, sourceNot, sourceAnd, sourceOr, sourceIff,
      sourceImplies, sourceReverseImplies, sourceXor, sourceNor, sourceNand,
      sourceAll, sourceEx, targetVerum, targetFalsum, targetPositive,
      targetNegative, targetEqual, targetNotEqual, targetAnd, targetOr,
      targetAll, targetEx, a, v, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local syntax "normalize_root_using " term,* : tactic
local macro_rules
  | `(tactic| normalize_root_using $_proofs:term,*) =>
      `(tactic|
        simp only [positive, negative, a] at * <;>
        simp [*, rewriteAt, language_rewrites, rewrites, leafRules, unaryRules,
          binaryRules, applyRuleUsing, matchPatternForRule_eq_syntactic,
          premisesUsing, premiseStepUsing, binaryRule, fourWayRule, mkRule,
          congruence, positive, negative, request, sourceVerum, sourceFalsum,
          sourcePredicate, sourceEqual, sourceNot, sourceAnd, sourceOr,
          sourceIff, sourceImplies, sourceReverseImplies, sourceXor, sourceNor,
          sourceNand, sourceAll, sourceEx, targetVerum, targetFalsum,
          targetPositive, targetNegative, targetEqual, targetNotEqual,
          targetAnd, targetOr, targetAll, targetEx, a, v, matchPattern,
          matchArgs, mergeBindings, applyBindingsForRule, applyBindings])

theorem positive_verum_rewriteAt_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (positive sourceVerum) = [targetVerum] := by
  normalize_root

theorem negative_verum_rewriteAt_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (negative sourceVerum) = [targetFalsum] := by
  normalize_root

theorem positive_falsum_rewriteAt_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (positive sourceFalsum) = [targetFalsum] := by
  normalize_root

theorem negative_falsum_rewriteAt_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (negative sourceFalsum) = [targetVerum] := by
  normalize_root

theorem positive_predicate_rewriteAt_exact (fuel : Nat)
    (relation arguments : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (positive (sourcePredicate relation arguments)) =
      [targetPositive relation arguments] := by
  normalize_root

theorem negative_predicate_rewriteAt_exact (fuel : Nat)
    (relation arguments : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (negative (sourcePredicate relation arguments)) =
      [targetNegative relation arguments] := by
  normalize_root

theorem positive_equal_rewriteAt_exact (fuel : Nat) (left right : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (positive (sourceEqual left right)) = [targetEqual left right] := by
  normalize_root

theorem negative_equal_rewriteAt_exact (fuel : Nat) (left right : Pattern) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (negative (sourceEqual left right)) = [targetNotEqual left right] := by
  normalize_root

theorem positive_not_rewriteAt_exact (fuel : Nat) (body result : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative body) = [result]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceNot body)) = [result] := by
  normalize_root_using bodyExact

theorem negative_not_rewriteAt_exact (fuel : Nat) (body result : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive body) = [result]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceNot body)) = [result] := by
  normalize_root_using bodyExact

theorem positive_all_rewriteAt_exact (fuel : Nat) (body result : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive body) = [result]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceAll body)) = [targetAll result] := by
  normalize_root_using bodyExact

theorem negative_all_rewriteAt_exact (fuel : Nat) (body result : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative body) = [result]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceAll body)) = [targetEx result] := by
  normalize_root_using bodyExact

theorem positive_ex_rewriteAt_exact (fuel : Nat) (body result : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive body) = [result]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceEx body)) = [targetEx result] := by
  normalize_root_using bodyExact

theorem negative_ex_rewriteAt_exact (fuel : Nat) (body result : Pattern)
    (bodyExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative body) = [result]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceEx body)) = [targetAll result] := by
  normalize_root_using bodyExact

theorem positive_and_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceAnd left right)) =
        [targetAnd leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem negative_and_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceAnd left right)) =
        [targetOr leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem positive_or_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceOr left right)) =
        [targetOr leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem negative_or_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceOr left right)) =
        [targetAnd leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem positive_implies_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceImplies left right)) =
        [targetOr leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem negative_implies_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceImplies left right)) =
        [targetAnd leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem positive_reverseImplies_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceReverseImplies left right)) =
        [targetOr rightResult leftResult] := by
  normalize_root_using leftExact, rightExact

theorem negative_reverseImplies_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceReverseImplies left right)) =
        [targetAnd rightResult leftResult] := by
  normalize_root_using leftExact, rightExact

theorem positive_nor_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceNor left right)) =
        [targetAnd leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem negative_nor_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceNor left right)) =
        [targetOr leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem positive_nand_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (negative right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceNand left right)) =
        [targetOr leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem negative_nand_rewriteAt_exact (fuel : Nat)
    (left right leftResult rightResult : Pattern)
    (leftExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive left) = [leftResult])
    (rightExact : rewriteAt (engineBasePremises RelationEnv.empty) language fuel
      (positive right) = [rightResult]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceNand left right)) =
        [targetAnd leftResult rightResult] := by
  normalize_root_using leftExact, rightExact

theorem positive_iff_rewriteAt_exact (fuel : Nat)
    (left right leftPositive leftNegative rightPositive rightNegative : Pattern)
    (leftPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive left) = [leftPositive])
    (leftNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative left) = [leftNegative])
    (rightPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive right) = [rightPositive])
    (rightNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative right) = [rightNegative]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceIff left right)) =
        [targetAnd (targetOr leftNegative rightPositive)
          (targetOr rightNegative leftPositive)] := by
  normalize_root_using leftPositiveExact, leftNegativeExact,
    rightPositiveExact, rightNegativeExact

theorem negative_iff_rewriteAt_exact (fuel : Nat)
    (left right leftPositive leftNegative rightPositive rightNegative : Pattern)
    (leftPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive left) = [leftPositive])
    (leftNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative left) = [leftNegative])
    (rightPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive right) = [rightPositive])
    (rightNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative right) = [rightNegative]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceIff left right)) =
        [targetOr (targetAnd leftPositive rightNegative)
          (targetAnd rightPositive leftNegative)] := by
  normalize_root_using leftPositiveExact, leftNegativeExact,
    rightPositiveExact, rightNegativeExact

theorem positive_xor_rewriteAt_exact (fuel : Nat)
    (left right leftPositive leftNegative rightPositive rightNegative : Pattern)
    (leftPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive left) = [leftPositive])
    (leftNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative left) = [leftNegative])
    (rightPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive right) = [rightPositive])
    (rightNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative right) = [rightNegative]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (positive (sourceXor left right)) =
        [targetOr (targetAnd leftPositive rightNegative)
          (targetAnd leftNegative rightPositive)] := by
  normalize_root_using leftPositiveExact, leftNegativeExact,
    rightPositiveExact, rightNegativeExact

theorem negative_xor_rewriteAt_exact (fuel : Nat)
    (left right leftPositive leftNegative rightPositive rightNegative : Pattern)
    (leftPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive left) = [leftPositive])
    (leftNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative left) = [leftNegative])
    (rightPositiveExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (positive right) = [rightPositive])
    (rightNegativeExact :
      rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (negative right) = [rightNegative]) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
      (negative (sourceXor left right)) =
        [targetAnd (targetOr leftNegative rightPositive)
          (targetOr rightNegative leftPositive)] := by
  normalize_root_using leftPositiveExact, leftNegativeExact,
    rightPositiveExact, rightNegativeExact

/-! ## A representation-independent formula spine -/

inductive FormulaPattern where
  | verum
  | falsum
  | predicate (relation arguments : Pattern)
  | equal (left right : Pattern)
  | not (body : FormulaPattern)
  | and (left right : FormulaPattern)
  | or (left right : FormulaPattern)
  | iff (left right : FormulaPattern)
  | implies (left right : FormulaPattern)
  | reverseImplies (left right : FormulaPattern)
  | xor (left right : FormulaPattern)
  | nor (left right : FormulaPattern)
  | nand (left right : FormulaPattern)
  | all (body : FormulaPattern)
  | ex (body : FormulaPattern)
  deriving Repr

def FormulaPattern.source : FormulaPattern -> Pattern
  | .verum => sourceVerum
  | .falsum => sourceFalsum
  | .predicate relation arguments => sourcePredicate relation arguments
  | .equal left right => sourceEqual left right
  | .not body => sourceNot body.source
  | .and left right => sourceAnd left.source right.source
  | .or left right => sourceOr left.source right.source
  | .iff left right => sourceIff left.source right.source
  | .implies left right => sourceImplies left.source right.source
  | .reverseImplies left right => sourceReverseImplies left.source right.source
  | .xor left right => sourceXor left.source right.source
  | .nor left right => sourceNor left.source right.source
  | .nand left right => sourceNand left.source right.source
  | .all body => sourceAll body.source
  | .ex body => sourceEx body.source

def FormulaPattern.normalize (polarity : Bool) : FormulaPattern -> Pattern
  | .verum => if polarity then targetVerum else targetFalsum
  | .falsum => if polarity then targetFalsum else targetVerum
  | .predicate relation arguments =>
      if polarity then targetPositive relation arguments
      else targetNegative relation arguments
  | .equal left right =>
      if polarity then targetEqual left right else targetNotEqual left right
  | .not body => body.normalize (!polarity)
  | .and left right =>
      if polarity then targetAnd (left.normalize true) (right.normalize true)
      else targetOr (left.normalize false) (right.normalize false)
  | .or left right =>
      if polarity then targetOr (left.normalize true) (right.normalize true)
      else targetAnd (left.normalize false) (right.normalize false)
  | .iff left right =>
      if polarity then
        targetAnd (targetOr (left.normalize false) (right.normalize true))
          (targetOr (right.normalize false) (left.normalize true))
      else
        targetOr (targetAnd (left.normalize true) (right.normalize false))
          (targetAnd (right.normalize true) (left.normalize false))
  | .implies left right =>
      if polarity then targetOr (left.normalize false) (right.normalize true)
      else targetAnd (left.normalize true) (right.normalize false)
  | .reverseImplies left right =>
      if polarity then targetOr (right.normalize false) (left.normalize true)
      else targetAnd (right.normalize true) (left.normalize false)
  | .xor left right =>
      if polarity then
        targetOr (targetAnd (left.normalize true) (right.normalize false))
          (targetAnd (left.normalize false) (right.normalize true))
      else
        targetAnd (targetOr (left.normalize false) (right.normalize true))
          (targetOr (right.normalize false) (left.normalize true))
  | .nor left right =>
      if polarity then targetAnd (left.normalize false) (right.normalize false)
      else targetOr (left.normalize true) (right.normalize true)
  | .nand left right =>
      if polarity then targetOr (left.normalize false) (right.normalize false)
      else targetAnd (left.normalize true) (right.normalize true)
  | .all body =>
      if polarity then targetAll (body.normalize true)
      else targetEx (body.normalize false)
  | .ex body =>
      if polarity then targetEx (body.normalize true)
      else targetAll (body.normalize false)

def FormulaPattern.height : FormulaPattern -> Nat
  | .verum | .falsum | .predicate _ _ | .equal _ _ => 1
  | .not body | .all body | .ex body => body.height + 1
  | .and left right | .or left right | .iff left right
  | .implies left right | .reverseImplies left right
  | .xor left right | .nor left right | .nand left right =>
      max left.height right.height + 1

/-!
The fuel bound is structural: one unit for the root rule and enough fuel for
the deepest congruence premise.  The conclusion is an exact singleton, not
mere membership, so the authored language neither loses nor invents a result.
-/
theorem FormulaPattern.rewriteAt_exact
    (formula : FormulaPattern) (polarity : Bool) (fuel : Nat)
    (enough : formula.height ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request polarity formula.source) =
      [formula.normalize polarity] := by
  induction formula generalizing polarity fuel with
  | verum =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_verum_rewriteAt_exact fuel
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_verum_rewriteAt_exact fuel
  | falsum =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_falsum_rewriteAt_exact fuel
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_falsum_rewriteAt_exact fuel
  | predicate relation arguments =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_predicate_rewriteAt_exact fuel relation arguments
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_predicate_rewriteAt_exact fuel relation arguments
  | equal left right =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_equal_rewriteAt_exact fuel left right
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_equal_rewriteAt_exact fuel left right
  | not body bodyIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have bodyEnough : body.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_not_rewriteAt_exact fuel body.source
                  (body.normalize true)
                  (bodyIH (polarity := true) (fuel := fuel) bodyEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_not_rewriteAt_exact fuel body.source
                  (body.normalize false)
                  (bodyIH (polarity := false) (fuel := fuel) bodyEnough)
  | and left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_and_rewriteAt_exact fuel left.source right.source
                  (left.normalize false) (right.normalize false)
                  (leftIH (polarity := false) (fuel := fuel) leftEnough)
                  (rightIH (polarity := false) (fuel := fuel) rightEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_and_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (right.normalize true)
                  (leftIH (polarity := true) (fuel := fuel) leftEnough)
                  (rightIH (polarity := true) (fuel := fuel) rightEnough)
  | or left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_or_rewriteAt_exact fuel left.source right.source
                  (left.normalize false) (right.normalize false)
                  (leftIH (polarity := false) (fuel := fuel) leftEnough)
                  (rightIH (polarity := false) (fuel := fuel) rightEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_or_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (right.normalize true)
                  (leftIH (polarity := true) (fuel := fuel) leftEnough)
                  (rightIH (polarity := true) (fuel := fuel) rightEnough)
  | iff left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          have leftPositive :=
            leftIH (polarity := true) (fuel := fuel) leftEnough
          have leftNegative :=
            leftIH (polarity := false) (fuel := fuel) leftEnough
          have rightPositive :=
            rightIH (polarity := true) (fuel := fuel) rightEnough
          have rightNegative :=
            rightIH (polarity := false) (fuel := fuel) rightEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_iff_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (left.normalize false)
                  (right.normalize true) (right.normalize false)
                  leftPositive leftNegative rightPositive rightNegative
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_iff_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (left.normalize false)
                  (right.normalize true) (right.normalize false)
                  leftPositive leftNegative rightPositive rightNegative
  | implies left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_implies_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (right.normalize false)
                  (leftIH (polarity := true) (fuel := fuel) leftEnough)
                  (rightIH (polarity := false) (fuel := fuel) rightEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_implies_rewriteAt_exact fuel left.source right.source
                  (left.normalize false) (right.normalize true)
                  (leftIH (polarity := false) (fuel := fuel) leftEnough)
                  (rightIH (polarity := true) (fuel := fuel) rightEnough)
  | reverseImplies left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_reverseImplies_rewriteAt_exact fuel
                  left.source right.source (left.normalize false)
                  (right.normalize true)
                  (leftIH (polarity := false) (fuel := fuel) leftEnough)
                  (rightIH (polarity := true) (fuel := fuel) rightEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_reverseImplies_rewriteAt_exact fuel
                  left.source right.source (left.normalize true)
                  (right.normalize false)
                  (leftIH (polarity := true) (fuel := fuel) leftEnough)
                  (rightIH (polarity := false) (fuel := fuel) rightEnough)
  | xor left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          have leftPositive :=
            leftIH (polarity := true) (fuel := fuel) leftEnough
          have leftNegative :=
            leftIH (polarity := false) (fuel := fuel) leftEnough
          have rightPositive :=
            rightIH (polarity := true) (fuel := fuel) rightEnough
          have rightNegative :=
            rightIH (polarity := false) (fuel := fuel) rightEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_xor_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (left.normalize false)
                  (right.normalize true) (right.normalize false)
                  leftPositive leftNegative rightPositive rightNegative
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_xor_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (left.normalize false)
                  (right.normalize true) (right.normalize false)
                  leftPositive leftNegative rightPositive rightNegative
  | nor left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_nor_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (right.normalize true)
                  (leftIH (polarity := true) (fuel := fuel) leftEnough)
                  (rightIH (polarity := true) (fuel := fuel) rightEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_nor_rewriteAt_exact fuel left.source right.source
                  (left.normalize false) (right.normalize false)
                  (leftIH (polarity := false) (fuel := fuel) leftEnough)
                  (rightIH (polarity := false) (fuel := fuel) rightEnough)
  | nand left right leftIH rightIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have maximumEnough : max left.height right.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          have leftEnough : left.height ≤ fuel :=
            (Nat.le_max_left _ _).trans maximumEnough
          have rightEnough : right.height ≤ fuel :=
            (Nat.le_max_right _ _).trans maximumEnough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_nand_rewriteAt_exact fuel left.source right.source
                  (left.normalize true) (right.normalize true)
                  (leftIH (polarity := true) (fuel := fuel) leftEnough)
                  (rightIH (polarity := true) (fuel := fuel) rightEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_nand_rewriteAt_exact fuel left.source right.source
                  (left.normalize false) (right.normalize false)
                  (leftIH (polarity := false) (fuel := fuel) leftEnough)
                  (rightIH (polarity := false) (fuel := fuel) rightEnough)
  | all body bodyIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have bodyEnough : body.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_all_rewriteAt_exact fuel body.source
                  (body.normalize false)
                  (bodyIH (polarity := false) (fuel := fuel) bodyEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_all_rewriteAt_exact fuel body.source
                  (body.normalize true)
                  (bodyIH (polarity := true) (fuel := fuel) bodyEnough)
  | ex body bodyIH =>
      cases fuel with
      | zero => simp [FormulaPattern.height] at enough
      | succ fuel =>
          have bodyEnough : body.height ≤ fuel := by
            simpa [FormulaPattern.height, Nat.succ_eq_add_one] using enough
          cases polarity with
          | false =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                negative_ex_rewriteAt_exact fuel body.source
                  (body.normalize false)
                  (bodyIH (polarity := false) (fuel := fuel) bodyEnough)
          | true =>
              simpa [request, FormulaPattern.source, FormulaPattern.normalize,
                Nat.succ_eq_add_one] using
                positive_ex_rewriteAt_exact fuel body.source
                  (body.normalize true)
                  (bodyIH (polarity := true) (fuel := fuel) bodyEnough)

/-! ## The typed semantic image -/

/-- Encoding choices for the first-order leaves.  The normalization GSLT is
parametric in these representations: it inspects only formula connectives,
never terms, predicate names, or argument-list storage. -/
structure SemanticPatternCodec where
  term : ∀ {depth : Nat},
    TptpFofNormalizationSemantics.Term depth -> Pattern
  terms : ∀ {depth arity : Nat},
    (Fin arity -> TptpFofNormalizationSemantics.Term depth) -> Pattern
  predicate : ∀ {arity : Nat},
    TptpFofNormalizationSemantics.PredicateSymbol arity -> Pattern

def semanticHeight {depth : Nat} :
    TptpFofNormalizationSemantics.Formula depth -> Nat
  | .verum | .falsum | .predicate _ _ | .equal _ _ => 1
  | .not body | .all body | .ex body => semanticHeight body + 1
  | .and left right | .or left right | .iff left right
  | .implies left right | .reverseImplies left right
  | .xor left right | .nor left right | .nand left right =>
      max (semanticHeight left) (semanticHeight right) + 1

def encodeSourceFormula (codec : SemanticPatternCodec) {depth : Nat} :
    TptpFofNormalizationSemantics.Formula depth -> FormulaPattern
  | .verum => .verum
  | .falsum => .falsum
  | .predicate predicate arguments =>
      .predicate (codec.predicate predicate) (codec.terms arguments)
  | .equal left right => .equal (codec.term left) (codec.term right)
  | .not body => .not (encodeSourceFormula codec body)
  | .and left right =>
      .and (encodeSourceFormula codec left) (encodeSourceFormula codec right)
  | .or left right =>
      .or (encodeSourceFormula codec left) (encodeSourceFormula codec right)
  | .iff left right =>
      .iff (encodeSourceFormula codec left) (encodeSourceFormula codec right)
  | .implies left right =>
      .implies (encodeSourceFormula codec left)
        (encodeSourceFormula codec right)
  | .reverseImplies left right =>
      .reverseImplies (encodeSourceFormula codec left)
        (encodeSourceFormula codec right)
  | .xor left right =>
      .xor (encodeSourceFormula codec left) (encodeSourceFormula codec right)
  | .nor left right =>
      .nor (encodeSourceFormula codec left) (encodeSourceFormula codec right)
  | .nand left right =>
      .nand (encodeSourceFormula codec left) (encodeSourceFormula codec right)
  | .all body => .all (encodeSourceFormula codec body)
  | .ex body => .ex (encodeSourceFormula codec body)

def encodeNNFFormula (codec : SemanticPatternCodec) {depth : Nat} :
    LO.FirstOrder.Semiformula TptpFofNormalizationSemantics.language Empty
      depth -> Pattern
  | .verum => targetVerum
  | .falsum => targetFalsum
  | .rel relation arguments =>
      match relation with
      | .predicate predicate =>
          targetPositive (codec.predicate predicate) (codec.terms arguments)
      | .equality =>
          targetEqual (codec.term (arguments 0)) (codec.term (arguments 1))
  | .nrel relation arguments =>
      match relation with
      | .predicate predicate =>
          targetNegative (codec.predicate predicate) (codec.terms arguments)
      | .equality =>
          targetNotEqual (codec.term (arguments 0)) (codec.term (arguments 1))
  | .and left right =>
      targetAnd (encodeNNFFormula codec left) (encodeNNFFormula codec right)
  | .or left right =>
      targetOr (encodeNNFFormula codec left) (encodeNNFFormula codec right)
  | .all body => targetAll (encodeNNFFormula codec body)
  | .ex body => targetEx (encodeNNFFormula codec body)

theorem encodeSourceFormula_height (codec : SemanticPatternCodec)
    {depth : Nat}
    (formula : TptpFofNormalizationSemantics.Formula depth) :
    (encodeSourceFormula codec formula).height = semanticHeight formula := by
  induction formula <;>
    simp [encodeSourceFormula, FormulaPattern.height, semanticHeight, *]

theorem encode_normalize_exact (codec : SemanticPatternCodec)
    {depth : Nat} (polarity : Bool)
    (formula : TptpFofNormalizationSemantics.Formula depth) :
    (encodeSourceFormula codec formula).normalize polarity =
      encodeNNFFormula codec
        (TptpFofNormalizationSemantics.normalize polarity formula) := by
  induction formula generalizing polarity <;>
    cases polarity <;>
    simp [encodeSourceFormula, FormulaPattern.normalize, encodeNNFFormula,
      TptpFofNormalizationSemantics.normalize, *]

/-- The actual authored GSLT implements the typed, semantically proved NNF
normalizer on every binder-resolved formula, for every leaf representation. -/
theorem typed_rewriteAt_exact (codec : SemanticPatternCodec)
    {depth : Nat} (polarity : Bool)
    (formula : TptpFofNormalizationSemantics.Formula depth) (fuel : Nat)
    (enough : semanticHeight formula ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty) language fuel
        (request polarity (encodeSourceFormula codec formula).source) =
      [encodeNNFFormula codec
        (TptpFofNormalizationSemantics.normalize polarity formula)] := by
  rw [← encode_normalize_exact codec polarity formula]
  apply FormulaPattern.rewriteAt_exact
  simpa only [encodeSourceFormula_height] using enough

end Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef
