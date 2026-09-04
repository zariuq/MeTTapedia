import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Authored evidence-bearing definitional CNF generation

This LanguageDef converts a definitionally named Skolem FOF matrix to clauses.
It traverses the definition and introduced-predicate ledgers in lockstep, so
the arity and identity used to construct each defined atom come from the
evidence already retained by naming.  A mismatch leaves the request
unreduced.

Every definition contributes exactly three clauses for its full predicate
equivalence.  The base case contributes the unit clause asserting the named
root.  The traversal is linear in the number of definitions and clauses.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def typed (entries : List (String × String)) : List (String × TypeExpr) :=
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

def indexZero : Pattern := a "tptp-fof-resolved:index-zero"
def indexSucc (index : Pattern) : Pattern :=
  a "tptp-fof-resolved:index-succ" [index]

def variablesRequest (remaining next : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:variables-request" [remaining, next]
def variablesResult (remaining next arguments : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:variables-result" [remaining, next, arguments]

def negateRequest (source : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:negate-request" [source]
def negateResult (source target : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:negate-result" [source, target]

def clausesRequest (root definitions introduced : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:clauses-request" [root, definitions, introduced]
def clausesResult (root definitions introduced clauses : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:clauses-result"
    [root, definitions, introduced, clauses]

def generateRequest (named : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:generate-request" [named]
def generateResult (named target : Pattern) : Pattern :=
  a "tptp-fof-cnf-gen:generate-result" [named, target]

def operationTerms : List GrammarRule := [
  ctor "tptp-fof-cnf-gen:variables-request"
    "TptpFofCnfGeneration:VariablesResult"
    [("remaining", "TptpResolvedFof:Index"),
     ("next", "TptpResolvedFof:Index")],
  ctor "tptp-fof-cnf-gen:variables-result"
    "TptpFofCnfGeneration:VariablesResult"
    [("remaining", "TptpResolvedFof:Index"),
     ("next", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-cnf-gen:negate-request"
    "TptpFofCnfGeneration:NegateResult"
    [("source", "TptpFofNamed:Reference")],
  ctor "tptp-fof-cnf-gen:negate-result"
    "TptpFofCnfGeneration:NegateResult"
    [("source", "TptpFofNamed:Reference"),
     ("target", "TptpFofNamed:Reference")],
  ctor "tptp-fof-cnf-gen:clauses-request"
    "TptpFofCnfGeneration:ClausesResult"
    [("root", "TptpFofNamed:Reference"),
     ("definitions", "TptpFofNamed:Definitions"),
     ("introduced", "TptpFofNamed:IntroducedList")],
  ctor "tptp-fof-cnf-gen:clauses-result"
    "TptpFofCnfGeneration:ClausesResult"
    [("root", "TptpFofNamed:Reference"),
     ("definitions", "TptpFofNamed:Definitions"),
     ("introduced", "TptpFofNamed:IntroducedList"),
     ("clauses", "TptpFofCnf:Clauses")],
  ctor "tptp-fof-cnf-gen:generate-request"
    "TptpFofCnfGeneration:GenerateResult"
    [("named", "TptpFofNamed:Output")],
  ctor "tptp-fof-cnf-gen:generate-result"
    "TptpFofCnfGeneration:GenerateResult"
    [("named", "TptpFofNamed:Output"),
     ("target", "TptpFofCnf:Output")]
]

def variablesRewrites : List RewriteRule := [
  mkRule "tptp-fof-cnf-gen:variables-zero"
    [("next", "TptpResolvedFof:Index")] []
    (variablesRequest indexZero (v "next"))
    (variablesResult indexZero (v "next")
      TptpFofSkolemLanguageDef.termsNil),
  mkRule "tptp-fof-cnf-gen:variables-succ"
    [("remaining", "TptpResolvedFof:Index"),
     ("next", "TptpResolvedFof:Index"),
     ("tail", "TptpFofSkolem:Terms")]
    [congruence
      (variablesRequest (v "remaining") (indexSucc (v "next")))
      (variablesResult (v "remaining") (indexSucc (v "next"))
        (v "tail"))]
    (variablesRequest (indexSucc (v "remaining")) (v "next"))
    (variablesResult (indexSucc (v "remaining")) (v "next")
      (TptpFofSkolemLanguageDef.termsCons
        (TptpFofSkolemLanguageDef.termVariable (v "next")) (v "tail")))
]

def negateRule (name : String) (source target : Pattern) : RewriteRule :=
  mkRule name [] [] (negateRequest source) (negateResult source target)

def negateRewrites : List RewriteRule := [
  negateRule "tptp-fof-cnf-gen:negate-verum"
    TptpFofDefinitionalCnfLanguageDef.refVerum
    TptpFofDefinitionalCnfLanguageDef.refFalsum,
  negateRule "tptp-fof-cnf-gen:negate-falsum"
    TptpFofDefinitionalCnfLanguageDef.refFalsum
    TptpFofDefinitionalCnfLanguageDef.refVerum,
  mkRule "tptp-fof-cnf-gen:negate-original-positive"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")] []
    (negateRequest
      (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
        (v "relation") (v "arguments")))
    (negateResult
      (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
        (v "relation") (v "arguments"))
      (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
        (v "relation") (v "arguments"))),
  mkRule "tptp-fof-cnf-gen:negate-original-negative"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")] []
    (negateRequest
      (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
        (v "relation") (v "arguments")))
    (negateResult
      (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
        (v "relation") (v "arguments"))
      (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
        (v "relation") (v "arguments"))),
  mkRule "tptp-fof-cnf-gen:negate-equal"
    [("left", "TptpFofSkolem:Term"),
     ("right", "TptpFofSkolem:Term")] []
    (negateRequest
      (TptpFofDefinitionalCnfLanguageDef.refEqual
        (v "left") (v "right")))
    (negateResult
      (TptpFofDefinitionalCnfLanguageDef.refEqual
        (v "left") (v "right"))
      (TptpFofDefinitionalCnfLanguageDef.refNotEqual
        (v "left") (v "right"))),
  mkRule "tptp-fof-cnf-gen:negate-not-equal"
    [("left", "TptpFofSkolem:Term"),
     ("right", "TptpFofSkolem:Term")] []
    (negateRequest
      (TptpFofDefinitionalCnfLanguageDef.refNotEqual
        (v "left") (v "right")))
    (negateResult
      (TptpFofDefinitionalCnfLanguageDef.refNotEqual
        (v "left") (v "right"))
      (TptpFofDefinitionalCnfLanguageDef.refEqual
        (v "left") (v "right"))),
  mkRule "tptp-fof-cnf-gen:negate-defined-positive"
    [("id", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms")] []
    (negateRequest
      (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
        (v "id") (v "arguments")))
    (negateResult
      (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
        (v "id") (v "arguments"))
      (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
        (v "id") (v "arguments"))),
  mkRule "tptp-fof-cnf-gen:negate-defined-negative"
    [("id", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms")] []
    (negateRequest
      (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
        (v "id") (v "arguments")))
    (negateResult
      (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
        (v "id") (v "arguments"))
      (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
        (v "id") (v "arguments")))
]

def unitClause (reference : Pattern) : Pattern :=
  TptpFofDefinitionalCnfLanguageDef.clauseCons reference
    TptpFofDefinitionalCnfLanguageDef.clauseNil

def binaryClause (first second : Pattern) : Pattern :=
  TptpFofDefinitionalCnfLanguageDef.clauseCons first
    (TptpFofDefinitionalCnfLanguageDef.clauseCons second
      TptpFofDefinitionalCnfLanguageDef.clauseNil)

def ternaryClause (first second third : Pattern) : Pattern :=
  TptpFofDefinitionalCnfLanguageDef.clauseCons first
    (TptpFofDefinitionalCnfLanguageDef.clauseCons second
      (TptpFofDefinitionalCnfLanguageDef.clauseCons third
        TptpFofDefinitionalCnfLanguageDef.clauseNil))

def prependThree (first second third tail : Pattern) : Pattern :=
  TptpFofDefinitionalCnfLanguageDef.clausesCons first
    (TptpFofDefinitionalCnfLanguageDef.clausesCons second
      (TptpFofDefinitionalCnfLanguageDef.clausesCons third tail))

def definitionRule (name : String) (isAnd : Bool) : RewriteRule :=
  let source := if isAnd then
      TptpFofDefinitionalCnfLanguageDef.definitionAnd
        (v "id") (v "source") (v "left") (v "right")
    else TptpFofDefinitionalCnfLanguageDef.definitionOr
        (v "id") (v "source") (v "left") (v "right")
  let head := TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
    (v "id") (v "arguments")
  let negativeHead := TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
    (v "id") (v "arguments")
  let first := if isAnd then binaryClause negativeHead (v "left")
    else ternaryClause negativeHead (v "left") (v "right")
  let second := if isAnd then binaryClause negativeHead (v "right")
    else binaryClause head (v "leftNegative")
  let third := if isAnd then
      ternaryClause head (v "leftNegative") (v "rightNegative")
    else binaryClause head (v "rightNegative")
  mkRule name
    [("root", "TptpFofNamed:Reference"),
     ("id", "TptpResolvedFof:Index"),
     ("source", "TptpFofSkolem:Formula"),
     ("left", "TptpFofNamed:Reference"),
     ("right", "TptpFofNamed:Reference"),
     ("tail", "TptpFofNamed:Definitions"),
     ("arity", "TptpResolvedFof:Index"),
     ("introducedTail", "TptpFofNamed:IntroducedList"),
     ("arguments", "TptpFofSkolem:Terms"),
     ("leftNegative", "TptpFofNamed:Reference"),
     ("rightNegative", "TptpFofNamed:Reference"),
     ("rest", "TptpFofCnf:Clauses")]
    [congruence
      (variablesRequest (v "arity") indexZero)
      (variablesResult (v "arity") indexZero (v "arguments")),
     congruence (negateRequest (v "left"))
      (negateResult (v "left") (v "leftNegative")),
     congruence (negateRequest (v "right"))
      (negateResult (v "right") (v "rightNegative")),
     congruence
      (clausesRequest (v "root") (v "tail") (v "introducedTail"))
      (clausesResult (v "root") (v "tail") (v "introducedTail")
        (v "rest"))]
    (clausesRequest (v "root")
      (TptpFofDefinitionalCnfLanguageDef.definitionsCons source (v "tail"))
      (TptpFofDefinitionalCnfLanguageDef.introducedCons
        (TptpFofDefinitionalCnfLanguageDef.introducedPredicate
          (v "id") (v "arity"))
        (v "introducedTail")))
    (clausesResult (v "root")
      (TptpFofDefinitionalCnfLanguageDef.definitionsCons source (v "tail"))
      (TptpFofDefinitionalCnfLanguageDef.introducedCons
        (TptpFofDefinitionalCnfLanguageDef.introducedPredicate
          (v "id") (v "arity"))
        (v "introducedTail"))
      (prependThree first second third (v "rest")))

@[simp] theorem definitionRule_left (name : String) (isAnd : Bool) :
    (definitionRule name isAnd).left =
      clausesRequest (v "root")
        (TptpFofDefinitionalCnfLanguageDef.definitionsCons
          (if isAnd then
            TptpFofDefinitionalCnfLanguageDef.definitionAnd
              (v "id") (v "source") (v "left") (v "right")
          else
            TptpFofDefinitionalCnfLanguageDef.definitionOr
              (v "id") (v "source") (v "left") (v "right"))
          (v "tail"))
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (TptpFofDefinitionalCnfLanguageDef.introducedPredicate
            (v "id") (v "arity"))
          (v "introducedTail")) := by
  rfl

def clausesRewrites : List RewriteRule := [
  mkRule "tptp-fof-cnf-gen:clauses-nil"
    [("root", "TptpFofNamed:Reference")] []
    (clausesRequest (v "root")
      TptpFofDefinitionalCnfLanguageDef.definitionsNil
      TptpFofDefinitionalCnfLanguageDef.introducedNil)
    (clausesResult (v "root")
      TptpFofDefinitionalCnfLanguageDef.definitionsNil
      TptpFofDefinitionalCnfLanguageDef.introducedNil
      (TptpFofDefinitionalCnfLanguageDef.clausesCons
        (unitClause (v "root"))
        TptpFofDefinitionalCnfLanguageDef.clausesNil)),
  definitionRule "tptp-fof-cnf-gen:clauses-and" true,
  definitionRule "tptp-fof-cnf-gen:clauses-or" false
]

def generateRewrites : List RewriteRule := [
  mkRule "tptp-fof-cnf-gen:generate"
    [("root", "TptpFofNamed:Reference"),
     ("next", "TptpResolvedFof:Index"),
     ("definitions", "TptpFofNamed:Definitions"),
     ("introduced", "TptpFofNamed:IntroducedList"),
     ("clauses", "TptpFofCnf:Clauses")]
    [congruence
      (clausesRequest (v "root") (v "definitions") (v "introduced"))
      (clausesResult (v "root") (v "definitions") (v "introduced")
        (v "clauses"))]
    (generateRequest
      (TptpFofDefinitionalCnfLanguageDef.namedOutput
        (v "root") (v "next") (v "definitions") (v "introduced")))
    (generateResult
      (TptpFofDefinitionalCnfLanguageDef.namedOutput
        (v "root") (v "next") (v "definitions") (v "introduced"))
      (TptpFofDefinitionalCnfLanguageDef.cnfOutput
        (TptpFofDefinitionalCnfLanguageDef.namedOutput
          (v "root") (v "next") (v "definitions") (v "introduced"))
        (v "clauses")))
]

def rewrites : List RewriteRule :=
  variablesRewrites ++ negateRewrites ++ clausesRewrites ++ generateRewrites

theorem rewrite_count : rewrites.length = 14 := by decide

def language : LanguageDef := {
  name := "TptpFofDefinitionalCnfGeneration"
  types := TptpFofDefinitionalCnfLanguageDef.language.types ++ [
    ("TptpFofCnfGeneration:VariablesResult" : TypeDecl),
    ("TptpFofCnfGeneration:NegateResult" : TypeDecl),
    ("TptpFofCnfGeneration:ClausesResult" : TypeDecl),
    ("TptpFofCnfGeneration:GenerateResult" : TypeDecl)]
  terms := TptpFofDefinitionalCnfLanguageDef.language.terms ++ operationTerms
  equations := []
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

private def constructorLabelNamespaced (label : String) : Bool :=
  label.startsWith "tptp-fof-"

private theorem constructorLabels_namespaced :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelNamespaced = true := by
  decide +kernel

private theorem plainName_not_constructor (name : String)
    (plain : constructorLabelNamespaced name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have namespaced := (List.all_eq_true.mp constructorLabels_namespaced)
    name membership
  simp [plain] at namespaced

private def requiredTypes : List String := [
  "String", "TptpResolvedFof:Index", "TptpFofSkolem:Term",
  "TptpFofSkolem:Terms", "TptpFofSkolem:Formula",
  "TptpFofNamed:Reference", "TptpFofNamed:Definition",
  "TptpFofNamed:Definitions", "TptpFofNamed:IntroducedPredicate",
  "TptpFofNamed:IntroducedList", "TptpFofNamed:Output",
  "TptpFofCnf:Clause", "TptpFofCnf:Clauses", "TptpFofCnf:Output"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) = true := by
  decide +kernel

@[simp] private theorem requiredType_declared (name : String)
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredTypes_declared name membership)

private def requiredSignatures : List (String × Nat) := [
  ("tptp-fof-resolved:index-zero", 0),
  ("tptp-fof-resolved:index-succ", 1),
  ("tptp-fof-skolem:term-variable", 1),
  ("tptp-fof-skolem:terms-nil", 0),
  ("tptp-fof-skolem:terms-cons", 2),
  ("tptp-fof-named:ref-verum", 0),
  ("tptp-fof-named:ref-falsum", 0),
  ("tptp-fof-named:ref-original-positive", 2),
  ("tptp-fof-named:ref-original-negative", 2),
  ("tptp-fof-named:ref-equal", 2),
  ("tptp-fof-named:ref-not-equal", 2),
  ("tptp-fof-named:ref-defined-positive", 2),
  ("tptp-fof-named:ref-defined-negative", 2),
  ("tptp-fof-named:definition-and", 4),
  ("tptp-fof-named:definition-or", 4),
  ("tptp-fof-named:definitions-nil", 0),
  ("tptp-fof-named:definitions-cons", 2),
  ("tptp-fof-named:introduced-predicate", 2),
  ("tptp-fof-named:introduced-nil", 0),
  ("tptp-fof-named:introduced-cons", 2),
  ("tptp-fof-named:output", 4),
  ("tptp-fof-cnf:clause-nil", 0),
  ("tptp-fof-cnf:clause-cons", 2),
  ("tptp-fof-cnf:clauses-nil", 0),
  ("tptp-fof-cnf:clauses-cons", 2),
  ("tptp-fof-cnf:output", 2),
  ("tptp-fof-cnf-gen:variables-request", 2),
  ("tptp-fof-cnf-gen:variables-result", 3),
  ("tptp-fof-cnf-gen:negate-request", 1),
  ("tptp-fof-cnf-gen:negate-result", 2),
  ("tptp-fof-cnf-gen:clauses-request", 3),
  ("tptp-fof-cnf-gen:clauses-result", 4),
  ("tptp-fof-cnf-gen:generate-request", 1),
  ("tptp-fof-cnf-gen:generate-result", 2)]

private theorem requiredSignatures_declared :
    requiredSignatures.all (fun signature => decide
      (signature ∈ RewriteValidationCertificate.constructorSignatures
        language)) = true := by
  decide +kernel

@[simp] private theorem requiredSignature_declared
    (signature : String × Nat) (membership : signature ∈ requiredSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures language :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredSignatures_declared signature membership)

local macro "certify_generation_row" : tactic =>
  `(tactic|
    (simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      requiredTypes, requiredSignatures, requiredType_declared,
      requiredSignature_declared, typed, mkRule, congruence, negateRule,
      definitionRule, variablesRequest, variablesResult, negateRequest,
      negateResult, clausesRequest, clausesResult, generateRequest,
      generateResult, indexZero, indexSucc, unitClause, binaryClause,
      ternaryClause, prependThree, a, v,
      TptpFofDefinitionalCnfLanguageDef.typeNames_exact,
      TptpFofDefinitionalCnfLanguageDef.constructorSignatures_exact,
      TptpFofDefinitionalCnfLanguageDef.constructorLabels_exact,
      TptpFofSkolemLanguageDef.typeNames_exact,
      TptpFofSkolemLanguageDef.constructorSignatures_exact,
      TptpFofSkolemLanguageDef.constructorLabels_exact,
      TptpFofDefinitionalCnfLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.refVerum,
      TptpFofDefinitionalCnfLanguageDef.refFalsum,
      TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
      TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
      TptpFofDefinitionalCnfLanguageDef.refEqual,
      TptpFofDefinitionalCnfLanguageDef.refNotEqual,
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
      TptpFofDefinitionalCnfLanguageDef.refDefinedNegative,
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofDefinitionalCnfLanguageDef.clauseNil,
      TptpFofDefinitionalCnfLanguageDef.clauseCons,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.a,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
      plainName_not_constructor, constructorLabelNamespaced] <;>
      decide +kernel))

local macro "certify_variables_row" : tactic =>
  `(tactic| (simp only [variablesRewrites]; certify_generation_row))
local macro "certify_negate_row" : tactic =>
  `(tactic| (simp only [negateRewrites]; certify_generation_row))
local macro "certify_clauses_row" : tactic =>
  `(tactic| (simp only [clausesRewrites]; certify_generation_row))
local macro "certify_generate_row" : tactic =>
  `(tactic| (simp only [generateRewrites]; certify_generation_row))

private theorem check_of_component_checks (rewrite : RewriteRule)
    (contextTypes :
      RewriteValidationCertificate.contextTypesCheck language rewrite = true)
    (leftDeclared :
      RewriteValidationCertificate.patternDeclaredCheck language
        rewrite.left = true)
    (rightDeclared :
      RewriteValidationCertificate.patternDeclaredCheck language
        rewrite.right = true)
    (premisesDeclared :
      RewriteValidationCertificate.premisesDeclaredCheck language rewrite =
        true)
    (allPatternsScoped :
      RewriteValidationCertificate.allPatternsScopedCheck rewrite = true)
    (fvarsAvoidConstructors :
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck language
        rewrite = true)
    (bindersAvoidConstructors :
      RewriteValidationCertificate.bindersAvoidConstructorsCheck language
        rewrite = true)
    (contextAvoidsConstructors :
      RewriteValidationCertificate.contextAvoidsConstructorsCheck language
        rewrite = true)
    (rightBound :
      RewriteValidationCertificate.rightBoundCheck rewrite = true) :
    RewriteValidationCertificate.check language rewrite = true := by
  simp [RewriteValidationCertificate.check, contextTypes, leftDeclared,
    rightDeclared, premisesDeclared, allPatternsScoped,
    fvarsAvoidConstructors, bindersAvoidConstructors,
    contextAvoidsConstructors, rightBound]

private def andRule : RewriteRule :=
  definitionRule "tptp-fof-cnf-gen:clauses-and" true

private theorem and_contextTypes :
    RewriteValidationCertificate.contextTypesCheck language andRule = true := by
  simp only [andRule]
  certify_generation_row
private theorem and_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language andRule.left =
      true := by
  simp only [andRule]
  certify_generation_row
private theorem and_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language andRule.right =
      true := by
  simp only [andRule]
  certify_generation_row
private theorem and_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language andRule =
      true := by
  simp only [andRule]
  certify_generation_row
private theorem and_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck andRule = true := by
  simp only [andRule]
  certify_generation_row
private theorem and_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language andRule =
      true := by
  simp only [andRule]
  certify_generation_row
private theorem and_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      andRule = true := by
  simp only [andRule]
  certify_generation_row
private theorem and_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      andRule = true := by
  simp only [andRule]
  certify_generation_row
private theorem and_rightBound :
    RewriteValidationCertificate.rightBoundCheck andRule = true := by
  simp only [andRule]
  certify_generation_row

private def orRule : RewriteRule :=
  definitionRule "tptp-fof-cnf-gen:clauses-or" false

private theorem or_contextTypes :
    RewriteValidationCertificate.contextTypesCheck language orRule = true := by
  simp only [orRule]
  certify_generation_row
private theorem or_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language orRule.left =
      true := by
  simp only [orRule]
  certify_generation_row
private theorem or_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language orRule.right =
      true := by
  simp only [orRule]
  certify_generation_row
private theorem or_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language orRule =
      true := by
  simp only [orRule]
  certify_generation_row
private theorem or_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck orRule = true := by
  simp only [orRule]
  certify_generation_row
private theorem or_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language orRule =
      true := by
  simp only [orRule]
  certify_generation_row
private theorem or_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      orRule = true := by
  simp only [orRule]
  certify_generation_row
private theorem or_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      orRule = true := by
  simp only [orRule]
  certify_generation_row
private theorem or_rightBound :
    RewriteValidationCertificate.rightBoundCheck orRule = true := by
  simp only [orRule]
  certify_generation_row

private theorem rewrite00_checked :
    RewriteValidationCertificate.check language variablesRewrites[0] = true := by
  certify_variables_row
private theorem rewrite01_checked :
    RewriteValidationCertificate.check language variablesRewrites[1] = true := by
  certify_variables_row
private theorem rewrite02_checked :
    RewriteValidationCertificate.check language negateRewrites[0] = true := by
  certify_negate_row
private theorem rewrite03_checked :
    RewriteValidationCertificate.check language negateRewrites[1] = true := by
  certify_negate_row
private theorem rewrite04_checked :
    RewriteValidationCertificate.check language negateRewrites[2] = true := by
  certify_negate_row
private theorem rewrite05_checked :
    RewriteValidationCertificate.check language negateRewrites[3] = true := by
  certify_negate_row
private theorem rewrite06_checked :
    RewriteValidationCertificate.check language negateRewrites[4] = true := by
  certify_negate_row
private theorem rewrite07_checked :
    RewriteValidationCertificate.check language negateRewrites[5] = true := by
  certify_negate_row
private theorem rewrite08_checked :
    RewriteValidationCertificate.check language negateRewrites[6] = true := by
  certify_negate_row
private theorem rewrite09_checked :
    RewriteValidationCertificate.check language negateRewrites[7] = true := by
  certify_negate_row
private theorem rewrite10_checked :
    RewriteValidationCertificate.check language clausesRewrites[0] = true := by
  certify_clauses_row
private theorem rewrite11_checked :
    RewriteValidationCertificate.check language clausesRewrites[1] = true := by
  simpa [clausesRewrites, andRule] using
    check_of_component_checks andRule and_contextTypes and_leftDeclared
      and_rightDeclared and_premisesDeclared and_allPatternsScoped
      and_fvarsAvoidConstructors and_bindersAvoidConstructors
      and_contextAvoidsConstructors and_rightBound
private theorem rewrite12_checked :
    RewriteValidationCertificate.check language clausesRewrites[2] = true := by
  simpa [clausesRewrites, orRule] using
    check_of_component_checks orRule or_contextTypes or_leftDeclared
      or_rightDeclared or_premisesDeclared or_allPatternsScoped
      or_fvarsAvoidConstructors or_bindersAvoidConstructors
      or_contextAvoidsConstructors or_rightBound
private theorem rewrite13_checked :
    RewriteValidationCertificate.check language generateRewrites[0] = true := by
  certify_generate_row

private theorem constructorLabels_nodup :
    (language.terms.map (fun term => term.label)).Nodup := by
  decide +kernel

private theorem every_rewrite_checked (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.check language rewrite = true := by
  simp only [rewrites, variablesRewrites, negateRewrites, clausesRewrites,
    generateRewrites, List.append_assoc, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with variableRows | negations | clauses | generation
  · rcases variableRows with (rfl | rfl)
    · simpa [variablesRewrites] using rewrite00_checked
    · simpa [variablesRewrites] using rewrite01_checked
  · rcases negations with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · simpa [negateRewrites] using rewrite02_checked
    · simpa [negateRewrites] using rewrite03_checked
    · simpa [negateRewrites] using rewrite04_checked
    · simpa [negateRewrites] using rewrite05_checked
    · simpa [negateRewrites] using rewrite06_checked
    · simpa [negateRewrites] using rewrite07_checked
    · simpa [negateRewrites] using rewrite08_checked
    · simpa [negateRewrites] using rewrite09_checked
  · rcases clauses with (rfl | rfl | rfl)
    · simpa [clausesRewrites] using rewrite10_checked
    · simpa [clausesRewrites] using rewrite11_checked
    · simpa [clausesRewrites] using rewrite12_checked
  · rcases generation with rfl
    simpa [generateRewrites] using rewrite13_checked

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
    constructorLabels_nodup
  exact every_rewrite_checked rewrite membership

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def sourceInclusion :
    StructuralMorphism TptpFofDefinitionalCnfLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈
      TptpFofDefinitionalCnfLanguageDef.language.equations at membership
    simp [TptpFofDefinitionalCnfLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈
      TptpFofDefinitionalCnfLanguageDef.language.rewrites at membership
    simp [TptpFofDefinitionalCnfLanguageDef.no_rewrites] at membership

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact language_supported

def wire : String := (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit := IO.FS.writeFile path wire

#print axioms language_validate
#print axioms sourceInclusion
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationLanguageDef
