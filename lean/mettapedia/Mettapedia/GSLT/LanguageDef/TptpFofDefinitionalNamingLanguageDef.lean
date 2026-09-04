import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Authored linear definitional naming transformation

This LanguageDef removes only a leading universal prefix and names the
remaining quantifier-free Skolem matrix.  The traversal accumulates definition
and fresh-predicate rows in reverse postorder, then reverses each ledger once.
Thus every source node is visited once and no subtree list is repeatedly
appended.

There is deliberately no rule for an existential or for a universal below a
Boolean connective.  Such inputs remain unreduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingLanguageDef

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
  a "tptp-fof-name:variables-request" [remaining, next]
def variablesResult (remaining next arguments : Pattern) : Pattern :=
  a "tptp-fof-name:variables-result" [remaining, next, arguments]

def nameRequest (depth frontier source definitions introduced : Pattern) :
    Pattern :=
  a "tptp-fof-name:name-request"
    [depth, frontier, source, definitions, introduced]
def nameResult (depth frontier source root next definitions introduced :
    Pattern) : Pattern :=
  a "tptp-fof-name:name-result"
    [depth, frontier, source, root, next, definitions, introduced]

def reverseDefinitionsRequest (source accumulator : Pattern) : Pattern :=
  a "tptp-fof-name:reverse-definitions-request" [source, accumulator]
def reverseDefinitionsResult (source accumulator target : Pattern) : Pattern :=
  a "tptp-fof-name:reverse-definitions-result"
    [source, accumulator, target]
def reverseIntroducedRequest (source accumulator : Pattern) : Pattern :=
  a "tptp-fof-name:reverse-introduced-request" [source, accumulator]
def reverseIntroducedResult (source accumulator target : Pattern) : Pattern :=
  a "tptp-fof-name:reverse-introduced-result"
    [source, accumulator, target]

def openRequest (depth frontier source : Pattern) : Pattern :=
  a "tptp-fof-name:open-request" [depth, frontier, source]
def openResult (depth frontier source target : Pattern) : Pattern :=
  a "tptp-fof-name:open-result" [depth, frontier, source, target]

def operationTerms : List GrammarRule := [
  ctor "tptp-fof-name:variables-request" "TptpFofName:VariablesResult"
    [("remaining", "TptpResolvedFof:Index"),
     ("next", "TptpResolvedFof:Index")],
  ctor "tptp-fof-name:variables-result" "TptpFofName:VariablesResult"
    [("remaining", "TptpResolvedFof:Index"),
     ("next", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-name:name-request" "TptpFofName:NameResult"
    [("depth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("source", "TptpFofSkolem:Formula"),
     ("definitions", "TptpFofNamed:Definitions"),
     ("introduced", "TptpFofNamed:IntroducedList")],
  ctor "tptp-fof-name:name-result" "TptpFofName:NameResult"
    [("depth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("source", "TptpFofSkolem:Formula"),
     ("root", "TptpFofNamed:Reference"),
     ("next", "TptpResolvedFof:Index"),
     ("definitions", "TptpFofNamed:Definitions"),
     ("introduced", "TptpFofNamed:IntroducedList")],
  ctor "tptp-fof-name:reverse-definitions-request"
    "TptpFofName:ReverseDefinitionsResult"
    [("source", "TptpFofNamed:Definitions"),
     ("accumulator", "TptpFofNamed:Definitions")],
  ctor "tptp-fof-name:reverse-definitions-result"
    "TptpFofName:ReverseDefinitionsResult"
    [("source", "TptpFofNamed:Definitions"),
     ("accumulator", "TptpFofNamed:Definitions"),
     ("target", "TptpFofNamed:Definitions")],
  ctor "tptp-fof-name:reverse-introduced-request"
    "TptpFofName:ReverseIntroducedResult"
    [("source", "TptpFofNamed:IntroducedList"),
     ("accumulator", "TptpFofNamed:IntroducedList")],
  ctor "tptp-fof-name:reverse-introduced-result"
    "TptpFofName:ReverseIntroducedResult"
    [("source", "TptpFofNamed:IntroducedList"),
     ("accumulator", "TptpFofNamed:IntroducedList"),
     ("target", "TptpFofNamed:IntroducedList")],
  ctor "tptp-fof-name:open-request" "TptpFofName:OpenResult"
    [("depth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("source", "TptpFofSkolem:Formula")],
  ctor "tptp-fof-name:open-result" "TptpFofName:OpenResult"
    [("depth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("source", "TptpFofSkolem:Formula"),
     ("target", "TptpFofNamed:Output")]
]

def variablesRewrites : List RewriteRule := [
  mkRule "tptp-fof-name:variables-zero"
    [("next", "TptpResolvedFof:Index")] []
    (variablesRequest indexZero (v "next"))
    (variablesResult indexZero (v "next")
      TptpFofSkolemLanguageDef.termsNil),
  mkRule "tptp-fof-name:variables-succ"
    [("remaining", "TptpResolvedFof:Index"),
     ("next", "TptpResolvedFof:Index"),
     ("tail", "TptpFofSkolem:Terms")]
    [congruence
      (variablesRequest (v "remaining")
        (indexSucc (v "next")))
      (variablesResult (v "remaining")
        (indexSucc (v "next")) (v "tail"))]
    (variablesRequest
      (indexSucc (v "remaining")) (v "next"))
    (variablesResult
      (indexSucc (v "remaining")) (v "next")
      (TptpFofSkolemLanguageDef.termsCons
        (TptpFofSkolemLanguageDef.termVariable (v "next")) (v "tail")))
]

def leafNameRule (ruleName : String)
    (extraContext : List (String × String))
    (source root : Pattern) : RewriteRule :=
  mkRule ruleName
    ([ ("depth", "TptpResolvedFof:Index"),
       ("frontier", "TptpResolvedFof:Index"),
       ("definitions", "TptpFofNamed:Definitions"),
       ("introduced", "TptpFofNamed:IntroducedList") ] ++ extraContext) []
    (nameRequest (v "depth") (v "frontier") source
      (v "definitions") (v "introduced"))
    (nameResult (v "depth") (v "frontier") source root (v "frontier")
      (v "definitions") (v "introduced"))

def leafNameRewrites : List RewriteRule := [
  leafNameRule "tptp-fof-name:verum" []
    TptpFofSkolemLanguageDef.verum
    TptpFofDefinitionalCnfLanguageDef.refVerum,
  leafNameRule "tptp-fof-name:falsum" []
    TptpFofSkolemLanguageDef.falsum
    TptpFofDefinitionalCnfLanguageDef.refFalsum,
  leafNameRule "tptp-fof-name:positive"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")]
    (TptpFofSkolemLanguageDef.positive (v "relation") (v "arguments"))
    (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
      (v "relation") (v "arguments")),
  leafNameRule "tptp-fof-name:negative"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")]
    (TptpFofSkolemLanguageDef.negative (v "relation") (v "arguments"))
    (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
      (v "relation") (v "arguments")),
  leafNameRule "tptp-fof-name:equal"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")]
    (TptpFofSkolemLanguageDef.equal (v "left") (v "right"))
    (TptpFofDefinitionalCnfLanguageDef.refEqual (v "left") (v "right")),
  leafNameRule "tptp-fof-name:not-equal"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")]
    (TptpFofSkolemLanguageDef.notEqual (v "left") (v "right"))
    (TptpFofDefinitionalCnfLanguageDef.refNotEqual (v "left") (v "right"))
]

def connectiveNameRule (ruleName : String) (isAnd : Bool) : RewriteRule :=
  let source := if isAnd then
      TptpFofSkolemLanguageDef.and (v "left") (v "right")
    else TptpFofSkolemLanguageDef.or (v "left") (v "right")
  let definition := if isAnd then
      TptpFofDefinitionalCnfLanguageDef.definitionAnd (v "rightNext")
        source (v "leftRoot") (v "rightRoot")
    else TptpFofDefinitionalCnfLanguageDef.definitionOr (v "rightNext")
        source (v "leftRoot") (v "rightRoot")
  mkRule ruleName
    [("depth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("left", "TptpFofSkolem:Formula"),
     ("right", "TptpFofSkolem:Formula"),
     ("definitions", "TptpFofNamed:Definitions"),
     ("introduced", "TptpFofNamed:IntroducedList"),
     ("leftRoot", "TptpFofNamed:Reference"),
     ("leftNext", "TptpResolvedFof:Index"),
     ("leftDefinitions", "TptpFofNamed:Definitions"),
     ("leftIntroduced", "TptpFofNamed:IntroducedList"),
     ("rightRoot", "TptpFofNamed:Reference"),
     ("rightNext", "TptpResolvedFof:Index"),
     ("rightDefinitions", "TptpFofNamed:Definitions"),
     ("rightIntroduced", "TptpFofNamed:IntroducedList"),
     ("arguments", "TptpFofSkolem:Terms")]
    [congruence
      (nameRequest (v "depth") (v "frontier") (v "left")
        (v "definitions") (v "introduced"))
      (nameResult (v "depth") (v "frontier") (v "left")
        (v "leftRoot") (v "leftNext") (v "leftDefinitions")
        (v "leftIntroduced")),
     congruence
      (nameRequest (v "depth") (v "leftNext") (v "right")
        (v "leftDefinitions") (v "leftIntroduced"))
      (nameResult (v "depth") (v "leftNext") (v "right")
        (v "rightRoot") (v "rightNext") (v "rightDefinitions")
        (v "rightIntroduced")),
     congruence
      (variablesRequest (v "depth") indexZero)
      (variablesResult (v "depth") indexZero
        (v "arguments"))]
    (nameRequest (v "depth") (v "frontier") source
      (v "definitions") (v "introduced"))
    (nameResult (v "depth") (v "frontier") source
      (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
        (v "rightNext") (v "arguments"))
      (indexSucc (v "rightNext"))
      (TptpFofDefinitionalCnfLanguageDef.definitionsCons definition
        (v "rightDefinitions"))
      (TptpFofDefinitionalCnfLanguageDef.introducedCons
        (TptpFofDefinitionalCnfLanguageDef.introducedPredicate
          (v "rightNext") (v "depth"))
        (v "rightIntroduced")))

def connectiveNameRewrites : List RewriteRule := [
  connectiveNameRule "tptp-fof-name:and" true,
  connectiveNameRule "tptp-fof-name:or" false
]

def reverseRewrites : List RewriteRule := [
  mkRule "tptp-fof-name:reverse-definitions-nil"
    [("accumulator", "TptpFofNamed:Definitions")] []
    (reverseDefinitionsRequest
      TptpFofDefinitionalCnfLanguageDef.definitionsNil (v "accumulator"))
    (reverseDefinitionsResult
      TptpFofDefinitionalCnfLanguageDef.definitionsNil (v "accumulator")
      (v "accumulator")),
  mkRule "tptp-fof-name:reverse-definitions-cons"
    [("head", "TptpFofNamed:Definition"),
     ("tail", "TptpFofNamed:Definitions"),
     ("accumulator", "TptpFofNamed:Definitions"),
     ("target", "TptpFofNamed:Definitions")]
    [congruence
      (reverseDefinitionsRequest (v "tail")
        (TptpFofDefinitionalCnfLanguageDef.definitionsCons
          (v "head") (v "accumulator")))
      (reverseDefinitionsResult (v "tail")
        (TptpFofDefinitionalCnfLanguageDef.definitionsCons
          (v "head") (v "accumulator")) (v "target"))]
    (reverseDefinitionsRequest
      (TptpFofDefinitionalCnfLanguageDef.definitionsCons
        (v "head") (v "tail")) (v "accumulator"))
    (reverseDefinitionsResult
      (TptpFofDefinitionalCnfLanguageDef.definitionsCons
        (v "head") (v "tail")) (v "accumulator") (v "target")),
  mkRule "tptp-fof-name:reverse-introduced-nil"
    [("accumulator", "TptpFofNamed:IntroducedList")] []
    (reverseIntroducedRequest
      TptpFofDefinitionalCnfLanguageDef.introducedNil (v "accumulator"))
    (reverseIntroducedResult
      TptpFofDefinitionalCnfLanguageDef.introducedNil (v "accumulator")
      (v "accumulator")),
  mkRule "tptp-fof-name:reverse-introduced-cons"
    [("head", "TptpFofNamed:IntroducedPredicate"),
     ("tail", "TptpFofNamed:IntroducedList"),
     ("accumulator", "TptpFofNamed:IntroducedList"),
     ("target", "TptpFofNamed:IntroducedList")]
    [congruence
      (reverseIntroducedRequest (v "tail")
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (v "head") (v "accumulator")))
      (reverseIntroducedResult (v "tail")
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (v "head") (v "accumulator")) (v "target"))]
    (reverseIntroducedRequest
      (TptpFofDefinitionalCnfLanguageDef.introducedCons
        (v "head") (v "tail")) (v "accumulator"))
    (reverseIntroducedResult
      (TptpFofDefinitionalCnfLanguageDef.introducedCons
        (v "head") (v "tail")) (v "accumulator") (v "target"))
]

def openMatrixRule (ruleName : String)
    (extraContext : List (String × String)) (source : Pattern) : RewriteRule :=
  mkRule ruleName
    ([ ("depth", "TptpResolvedFof:Index"),
       ("frontier", "TptpResolvedFof:Index") ] ++ extraContext ++ [
       ("root", "TptpFofNamed:Reference"),
       ("next", "TptpResolvedFof:Index"),
       ("reverseDefinitions", "TptpFofNamed:Definitions"),
       ("reverseIntroduced", "TptpFofNamed:IntroducedList"),
       ("definitions", "TptpFofNamed:Definitions"),
       ("introduced", "TptpFofNamed:IntroducedList") ])
    [congruence
      (nameRequest (v "depth") (v "frontier") source
        TptpFofDefinitionalCnfLanguageDef.definitionsNil
        TptpFofDefinitionalCnfLanguageDef.introducedNil)
      (nameResult (v "depth") (v "frontier") source (v "root")
        (v "next") (v "reverseDefinitions") (v "reverseIntroduced")),
     congruence
      (reverseDefinitionsRequest (v "reverseDefinitions")
        TptpFofDefinitionalCnfLanguageDef.definitionsNil)
      (reverseDefinitionsResult (v "reverseDefinitions")
        TptpFofDefinitionalCnfLanguageDef.definitionsNil (v "definitions")),
     congruence
      (reverseIntroducedRequest (v "reverseIntroduced")
        TptpFofDefinitionalCnfLanguageDef.introducedNil)
      (reverseIntroducedResult (v "reverseIntroduced")
        TptpFofDefinitionalCnfLanguageDef.introducedNil (v "introduced"))]
    (openRequest (v "depth") (v "frontier") source)
    (openResult (v "depth") (v "frontier") source
      (TptpFofDefinitionalCnfLanguageDef.namedOutput
        (v "root") (v "next") (v "definitions") (v "introduced")))

def openRewrites : List RewriteRule := [
  mkRule "tptp-fof-name:open-all"
    [("depth", "TptpResolvedFof:Index"),
     ("frontier", "TptpResolvedFof:Index"),
     ("body", "TptpFofSkolem:Formula"),
     ("target", "TptpFofNamed:Output")]
    [congruence
      (openRequest (indexSucc (v "depth"))
        (v "frontier") (v "body"))
      (openResult (indexSucc (v "depth"))
        (v "frontier") (v "body") (v "target"))]
    (openRequest (v "depth") (v "frontier")
      (TptpFofSkolemLanguageDef.all (v "body")))
    (openResult (v "depth") (v "frontier")
      (TptpFofSkolemLanguageDef.all (v "body")) (v "target")),
  openMatrixRule "tptp-fof-name:open-verum" []
    TptpFofSkolemLanguageDef.verum,
  openMatrixRule "tptp-fof-name:open-falsum" []
    TptpFofSkolemLanguageDef.falsum,
  openMatrixRule "tptp-fof-name:open-positive"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")]
    (TptpFofSkolemLanguageDef.positive (v "relation") (v "arguments")),
  openMatrixRule "tptp-fof-name:open-negative"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")]
    (TptpFofSkolemLanguageDef.negative (v "relation") (v "arguments")),
  openMatrixRule "tptp-fof-name:open-equal"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")]
    (TptpFofSkolemLanguageDef.equal (v "left") (v "right")),
  openMatrixRule "tptp-fof-name:open-not-equal"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")]
    (TptpFofSkolemLanguageDef.notEqual (v "left") (v "right")),
  openMatrixRule "tptp-fof-name:open-and"
    [("left", "TptpFofSkolem:Formula"),
     ("right", "TptpFofSkolem:Formula")]
    (TptpFofSkolemLanguageDef.and (v "left") (v "right")),
  openMatrixRule "tptp-fof-name:open-or"
    [("left", "TptpFofSkolem:Formula"),
     ("right", "TptpFofSkolem:Formula")]
    (TptpFofSkolemLanguageDef.or (v "left") (v "right"))
]

def rewrites : List RewriteRule :=
  variablesRewrites ++ leafNameRewrites ++ connectiveNameRewrites ++
    reverseRewrites ++ openRewrites

theorem rewrite_count : rewrites.length = 23 := by decide

def language : LanguageDef := {
  name := "TptpFofDefinitionalNaming"
  types := TptpFofDefinitionalCnfLanguageDef.language.types ++ [
    ("TptpFofName:VariablesResult" : TypeDecl),
    ("TptpFofName:NameResult" : TypeDecl),
    ("TptpFofName:ReverseDefinitionsResult" : TypeDecl),
    ("TptpFofName:ReverseIntroducedResult" : TypeDecl),
    ("TptpFofName:OpenResult" : TypeDecl)]
  terms := TptpFofDefinitionalCnfLanguageDef.language.terms ++ operationTerms
  equations := []
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

private theorem language_typeNames :
    language.typeNames =
      TptpFofDefinitionalCnfLanguageDef.language.typeNames ++ [
        "TptpFofName:VariablesResult", "TptpFofName:NameResult",
        "TptpFofName:ReverseDefinitionsResult",
        "TptpFofName:ReverseIntroducedResult", "TptpFofName:OpenResult"] := by
  rfl

private theorem language_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofDefinitionalCnfLanguageDef.language ++ [
        ("tptp-fof-name:variables-request", 2),
        ("tptp-fof-name:variables-result", 3),
        ("tptp-fof-name:name-request", 5),
        ("tptp-fof-name:name-result", 7),
        ("tptp-fof-name:reverse-definitions-request", 2),
        ("tptp-fof-name:reverse-definitions-result", 3),
        ("tptp-fof-name:reverse-introduced-request", 2),
        ("tptp-fof-name:reverse-introduced-result", 3),
        ("tptp-fof-name:open-request", 3),
        ("tptp-fof-name:open-result", 4)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    operationTerms, ctor]

private theorem language_constructorLabels :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofDefinitionalCnfLanguageDef.language ++ [
        "tptp-fof-name:variables-request",
        "tptp-fof-name:variables-result",
        "tptp-fof-name:name-request", "tptp-fof-name:name-result",
        "tptp-fof-name:reverse-definitions-request",
        "tptp-fof-name:reverse-definitions-result",
        "tptp-fof-name:reverse-introduced-request",
        "tptp-fof-name:reverse-introduced-result",
        "tptp-fof-name:open-request", "tptp-fof-name:open-result"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    operationTerms, ctor]

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
  "TptpFofNamed:IntroducedList", "TptpFofNamed:Output"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) =
      true := by
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
  ("tptp-fof-skolem:verum", 0),
  ("tptp-fof-skolem:falsum", 0),
  ("tptp-fof-skolem:positive", 2),
  ("tptp-fof-skolem:negative", 2),
  ("tptp-fof-skolem:equal", 2),
  ("tptp-fof-skolem:not-equal", 2),
  ("tptp-fof-skolem:and", 2),
  ("tptp-fof-skolem:or", 2),
  ("tptp-fof-skolem:all", 1),
  ("tptp-fof-named:ref-verum", 0),
  ("tptp-fof-named:ref-falsum", 0),
  ("tptp-fof-named:ref-original-positive", 2),
  ("tptp-fof-named:ref-original-negative", 2),
  ("tptp-fof-named:ref-equal", 2),
  ("tptp-fof-named:ref-not-equal", 2),
  ("tptp-fof-named:ref-defined-positive", 2),
  ("tptp-fof-named:definition-and", 4),
  ("tptp-fof-named:definition-or", 4),
  ("tptp-fof-named:definitions-nil", 0),
  ("tptp-fof-named:definitions-cons", 2),
  ("tptp-fof-named:introduced-predicate", 2),
  ("tptp-fof-named:introduced-nil", 0),
  ("tptp-fof-named:introduced-cons", 2),
  ("tptp-fof-named:output", 4),
  ("tptp-fof-name:variables-request", 2),
  ("tptp-fof-name:variables-result", 3),
  ("tptp-fof-name:name-request", 5),
  ("tptp-fof-name:name-result", 7),
  ("tptp-fof-name:reverse-definitions-request", 2),
  ("tptp-fof-name:reverse-definitions-result", 3),
  ("tptp-fof-name:reverse-introduced-request", 2),
  ("tptp-fof-name:reverse-introduced-result", 3),
  ("tptp-fof-name:open-request", 3),
  ("tptp-fof-name:open-result", 4)]

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

local macro "certify_naming_row" : tactic =>
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
      requiredSignature_declared, leafNameRule, connectiveNameRule,
      openMatrixRule,
      typed, mkRule, congruence, variablesRequest, variablesResult,
      nameRequest, nameResult, reverseDefinitionsRequest,
      reverseDefinitionsResult, reverseIntroducedRequest,
      reverseIntroducedResult, openRequest, openResult, indexZero,
      indexSucc, a, v,
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
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.verum,
      TptpFofSkolemLanguageDef.falsum,
      TptpFofSkolemLanguageDef.positive,
      TptpFofSkolemLanguageDef.negative,
      TptpFofSkolemLanguageDef.equal,
      TptpFofSkolemLanguageDef.notEqual,
      TptpFofSkolemLanguageDef.and,
      TptpFofSkolemLanguageDef.or,
      TptpFofSkolemLanguageDef.all,
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
  `(tactic| (simp only [variablesRewrites]; certify_naming_row))
local macro "certify_leaf_row" : tactic =>
  `(tactic| (simp only [leafNameRewrites]; certify_naming_row))
local macro "certify_connective_row" : tactic =>
  `(tactic| (simp only [connectiveNameRewrites]; certify_naming_row))
local macro "certify_reverse_row" : tactic =>
  `(tactic| (simp only [reverseRewrites]; certify_naming_row))
local macro "certify_open_row" : tactic =>
  `(tactic| (simp only [openRewrites]; certify_naming_row))

private theorem rewrite00_checked :
    RewriteValidationCertificate.check language variablesRewrites[0] = true := by
  certify_variables_row
private theorem rewrite01_checked :
    RewriteValidationCertificate.check language variablesRewrites[1] = true := by
  certify_variables_row
private theorem rewrite02_checked :
    RewriteValidationCertificate.check language leafNameRewrites[0] = true := by
  certify_leaf_row
private theorem rewrite03_checked :
    RewriteValidationCertificate.check language leafNameRewrites[1] = true := by
  certify_leaf_row
private theorem rewrite04_checked :
    RewriteValidationCertificate.check language leafNameRewrites[2] = true := by
  certify_leaf_row
private theorem rewrite05_checked :
    RewriteValidationCertificate.check language leafNameRewrites[3] = true := by
  certify_leaf_row
private theorem rewrite06_checked :
    RewriteValidationCertificate.check language leafNameRewrites[4] = true := by
  certify_leaf_row
private theorem rewrite07_checked :
    RewriteValidationCertificate.check language leafNameRewrites[5] = true := by
  certify_leaf_row

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
  connectiveNameRule "tptp-fof-name:and" true

private theorem and_contextTypes :
    RewriteValidationCertificate.contextTypesCheck language andRule = true := by
  simp only [andRule]
  certify_naming_row
private theorem and_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language andRule.left =
      true := by
  simp only [andRule]
  certify_naming_row
private theorem and_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language andRule.right =
      true := by
  simp only [andRule]
  certify_naming_row
private theorem and_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language andRule =
      true := by
  simp only [andRule]
  certify_naming_row
private theorem and_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck andRule = true := by
  simp only [andRule]
  certify_naming_row
private theorem and_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language andRule =
      true := by
  simp only [andRule]
  certify_naming_row
private theorem and_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      andRule = true := by
  simp only [andRule]
  certify_naming_row
private theorem and_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      andRule = true := by
  simp only [andRule]
  certify_naming_row
private theorem and_rightBound :
    RewriteValidationCertificate.rightBoundCheck andRule = true := by
  simp only [andRule]
  certify_naming_row

private def orRule : RewriteRule :=
  connectiveNameRule "tptp-fof-name:or" false

private theorem or_contextTypes :
    RewriteValidationCertificate.contextTypesCheck language orRule = true := by
  simp only [orRule]
  certify_naming_row
private theorem or_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language orRule.left =
      true := by
  simp only [orRule]
  certify_naming_row
private theorem or_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language orRule.right =
      true := by
  simp only [orRule]
  certify_naming_row
private theorem or_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language orRule =
      true := by
  simp only [orRule]
  certify_naming_row
private theorem or_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck orRule = true := by
  simp only [orRule]
  certify_naming_row
private theorem or_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language orRule =
      true := by
  simp only [orRule]
  certify_naming_row
private theorem or_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      orRule = true := by
  simp only [orRule]
  certify_naming_row
private theorem or_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      orRule = true := by
  simp only [orRule]
  certify_naming_row
private theorem or_rightBound :
    RewriteValidationCertificate.rightBoundCheck orRule = true := by
  simp only [orRule]
  certify_naming_row

private theorem rewrite08_checked :
    RewriteValidationCertificate.check language connectiveNameRewrites[0] = true := by
  simpa [connectiveNameRewrites, andRule] using
    check_of_component_checks andRule and_contextTypes and_leftDeclared
      and_rightDeclared and_premisesDeclared and_allPatternsScoped
      and_fvarsAvoidConstructors and_bindersAvoidConstructors
      and_contextAvoidsConstructors and_rightBound
private theorem rewrite09_checked :
    RewriteValidationCertificate.check language connectiveNameRewrites[1] = true := by
  simpa [connectiveNameRewrites, orRule] using
    check_of_component_checks orRule or_contextTypes or_leftDeclared
      or_rightDeclared or_premisesDeclared or_allPatternsScoped
      or_fvarsAvoidConstructors or_bindersAvoidConstructors
      or_contextAvoidsConstructors or_rightBound
private theorem rewrite10_checked :
    RewriteValidationCertificate.check language reverseRewrites[0] = true := by
  certify_reverse_row
private theorem rewrite11_checked :
    RewriteValidationCertificate.check language reverseRewrites[1] = true := by
  certify_reverse_row
private theorem rewrite12_checked :
    RewriteValidationCertificate.check language reverseRewrites[2] = true := by
  certify_reverse_row
private theorem rewrite13_checked :
    RewriteValidationCertificate.check language reverseRewrites[3] = true := by
  certify_reverse_row
private theorem rewrite14_checked :
    RewriteValidationCertificate.check language openRewrites[0] = true := by
  certify_open_row
private theorem rewrite15_checked :
    RewriteValidationCertificate.check language openRewrites[1] = true := by
  certify_open_row
private theorem rewrite16_checked :
    RewriteValidationCertificate.check language openRewrites[2] = true := by
  certify_open_row
private theorem rewrite17_checked :
    RewriteValidationCertificate.check language openRewrites[3] = true := by
  certify_open_row
private theorem rewrite18_checked :
    RewriteValidationCertificate.check language openRewrites[4] = true := by
  certify_open_row
private theorem rewrite19_checked :
    RewriteValidationCertificate.check language openRewrites[5] = true := by
  certify_open_row
private theorem rewrite20_checked :
    RewriteValidationCertificate.check language openRewrites[6] = true := by
  certify_open_row
private theorem rewrite21_checked :
    RewriteValidationCertificate.check language openRewrites[7] = true := by
  certify_open_row
private theorem rewrite22_checked :
    RewriteValidationCertificate.check language openRewrites[8] = true := by
  certify_open_row

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  decide +kernel

private theorem every_rewrite_checked (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.check language rewrite = true := by
  simp only [rewrites, variablesRewrites, leafNameRewrites,
    connectiveNameRewrites, reverseRewrites, openRewrites,
    List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at membership
  rcases membership with variableRows | leaves | connectives | reversals | opens
  · rcases variableRows with (rfl | rfl)
    · simpa [variablesRewrites] using rewrite00_checked
    · simpa [variablesRewrites] using rewrite01_checked
  · rcases leaves with (rfl | rfl | rfl | rfl | rfl | rfl)
    · simpa [leafNameRewrites] using rewrite02_checked
    · simpa [leafNameRewrites] using rewrite03_checked
    · simpa [leafNameRewrites] using rewrite04_checked
    · simpa [leafNameRewrites] using rewrite05_checked
    · simpa [leafNameRewrites] using rewrite06_checked
    · simpa [leafNameRewrites] using rewrite07_checked
  · rcases connectives with (rfl | rfl)
    · simpa [connectiveNameRewrites] using rewrite08_checked
    · simpa [connectiveNameRewrites] using rewrite09_checked
  · rcases reversals with (rfl | rfl | rfl | rfl)
    · simpa [reverseRewrites] using rewrite10_checked
    · simpa [reverseRewrites] using rewrite11_checked
    · simpa [reverseRewrites] using rewrite12_checked
    · simpa [reverseRewrites] using rewrite13_checked
  · rcases opens with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · simpa [openRewrites] using rewrite14_checked
    · simpa [openRewrites] using rewrite15_checked
    · simpa [openRewrites] using rewrite16_checked
    · simpa [openRewrites] using rewrite17_checked
    · simpa [openRewrites] using rewrite18_checked
    · simpa [openRewrites] using rewrite19_checked
    · simpa [openRewrites] using rewrite20_checked
    · simpa [openRewrites] using rewrite21_checked
    · simpa [openRewrites] using rewrite22_checked

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

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingLanguageDef
