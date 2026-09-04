import Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpResolvedFofLanguageDef
import Mettapedia.GSLT.LanguageDef.PatternEqualityDecision
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Named FOF to binder-resolved FOF

This authored GSLT transformation replaces source variable spellings with
structural de Bruijn indices. An explicit environment is threaded through
terms and formulas. Binder entry extends that environment; variable lookup
returns the first matching entry, so shadowing resolves to the nearest
binder. A missing entry has no rule and therefore rejects a free variable.

The only non-contextual service is the language-independent total pattern
equality decision. It selects a disjoint decision constructor before authored
lookup rules continue. No TPTP constructor dispatch is hidden in the service.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern :=
  .fvar name

def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def ctor (label category : String)
    (parameters : List (String × String))
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

def environmentNil : Pattern :=
  a "tptp-fof-resolve:environment-nil"

def environmentCons (name tail : Pattern) : Pattern :=
  a "tptp-fof-resolve:environment-cons" [name, tail]

def resolveClosed (formula : Pattern) : Pattern :=
  a "tptp-fof-resolve:closed" [formula]

def resolveFormula (environment formula : Pattern) : Pattern :=
  a "tptp-fof-resolve:formula" [environment, formula]

def resolveTerm (environment term : Pattern) : Pattern :=
  a "tptp-fof-resolve:term" [environment, term]

def resolveTerms (environment terms : Pattern) : Pattern :=
  a "tptp-fof-resolve:terms" [environment, terms]

def lookup (name environment : Pattern) : Pattern :=
  a "tptp-fof-resolve:lookup" [name, environment]

def lookupDecision (decision name tail : Pattern) : Pattern :=
  a "tptp-fof-resolve:lookup-decision" [decision, name, tail]

def sourceName (value : Pattern) : Pattern :=
  a "tptp-fof-named:name" [value]

def sourceVariable (name : Pattern) : Pattern :=
  a "tptp-fof-named:term-variable" [sourceName name]

def sourceFunction (head arguments : Pattern) : Pattern :=
  a "tptp-fof-named:term-function" [head, arguments]

def sourceTermsNil : Pattern :=
  a "tptp-fof-named:terms-nil"

def sourceTermsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-named:terms-cons" [head, tail]

def targetIndexZero : Pattern :=
  a "tptp-fof-resolved:index-zero"

def targetIndexSucc (predecessor : Pattern) : Pattern :=
  a "tptp-fof-resolved:index-succ" [predecessor]

def targetVariable (index : Pattern) : Pattern :=
  a "tptp-fof-resolved:term-variable" [index]

def targetFunction (name arguments : Pattern) : Pattern :=
  a "tptp-fof-resolved:term-function" [name, arguments]

def targetTermsNil : Pattern :=
  a "tptp-fof-resolved:terms-nil"

def targetTermsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-resolved:terms-cons" [head, tail]

def sourceFormula (constructor : String) (arguments : List Pattern := []) :
    Pattern :=
  a ("tptp-fof-named:" ++ constructor) arguments

def targetFormula (constructor : String) (arguments : List Pattern := []) :
    Pattern :=
  a ("tptp-fof-resolved:" ++ constructor) arguments

def lookupRules : List RewriteRule := [
  mkRule "tptp-fof-resolve:lookup-cons"
    [("name", "String"), ("head", "String"),
     ("tail", "TptpResolve:Environment"),
     ("decision", "PatternEqualityDecision:Result"),
     ("index", "TptpResolvedFof:Index")]
    [.relationQuery PatternEqualityDecision.relationName
      [v "name", v "head", v "decision"],
     congruence
       (lookupDecision (v "decision") (v "name") (v "tail"))
       (v "index")]
    (lookup (v "name") (environmentCons (v "head") (v "tail")))
    (v "index"),
  mkRule "tptp-fof-resolve:lookup-equal"
    [("name", "String"), ("tail", "TptpResolve:Environment")] []
    (lookupDecision PatternEqualityDecision.equal (v "name") (v "tail"))
    targetIndexZero,
  mkRule "tptp-fof-resolve:lookup-different"
    [("name", "String"), ("tail", "TptpResolve:Environment"),
     ("index", "TptpResolvedFof:Index")]
    [congruence (lookup (v "name") (v "tail")) (v "index")]
    (lookupDecision PatternEqualityDecision.different (v "name") (v "tail"))
    (targetIndexSucc (v "index"))
]

def termRules : List RewriteRule := [
  mkRule "tptp-fof-resolve:term-variable"
    [("environment", "TptpResolve:Environment"), ("name", "String"),
     ("index", "TptpResolvedFof:Index")]
    [congruence (lookup (v "name") (v "environment")) (v "index")]
    (resolveTerm (v "environment") (sourceVariable (v "name")))
    (targetVariable (v "index")),
  mkRule "tptp-fof-resolve:term-function"
    [("environment", "TptpResolve:Environment"),
     ("head", "TptpFofSymbol:FunctionHead"),
     ("arguments", "TptpNamedFof:Terms"),
     ("argumentsResult", "TptpResolvedFof:Terms")]
    [congruence (resolveTerms (v "environment") (v "arguments"))
      (v "argumentsResult")]
    (resolveTerm (v "environment")
      (sourceFunction (v "head") (v "arguments")))
    (targetFunction (v "head") (v "argumentsResult")),
  mkRule "tptp-fof-resolve:terms-nil"
    [("environment", "TptpResolve:Environment")] []
    (resolveTerms (v "environment") sourceTermsNil)
    targetTermsNil,
  mkRule "tptp-fof-resolve:terms-cons"
    [("environment", "TptpResolve:Environment"),
     ("head", "TptpNamedFof:Term"), ("tail", "TptpNamedFof:Terms"),
     ("headResult", "TptpResolvedFof:Term"),
     ("tailResult", "TptpResolvedFof:Terms")]
    [congruence (resolveTerm (v "environment") (v "head")) (v "headResult"),
     congruence (resolveTerms (v "environment") (v "tail")) (v "tailResult")]
    (resolveTerms (v "environment") (sourceTermsCons (v "head") (v "tail")))
    (targetTermsCons (v "headResult") (v "tailResult"))
]

def formulaLeafRules : List RewriteRule := [
  mkRule "tptp-fof-resolve:formula-verum"
    [("environment", "TptpResolve:Environment")] []
    (resolveFormula (v "environment") (sourceFormula "verum"))
    (targetFormula "verum"),
  mkRule "tptp-fof-resolve:formula-falsum"
    [("environment", "TptpResolve:Environment")] []
    (resolveFormula (v "environment") (sourceFormula "falsum"))
    (targetFormula "falsum")
]

def formulaAtomRules : List RewriteRule := [
  mkRule "tptp-fof-resolve:formula-predicate"
    [("environment", "TptpResolve:Environment"),
     ("head", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpNamedFof:Terms"),
     ("argumentsResult", "TptpResolvedFof:Terms")]
    [congruence (resolveTerms (v "environment") (v "arguments"))
      (v "argumentsResult")]
    (resolveFormula (v "environment")
      (sourceFormula "predicate" [v "head", v "arguments"]))
    (targetFormula "predicate" [v "head", v "argumentsResult"]),
  mkRule "tptp-fof-resolve:formula-equal"
    [("environment", "TptpResolve:Environment"),
     ("left", "TptpNamedFof:Term"), ("right", "TptpNamedFof:Term"),
     ("leftResult", "TptpResolvedFof:Term"),
     ("rightResult", "TptpResolvedFof:Term")]
    [congruence (resolveTerm (v "environment") (v "left")) (v "leftResult"),
     congruence (resolveTerm (v "environment") (v "right")) (v "rightResult")]
    (resolveFormula (v "environment")
      (sourceFormula "equal" [v "left", v "right"]))
    (targetFormula "equal" [v "leftResult", v "rightResult"])
]

def unaryFormulaRule : RewriteRule :=
  mkRule "tptp-fof-resolve:formula-not"
    [("environment", "TptpResolve:Environment"),
     ("body", "TptpNamedFof:Formula"),
     ("bodyResult", "TptpResolvedFof:Formula")]
    [congruence (resolveFormula (v "environment") (v "body"))
      (v "bodyResult")]
    (resolveFormula (v "environment") (sourceFormula "not" [v "body"]))
    (targetFormula "not" [v "bodyResult"])

def binaryFormulaRule (constructor : String) : RewriteRule :=
  mkRule ("tptp-fof-resolve:formula-" ++ constructor)
    [("environment", "TptpResolve:Environment"),
     ("left", "TptpNamedFof:Formula"),
     ("right", "TptpNamedFof:Formula"),
     ("leftResult", "TptpResolvedFof:Formula"),
     ("rightResult", "TptpResolvedFof:Formula")]
    [congruence (resolveFormula (v "environment") (v "left"))
      (v "leftResult"),
     congruence (resolveFormula (v "environment") (v "right"))
      (v "rightResult")]
    (resolveFormula (v "environment")
      (sourceFormula constructor [v "left", v "right"]))
    (targetFormula constructor [v "leftResult", v "rightResult"])

def binaryFormulaRules : List RewriteRule :=
  ["and", "or", "iff", "implies", "reverse-implies", "xor", "nor", "nand"].map
    binaryFormulaRule

def binderFormulaRule (constructor : String) : RewriteRule :=
  mkRule ("tptp-fof-resolve:formula-" ++ constructor)
    [("environment", "TptpResolve:Environment"), ("binder", "String"),
     ("body", "TptpNamedFof:Formula"),
     ("bodyResult", "TptpResolvedFof:Formula")]
    [congruence
      (resolveFormula (environmentCons (v "binder") (v "environment"))
        (v "body"))
      (v "bodyResult")]
    (resolveFormula (v "environment")
      (sourceFormula constructor [sourceName (v "binder"), v "body"]))
    (targetFormula constructor [v "bodyResult"])

def binderFormulaRules : List RewriteRule :=
  [binderFormulaRule "all", binderFormulaRule "ex"]

def closedRule : RewriteRule :=
  mkRule "tptp-fof-resolve:closed"
    [("formula", "TptpNamedFof:Formula"),
     ("result", "TptpResolvedFof:Formula")]
    [congruence (resolveFormula environmentNil (v "formula")) (v "result")]
    (resolveClosed (v "formula"))
    (v "result")

def rewrites : List RewriteRule :=
  lookupRules ++ termRules ++ formulaLeafRules ++ formulaAtomRules ++
    [unaryFormulaRule] ++ binaryFormulaRules ++ binderFormulaRules ++
    [closedRule]

def supportTerms : List GrammarRule := [
  ctor "tptp-fof-resolve:environment-nil" "TptpResolve:Environment" [],
  ctor "tptp-fof-resolve:environment-cons" "TptpResolve:Environment"
    [("name", "String"), ("tail", "TptpResolve:Environment")],
  ctor "tptp-fof-resolve:closed" "TptpResolvedFof:Formula"
    [("formula", "TptpNamedFof:Formula")] (some .rewrite),
  ctor "tptp-fof-resolve:formula" "TptpResolvedFof:Formula"
    [("environment", "TptpResolve:Environment"),
     ("formula", "TptpNamedFof:Formula")] (some .rewrite),
  ctor "tptp-fof-resolve:term" "TptpResolvedFof:Term"
    [("environment", "TptpResolve:Environment"),
     ("term", "TptpNamedFof:Term")] (some .rewrite),
  ctor "tptp-fof-resolve:terms" "TptpResolvedFof:Terms"
    [("environment", "TptpResolve:Environment"),
     ("terms", "TptpNamedFof:Terms")] (some .rewrite),
  ctor "tptp-fof-resolve:lookup" "TptpResolvedFof:Index"
    [("name", "String"), ("environment", "TptpResolve:Environment")]
    (some .rewrite),
  ctor "tptp-fof-resolve:lookup-decision" "TptpResolvedFof:Index"
    [("decision", "PatternEqualityDecision:Result"), ("name", "String"),
     ("tail", "TptpResolve:Environment")] (some .rewrite)
]

/-- The source and target share the builtin `String` row and the complete
lossless FOF symbol-head carrier. -/
def additionalTypes : List TypeDecl :=
  TptpResolvedFofLanguageDef.ownTypes ++
    PatternEqualityDecision.language.types ++
      [("TptpResolve:Environment" : TypeDecl)]

def language : LanguageDef := {
  name := "TptpNamedFofToResolved"
  types := TptpNamedFofLanguageDef.language.types ++ additionalTypes
  terms := TptpNamedFofLanguageDef.language.terms ++
    TptpResolvedFofLanguageDef.ownTerms ++
    PatternEqualityDecision.language.terms ++ supportTerms
  equations := []
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

theorem rewrite_count : rewrites.length = 23 := by
  decide

private theorem language_typeNames : language.typeNames =
    ["String", "TptpFofSymbol:FunctionHead",
     "TptpFofSymbol:PredicateHead",
     "TptpNamedFof:Name", "TptpNamedFof:Term",
     "TptpNamedFof:Terms", "TptpNamedFof:Formula",
     "TptpResolvedFof:Index", "TptpResolvedFof:Term",
     "TptpResolvedFof:Terms", "TptpResolvedFof:Formula",
     "PatternEqualityDecision:Result", "TptpResolve:Environment"] := by
  rfl

private theorem language_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures language =
    [("tptp-fof-symbol:function-plain", 1),
     ("tptp-fof-symbol:function-defined", 1),
     ("tptp-fof-symbol:function-system", 1),
     ("tptp-fof-symbol:function-integer", 1),
     ("tptp-fof-symbol:function-rational", 1),
     ("tptp-fof-symbol:function-real", 1),
     ("tptp-fof-symbol:function-distinct-object", 1),
     ("tptp-fof-symbol:predicate-plain", 1),
     ("tptp-fof-symbol:predicate-defined", 1),
     ("tptp-fof-symbol:predicate-system", 1),
     ("tptp-fof-named:name", 1), ("tptp-fof-named:term-variable", 1),
     ("tptp-fof-named:term-function", 2),
     ("tptp-fof-named:terms-nil", 0),
     ("tptp-fof-named:terms-cons", 2), ("tptp-fof-named:verum", 0),
     ("tptp-fof-named:falsum", 0), ("tptp-fof-named:predicate", 2),
     ("tptp-fof-named:equal", 2), ("tptp-fof-named:not", 1),
     ("tptp-fof-named:and", 2), ("tptp-fof-named:or", 2),
     ("tptp-fof-named:iff", 2), ("tptp-fof-named:implies", 2),
     ("tptp-fof-named:reverse-implies", 2), ("tptp-fof-named:xor", 2),
     ("tptp-fof-named:nor", 2), ("tptp-fof-named:nand", 2),
     ("tptp-fof-named:all", 2), ("tptp-fof-named:ex", 2),
     ("tptp-fof-resolved:index-zero", 0),
     ("tptp-fof-resolved:index-succ", 1),
     ("tptp-fof-resolved:term-variable", 1),
     ("tptp-fof-resolved:term-function", 2),
     ("tptp-fof-resolved:terms-nil", 0),
     ("tptp-fof-resolved:terms-cons", 2),
     ("tptp-fof-resolved:verum", 0), ("tptp-fof-resolved:falsum", 0),
     ("tptp-fof-resolved:predicate", 2),
     ("tptp-fof-resolved:equal", 2), ("tptp-fof-resolved:not", 1),
     ("tptp-fof-resolved:and", 2), ("tptp-fof-resolved:or", 2),
     ("tptp-fof-resolved:iff", 2), ("tptp-fof-resolved:implies", 2),
     ("tptp-fof-resolved:reverse-implies", 2),
     ("tptp-fof-resolved:xor", 2), ("tptp-fof-resolved:nor", 2),
     ("tptp-fof-resolved:nand", 2), ("tptp-fof-resolved:all", 1),
     ("tptp-fof-resolved:ex", 1),
     ("pattern-equality-decision:equal", 0),
     ("pattern-equality-decision:different", 0),
     ("tptp-fof-resolve:environment-nil", 0),
     ("tptp-fof-resolve:environment-cons", 2),
     ("tptp-fof-resolve:closed", 1), ("tptp-fof-resolve:formula", 2),
     ("tptp-fof-resolve:term", 2), ("tptp-fof-resolve:terms", 2),
     ("tptp-fof-resolve:lookup", 2),
     ("tptp-fof-resolve:lookup-decision", 3)] := by
  rfl

private theorem language_constructorLabels :
    RewriteValidationCertificate.constructorLabels language =
    ["tptp-fof-symbol:function-plain",
     "tptp-fof-symbol:function-defined",
     "tptp-fof-symbol:function-system",
     "tptp-fof-symbol:function-integer",
     "tptp-fof-symbol:function-rational",
     "tptp-fof-symbol:function-real",
     "tptp-fof-symbol:function-distinct-object",
     "tptp-fof-symbol:predicate-plain",
     "tptp-fof-symbol:predicate-defined",
     "tptp-fof-symbol:predicate-system",
     "tptp-fof-named:name", "tptp-fof-named:term-variable",
     "tptp-fof-named:term-function", "tptp-fof-named:terms-nil",
     "tptp-fof-named:terms-cons", "tptp-fof-named:verum",
     "tptp-fof-named:falsum", "tptp-fof-named:predicate",
     "tptp-fof-named:equal", "tptp-fof-named:not", "tptp-fof-named:and",
     "tptp-fof-named:or", "tptp-fof-named:iff",
     "tptp-fof-named:implies", "tptp-fof-named:reverse-implies",
     "tptp-fof-named:xor", "tptp-fof-named:nor", "tptp-fof-named:nand",
     "tptp-fof-named:all", "tptp-fof-named:ex",
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
     "tptp-fof-resolved:ex", "pattern-equality-decision:equal",
     "pattern-equality-decision:different",
     "tptp-fof-resolve:environment-nil",
     "tptp-fof-resolve:environment-cons", "tptp-fof-resolve:closed",
     "tptp-fof-resolve:formula", "tptp-fof-resolve:term",
     "tptp-fof-resolve:terms", "tptp-fof-resolve:lookup",
     "tptp-fof-resolve:lookup-decision"] := by
  rfl

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  decide +kernel

private def constructorLabelNamespaced (label : String) : Bool :=
  label.startsWith "tptp-fof-symbol:" ||
    label.startsWith "tptp-fof-named:" ||
    label.startsWith "tptp-fof-resolved:" ||
      label.startsWith "pattern-equality-decision:" ||
        label.startsWith "tptp-fof-resolve:"

private theorem constructorLabels_namespaced :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelNamespaced = true := by
  rw [language_constructorLabels]
  decide +kernel

private theorem plainName_not_constructor (name : String)
    (plain : constructorLabelNamespaced name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have namespaced := (List.all_eq_true.mp constructorLabels_namespaced)
    name membership
  simp [plain] at namespaced

local macro "certify_resolver_row" : tactic =>
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
      typed, mkRule, congruence, environmentNil, environmentCons,
      resolveClosed, resolveFormula, resolveTerm, resolveTerms, lookup,
      lookupDecision, sourceName, sourceVariable, sourceFunction,
      sourceTermsNil, sourceTermsCons, targetIndexZero, targetIndexSucc,
      targetVariable, targetFunction, targetTermsNil, targetTermsCons,
      sourceFormula, targetFormula, unaryFormulaRule, binaryFormulaRule,
      binderFormulaRule, closedRule, lookupRules, termRules,
      formulaAtomRules, binaryFormulaRules, binderFormulaRules, a, v,
      PatternEqualityDecision.equal, PatternEqualityDecision.different,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.zipHead, Pattern.mapHead,
      Pattern.evalHead, plainName_not_constructor,
      constructorLabelNamespaced] <;>
    decide +kernel)

private theorem lookupRule0_checked :
    RewriteValidationCertificate.check language
      (lookupRules.get ⟨0, by decide⟩) = true := by
  certify_resolver_row

private theorem lookupRule1_checked :
    RewriteValidationCertificate.check language
      (lookupRules.get ⟨1, by decide⟩) = true := by
  certify_resolver_row

private theorem lookupRule2_checked :
    RewriteValidationCertificate.check language
      (lookupRules.get ⟨2, by decide⟩) = true := by
  certify_resolver_row

private theorem lookupRules_checked :
    lookupRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [lookupRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨lookupRule0_checked, lookupRule1_checked, lookupRule2_checked,
    True.intro⟩

private theorem termRule0_checked :
    RewriteValidationCertificate.check language
      (termRules.get ⟨0, by decide⟩) = true := by
  certify_resolver_row

private theorem termRule1_checked :
    RewriteValidationCertificate.check language
      (termRules.get ⟨1, by decide⟩) = true := by
  certify_resolver_row

private theorem termRule2_checked :
    RewriteValidationCertificate.check language
      (termRules.get ⟨2, by decide⟩) = true := by
  certify_resolver_row

private theorem termRule3_checked :
    RewriteValidationCertificate.check language
      (termRules.get ⟨3, by decide⟩) = true := by
  certify_resolver_row

private theorem termRules_checked :
    termRules.all (RewriteValidationCertificate.check language) = true := by
  simp only [termRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨termRule0_checked, termRule1_checked, termRule2_checked,
    termRule3_checked, True.intro⟩

private theorem formulaLeafRules_checked :
    formulaLeafRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [formulaLeafRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals certify_resolver_row

private theorem formulaAtomRule0_checked :
    RewriteValidationCertificate.check language
      (formulaAtomRules.get ⟨0, by decide⟩) = true := by
  certify_resolver_row

private theorem formulaAtomRule1_checked :
    RewriteValidationCertificate.check language
      (formulaAtomRules.get ⟨1, by decide⟩) = true := by
  certify_resolver_row

private theorem formulaAtomRules_checked :
    formulaAtomRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [formulaAtomRules, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨formulaAtomRule0_checked, formulaAtomRule1_checked, True.intro⟩

private theorem unaryFormulaRule_checked :
    RewriteValidationCertificate.check language unaryFormulaRule = true := by
  certify_resolver_row

private theorem binaryFormulaRule0_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨0, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRule1_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨1, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRule2_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨2, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRule3_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨3, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRule4_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨4, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRule5_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨5, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRule6_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨6, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRule7_checked :
    RewriteValidationCertificate.check language
      (binaryFormulaRules.get ⟨7, by decide⟩) = true := by
  certify_resolver_row

private theorem binaryFormulaRules_checked :
    binaryFormulaRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [binaryFormulaRules, List.map, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  exact ⟨binaryFormulaRule0_checked, binaryFormulaRule1_checked,
    binaryFormulaRule2_checked, binaryFormulaRule3_checked,
    binaryFormulaRule4_checked, binaryFormulaRule5_checked,
    binaryFormulaRule6_checked, binaryFormulaRule7_checked, True.intro⟩

private theorem binderFormulaRule0_checked :
    RewriteValidationCertificate.check language
      (binderFormulaRules.get ⟨0, by decide⟩) = true := by
  certify_resolver_row

private theorem binderFormulaRule1_checked :
    RewriteValidationCertificate.check language
      (binderFormulaRules.get ⟨1, by decide⟩) = true := by
  certify_resolver_row

private theorem binderFormulaRules_checked :
    binderFormulaRules.all
      (RewriteValidationCertificate.check language) = true := by
  simp only [binderFormulaRules, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  exact ⟨binderFormulaRule0_checked, binderFormulaRule1_checked, True.intro⟩

private theorem closedRule_checked :
    RewriteValidationCertificate.check language closedRule = true := by
  certify_resolver_row

private theorem checkedRow_validate {rows : List RewriteRule}
    (checks : rows.all (RewriteValidationCertificate.check language) = true)
    {rewrite : RewriteRule} (membership : rewrite ∈ rows) :
    language.validateRewrite rewrite = [] := by
  apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
    constructorLabels_nodup
  exact (List.all_eq_true.mp checks) rewrite membership

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  change rewrite ∈ rewrites at membership
  unfold rewrites at membership
  simp only [List.append_assoc] at membership
  rcases List.mem_append.mp membership with lookupMembership | membership
  · exact checkedRow_validate lookupRules_checked lookupMembership
  rcases List.mem_append.mp membership with termMembership | membership
  · exact checkedRow_validate termRules_checked termMembership
  rcases List.mem_append.mp membership with leafMembership | membership
  · exact checkedRow_validate formulaLeafRules_checked leafMembership
  rcases List.mem_append.mp membership with atomMembership | membership
  · exact checkedRow_validate formulaAtomRules_checked atomMembership
  rcases List.mem_append.mp membership with unaryMembership | membership
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at unaryMembership
    rcases unaryMembership with rfl
    exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup unaryFormulaRule_checked
  rcases List.mem_append.mp membership with binaryMembership | membership
  · exact checkedRow_validate binaryFormulaRules_checked binaryMembership
  rcases List.mem_append.mp membership with binderMembership | closedMembership
  · exact checkedRow_validate binderFormulaRules_checked binderMembership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at closedMembership
  rcases closedMembership with rfl
  exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
    constructorLabels_nodup closedRule_checked

theorem source_types_are_prefix :
    TptpNamedFofLanguageDef.language.types.IsPrefix language.types := by
  simp [language]

theorem source_terms_are_prefix :
    TptpNamedFofLanguageDef.language.terms.IsPrefix language.terms := by
  simp [language]

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

namespace Canary

def sameName : Pattern := a "X"
def otherName : Pattern := a "Y"

theorem equality_service_selects_equal :
    PatternEqualityDecision.relationTuples
      PatternEqualityDecision.relationName
      [sameName, sameName, v "decision"] =
        [[sameName, sameName, PatternEqualityDecision.equal]] := by
  exact PatternEqualityDecision.equal_exact sameName (v "decision")

theorem equality_service_selects_different :
    PatternEqualityDecision.relationTuples
      PatternEqualityDecision.relationName
      [sameName, otherName, v "decision"] =
        [[sameName, otherName, PatternEqualityDecision.different]] := by
  apply PatternEqualityDecision.different_exact
  decide

theorem free_lookup_has_no_root_rule :
    rewrites.filter (fun rule =>
      match rule.left with
      | .apply "tptp-fof-resolve:lookup"
          [_, .apply "tptp-fof-resolve:environment-nil" []] => true
      | _ => false) = [] := by
  decide +kernel

end Canary

#print axioms rewrite_count
#print axioms language_validate
#print axioms source_types_are_prefix
#print axioms source_terms_are_prefix
#print axioms language_supported
#print axioms Canary.equality_service_selects_equal
#print axioms Canary.equality_service_selects_different
#print axioms Canary.free_lookup_has_no_root_rule

end Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef
