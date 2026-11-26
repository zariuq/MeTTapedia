import Mettapedia.GSLT.LanguageDef.BaseSortDeclarations
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
  BaseSortDeclarations.context entries

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
    (premises : List Premise) (left right : Pattern) : RewriteRule :=
  BaseSortDeclarations.rule name (typed context) premises left right

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

end Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef
