import Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationSemantics
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Authored allocated-CNF to official-TPTP serialization

This language traverses the source-owned clausification carrier and constructs
official TPTP 9.2 CNF abstract syntax.  It has no name-generation primitive.
Four explicit finite-plan relations supply clause names, variable names,
Skolem functors, and definition functors; all other work is expressed by the
authored structural rules below.

The output retains the source clause identity, the selected official name,
the source clause, and the official annotated formula.  Text rendering and
file effects remain later, separate transformations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
open Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationPlan

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def typed (entries : List (String × String)) : List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def ctor (label category : String) (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
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

def relation (name : String) (arguments : List Pattern) : Premise :=
  .relationQuery name arguments

/-! ## Request and result carrier -/

def renderedTermsNil : Pattern :=
  a "tptp-cnf-official-serialization:rendered-terms-nil"

def renderedTermsCons (head tail : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:rendered-terms-cons" [head, tail]

def serializedEntry (identity name clause annotated : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:entry"
    [identity, name, clause, annotated]

def serializedEntriesNil : Pattern :=
  a "tptp-cnf-official-serialization:entries-nil"

def serializedEntriesCons (head tail : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:entries-cons" [head, tail]

def output (source polarity entries : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:output" [source, polarity, entries]

def serialize (source : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:serialize" [source]

def serializeTerm (source : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:term" [source]

def serializeTerms (source : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:terms" [source]

def serializeArguments (source : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:arguments" [source]

def plainTermBuilder (functor terms : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:plain-term" [functor, terms]

def definedTermBuilder (functor terms : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:defined-term" [functor, terms]

def systemTermBuilder (functor terms : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:system-term" [functor, terms]

def serializeLiteral (source : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:literal" [source]

def serializeAtomic (relationHead terms : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:atomic" [relationHead, terms]

def plainAtomicBuilder (functor terms : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:plain-atomic" [functor, terms]

def serializeClause (source : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:clause" [source]

def serializeClauseTail (source accumulator : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:clause-tail" [source, accumulator]

def serializeEntries (polarity source : Pattern) : Pattern :=
  a "tptp-cnf-official-serialization:entries" [polarity, source]

def addedTypes : List TypeDecl := [
  "TptpFofCnfOfficialSerialization:RenderedTerms",
  "TptpFofCnfOfficialSerialization:Entry",
  "TptpFofCnfOfficialSerialization:Entries",
  "TptpFofCnfOfficialSerialization:Output"]

def lexicalTerms : List GrammarRule := [
  ctor "axiom" "String" [],
  ctor "negated_conjecture" "String" [],
  ctor "$true" "String" [],
  ctor "$false" "String" []]

def ownTerms : List GrammarRule := [
  ctor "tptp-cnf-official-serialization:rendered-terms-nil"
    "TptpFofCnfOfficialSerialization:RenderedTerms" [],
  ctor "tptp-cnf-official-serialization:rendered-terms-cons"
    "TptpFofCnfOfficialSerialization:RenderedTerms"
    [("head", "Tptp92Ast:fof-term"),
     ("tail", "TptpFofCnfOfficialSerialization:RenderedTerms")],
  ctor "tptp-cnf-official-serialization:entry"
    "TptpFofCnfOfficialSerialization:Entry"
    [("identity", "TptpFofBatch:ClauseId"),
     ("name", "Tptp92Ast:name"),
     ("clause", "TptpFofCnf:Clause"),
     ("annotated", "Tptp92Ast:annotated-formula")],
  ctor "tptp-cnf-official-serialization:entries-nil"
    "TptpFofCnfOfficialSerialization:Entries" [],
  ctor "tptp-cnf-official-serialization:entries-cons"
    "TptpFofCnfOfficialSerialization:Entries"
    [("head", "TptpFofCnfOfficialSerialization:Entry"),
     ("tail", "TptpFofCnfOfficialSerialization:Entries")],
  ctor "tptp-cnf-official-serialization:output"
    "TptpFofCnfOfficialSerialization:Output"
    [("source", "TptpFofCnfAllocated:Output"),
     ("polarity", "TptpFofBatch:Polarity"),
     ("entries", "TptpFofCnfOfficialSerialization:Entries")],
  ctor "tptp-cnf-official-serialization:serialize"
    "TptpFofCnfOfficialSerialization:Output"
    [("source", "TptpFofCnfAllocated:Output")] (some .rewrite),
  ctor "tptp-cnf-official-serialization:term" "Tptp92Ast:fof-term"
    [("source", "TptpFofSkolem:Term")] (some .rewrite),
  ctor "tptp-cnf-official-serialization:terms"
    "TptpFofCnfOfficialSerialization:RenderedTerms"
    [("source", "TptpFofSkolem:Terms")] (some .rewrite),
  ctor "tptp-cnf-official-serialization:arguments"
    "Tptp92Ast:fof-arguments"
    [("source", "TptpFofCnfOfficialSerialization:RenderedTerms")]
    (some .rewrite),
  ctor "tptp-cnf-official-serialization:plain-term"
    "Tptp92Ast:fof-term"
    [("functor", "Tptp92Ast:functor"),
     ("terms", "TptpFofCnfOfficialSerialization:RenderedTerms")]
    (some .rewrite),
  ctor "tptp-cnf-official-serialization:defined-term"
    "Tptp92Ast:fof-term"
    [("functor", "Tptp92Ast:defined-functor"),
     ("terms", "TptpFofCnfOfficialSerialization:RenderedTerms")]
    (some .rewrite),
  ctor "tptp-cnf-official-serialization:system-term"
    "Tptp92Ast:fof-term"
    [("functor", "Tptp92Ast:system-functor"),
     ("terms", "TptpFofCnfOfficialSerialization:RenderedTerms")]
    (some .rewrite),
  ctor "tptp-cnf-official-serialization:literal"
    "Tptp92Ast:cnf-literal"
    [("source", "TptpFofNamed:Reference")] (some .rewrite),
  ctor "tptp-cnf-official-serialization:atomic"
    "Tptp92Ast:fof-atomic-formula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("terms", "TptpFofCnfOfficialSerialization:RenderedTerms")]
    (some .rewrite),
  ctor "tptp-cnf-official-serialization:plain-atomic"
    "Tptp92Ast:fof-atomic-formula"
    [("functor", "Tptp92Ast:functor"),
     ("terms", "TptpFofCnfOfficialSerialization:RenderedTerms")]
    (some .rewrite),
  ctor "tptp-cnf-official-serialization:clause"
    "Tptp92Ast:cnf-formula"
    [("source", "TptpFofCnf:Clause")] (some .rewrite),
  ctor "tptp-cnf-official-serialization:clause-tail"
    "Tptp92Ast:cnf-formula"
    [("source", "TptpFofCnf:Clause"),
     ("accumulator", "Tptp92Ast:cnf-disjunction")] (some .rewrite),
  ctor "tptp-cnf-official-serialization:entries"
    "TptpFofCnfOfficialSerialization:Entries"
    [("polarity", "TptpFofBatch:Polarity"),
     ("source", "TptpFofCnfAllocated:ClauseEntries")] (some .rewrite)]

def localTerms : List GrammarRule := lexicalTerms ++ ownTerms

/-! ## Official AST constructors used by the rules -/

def quotedAtomicWord (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:atomic-word:alt-2" [
    a "tptp92-ast:token:single-quoted" [lexeme]]

def plainFunctor (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:functor:alt-1" [quotedAtomicWord lexeme]

def definedFunctorAst (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:defined-functor:alt-1" [
    a "tptp92-ast:atomic-defined-word:alt-1" [
      a "tptp92-ast:token:dollar-word" [lexeme]]]

def systemFunctorAst (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:system-functor:alt-1" [
    a "tptp92-ast:atomic-system-word:alt-1" [
      a "tptp92-ast:token:dollar-dollar-word" [lexeme]]]

def plainConstantTerm (functor : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-1" [
        a "tptp92-ast:constant:alt-1" [functor]]]]

def plainAppliedTerm (functor arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-2" [functor, arguments]]]

def definedConstantTerm (functor : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [
      a "tptp92-ast:fof-defined-term:alt-2" [
        a "tptp92-ast:fof-defined-atomic-term:alt-1" [
          a "tptp92-ast:fof-defined-plain-term:alt-1" [
            a "tptp92-ast:defined-constant:alt-1" [functor]]]]]]

def definedAppliedTerm (functor arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [
      a "tptp92-ast:fof-defined-term:alt-2" [
        a "tptp92-ast:fof-defined-atomic-term:alt-1" [
          a "tptp92-ast:fof-defined-plain-term:alt-2"
            [functor, arguments]]]]]

def systemConstantTerm (functor : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-3" [
      a "tptp92-ast:fof-system-term:alt-1" [
        a "tptp92-ast:system-constant:alt-1" [functor]]]]

def systemAppliedTerm (functor arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-3" [
      a "tptp92-ast:fof-system-term:alt-2" [functor, arguments]]]

def numericTerm (alternative tokenLabel : String) (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [
      a "tptp92-ast:fof-defined-term:alt-1" [
        a "tptp92-ast:defined-term:alt-1" [
          a alternative [a tokenLabel [lexeme]]]]]]

def distinctObjectTerm (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [
      a "tptp92-ast:fof-defined-term:alt-1" [
        a "tptp92-ast:defined-term:alt-2" [
          a "tptp92-ast:token:distinct-object" [lexeme]]]]]

def plainConstantAtomic (functor : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-1" [
        a "tptp92-ast:constant:alt-1" [functor]]]]

def plainAppliedAtomic (functor arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-2" [functor, arguments]]]

def definedAppliedAtomic (functor arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-1" [
      a "tptp92-ast:fof-defined-plain-formula:alt-1" [
        a "tptp92-ast:fof-defined-plain-term:alt-2"
          [functor, arguments]]]]

def systemConstantAtomic (functor : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-3" [
    a "tptp92-ast:fof-system-atomic-formula:alt-1" [
      a "tptp92-ast:fof-system-term:alt-1" [
        a "tptp92-ast:system-constant:alt-1" [functor]]]]

def systemAppliedAtomic (functor arguments : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-3" [
    a "tptp92-ast:fof-system-atomic-formula:alt-1" [
      a "tptp92-ast:fof-system-term:alt-2" [functor, arguments]]]

def truthAtomic (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-1" [
      a "tptp92-ast:fof-defined-plain-formula:alt-1" [
        a "tptp92-ast:fof-defined-plain-term:alt-1" [
          a "tptp92-ast:defined-constant:alt-1" [
            definedFunctorAst lexeme]]]]]

def equalityAtomic (left right : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-2" [
      a "tptp92-ast:fof-defined-infix-formula:alt-1" [
        left,
        a "tptp92-ast:defined-infix-pred:alt-1" [
          a "tptp92-ast:infix-equality:alt-1"], right]]]

def positiveLiteral (formula : Pattern) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-1" [formula]

def negativeLiteral (formula : Pattern) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-2" [formula]

def inequalityLiteral (left right : Pattern) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-4" [
    a "tptp92-ast:fof-infix-unary:alt-1" [
      left, a "tptp92-ast:infix-inequality:alt-1", right]]

def oneDisjunction (literal : Pattern) : Pattern :=
  a "tptp92-ast:cnf-disjunction:alt-1" [literal]

def moreDisjunction (left literal : Pattern) : Pattern :=
  a "tptp92-ast:cnf-disjunction:alt-2" [left, literal]

def cnfFormula (body : Pattern) : Pattern :=
  a "tptp92-ast:cnf-formula:alt-1" [body]

def formulaRole (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:formula-role:alt-1" [
    a "tptp92-ast:token:lower-word" [lexeme]]

def annotatedCnf (name role formula : Pattern) : Pattern :=
  a "tptp92-ast:annotated-formula:alt-5" [
    a "tptp92-ast:cnf-annotated:alt-1" [
      name, role, formula, a "tptp92-ast:annotations:alt-2"]]

/-! ## Authored structural rules -/

def termVariableRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:term-variable" [
      ("index", "TptpResolvedFof:Index"),
      ("variable", "Tptp92Ast:variable")]
    [relation variableRelation [v "index", v "variable"]]
    (serializeTerm <| a "tptp-fof-skolem:term-variable" [v "index"])
    (a "tptp92-ast:fof-term:alt-2" [v "variable"])

def originalTermRule (name sourceHead : String)
    (builder : Pattern -> Pattern -> Pattern) : RewriteRule :=
  mkRule name [
      ("lexeme", "String"), ("source-terms", "TptpFofSkolem:Terms"),
      ("rendered-terms", "TptpFofCnfOfficialSerialization:RenderedTerms"),
      ("target", "Tptp92Ast:fof-term")]
    [congruence (serializeTerms (v "source-terms")) (v "rendered-terms"),
     congruence (builder (v "lexeme") (v "rendered-terms")) (v "target")]
    (serializeTerm <| a "tptp-fof-skolem:term-original" [
      a sourceHead [v "lexeme"], v "source-terms"])
    (v "target")

def generatedTermRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:term-generated" [
      ("identity", "TptpResolvedFof:Index"),
      ("source-terms", "TptpFofSkolem:Terms"),
      ("functor", "Tptp92Ast:functor"),
      ("rendered-terms", "TptpFofCnfOfficialSerialization:RenderedTerms"),
      ("target", "Tptp92Ast:fof-term")]
    [relation skolemFunctorRelation [v "identity", v "functor"],
     congruence (serializeTerms (v "source-terms")) (v "rendered-terms"),
     congruence (plainTermBuilder (v "functor") (v "rendered-terms"))
       (v "target")]
    (serializeTerm <| a "tptp-fof-skolem:term-generated" [
      v "identity", v "source-terms"])
    (v "target")

def numericTermRule (name sourceHead alternative tokenLabel : String) :
    RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (serializeTerm <| a "tptp-fof-skolem:term-original" [
      a sourceHead [v "lexeme"],
      a "tptp-fof-skolem:terms-nil"])
    (numericTerm alternative tokenLabel (v "lexeme"))

def distinctObjectTermRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:term-distinct-object"
    [("lexeme", "String")] []
    (serializeTerm <| a "tptp-fof-skolem:term-original" [
      a "tptp-fof-symbol:function-distinct-object" [v "lexeme"],
      a "tptp-fof-skolem:terms-nil"])
    (distinctObjectTerm (v "lexeme"))

def termsNilRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:terms-nil" [] []
    (serializeTerms <| a "tptp-fof-skolem:terms-nil") renderedTermsNil

def termsConsRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:terms-cons" [
      ("head", "TptpFofSkolem:Term"),
      ("tail", "TptpFofSkolem:Terms"),
      ("rendered-head", "Tptp92Ast:fof-term"),
      ("rendered-tail", "TptpFofCnfOfficialSerialization:RenderedTerms")]
    [congruence (serializeTerm (v "head")) (v "rendered-head"),
     congruence (serializeTerms (v "tail")) (v "rendered-tail")]
    (serializeTerms <| a "tptp-fof-skolem:terms-cons"
      [v "head", v "tail"])
    (renderedTermsCons (v "rendered-head") (v "rendered-tail"))

def argumentsOneRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:arguments-one"
    [("head", "Tptp92Ast:fof-term")] []
    (serializeArguments <| renderedTermsCons (v "head") renderedTermsNil)
    (a "tptp92-ast:fof-arguments:alt-1" [v "head"])

def argumentsMoreRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:arguments-more" [
      ("head", "Tptp92Ast:fof-term"),
      ("tail-head", "Tptp92Ast:fof-term"),
      ("tail", "TptpFofCnfOfficialSerialization:RenderedTerms"),
      ("rendered-tail", "Tptp92Ast:fof-arguments")]
    [congruence
      (serializeArguments <| renderedTermsCons (v "tail-head") (v "tail"))
      (v "rendered-tail")]
    (serializeArguments <| renderedTermsCons (v "head") <|
      renderedTermsCons (v "tail-head") (v "tail"))
    (a "tptp92-ast:fof-arguments:alt-2"
      [v "head", v "rendered-tail"])

def nullaryBuilderRule (name : String)
    (request : Pattern -> Pattern -> Pattern)
    (result : Pattern -> Pattern) (functorSort : String) : RewriteRule :=
  mkRule name [("functor", functorSort)] []
    (request (v "functor") renderedTermsNil)
    (result (v "functor"))

def appliedBuilderRule (name : String)
    (request : Pattern -> Pattern -> Pattern)
    (result : Pattern -> Pattern -> Pattern) (functorSort : String) :
    RewriteRule :=
  mkRule name [
      ("functor", functorSort), ("head", "Tptp92Ast:fof-term"),
      ("tail", "TptpFofCnfOfficialSerialization:RenderedTerms"),
      ("arguments", "Tptp92Ast:fof-arguments")]
    [congruence
      (serializeArguments <| renderedTermsCons (v "head") (v "tail"))
      (v "arguments")]
    (request (v "functor") <| renderedTermsCons (v "head") (v "tail"))
    (result (v "functor") (v "arguments"))

def plainOriginalTermRule : RewriteRule :=
  originalTermRule "tptp-cnf-official-serialization:term-original-plain"
    "tptp-fof-symbol:function-plain"
    (fun lexeme terms => plainTermBuilder (plainFunctor lexeme) terms)

def definedOriginalTermRule : RewriteRule :=
  originalTermRule "tptp-cnf-official-serialization:term-original-defined"
    "tptp-fof-symbol:function-defined"
    (fun lexeme terms => definedTermBuilder (definedFunctorAst lexeme) terms)

def systemOriginalTermRule : RewriteRule :=
  originalTermRule "tptp-cnf-official-serialization:term-original-system"
    "tptp-fof-symbol:function-system"
    (fun lexeme terms => systemTermBuilder (systemFunctorAst lexeme) terms)

def plainTermNullaryRule : RewriteRule :=
  nullaryBuilderRule "tptp-cnf-official-serialization:plain-term-nullary"
    plainTermBuilder plainConstantTerm "Tptp92Ast:functor"

def plainTermAppliedRule : RewriteRule :=
  appliedBuilderRule "tptp-cnf-official-serialization:plain-term-applied"
    plainTermBuilder plainAppliedTerm "Tptp92Ast:functor"

def definedTermNullaryRule : RewriteRule :=
  nullaryBuilderRule "tptp-cnf-official-serialization:defined-term-nullary"
    definedTermBuilder definedConstantTerm "Tptp92Ast:defined-functor"

def definedTermAppliedRule : RewriteRule :=
  appliedBuilderRule "tptp-cnf-official-serialization:defined-term-applied"
    definedTermBuilder definedAppliedTerm "Tptp92Ast:defined-functor"

def systemTermNullaryRule : RewriteRule :=
  nullaryBuilderRule "tptp-cnf-official-serialization:system-term-nullary"
    systemTermBuilder systemConstantTerm "Tptp92Ast:system-functor"

def systemTermAppliedRule : RewriteRule :=
  appliedBuilderRule "tptp-cnf-official-serialization:system-term-applied"
    systemTermBuilder systemAppliedTerm "Tptp92Ast:system-functor"

def truthLiteralRule (name source result : String) : RewriteRule :=
  mkRule name [] []
    (serializeLiteral <| a source)
    (positiveLiteral <| truthAtomic <| a result)

def originalLiteralRule (name source : String)
    (wrap : Pattern -> Pattern) : RewriteRule :=
  mkRule name [
      ("relation", "TptpFofSymbol:PredicateHead"),
      ("source-terms", "TptpFofSkolem:Terms"),
      ("rendered-terms", "TptpFofCnfOfficialSerialization:RenderedTerms"),
      ("atomic", "Tptp92Ast:fof-atomic-formula")]
    [congruence (serializeTerms (v "source-terms")) (v "rendered-terms"),
     congruence
       (serializeAtomic (v "relation") (v "rendered-terms")) (v "atomic")]
    (serializeLiteral <| a source [v "relation", v "source-terms"])
    (wrap (v "atomic"))

def equalityLiteralRule (name source : String)
    (wrap : Pattern -> Pattern -> Pattern) : RewriteRule :=
  mkRule name [
      ("left", "TptpFofSkolem:Term"),
      ("right", "TptpFofSkolem:Term"),
      ("rendered-left", "Tptp92Ast:fof-term"),
      ("rendered-right", "Tptp92Ast:fof-term")]
    [congruence (serializeTerm (v "left")) (v "rendered-left"),
     congruence (serializeTerm (v "right")) (v "rendered-right")]
    (serializeLiteral <| a source [v "left", v "right"])
    (wrap (v "rendered-left") (v "rendered-right"))

def generatedLiteralRule (name source : String)
    (wrap : Pattern -> Pattern) : RewriteRule :=
  mkRule name [
      ("identity", "TptpResolvedFof:Index"),
      ("source-terms", "TptpFofSkolem:Terms"),
      ("functor", "Tptp92Ast:functor"),
      ("rendered-terms", "TptpFofCnfOfficialSerialization:RenderedTerms"),
      ("atomic", "Tptp92Ast:fof-atomic-formula")]
    [relation definitionFunctorRelation [v "identity", v "functor"],
     congruence (serializeTerms (v "source-terms")) (v "rendered-terms"),
     congruence
       (plainAtomicBuilder (v "functor") (v "rendered-terms")) (v "atomic")]
    (serializeLiteral <| a source [v "identity", v "source-terms"])
    (wrap (v "atomic"))

def atomicRule (name sourceHead : String)
    (render : Pattern -> Pattern -> Pattern) : RewriteRule :=
  mkRule name [
      ("lexeme", "String"), ("head", "Tptp92Ast:fof-term"),
      ("tail", "TptpFofCnfOfficialSerialization:RenderedTerms"),
      ("arguments", "Tptp92Ast:fof-arguments")]
    [congruence
      (serializeArguments <| renderedTermsCons (v "head") (v "tail"))
      (v "arguments")]
    (serializeAtomic (a sourceHead [v "lexeme"])
      (renderedTermsCons (v "head") (v "tail")))
    (render (v "lexeme") (v "arguments"))

def atomicNullaryRule (name sourceHead : String)
    (render : Pattern -> Pattern) : RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (serializeAtomic (a sourceHead [v "lexeme"]) renderedTermsNil)
    (render (v "lexeme"))

def plainAtomicNullaryRule : RewriteRule :=
  atomicNullaryRule "tptp-cnf-official-serialization:atomic-plain-nullary"
    "tptp-fof-symbol:predicate-plain"
    (fun lexeme => plainConstantAtomic (plainFunctor lexeme))

def plainAtomicAppliedRule : RewriteRule :=
  atomicRule "tptp-cnf-official-serialization:atomic-plain-applied"
    "tptp-fof-symbol:predicate-plain"
    (fun lexeme arguments => plainAppliedAtomic (plainFunctor lexeme) arguments)

def definedAtomicAppliedRule : RewriteRule :=
  atomicRule "tptp-cnf-official-serialization:atomic-defined-applied"
    "tptp-fof-symbol:predicate-defined"
    (fun lexeme arguments =>
      definedAppliedAtomic (definedFunctorAst lexeme) arguments)

def systemAtomicNullaryRule : RewriteRule :=
  atomicNullaryRule "tptp-cnf-official-serialization:atomic-system-nullary"
    "tptp-fof-symbol:predicate-system"
    (fun lexeme => systemConstantAtomic (systemFunctorAst lexeme))

def systemAtomicAppliedRule : RewriteRule :=
  atomicRule "tptp-cnf-official-serialization:atomic-system-applied"
    "tptp-fof-symbol:predicate-system"
    (fun lexeme arguments =>
      systemAppliedAtomic (systemFunctorAst lexeme) arguments)

def plainAtomicBuilderNullaryRule : RewriteRule :=
  nullaryBuilderRule
    "tptp-cnf-official-serialization:plain-atomic-nullary"
    plainAtomicBuilder plainConstantAtomic "Tptp92Ast:functor"

def plainAtomicBuilderAppliedRule : RewriteRule :=
  appliedBuilderRule
    "tptp-cnf-official-serialization:plain-atomic-applied"
    plainAtomicBuilder plainAppliedAtomic "Tptp92Ast:functor"

def verumLiteralRule : RewriteRule :=
  truthLiteralRule "tptp-cnf-official-serialization:literal-verum"
    "tptp-fof-named:ref-verum" "$true"

def falsumLiteralRule : RewriteRule :=
  truthLiteralRule "tptp-cnf-official-serialization:literal-falsum"
    "tptp-fof-named:ref-falsum" "$false"

def originalPositiveLiteralRule : RewriteRule :=
  originalLiteralRule
    "tptp-cnf-official-serialization:literal-original-positive"
    "tptp-fof-named:ref-original-positive" positiveLiteral

def originalNegativeLiteralRule : RewriteRule :=
  originalLiteralRule
    "tptp-cnf-official-serialization:literal-original-negative"
    "tptp-fof-named:ref-original-negative" negativeLiteral

def equalLiteralRule : RewriteRule :=
  equalityLiteralRule "tptp-cnf-official-serialization:literal-equal"
    "tptp-fof-named:ref-equal"
    (fun left right => positiveLiteral (equalityAtomic left right))

def notEqualLiteralRule : RewriteRule :=
  equalityLiteralRule "tptp-cnf-official-serialization:literal-not-equal"
    "tptp-fof-named:ref-not-equal" inequalityLiteral

def definedPositiveLiteralRule : RewriteRule :=
  generatedLiteralRule
    "tptp-cnf-official-serialization:literal-defined-positive"
    "tptp-fof-named:ref-defined-positive" positiveLiteral

def definedNegativeLiteralRule : RewriteRule :=
  generatedLiteralRule
    "tptp-cnf-official-serialization:literal-defined-negative"
    "tptp-fof-named:ref-defined-negative" negativeLiteral

def emptyClauseRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:clause-empty" [] []
    (serializeClause <| a "tptp-fof-cnf:clause-nil")
    (cnfFormula <| oneDisjunction <| positiveLiteral <|
      truthAtomic <| a "$false")

def clauseStartRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:clause-start" [
      ("head", "TptpFofNamed:Reference"),
      ("tail", "TptpFofCnf:Clause"),
      ("literal", "Tptp92Ast:cnf-literal"),
      ("target", "Tptp92Ast:cnf-formula")]
    [congruence (serializeLiteral (v "head")) (v "literal"),
     congruence
       (serializeClauseTail (v "tail") <| oneDisjunction (v "literal"))
       (v "target")]
    (serializeClause <| a "tptp-fof-cnf:clause-cons"
      [v "head", v "tail"])
    (v "target")

def clauseTailNilRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:clause-tail-nil"
    [("accumulator", "Tptp92Ast:cnf-disjunction")] []
    (serializeClauseTail (a "tptp-fof-cnf:clause-nil") (v "accumulator"))
    (cnfFormula (v "accumulator"))

def clauseTailConsRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:clause-tail-cons" [
      ("head", "TptpFofNamed:Reference"),
      ("tail", "TptpFofCnf:Clause"),
      ("accumulator", "Tptp92Ast:cnf-disjunction"),
      ("literal", "Tptp92Ast:cnf-literal"),
      ("target", "Tptp92Ast:cnf-formula")]
    [congruence (serializeLiteral (v "head")) (v "literal"),
     congruence
       (serializeClauseTail (v "tail") <|
         moreDisjunction (v "accumulator") (v "literal"))
       (v "target")]
    (serializeClauseTail
      (a "tptp-fof-cnf:clause-cons" [v "head", v "tail"])
      (v "accumulator"))
    (v "target")

def entriesNilRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:entries-nil"
    [("polarity", "TptpFofBatch:Polarity")] []
    (serializeEntries (v "polarity") <|
      a "tptp-fof-cnf-allocated:entries-nil")
    serializedEntriesNil

def entriesConsRule (name polarityConstructor roleLexeme : String) :
    RewriteRule :=
  mkRule name [
      ("identity", "TptpFofBatch:ClauseId"),
      ("name-index", "TptpResolvedFof:Index"),
      ("clause", "TptpFofCnf:Clause"),
      ("rest", "TptpFofCnfAllocated:ClauseEntries"),
      ("name", "Tptp92Ast:name"),
      ("formula", "Tptp92Ast:cnf-formula"),
      ("rendered-rest", "TptpFofCnfOfficialSerialization:Entries")]
    [relation clauseNameRelation [v "name-index", v "name"],
     congruence (serializeClause (v "clause")) (v "formula"),
     congruence
       (serializeEntries (a polarityConstructor) (v "rest"))
       (v "rendered-rest")]
    (serializeEntries (a polarityConstructor) <|
      a "tptp-fof-cnf-allocated:entries-cons" [
        a "tptp-fof-cnf-allocated:clause-entry" [
          v "identity",
          a "tptp-fof-cnf-allocated:name" [v "name-index"],
          v "clause"], v "rest"])
    (serializedEntriesCons
      (serializedEntry (v "identity") (v "name") (v "clause") <|
        annotatedCnf (v "name") (formulaRole <| a roleLexeme) (v "formula"))
      (v "rendered-rest"))

def entriesPositiveRule : RewriteRule :=
  entriesConsRule "tptp-cnf-official-serialization:entries-positive"
    "tptp-fof-batch:positive" "axiom"

def entriesNegativeRule : RewriteRule :=
  entriesConsRule "tptp-cnf-official-serialization:entries-negative"
    "tptp-fof-batch:negative" "negated_conjecture"

def startRule : RewriteRule :=
  mkRule "tptp-cnf-official-serialization:start" [
      ("occurrence", "TptpFofBatch:Occurrence"),
      ("polarity", "TptpFofBatch:Polarity"),
      ("skolem", "TptpFofSkolem:Output"),
      ("cnf", "TptpFofCnf:Output"),
      ("source-entries", "TptpFofBatch:ClauseEntries"),
      ("first-name", "TptpResolvedFof:Index"),
      ("next-name", "TptpResolvedFof:Index"),
      ("allocated-entries", "TptpFofCnfAllocated:ClauseEntries"),
      ("rendered-entries", "TptpFofCnfOfficialSerialization:Entries")]
    [congruence
      (serializeEntries (v "polarity") (v "allocated-entries"))
      (v "rendered-entries")]
    (serialize <| a "tptp-fof-cnf-allocated:output" [
      a "tptp-fof-batch:output" [v "occurrence", v "polarity",
        v "skolem", v "cnf", v "source-entries"],
      v "first-name", v "next-name", v "allocated-entries"])
    (output
      (a "tptp-fof-cnf-allocated:output" [
        a "tptp-fof-batch:output" [v "occurrence", v "polarity",
          v "skolem", v "cnf", v "source-entries"],
        v "first-name", v "next-name", v "allocated-entries"])
      (v "polarity") (v "rendered-entries"))

def termRewrites : List RewriteRule := [
  termVariableRule, plainOriginalTermRule, definedOriginalTermRule,
  systemOriginalTermRule,
  numericTermRule "tptp-cnf-official-serialization:term-integer"
    "tptp-fof-symbol:function-integer" "tptp92-ast:number:alt-1"
    "tptp92-ast:token:integer",
  numericTermRule "tptp-cnf-official-serialization:term-rational"
    "tptp-fof-symbol:function-rational" "tptp92-ast:number:alt-2"
    "tptp92-ast:token:rational",
  numericTermRule "tptp-cnf-official-serialization:term-real"
    "tptp-fof-symbol:function-real" "tptp92-ast:number:alt-3"
    "tptp92-ast:token:real",
  distinctObjectTermRule, generatedTermRule]

def sequenceRewrites : List RewriteRule := [
  termsNilRule, termsConsRule, argumentsOneRule, argumentsMoreRule]

def termBuilderRewrites : List RewriteRule := [
  plainTermNullaryRule, plainTermAppliedRule,
  definedTermNullaryRule, definedTermAppliedRule,
  systemTermNullaryRule, systemTermAppliedRule]

def literalRewrites : List RewriteRule := [
  verumLiteralRule, falsumLiteralRule,
  originalPositiveLiteralRule, originalNegativeLiteralRule,
  equalLiteralRule, notEqualLiteralRule,
  definedPositiveLiteralRule, definedNegativeLiteralRule]

def atomicRewrites : List RewriteRule := [
  plainAtomicNullaryRule, plainAtomicAppliedRule, definedAtomicAppliedRule,
  systemAtomicNullaryRule, systemAtomicAppliedRule,
  plainAtomicBuilderNullaryRule, plainAtomicBuilderAppliedRule]

def clauseRewrites : List RewriteRule := [
  emptyClauseRule, clauseStartRule, clauseTailNilRule, clauseTailConsRule]

def batchRewrites : List RewriteRule := [
  entriesNilRule, entriesPositiveRule, entriesNegativeRule, startRule]

def rewrites : List RewriteRule :=
  termRewrites ++ sequenceRewrites ++ termBuilderRewrites ++
    literalRewrites ++ atomicRewrites ++ clauseRewrites ++ batchRewrites

/-! ## Combined signature and validation -/

def sourceAdditionalTypes : List TypeDecl :=
  TptpFofCnfAllocatedBatchLanguageDef.language.types.filter fun declaration =>
    declaration.name != "Integer" && declaration.name != "String"

def officialDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpOfficialAbstractSyntax.language {}

def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists
    (sourceAdditionalTypes ++ addedTypes)
    (TptpFofCnfAllocatedBatchLanguageDef.language.terms ++ localTerms)
    (some "TptpFofCnfOfficialSerializationV1")

def signatureDefinition : CalculusLanguageDef :=
  signatureExtension.apply officialDefinition

def signatureLanguage : LanguageDef := signatureDefinition.toLanguageDef

def language : LanguageDef := {
  signatureLanguage with rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := by
  rfl

private theorem addedTypesNodup :
    ((sourceAdditionalTypes ++ addedTypes).map (·.name)).Nodup := by
  decide +kernel

private theorem addedTypesDisjoint :
    List.Disjoint officialDefinition.typeNames
      ((sourceAdditionalTypes ++ addedTypes).map (·.name)) := by
  have officialNames : officialDefinition.typeNames.all
      (fun name => name == "Integer" || name == "String" ||
        name.startsWith "Tptp92Ast") = true := by
    simpa [officialDefinition] using
      TptpOfficialAbstractSyntax.typeNames_namespaced
  have addedNames : ((sourceAdditionalTypes ++ addedTypes).map (·.name)).all
      (fun name => !(name == "Integer") && !(name == "String") &&
        !(name.startsWith "Tptp92Ast")) = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro name officialMembership addedMembership
  have officialShape :=
    (List.all_eq_true.mp officialNames) name officialMembership
  have addedShape :=
    (List.all_eq_true.mp addedNames) name addedMembership
  simp at officialShape addedShape
  exact officialShape.elim
    (fun shared => shared.elim addedShape.1.1 addedShape.1.2)
    addedShape.2

private theorem addedTermsNodup :
    ((TptpFofCnfAllocatedBatchLanguageDef.language.terms ++ localTerms).map
      (·.label)).Nodup := by
  decide +kernel

private theorem addedTermsDisjoint :
    List.Disjoint (officialDefinition.terms.map (·.label))
      ((TptpFofCnfAllocatedBatchLanguageDef.language.terms ++ localTerms).map
        (·.label)) := by
  have officialNames : (officialDefinition.terms.map (·.label)).all
      (fun label => label.startsWith "tptp92-ast:") = true := by
    decide +kernel
  have addedNames :
      ((TptpFofCnfAllocatedBatchLanguageDef.language.terms ++ localTerms).map
        (·.label)).all
        (fun label => !(label.startsWith "tptp92-ast:")) = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label officialMembership addedMembership
  have officialShape :=
    (List.all_eq_true.mp officialNames) label officialMembership
  have addedShape :=
    (List.all_eq_true.mp addedNames) label addedMembership
  simp [officialShape] at addedShape

private theorem validateTerm_mono
    (source target : LanguageDef) (term : GrammarRule)
    (clean : source.validateTerm term = [])
    (typesMonotone : ∀ name ∈ source.typeNames, name ∈ target.typeNames) :
    target.validateTerm term = [] := by
  simp only [LanguageDef.validateTerm, List.append_eq_nil_iff] at clean ⊢
  refine ⟨⟨?_, ?_⟩, clean.2⟩
  · have sourceCategory : term.category ∈ source.typeNames := by
      by_contra missing
      simp [missing] at clean
    simp [typesMonotone term.category sourceCategory]
  · rw [List.flatMap_eq_nil_iff]
    intro parameter parameterMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMembership
    apply typesMonotone name
    have sourceParameterClean :=
      (List.flatMap_eq_nil_iff.mp clean.1.2) parameter parameterMembership
    exact LanguageDef.baseName_mem_of_validateTypeExpr_eq_nil
      source.typeNames s!"term {term.label}"
      (TermParam.typeExpr parameter) sourceParameterClean nameMembership

private theorem signatureLanguage_typeNames :
    signatureLanguage.typeNames =
      TptpOfficialAbstractSyntax.language.typeNames ++
        (sourceAdditionalTypes ++ addedTypes).map (·.name) := by
  simp [signatureLanguage, signatureDefinition, signatureExtension,
    officialDefinition, ConstructorSignatureExtension.ofLists,
    LanguageDef.typeNames]

private theorem sourceTypeMonotone (name : String)
    (membership : name ∈
      TptpFofCnfAllocatedBatchLanguageDef.language.typeNames) :
    name ∈ signatureLanguage.typeNames := by
  rw [signatureLanguage_typeNames]
  rw [LanguageDef.typeNames] at membership
  rcases List.mem_map.mp membership with
    ⟨declaration, declarationMembership, declarationName⟩
  subst name
  by_cases integer : declaration.name = "Integer"
  · apply List.mem_append_left
    simpa [integer] using
      (show "Integer" ∈ TptpOfficialAbstractSyntax.language.typeNames by
        decide +kernel)
  by_cases string : declaration.name = "String"
  · apply List.mem_append_left
    simpa [string] using
      (show "String" ∈ TptpOfficialAbstractSyntax.language.typeNames by
        decide +kernel)
  · apply List.mem_append_right
    rw [List.map_append]
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨declaration, by
      simp [sourceAdditionalTypes, declarationMembership, integer, string], rfl⟩

private theorem officialTypeMonotone (name : String)
    (membership : name ∈ TptpOfficialAbstractSyntax.language.typeNames) :
    name ∈ signatureLanguage.typeNames := by
  rw [signatureLanguage_typeNames]
  exact List.mem_append_left _ membership

private theorem addedTypeMonotone (name : String)
    (membership : name ∈ addedTypes.map (·.name)) :
    name ∈ signatureLanguage.typeNames := by
  rw [signatureLanguage_typeNames, List.map_append]
  exact List.mem_append_right _ (List.mem_append_right _ membership)

private def officialUsedTypeNames : List String := [
  "String",
  "Tptp92Ast:fof-term", "Tptp92Ast:name",
  "Tptp92Ast:annotated-formula", "Tptp92Ast:fof-arguments",
  "Tptp92Ast:functor", "Tptp92Ast:defined-functor",
  "Tptp92Ast:system-functor", "Tptp92Ast:cnf-literal",
  "Tptp92Ast:fof-atomic-formula", "Tptp92Ast:cnf-formula",
  "Tptp92Ast:cnf-disjunction", "Tptp92Ast:variable"]

private def sourceUsedTypeNames : List String := [
  "TptpFofBatch:ClauseId", "TptpFofCnf:Clause",
  "TptpFofCnfAllocated:Output", "TptpFofSkolem:Term",
  "TptpFofSkolem:Terms", "TptpFofNamed:Reference",
  "TptpFofSymbol:PredicateHead", "TptpFofBatch:Polarity",
  "TptpFofCnfAllocated:ClauseEntries",
  "TptpResolvedFof:Index", "TptpFofBatch:Occurrence", "TptpFofSkolem:Output",
  "TptpFofCnf:Output", "TptpFofBatch:ClauseEntries",
]

private def addedUsedTypeNames : List String := [
  "TptpFofCnfOfficialSerialization:RenderedTerms",
  "TptpFofCnfOfficialSerialization:Entry",
  "TptpFofCnfOfficialSerialization:Entries",
  "TptpFofCnfOfficialSerialization:Output"]

private def usedTypeNames : List String :=
  officialUsedTypeNames ++ sourceUsedTypeNames ++ addedUsedTypeNames

set_option maxRecDepth 10000 in
private theorem officialUsedTypeNamesPresentAll :
    officialUsedTypeNames.all (fun name =>
      decide (name ∈ TptpOfficialAbstractSyntax.language.typeNames)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem sourceUsedTypeNamesPresentAll :
    sourceUsedTypeNames.all (fun name => decide
      (name ∈ TptpFofCnfAllocatedBatchLanguageDef.language.typeNames)) =
        true := by
  decide +kernel

private theorem addedUsedTypeNamesPresentAll :
    addedUsedTypeNames.all (fun name =>
      decide (name ∈ addedTypes.map (·.name))) = true := by
  decide +kernel

private theorem usedTypeNamesPresent (name : String)
    (membership : name ∈ usedTypeNames) :
    name ∈ signatureLanguage.typeNames := by
  change name ∈
    officialUsedTypeNames ++ (sourceUsedTypeNames ++ addedUsedTypeNames)
    at membership
  simp only [List.mem_append] at membership
  rcases membership with
    (officialMembership | sourceMembership | addedMembership)
  · apply officialTypeMonotone name
    exact decide_eq_true_eq.mp
      ((List.all_eq_true.mp officialUsedTypeNamesPresentAll)
        name officialMembership)
  · apply sourceTypeMonotone name
    exact decide_eq_true_eq.mp
      ((List.all_eq_true.mp sourceUsedTypeNamesPresentAll)
        name sourceMembership)
  · apply addedTypeMonotone name
    exact decide_eq_true_eq.mp
      ((List.all_eq_true.mp addedUsedTypeNamesPresentAll)
        name addedMembership)

private def termTypeNames (term : GrammarRule) : List String :=
  term.category :: term.params.flatMap fun parameter =>
    (TermParam.typeExpr parameter).baseNames

private theorem localTermsUseOnlyDeclaredTypes :
    localTerms.all (fun term =>
      (termTypeNames term).all fun name => decide (name ∈ usedTypeNames)) =
        true := by
  decide +kernel

private theorem localTermsHaveEmptySyntax :
    localTerms.all (fun term => term.syntaxPattern == []) = true := by
  decide +kernel

private theorem localTermsValid (term : GrammarRule)
    (membership : term ∈ localTerms) :
    signatureLanguage.validateTerm term = [] := by
  have typeCheck := (List.all_eq_true.mp localTermsUseOnlyDeclaredTypes)
    term membership
  have syntaxCheck := (List.all_eq_true.mp localTermsHaveEmptySyntax)
    term membership
  have typeNamePresent (name : String)
      (nameMembership : name ∈ termTypeNames term) :
      name ∈ signatureLanguage.typeNames := by
    apply usedTypeNamesPresent name
    exact decide_eq_true_eq.mp
      ((List.all_eq_true.mp typeCheck) name nameMembership)
  simp only [LanguageDef.validateTerm, List.append_eq_nil_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [typeNamePresent term.category (by simp [termTypeNames])]
  · rw [List.flatMap_eq_nil_iff]
    intro parameter parameterMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMembership
    apply typeNamePresent name
    simp only [termTypeNames, List.mem_cons]
    right
    exact List.mem_flatMap.mpr
      ⟨parameter, parameterMembership, nameMembership⟩
  · have syntaxEmpty : term.syntaxPattern = [] :=
      beq_iff_eq.mp syntaxCheck
    simp [syntaxEmpty]

private theorem addedTermsValid (term : GrammarRule)
    (membership : term ∈
      TptpFofCnfAllocatedBatchLanguageDef.language.terms ++ localTerms) :
    signatureLanguage.validateTerm term = [] := by
  simp only [List.mem_append] at membership
  rcases membership with sourceMembership | localMembership
  · exact validateTerm_mono
      TptpFofCnfAllocatedBatchLanguageDef.language signatureLanguage term
      (LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
        TptpFofCnfAllocatedBatchLanguageDef.language
        TptpFofCnfAllocatedBatchLanguageDef.language_validate
        term sourceMembership)
      sourceTypeMonotone
  · exact localTermsValid term localMembership

theorem signatureLanguage_validate : signatureLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    officialDefinition (sourceAdditionalTypes ++ addedTypes)
    (TptpFofCnfAllocatedBatchLanguageDef.language.terms ++ localTerms)
    (some "TptpFofCnfOfficialSerializationV1")
  · exact TptpOfficialAbstractSyntax.language_validate
  · rfl
  · rfl
  · exact addedTypesNodup
  · exact addedTypesDisjoint
  · exact addedTermsNodup
  · exact addedTermsDisjoint
  · exact addedTermsValid

/-! ## Finite-support rewrite certification -/

private def rewritePatterns (rewrite : RewriteRule) : List Pattern :=
  [rewrite.left, rewrite.right] ++
    rewrite.premises.flatMap LanguageDef.premisePatterns

private def rewriteConstructorRefs (rewrite : RewriteRule) :
    List (String × Nat) :=
  (rewritePatterns rewrite).flatMap Pattern.constructorRefs

private def referencedConstructorSignatures : List (String × Nat) :=
  [
    ("tptp-cnf-official-serialization:term", 1),
    ("tptp-fof-skolem:term-variable", 1),
    ("tptp92-ast:fof-term:alt-2", 1),
    ("tptp-fof-skolem:term-original", 2),
    ("tptp-fof-symbol:function-plain", 1),
    ("tptp-cnf-official-serialization:terms", 1),
    ("tptp-cnf-official-serialization:plain-term", 2),
    ("tptp92-ast:functor:alt-1", 1),
    ("tptp92-ast:atomic-word:alt-2", 1),
    ("tptp92-ast:token:single-quoted", 1),
    ("tptp-fof-symbol:function-defined", 1),
    ("tptp-cnf-official-serialization:defined-term", 2),
    ("tptp92-ast:defined-functor:alt-1", 1),
    ("tptp92-ast:atomic-defined-word:alt-1", 1),
    ("tptp92-ast:token:dollar-word", 1),
    ("tptp-fof-symbol:function-system", 1),
    ("tptp-cnf-official-serialization:system-term", 2),
    ("tptp92-ast:system-functor:alt-1", 1),
    ("tptp92-ast:atomic-system-word:alt-1", 1),
    ("tptp92-ast:token:dollar-dollar-word", 1),
    ("tptp-fof-symbol:function-integer", 1),
    ("tptp-fof-skolem:terms-nil", 0),
    ("tptp92-ast:fof-term:alt-1", 1),
    ("tptp92-ast:fof-function-term:alt-2", 1),
    ("tptp92-ast:fof-defined-term:alt-1", 1),
    ("tptp92-ast:defined-term:alt-1", 1),
    ("tptp92-ast:number:alt-1", 1),
    ("tptp92-ast:token:integer", 1),
    ("tptp-fof-symbol:function-rational", 1),
    ("tptp92-ast:number:alt-2", 1),
    ("tptp92-ast:token:rational", 1),
    ("tptp-fof-symbol:function-real", 1),
    ("tptp92-ast:number:alt-3", 1),
    ("tptp92-ast:token:real", 1),
    ("tptp-fof-symbol:function-distinct-object", 1),
    ("tptp92-ast:defined-term:alt-2", 1),
    ("tptp92-ast:token:distinct-object", 1),
    ("tptp-fof-skolem:term-generated", 2),
    ("tptp-cnf-official-serialization:rendered-terms-nil", 0),
    ("tptp-fof-skolem:terms-cons", 2),
    ("tptp-cnf-official-serialization:rendered-terms-cons", 2),
    ("tptp-cnf-official-serialization:arguments", 1),
    ("tptp92-ast:fof-arguments:alt-1", 1),
    ("tptp92-ast:fof-arguments:alt-2", 2),
    ("tptp92-ast:fof-function-term:alt-1", 1),
    ("tptp92-ast:fof-plain-term:alt-1", 1),
    ("tptp92-ast:constant:alt-1", 1),
    ("tptp92-ast:fof-plain-term:alt-2", 2),
    ("tptp92-ast:fof-defined-term:alt-2", 1),
    ("tptp92-ast:fof-defined-atomic-term:alt-1", 1),
    ("tptp92-ast:fof-defined-plain-term:alt-1", 1),
    ("tptp92-ast:defined-constant:alt-1", 1),
    ("tptp92-ast:fof-defined-plain-term:alt-2", 2),
    ("tptp92-ast:fof-function-term:alt-3", 1),
    ("tptp92-ast:fof-system-term:alt-1", 1),
    ("tptp92-ast:system-constant:alt-1", 1),
    ("tptp92-ast:fof-system-term:alt-2", 2),
    ("tptp-cnf-official-serialization:literal", 1),
    ("tptp-fof-named:ref-verum", 0),
    ("tptp92-ast:cnf-literal:alt-1", 1),
    ("tptp92-ast:fof-atomic-formula:alt-2", 1),
    ("tptp92-ast:fof-defined-atomic-formula:alt-1", 1),
    ("tptp92-ast:fof-defined-plain-formula:alt-1", 1),
    ("$true", 0),
    ("tptp-fof-named:ref-falsum", 0),
    ("$false", 0),
    ("tptp-fof-named:ref-original-positive", 2),
    ("tptp-cnf-official-serialization:atomic", 2),
    ("tptp-fof-named:ref-original-negative", 2),
    ("tptp92-ast:cnf-literal:alt-2", 1),
    ("tptp-fof-named:ref-equal", 2),
    ("tptp92-ast:fof-defined-atomic-formula:alt-2", 1),
    ("tptp92-ast:fof-defined-infix-formula:alt-1", 3),
    ("tptp92-ast:defined-infix-pred:alt-1", 1),
    ("tptp92-ast:infix-equality:alt-1", 0),
    ("tptp-fof-named:ref-not-equal", 2),
    ("tptp92-ast:cnf-literal:alt-4", 1),
    ("tptp92-ast:fof-infix-unary:alt-1", 3),
    ("tptp92-ast:infix-inequality:alt-1", 0),
    ("tptp-fof-named:ref-defined-positive", 2),
    ("tptp-cnf-official-serialization:plain-atomic", 2),
    ("tptp-fof-named:ref-defined-negative", 2),
    ("tptp-fof-symbol:predicate-plain", 1),
    ("tptp92-ast:fof-atomic-formula:alt-1", 1),
    ("tptp92-ast:fof-plain-atomic-formula:alt-1", 1),
    ("tptp-fof-symbol:predicate-defined", 1),
    ("tptp-fof-symbol:predicate-system", 1),
    ("tptp92-ast:fof-atomic-formula:alt-3", 1),
    ("tptp92-ast:fof-system-atomic-formula:alt-1", 1),
    ("tptp-cnf-official-serialization:clause", 1),
    ("tptp-fof-cnf:clause-nil", 0),
    ("tptp92-ast:cnf-formula:alt-1", 1),
    ("tptp92-ast:cnf-disjunction:alt-1", 1),
    ("tptp-fof-cnf:clause-cons", 2),
    ("tptp-cnf-official-serialization:clause-tail", 2),
    ("tptp92-ast:cnf-disjunction:alt-2", 2),
    ("tptp-cnf-official-serialization:entries", 2),
    ("tptp-fof-cnf-allocated:entries-nil", 0),
    ("tptp-cnf-official-serialization:entries-nil", 0),
    ("tptp-fof-batch:positive", 0),
    ("tptp-fof-cnf-allocated:entries-cons", 2),
    ("tptp-fof-cnf-allocated:clause-entry", 3),
    ("tptp-fof-cnf-allocated:name", 1),
    ("tptp-cnf-official-serialization:entries-cons", 2),
    ("tptp-cnf-official-serialization:entry", 4),
    ("tptp92-ast:annotated-formula:alt-5", 1),
    ("tptp92-ast:cnf-annotated:alt-1", 4),
    ("tptp92-ast:formula-role:alt-1", 1),
    ("tptp92-ast:token:lower-word", 1),
    ("axiom", 0),
    ("tptp92-ast:annotations:alt-2", 0),
    ("tptp-fof-batch:negative", 0),
    ("negated_conjecture", 0),
    ("tptp-cnf-official-serialization:serialize", 1),
    ("tptp-fof-cnf-allocated:output", 4),
    ("tptp-fof-batch:output", 5),
    ("tptp-cnf-official-serialization:output", 3)
  ]

private def supportTerm (signature : String × Nat) : GrammarRule := {
  label := signature.1
  category := "String"
  params := List.replicate signature.2
    (.simple "argument" (.base "String"))
  syntaxPattern := []
  evalPolicy? := none
}

private def supportLanguage : LanguageDef := {
  name := "TptpFofCnfOfficialSerializationSupportV1"
  types := usedTypeNames.map TypeDecl.plain
  terms := referencedConstructorSignatures.map supportTerm
  equations := []
  rewrites := []
}

private def termSupportSignatures : List (String × Nat) := [
  ("tptp-cnf-official-serialization:term", 1),
  ("tptp-fof-skolem:term-variable", 1),
  ("tptp92-ast:fof-term:alt-2", 1),
  ("tptp-fof-skolem:term-original", 2),
  ("tptp-fof-symbol:function-plain", 1),
  ("tptp-cnf-official-serialization:terms", 1),
  ("tptp-cnf-official-serialization:plain-term", 2),
  ("tptp92-ast:functor:alt-1", 1),
  ("tptp92-ast:atomic-word:alt-2", 1),
  ("tptp92-ast:token:single-quoted", 1),
  ("tptp-fof-symbol:function-defined", 1),
  ("tptp-cnf-official-serialization:defined-term", 2),
  ("tptp92-ast:defined-functor:alt-1", 1),
  ("tptp92-ast:atomic-defined-word:alt-1", 1),
  ("tptp92-ast:token:dollar-word", 1),
  ("tptp-fof-symbol:function-system", 1),
  ("tptp-cnf-official-serialization:system-term", 2),
  ("tptp92-ast:system-functor:alt-1", 1),
  ("tptp92-ast:atomic-system-word:alt-1", 1),
  ("tptp92-ast:token:dollar-dollar-word", 1),
  ("tptp-fof-symbol:function-integer", 1),
  ("tptp-fof-skolem:terms-nil", 0),
  ("tptp92-ast:fof-term:alt-1", 1),
  ("tptp92-ast:fof-function-term:alt-2", 1),
  ("tptp92-ast:fof-defined-term:alt-1", 1),
  ("tptp92-ast:defined-term:alt-1", 1),
  ("tptp92-ast:number:alt-1", 1),
  ("tptp92-ast:token:integer", 1),
  ("tptp-fof-symbol:function-rational", 1),
  ("tptp92-ast:number:alt-2", 1),
  ("tptp92-ast:token:rational", 1),
  ("tptp-fof-symbol:function-real", 1),
  ("tptp92-ast:number:alt-3", 1),
  ("tptp92-ast:token:real", 1),
  ("tptp-fof-symbol:function-distinct-object", 1),
  ("tptp92-ast:defined-term:alt-2", 1),
  ("tptp92-ast:token:distinct-object", 1),
  ("tptp-fof-skolem:term-generated", 2)]

private def sequenceSupportSignatures : List (String × Nat) := [
  ("tptp-cnf-official-serialization:terms", 1),
  ("tptp-fof-skolem:terms-nil", 0),
  ("tptp-cnf-official-serialization:rendered-terms-nil", 0),
  ("tptp-fof-skolem:terms-cons", 2),
  ("tptp-cnf-official-serialization:rendered-terms-cons", 2),
  ("tptp-cnf-official-serialization:term", 1),
  ("tptp-cnf-official-serialization:arguments", 1),
  ("tptp92-ast:fof-arguments:alt-1", 1),
  ("tptp92-ast:fof-arguments:alt-2", 2)]

private def termBuilderSupportSignatures : List (String × Nat) := [
  ("tptp-cnf-official-serialization:plain-term", 2),
  ("tptp-cnf-official-serialization:rendered-terms-nil", 0),
  ("tptp92-ast:fof-term:alt-1", 1),
  ("tptp92-ast:fof-function-term:alt-1", 1),
  ("tptp92-ast:fof-plain-term:alt-1", 1),
  ("tptp92-ast:constant:alt-1", 1),
  ("tptp-cnf-official-serialization:rendered-terms-cons", 2),
  ("tptp92-ast:fof-plain-term:alt-2", 2),
  ("tptp-cnf-official-serialization:arguments", 1),
  ("tptp-cnf-official-serialization:defined-term", 2),
  ("tptp92-ast:fof-function-term:alt-2", 1),
  ("tptp92-ast:fof-defined-term:alt-2", 1),
  ("tptp92-ast:fof-defined-atomic-term:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-term:alt-1", 1),
  ("tptp92-ast:defined-constant:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-term:alt-2", 2),
  ("tptp-cnf-official-serialization:system-term", 2),
  ("tptp92-ast:fof-function-term:alt-3", 1),
  ("tptp92-ast:fof-system-term:alt-1", 1),
  ("tptp92-ast:system-constant:alt-1", 1),
  ("tptp92-ast:fof-system-term:alt-2", 2)]

private def literalSupportSignatures : List (String × Nat) := [
  ("tptp-cnf-official-serialization:literal", 1),
  ("tptp-fof-named:ref-verum", 0),
  ("tptp92-ast:cnf-literal:alt-1", 1),
  ("tptp92-ast:fof-atomic-formula:alt-2", 1),
  ("tptp92-ast:fof-defined-atomic-formula:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-formula:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-term:alt-1", 1),
  ("tptp92-ast:defined-constant:alt-1", 1),
  ("tptp92-ast:defined-functor:alt-1", 1),
  ("tptp92-ast:atomic-defined-word:alt-1", 1),
  ("tptp92-ast:token:dollar-word", 1),
  ("$true", 0),
  ("tptp-fof-named:ref-falsum", 0),
  ("$false", 0),
  ("tptp-fof-named:ref-original-positive", 2),
  ("tptp-cnf-official-serialization:terms", 1),
  ("tptp-cnf-official-serialization:atomic", 2),
  ("tptp-fof-named:ref-original-negative", 2),
  ("tptp92-ast:cnf-literal:alt-2", 1),
  ("tptp-fof-named:ref-equal", 2),
  ("tptp92-ast:fof-defined-atomic-formula:alt-2", 1),
  ("tptp92-ast:fof-defined-infix-formula:alt-1", 3),
  ("tptp92-ast:defined-infix-pred:alt-1", 1),
  ("tptp92-ast:infix-equality:alt-1", 0),
  ("tptp-cnf-official-serialization:term", 1),
  ("tptp-fof-named:ref-not-equal", 2),
  ("tptp92-ast:cnf-literal:alt-4", 1),
  ("tptp92-ast:fof-infix-unary:alt-1", 3),
  ("tptp92-ast:infix-inequality:alt-1", 0),
  ("tptp-fof-named:ref-defined-positive", 2),
  ("tptp-cnf-official-serialization:plain-atomic", 2),
  ("tptp-fof-named:ref-defined-negative", 2)]

private def atomicSupportSignatures : List (String × Nat) := [
  ("tptp-cnf-official-serialization:atomic", 2),
  ("tptp-fof-symbol:predicate-plain", 1),
  ("tptp-cnf-official-serialization:rendered-terms-nil", 0),
  ("tptp92-ast:fof-atomic-formula:alt-1", 1),
  ("tptp92-ast:fof-plain-atomic-formula:alt-1", 1),
  ("tptp92-ast:fof-plain-term:alt-1", 1),
  ("tptp92-ast:constant:alt-1", 1),
  ("tptp92-ast:functor:alt-1", 1),
  ("tptp92-ast:atomic-word:alt-2", 1),
  ("tptp92-ast:token:single-quoted", 1),
  ("tptp-cnf-official-serialization:rendered-terms-cons", 2),
  ("tptp92-ast:fof-plain-term:alt-2", 2),
  ("tptp-cnf-official-serialization:arguments", 1),
  ("tptp-fof-symbol:predicate-defined", 1),
  ("tptp92-ast:fof-atomic-formula:alt-2", 1),
  ("tptp92-ast:fof-defined-atomic-formula:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-formula:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-term:alt-2", 2),
  ("tptp92-ast:defined-functor:alt-1", 1),
  ("tptp92-ast:atomic-defined-word:alt-1", 1),
  ("tptp92-ast:token:dollar-word", 1),
  ("tptp-fof-symbol:predicate-system", 1),
  ("tptp92-ast:fof-atomic-formula:alt-3", 1),
  ("tptp92-ast:fof-system-atomic-formula:alt-1", 1),
  ("tptp92-ast:fof-system-term:alt-1", 1),
  ("tptp92-ast:system-constant:alt-1", 1),
  ("tptp92-ast:system-functor:alt-1", 1),
  ("tptp92-ast:atomic-system-word:alt-1", 1),
  ("tptp92-ast:token:dollar-dollar-word", 1),
  ("tptp92-ast:fof-system-term:alt-2", 2),
  ("tptp-cnf-official-serialization:plain-atomic", 2)]

private def clauseSupportSignatures : List (String × Nat) := [
  ("tptp-cnf-official-serialization:clause", 1),
  ("tptp-fof-cnf:clause-nil", 0),
  ("tptp92-ast:cnf-formula:alt-1", 1),
  ("tptp92-ast:cnf-disjunction:alt-1", 1),
  ("tptp92-ast:cnf-literal:alt-1", 1),
  ("tptp92-ast:fof-atomic-formula:alt-2", 1),
  ("tptp92-ast:fof-defined-atomic-formula:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-formula:alt-1", 1),
  ("tptp92-ast:fof-defined-plain-term:alt-1", 1),
  ("tptp92-ast:defined-constant:alt-1", 1),
  ("tptp92-ast:defined-functor:alt-1", 1),
  ("tptp92-ast:atomic-defined-word:alt-1", 1),
  ("tptp92-ast:token:dollar-word", 1),
  ("$false", 0),
  ("tptp-fof-cnf:clause-cons", 2),
  ("tptp-cnf-official-serialization:literal", 1),
  ("tptp-cnf-official-serialization:clause-tail", 2),
  ("tptp92-ast:cnf-disjunction:alt-2", 2)]

private def batchSupportSignatures : List (String × Nat) := [
  ("tptp-cnf-official-serialization:entries", 2),
  ("tptp-fof-cnf-allocated:entries-nil", 0),
  ("tptp-cnf-official-serialization:entries-nil", 0),
  ("tptp-fof-batch:positive", 0),
  ("tptp-fof-cnf-allocated:entries-cons", 2),
  ("tptp-fof-cnf-allocated:clause-entry", 3),
  ("tptp-fof-cnf-allocated:name", 1),
  ("tptp-cnf-official-serialization:entries-cons", 2),
  ("tptp-cnf-official-serialization:entry", 4),
  ("tptp92-ast:annotated-formula:alt-5", 1),
  ("tptp92-ast:cnf-annotated:alt-1", 4),
  ("tptp92-ast:formula-role:alt-1", 1),
  ("tptp92-ast:token:lower-word", 1),
  ("axiom", 0),
  ("tptp92-ast:annotations:alt-2", 0),
  ("tptp-cnf-official-serialization:clause", 1),
  ("tptp-fof-batch:negative", 0),
  ("negated_conjecture", 0),
  ("tptp-cnf-official-serialization:serialize", 1),
  ("tptp-fof-cnf-allocated:output", 4),
  ("tptp-fof-batch:output", 5),
  ("tptp-cnf-official-serialization:output", 3)]

private def supportLanguageFor (name : String)
    (signatures : List (String × Nat)) : LanguageDef := {
  name
  types := usedTypeNames.map TypeDecl.plain
  terms := signatures.map supportTerm
  equations := []
  rewrites := []
}

private def termSupportLanguage : LanguageDef :=
  supportLanguageFor "TptpFofCnfOfficialSerializationTermSupportV1"
    termSupportSignatures

private def sequenceSupportLanguage : LanguageDef :=
  supportLanguageFor "TptpFofCnfOfficialSerializationSequenceSupportV1"
    sequenceSupportSignatures

private def termBuilderSupportLanguage : LanguageDef :=
  supportLanguageFor "TptpFofCnfOfficialSerializationTermBuilderSupportV1"
    termBuilderSupportSignatures

private def literalSupportLanguage : LanguageDef :=
  supportLanguageFor "TptpFofCnfOfficialSerializationLiteralSupportV1"
    literalSupportSignatures

private def atomicSupportLanguage : LanguageDef :=
  supportLanguageFor "TptpFofCnfOfficialSerializationAtomicSupportV1"
    atomicSupportSignatures

private def clauseSupportLanguage : LanguageDef :=
  supportLanguageFor "TptpFofCnfOfficialSerializationClauseSupportV1"
    clauseSupportSignatures

private def batchSupportLanguage : LanguageDef :=
  supportLanguageFor "TptpFofCnfOfficialSerializationBatchSupportV1"
    batchSupportSignatures

@[simp] private theorem supportLanguageFor_typeNames
    (name : String) (signatures : List (String × Nat)) :
    (supportLanguageFor name signatures).typeNames = usedTypeNames := by
  rfl

@[simp] private theorem supportLanguageFor_constructorSignatures
    (name : String) (signatures : List (String × Nat)) :
    RewriteValidationCertificate.constructorSignatures
        (supportLanguageFor name signatures) = signatures := by
  simp [RewriteValidationCertificate.constructorSignatures,
    supportLanguageFor, supportTerm, List.map_map, Function.comp_def]

@[simp] private theorem supportLanguageFor_constructorLabels
    (name : String) (signatures : List (String × Nat)) :
    RewriteValidationCertificate.constructorLabels
        (supportLanguageFor name signatures) = signatures.map Prod.fst := by
  simp [RewriteValidationCertificate.constructorLabels,
    supportLanguageFor, supportTerm, List.map_map, Function.comp_def]

@[simp] private theorem supportLanguage_typeNames :
    supportLanguage.typeNames = usedTypeNames := by
  rfl

@[simp] private theorem supportLanguage_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures supportLanguage =
      referencedConstructorSignatures := by
  simp [RewriteValidationCertificate.constructorSignatures,
    supportLanguage, supportTerm, List.map_map, Function.comp_def]

@[simp] private theorem supportLanguage_constructorLabels :
    RewriteValidationCertificate.constructorLabels supportLanguage =
      referencedConstructorSignatures.map Prod.fst := by
  simp [RewriteValidationCertificate.constructorLabels,
    supportLanguage, supportTerm, List.map_map, Function.comp_def]

local macro "reduce_serialization_rows" : tactic =>
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
      Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames,
      supportLanguage_typeNames, supportLanguage_constructorSignatures,
      supportLanguage_constructorLabels, referencedConstructorSignatures,
      rewriteConstructorRefs, rewritePatterns, rewrites, termRewrites,
      sequenceRewrites, termBuilderRewrites, literalRewrites,
      atomicRewrites, clauseRewrites, batchRewrites,
      termSupportLanguage, sequenceSupportLanguage,
      termBuilderSupportLanguage, literalSupportLanguage,
      atomicSupportLanguage, clauseSupportLanguage, batchSupportLanguage,
      termSupportSignatures, sequenceSupportSignatures,
      termBuilderSupportSignatures, literalSupportSignatures,
      atomicSupportSignatures, clauseSupportSignatures,
      batchSupportSignatures, usedTypeNames, officialUsedTypeNames,
      sourceUsedTypeNames, addedUsedTypeNames,
      termVariableRule, originalTermRule, generatedTermRule,
      numericTermRule, distinctObjectTermRule, termsNilRule, termsConsRule,
      argumentsOneRule, argumentsMoreRule, nullaryBuilderRule,
      appliedBuilderRule, plainOriginalTermRule, definedOriginalTermRule,
      systemOriginalTermRule, plainTermNullaryRule, plainTermAppliedRule,
      definedTermNullaryRule, definedTermAppliedRule,
      systemTermNullaryRule, systemTermAppliedRule, truthLiteralRule,
      originalLiteralRule, equalityLiteralRule, generatedLiteralRule,
      atomicRule, atomicNullaryRule, plainAtomicNullaryRule,
      plainAtomicAppliedRule, definedAtomicAppliedRule,
      systemAtomicNullaryRule, systemAtomicAppliedRule,
      plainAtomicBuilderNullaryRule, plainAtomicBuilderAppliedRule,
      verumLiteralRule, falsumLiteralRule, originalPositiveLiteralRule,
      originalNegativeLiteralRule, equalLiteralRule, notEqualLiteralRule,
      definedPositiveLiteralRule, definedNegativeLiteralRule,
      emptyClauseRule, clauseStartRule, clauseTailNilRule,
      clauseTailConsRule, entriesNilRule, entriesConsRule,
      entriesPositiveRule, entriesNegativeRule, startRule,
      mkRule, typed, congruence, relation,
      renderedTermsNil, renderedTermsCons, serializedEntry,
      serializedEntriesNil, serializedEntriesCons, output, serialize,
      serializeTerm, serializeTerms, serializeArguments, plainTermBuilder,
      definedTermBuilder, systemTermBuilder, serializeLiteral,
      serializeAtomic, plainAtomicBuilder, serializeClause,
      serializeClauseTail, serializeEntries, quotedAtomicWord, plainFunctor,
      definedFunctorAst, systemFunctorAst, plainConstantTerm,
      plainAppliedTerm, definedConstantTerm, definedAppliedTerm,
      systemConstantTerm, systemAppliedTerm, numericTerm,
      distinctObjectTerm, plainConstantAtomic, plainAppliedAtomic,
      definedAppliedAtomic, systemConstantAtomic, systemAppliedAtomic,
      truthAtomic, equalityAtomic, positiveLiteral, negativeLiteral,
      inequalityLiteral, oneDisjunction, moreDisjunction, cnfFormula,
      formulaRole, annotatedCnf, a, v,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames])

set_option maxRecDepth 10000 in
private theorem termVariableSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      termVariableRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem plainOriginalTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      plainOriginalTermRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem definedOriginalTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      definedOriginalTermRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem systemOriginalTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      systemOriginalTermRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem integerTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      (numericTermRule "tptp-cnf-official-serialization:term-integer"
        "tptp-fof-symbol:function-integer" "tptp92-ast:number:alt-1"
        "tptp92-ast:token:integer") = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem rationalTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      (numericTermRule "tptp-cnf-official-serialization:term-rational"
        "tptp-fof-symbol:function-rational" "tptp92-ast:number:alt-2"
        "tptp92-ast:token:rational") = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem realTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      (numericTermRule "tptp-cnf-official-serialization:term-real"
        "tptp-fof-symbol:function-real" "tptp92-ast:number:alt-3"
        "tptp92-ast:token:real") = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem distinctObjectTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      distinctObjectTermRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem generatedTermSupportCheck :
    RewriteValidationCertificate.check termSupportLanguage
      generatedTermRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem termSupportChecks :
    termRewrites.all (fun rewrite =>
      RewriteValidationCertificate.check termSupportLanguage rewrite) = true := by
  simp [termRewrites, termVariableSupportCheck,
    plainOriginalTermSupportCheck, definedOriginalTermSupportCheck,
    systemOriginalTermSupportCheck, integerTermSupportCheck,
    rationalTermSupportCheck, realTermSupportCheck,
    distinctObjectTermSupportCheck, generatedTermSupportCheck]

set_option maxRecDepth 10000 in
private theorem sequenceSupportChecks :
    sequenceRewrites.all (fun rewrite =>
      RewriteValidationCertificate.check sequenceSupportLanguage rewrite) = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem termBuilderSupportChecks :
    termBuilderRewrites.all (fun rewrite =>
      RewriteValidationCertificate.check termBuilderSupportLanguage rewrite) = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem verumLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      verumLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem falsumLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      falsumLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem originalPositiveLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      originalPositiveLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem originalNegativeLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      originalNegativeLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem equalLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      equalLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem notEqualLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      notEqualLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem definedPositiveLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      definedPositiveLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem definedNegativeLiteralSupportCheck :
    RewriteValidationCertificate.check literalSupportLanguage
      definedNegativeLiteralRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem literalSupportChecks :
    literalRewrites.all (fun rewrite =>
      RewriteValidationCertificate.check literalSupportLanguage rewrite) = true := by
  simp [literalRewrites, verumLiteralSupportCheck,
    falsumLiteralSupportCheck, originalPositiveLiteralSupportCheck,
    originalNegativeLiteralSupportCheck, equalLiteralSupportCheck,
    notEqualLiteralSupportCheck, definedPositiveLiteralSupportCheck,
    definedNegativeLiteralSupportCheck]

set_option maxRecDepth 10000 in
private theorem atomicSupportChecks :
    atomicRewrites.all (fun rewrite =>
      RewriteValidationCertificate.check atomicSupportLanguage rewrite) = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem clauseSupportChecks :
    clauseRewrites.all (fun rewrite =>
      RewriteValidationCertificate.check clauseSupportLanguage rewrite) = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem entriesNilSupportCheck :
    RewriteValidationCertificate.check batchSupportLanguage
      entriesNilRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem entriesPositiveSupportCheck :
    RewriteValidationCertificate.check batchSupportLanguage
      entriesPositiveRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem entriesNegativeSupportCheck :
    RewriteValidationCertificate.check batchSupportLanguage
      entriesNegativeRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem startSupportCheck :
    RewriteValidationCertificate.check batchSupportLanguage
      startRule = true := by
  reduce_serialization_rows

set_option maxRecDepth 10000 in
private theorem batchSupportChecks :
    batchRewrites.all (fun rewrite =>
      RewriteValidationCertificate.check batchSupportLanguage rewrite) = true := by
  simp [batchRewrites, entriesNilSupportCheck,
    entriesPositiveSupportCheck, entriesNegativeSupportCheck,
    startSupportCheck]

private def schemaNameUniverse : List String :=
  ["index", "variable", "lexeme", "source-terms", "target",
   "rendered-terms", "identity", "functor", "head", "tail",
   "rendered-head", "rendered-tail", "tail-head", "arguments",
   "relation", "atomic", "left", "right", "rendered-left",
   "rendered-right", "literal", "accumulator", "polarity",
   "name-index", "clause", "rest", "name", "formula", "rendered-rest",
   "occurrence", "skolem", "cnf", "source-entries", "first-name",
   "next-name", "allocated-entries", "rendered-entries"]

set_option maxRecDepth 10000 in
private theorem termSchemaNamesRecorded :
    termRewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  reduce_serialization_rows
  all_goals simp [schemaNameUniverse]
  all_goals aesop

set_option maxRecDepth 10000 in
private theorem sequenceSchemaNamesRecorded :
    sequenceRewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  reduce_serialization_rows
  all_goals simp [schemaNameUniverse]
  all_goals aesop

set_option maxRecDepth 10000 in
private theorem termBuilderSchemaNamesRecorded :
    termBuilderRewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  reduce_serialization_rows
  all_goals simp [schemaNameUniverse]
  all_goals aesop

set_option maxRecDepth 10000 in
private theorem literalSchemaNamesRecorded :
    literalRewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  reduce_serialization_rows
  all_goals simp [schemaNameUniverse]
  all_goals aesop

set_option maxRecDepth 10000 in
private theorem atomicSchemaNamesRecorded :
    atomicRewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  reduce_serialization_rows
  all_goals simp [schemaNameUniverse]
  all_goals aesop

set_option maxRecDepth 10000 in
private theorem clauseSchemaNamesRecorded :
    clauseRewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  reduce_serialization_rows
  all_goals simp [schemaNameUniverse]
  all_goals aesop

set_option maxRecDepth 10000 in
private theorem batchSchemaNamesRecorded :
    batchRewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  reduce_serialization_rows
  all_goals simp [schemaNameUniverse]
  all_goals aesop

private theorem schemaNamesRecordedAll :
    rewrites.all (fun rewrite =>
      (Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.schemaNames
        rewrite).all (fun name => decide (name ∈ schemaNameUniverse))) = true := by
  simp [rewrites, termSchemaNamesRecorded, sequenceSchemaNamesRecorded,
    termBuilderSchemaNamesRecorded, literalSchemaNamesRecorded,
    atomicSchemaNamesRecorded, clauseSchemaNamesRecorded,
    batchSchemaNamesRecorded]

set_option maxRecDepth 10000 in
private theorem referencedConstructorsDeclaredAll :
    referencedConstructorSignatures.all (fun signature =>
      decide (signature ∈
        RewriteValidationCertificate.constructorSignatures language)) =
      true := by
  decide +kernel

private theorem termSupportSignaturesCovered :
    termSupportSignatures.all (fun signature =>
      decide (signature ∈ referencedConstructorSignatures)) = true := by
  decide +kernel

private theorem sequenceSupportSignaturesCovered :
    sequenceSupportSignatures.all (fun signature =>
      decide (signature ∈ referencedConstructorSignatures)) = true := by
  decide +kernel

private theorem termBuilderSupportSignaturesCovered :
    termBuilderSupportSignatures.all (fun signature =>
      decide (signature ∈ referencedConstructorSignatures)) = true := by
  decide +kernel

private theorem literalSupportSignaturesCovered :
    literalSupportSignatures.all (fun signature =>
      decide (signature ∈ referencedConstructorSignatures)) = true := by
  decide +kernel

private theorem atomicSupportSignaturesCovered :
    atomicSupportSignatures.all (fun signature =>
      decide (signature ∈ referencedConstructorSignatures)) = true := by
  decide +kernel

private theorem clauseSupportSignaturesCovered :
    clauseSupportSignatures.all (fun signature =>
      decide (signature ∈ referencedConstructorSignatures)) = true := by
  decide +kernel

private theorem batchSupportSignaturesCovered :
    batchSupportSignatures.all (fun signature =>
      decide (signature ∈ referencedConstructorSignatures)) = true := by
  decide +kernel

private def targetConstructorClass (name : String) : Bool :=
  name.startsWith "tptp92-ast:" || name.startsWith "tptp-" ||
    name == "axiom" || name == "negated_conjecture" ||
      name == "$true" || name == "$false"

private theorem addedConstructorLabelsClassified :
    ((TptpFofCnfAllocatedBatchLanguageDef.language.terms ++ localTerms).map
      (·.label)).all targetConstructorClass = true := by
  decide +kernel

private theorem targetConstructorLabelsClassified :
    (RewriteValidationCertificate.constructorLabels language).all
      targetConstructorClass = true := by
  rw [List.all_eq_true]
  intro label membership
  have split :
      label ∈ TptpOfficialAbstractSyntax.language.terms.map (·.label) ∨
      label ∈
        (TptpFofCnfAllocatedBatchLanguageDef.language.terms ++
          localTerms).map (·.label) := by
    simpa [RewriteValidationCertificate.constructorLabels, language,
      signatureLanguage, signatureDefinition, signatureExtension,
      officialDefinition, ConstructorSignatureExtension.ofLists,
      List.map_append] using membership
  rcases split with officialMembership | addedMembership
  · have namespaced := (List.all_eq_true.mp
      TptpOfficialAbstractSyntax.constructorLabels_namespaced)
      label officialMembership
    simp [targetConstructorClass, namespaced]
  · exact (List.all_eq_true.mp addedConstructorLabelsClassified)
      label addedMembership

set_option maxRecDepth 10000 in
private theorem schemaNamesOutsideTargetClass :
    schemaNameUniverse.all (fun name => !targetConstructorClass name) = true := by
  decide +kernel

private theorem schemaNameAvoidsTarget (name : String)
    (membership : name ∈ schemaNameUniverse) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro constructorMembership
  have classified := (List.all_eq_true.mp
    targetConstructorLabelsClassified) name constructorMembership
  have outside := (List.all_eq_true.mp schemaNamesOutsideTargetClass)
    name membership
  simp [classified] at outside

private theorem certificateFromSupport
    (support : LanguageDef) (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites)
    (checked : RewriteValidationCertificate.check support rewrite = true)
    (supportTypes : support.typeNames = usedTypeNames)
    (supportSignatures : ∀ signature ∈
      RewriteValidationCertificate.constructorSignatures support,
      signature ∈ referencedConstructorSignatures) :
    RewriteValidationCertificate.Certificate language rewrite := by
  have supportCertificate :=
    RewriteValidationCertificate.certificate_of_check checked
  apply
    Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension.Certificate.embed
      supportCertificate
  refine {
    typeNames := ?_
    signatures := ?_
    avoidsSchema := ?_ }
  · intro name nameMembership
    rw [supportTypes] at nameMembership
    exact usedTypeNamesPresent name nameMembership
  · intro signature signatureMembership
    exact decide_eq_true_eq.mp
      ((List.all_eq_true.mp referencedConstructorsDeclaredAll) signature
        (supportSignatures signature signatureMembership))
  · intro name nameMembership
    apply schemaNameAvoidsTarget name
    have recorded := (List.all_eq_true.mp schemaNamesRecordedAll)
      rewrite membership
    exact decide_eq_true_eq.mp
      ((List.all_eq_true.mp recorded) name nameMembership)

private theorem rewritesMembershipCases (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    rewrite ∈ termRewrites ∨ rewrite ∈ sequenceRewrites ∨
      rewrite ∈ termBuilderRewrites ∨ rewrite ∈ literalRewrites ∨
      rewrite ∈ atomicRewrites ∨ rewrite ∈ clauseRewrites ∨
      rewrite ∈ batchRewrites := by
  rw [rewrites] at membership
  rcases List.mem_append.mp membership with membership | batchMembership
  · rcases List.mem_append.mp membership with membership | clauseMembership
    · rcases List.mem_append.mp membership with membership | atomicMembership
      · rcases List.mem_append.mp membership with membership | literalMembership
        · rcases List.mem_append.mp membership with membership |
            termBuilderMembership
          · rcases List.mem_append.mp membership with termMembership |
              sequenceMembership
            · exact Or.inl termMembership
            · exact Or.inr (Or.inl sequenceMembership)
          · exact Or.inr (Or.inr (Or.inl termBuilderMembership))
        · exact Or.inr (Or.inr (Or.inr (Or.inl literalMembership)))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl atomicMembership))))
    · exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl clauseMembership)))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr batchMembership)))))

private theorem rewritesValid (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    language.validateRewrite rewrite = [] := by
  have fullMembership : rewrite ∈ rewrites := membership
  have targetCertificate :
      RewriteValidationCertificate.Certificate language rewrite := by
    rcases rewritesMembershipCases rewrite membership with
      termMembership | sequenceMembership |
      termBuilderMembership | literalMembership | atomicMembership |
      clauseMembership | batchMembership
    · apply certificateFromSupport termSupportLanguage rewrite fullMembership
        ((List.all_eq_true.mp termSupportChecks) rewrite termMembership)
      · rfl
      · intro signature signatureMembership
        have signatureMembership' : signature ∈ termSupportSignatures := by
          simpa [termSupportLanguage] using signatureMembership
        exact decide_eq_true_eq.mp
          ((List.all_eq_true.mp termSupportSignaturesCovered)
            signature signatureMembership')
    · apply certificateFromSupport sequenceSupportLanguage rewrite fullMembership
        ((List.all_eq_true.mp sequenceSupportChecks) rewrite
          sequenceMembership)
      · rfl
      · intro signature signatureMembership
        have signatureMembership' : signature ∈ sequenceSupportSignatures := by
          simpa [sequenceSupportLanguage] using signatureMembership
        exact decide_eq_true_eq.mp
          ((List.all_eq_true.mp sequenceSupportSignaturesCovered)
            signature signatureMembership')
    · apply certificateFromSupport termBuilderSupportLanguage rewrite
        fullMembership
        ((List.all_eq_true.mp termBuilderSupportChecks) rewrite
          termBuilderMembership)
      · rfl
      · intro signature signatureMembership
        have signatureMembership' : signature ∈ termBuilderSupportSignatures := by
          simpa [termBuilderSupportLanguage] using signatureMembership
        exact decide_eq_true_eq.mp
          ((List.all_eq_true.mp termBuilderSupportSignaturesCovered)
            signature signatureMembership')
    · apply certificateFromSupport literalSupportLanguage rewrite fullMembership
        ((List.all_eq_true.mp literalSupportChecks) rewrite literalMembership)
      · rfl
      · intro signature signatureMembership
        have signatureMembership' : signature ∈ literalSupportSignatures := by
          simpa [literalSupportLanguage] using signatureMembership
        exact decide_eq_true_eq.mp
          ((List.all_eq_true.mp literalSupportSignaturesCovered)
            signature signatureMembership')
    · apply certificateFromSupport atomicSupportLanguage rewrite fullMembership
        ((List.all_eq_true.mp atomicSupportChecks) rewrite atomicMembership)
      · rfl
      · intro signature signatureMembership
        have signatureMembership' : signature ∈ atomicSupportSignatures := by
          simpa [atomicSupportLanguage] using signatureMembership
        exact decide_eq_true_eq.mp
          ((List.all_eq_true.mp atomicSupportSignaturesCovered)
            signature signatureMembership')
    · apply certificateFromSupport clauseSupportLanguage rewrite fullMembership
        ((List.all_eq_true.mp clauseSupportChecks) rewrite clauseMembership)
      · rfl
      · intro signature signatureMembership
        have signatureMembership' : signature ∈ clauseSupportSignatures := by
          simpa [clauseSupportLanguage] using signatureMembership
        exact decide_eq_true_eq.mp
          ((List.all_eq_true.mp clauseSupportSignaturesCovered)
            signature signatureMembership')
    · apply certificateFromSupport batchSupportLanguage rewrite fullMembership
        ((List.all_eq_true.mp batchSupportChecks) rewrite batchMembership)
      · rfl
      · intro signature signatureMembership
        have signatureMembership' : signature ∈ batchSupportSignatures := by
          simpa [batchSupportLanguage] using signatureMembership
        exact decide_eq_true_eq.mp
          ((List.all_eq_true.mp batchSupportSignaturesCovered)
            signature signatureMembership')
  exact RewriteValidationCertificate.validateRewrite_eq_nil
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil signatureLanguage
      signatureLanguage_validate)
    targetCertificate

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact LanguageDef.equationNames_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · decide +kernel
  · intro term membership
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate term membership
  · intro equation membership
    exact LanguageDef.validateEquation_eq_nil_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate equation membership
  · exact rewritesValid

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

theorem source_types_are_present :
    ∀ name ∈ TptpFofCnfAllocatedBatchLanguageDef.language.typeNames,
      name ∈ language.typeNames := by
  intro name membership
  exact sourceTypeMonotone name membership

theorem official_types_are_prefix :
    TptpOfficialAbstractSyntax.language.types.IsPrefix language.types := by
  simp [language, signatureLanguage, signatureDefinition,
    signatureExtension, officialDefinition,
    ConstructorSignatureExtension.ofLists]

theorem rewrite_names_nodup : (rewrites.map (·.name)).Nodup := by
  decide +kernel

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

theorem wire_isSome : (CanonicalWire.renderLanguage? language).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact language_supported

def wire : String := (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit := IO.FS.writeFile path wire

#print axioms signatureLanguage_validate
#print axioms language_validate
#print axioms source_types_are_present
#print axioms official_types_are_prefix
#print axioms rewrite_names_nodup
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationLanguageDef
