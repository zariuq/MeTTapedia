import Mettapedia.GSLT.LanguageDef.TptpFofSkolemLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfSemantics
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT

/-!
# Canonical evidence-bearing definitional CNF carrier

This inert LanguageDef extends Skolem FOF with two explicit intermediate data
languages.  Named output retains its topologically ordered full-equivalence
definitions and fresh-predicate ledger.  CNF output retains that named object
beside the generated clause list, so later serialization or proof production
cannot erase the evidence connecting clauses to their source matrix.

The carrier has no equations, rewrites, or evaluation policy.  Authored
transformations into the carrier are separate LanguageDefs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.TypeSynthesis

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

def targetTerms : List GrammarRule := [
  ctor "tptp-fof-named:ref-verum" "TptpFofNamed:Reference" [],
  ctor "tptp-fof-named:ref-falsum" "TptpFofNamed:Reference" [],
  ctor "tptp-fof-named:ref-original-positive" "TptpFofNamed:Reference"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-named:ref-original-negative" "TptpFofNamed:Reference"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-named:ref-equal" "TptpFofNamed:Reference"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")],
  ctor "tptp-fof-named:ref-not-equal" "TptpFofNamed:Reference"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")],
  ctor "tptp-fof-named:ref-defined-positive" "TptpFofNamed:Reference"
    [("id", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-named:ref-defined-negative" "TptpFofNamed:Reference"
    [("id", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-named:definition-and" "TptpFofNamed:Definition"
    [("id", "TptpResolvedFof:Index"),
     ("source", "TptpFofSkolem:Formula"),
     ("left", "TptpFofNamed:Reference"),
     ("right", "TptpFofNamed:Reference")],
  ctor "tptp-fof-named:definition-or" "TptpFofNamed:Definition"
    [("id", "TptpResolvedFof:Index"),
     ("source", "TptpFofSkolem:Formula"),
     ("left", "TptpFofNamed:Reference"),
     ("right", "TptpFofNamed:Reference")],
  ctor "tptp-fof-named:definitions-nil" "TptpFofNamed:Definitions" [],
  ctor "tptp-fof-named:definitions-cons" "TptpFofNamed:Definitions"
    [("head", "TptpFofNamed:Definition"),
     ("tail", "TptpFofNamed:Definitions")],
  ctor "tptp-fof-named:introduced-predicate"
    "TptpFofNamed:IntroducedPredicate"
    [("id", "TptpResolvedFof:Index"),
     ("arity", "TptpResolvedFof:Index")],
  ctor "tptp-fof-named:introduced-nil" "TptpFofNamed:IntroducedList" [],
  ctor "tptp-fof-named:introduced-cons" "TptpFofNamed:IntroducedList"
    [("head", "TptpFofNamed:IntroducedPredicate"),
     ("tail", "TptpFofNamed:IntroducedList")],
  ctor "tptp-fof-named:output" "TptpFofNamed:Output"
    [("root", "TptpFofNamed:Reference"),
     ("next", "TptpResolvedFof:Index"),
     ("definitions", "TptpFofNamed:Definitions"),
     ("introduced", "TptpFofNamed:IntroducedList")],
  ctor "tptp-fof-cnf:clause-nil" "TptpFofCnf:Clause" [],
  ctor "tptp-fof-cnf:clause-cons" "TptpFofCnf:Clause"
    [("head", "TptpFofNamed:Reference"),
     ("tail", "TptpFofCnf:Clause")],
  ctor "tptp-fof-cnf:clauses-nil" "TptpFofCnf:Clauses" [],
  ctor "tptp-fof-cnf:clauses-cons" "TptpFofCnf:Clauses"
    [("head", "TptpFofCnf:Clause"),
     ("tail", "TptpFofCnf:Clauses")],
  ctor "tptp-fof-cnf:output" "TptpFofCnf:Output"
    [("named", "TptpFofNamed:Output"),
     ("clauses", "TptpFofCnf:Clauses")]
]

def language : LanguageDef := {
  name := "TptpFofDefinitionalCnf"
  types := TptpFofSkolemLanguageDef.language.types ++ [
    ("TptpFofNamed:Reference" : TypeDecl),
    ("TptpFofNamed:Definition" : TypeDecl),
    ("TptpFofNamed:Definitions" : TypeDecl),
    ("TptpFofNamed:IntroducedPredicate" : TypeDecl),
    ("TptpFofNamed:IntroducedList" : TypeDecl),
    ("TptpFofNamed:Output" : TypeDecl),
    ("TptpFofCnf:Clause" : TypeDecl),
    ("TptpFofCnf:Clauses" : TypeDecl),
    ("TptpFofCnf:Output" : TypeDecl)]
  terms := TptpFofSkolemLanguageDef.language.terms ++ targetTerms
  equations := []
  rewrites := []
}

/-! The explicit inventories let later authored transformations certify their
rows without repeatedly unfolding the complete inherited FOF carrier. -/

@[simp] theorem typeNames_exact : language.typeNames =
    TptpFofSkolemLanguageDef.language.typeNames ++ [
      "TptpFofNamed:Reference", "TptpFofNamed:Definition",
      "TptpFofNamed:Definitions", "TptpFofNamed:IntroducedPredicate",
      "TptpFofNamed:IntroducedList", "TptpFofNamed:Output",
      "TptpFofCnf:Clause", "TptpFofCnf:Clauses", "TptpFofCnf:Output"] := by
  rfl

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofSkolemLanguageDef.language ++ [
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
        ("tptp-fof-cnf:output", 2)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    targetTerms, ctor]

@[simp] theorem constructorLabels_exact :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofSkolemLanguageDef.language ++ [
        "tptp-fof-named:ref-verum", "tptp-fof-named:ref-falsum",
        "tptp-fof-named:ref-original-positive",
        "tptp-fof-named:ref-original-negative",
        "tptp-fof-named:ref-equal", "tptp-fof-named:ref-not-equal",
        "tptp-fof-named:ref-defined-positive",
        "tptp-fof-named:ref-defined-negative",
        "tptp-fof-named:definition-and", "tptp-fof-named:definition-or",
        "tptp-fof-named:definitions-nil",
        "tptp-fof-named:definitions-cons",
        "tptp-fof-named:introduced-predicate",
        "tptp-fof-named:introduced-nil",
        "tptp-fof-named:introduced-cons", "tptp-fof-named:output",
        "tptp-fof-cnf:clause-nil", "tptp-fof-cnf:clause-cons",
        "tptp-fof-cnf:clauses-nil", "tptp-fof-cnf:clauses-cons",
        "tptp-fof-cnf:output"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    targetTerms, ctor]

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def sourceInclusion :
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

theorem every_constructor_is_inert :
    language.terms.all (fun term => term.evalPolicy? = none) = true := by
  decide +kernel

theorem no_equations : language.equations = [] := rfl
theorem no_rewrites : language.rewrites = [] := rfl

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language (ReductionRespectsEquations.of_equation_free rfl)

theorem theory_no_step (source target : Pattern) :
    Not (theory.Step source target) := by
  intro reduction
  unfold theory at reduction
  rw [languageGSLT_step] at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember => simp [language] at ruleMember

/-! ## Canonical pattern constructors -/

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def refVerum : Pattern := a "tptp-fof-named:ref-verum"
def refFalsum : Pattern := a "tptp-fof-named:ref-falsum"
def refOriginalPositive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-named:ref-original-positive" [relation, arguments]
def refOriginalNegative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-named:ref-original-negative" [relation, arguments]
def refEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-named:ref-equal" [left, right]
def refNotEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-named:ref-not-equal" [left, right]
def refDefinedPositive (id arguments : Pattern) : Pattern :=
  a "tptp-fof-named:ref-defined-positive" [id, arguments]
def refDefinedNegative (id arguments : Pattern) : Pattern :=
  a "tptp-fof-named:ref-defined-negative" [id, arguments]
def definitionAnd (id source left right : Pattern) : Pattern :=
  a "tptp-fof-named:definition-and" [id, source, left, right]
def definitionOr (id source left right : Pattern) : Pattern :=
  a "tptp-fof-named:definition-or" [id, source, left, right]
def definitionsNil : Pattern := a "tptp-fof-named:definitions-nil"
def definitionsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-named:definitions-cons" [head, tail]
def introducedPredicate (id arity : Pattern) : Pattern :=
  a "tptp-fof-named:introduced-predicate" [id, arity]
def introducedNil : Pattern := a "tptp-fof-named:introduced-nil"
def introducedCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-named:introduced-cons" [head, tail]
def namedOutput (root next definitions introduced : Pattern) : Pattern :=
  a "tptp-fof-named:output" [root, next, definitions, introduced]
def clauseNil : Pattern := a "tptp-fof-cnf:clause-nil"
def clauseCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-cnf:clause-cons" [head, tail]
def clausesNil : Pattern := a "tptp-fof-cnf:clauses-nil"
def clausesCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-cnf:clauses-cons" [head, tail]
def cnfOutput (named clauses : Pattern) : Pattern :=
  a "tptp-fof-cnf:output" [named, clauses]

/-! ## Canonical semantic encoding -/

open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics

noncomputable def encodeNamedTerm {depth : Nat} (term : Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => TptpFofSkolemLanguageDef.termVariable
      (TptpResolvedFofLanguageDef.encodeIndex index))
    (fun impossible => nomatch impossible)
    (fun {arity}
      (function : TptpFofSkolemizationSemantics.FunctionSymbol arity)
      _ encodedArguments =>
      match function with
      | TptpFofSkolemizationSemantics.FunctionSymbol.original sourceFunction =>
          TptpFofSkolemLanguageDef.termOriginal
            (TptpFofSymbolLanguageDef.encodeFunctionHead
              ⟨sourceFunction.kind, sourceFunction.name⟩)
            (TptpFofSkolemLanguageDef.encodeTermPatterns
              (List.ofFn encodedArguments))
      | TptpFofSkolemizationSemantics.FunctionSymbol.generated id =>
          TptpFofSkolemLanguageDef.termGenerated
            (TptpResolvedFofLanguageDef.encodeNatIndex id)
            (TptpFofSkolemLanguageDef.encodeTermPatterns
              (List.ofFn encodedArguments)))
    term

noncomputable def encodeNamedTerms {depth arity : Nat}
    (terms : Fin arity → Term depth) : Pattern :=
  TptpFofSkolemLanguageDef.encodeTermPatterns
    (List.ofFn (fun index => encodeNamedTerm (terms index)))

theorem encodeNamedTerm_translateTerm_exact {depth : Nat}
    (term : Source.Term depth) :
    encodeNamedTerm (translateTerm term) =
      TptpFofSkolemLanguageDef.encodeTerm term := by
  induction term with
  | bvar index => rfl
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      cases function with
      | original sourceFunction =>
          simp only [translateTerm, encodeNamedTerm,
            TptpFofSkolemLanguageDef.encodeTerm]
          congr 2
          exact List.ofFn_inj.mpr (funext inductionHypothesis)
      | generated id =>
          simp only [translateTerm, encodeNamedTerm,
            TptpFofSkolemLanguageDef.encodeTerm]
          congr 2
          exact List.ofFn_inj.mpr (funext inductionHypothesis)

noncomputable def encodeReference {depth : Nat} : Reference depth → Pattern
  | .verum => refVerum
  | .falsum => refFalsum
  | .positive (.original (.predicate predicate)) arguments =>
      refOriginalPositive
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (encodeNamedTerms arguments)
  | .positive (.original .equality) arguments =>
      refEqual
        (encodeNamedTerm (arguments 0))
        (encodeNamedTerm (arguments 1))
  | .positive (.defined id) arguments =>
      refDefinedPositive
        (TptpResolvedFofLanguageDef.encodeNatIndex id)
        (encodeNamedTerms arguments)
  | .negative (.original (.predicate predicate)) arguments =>
      refOriginalNegative
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (encodeNamedTerms arguments)
  | .negative (.original .equality) arguments =>
      refNotEqual
        (encodeNamedTerm (arguments 0))
        (encodeNamedTerm (arguments 1))
  | .negative (.defined id) arguments =>
      refDefinedNegative
        (TptpResolvedFofLanguageDef.encodeNatIndex id)
        (encodeNamedTerms arguments)

noncomputable def encodeDefinition {depth : Nat}
    (definition : Definition depth)
    (quantifierFree : QuantifierFree definition.source) : Pattern :=
  match definition.connective with
  | .and => definitionAnd
      (TptpResolvedFofLanguageDef.encodeNatIndex definition.id)
      (TptpFofSkolemLanguageDef.encodeFormula definition.source
        quantifierFree.existentialFree)
      (encodeReference definition.left) (encodeReference definition.right)
  | .or => definitionOr
      (TptpResolvedFofLanguageDef.encodeNatIndex definition.id)
      (TptpFofSkolemLanguageDef.encodeFormula definition.source
        quantifierFree.existentialFree)
      (encodeReference definition.left) (encodeReference definition.right)

noncomputable def encodeDefinitions {depth : Nat}
    (definitions : List (Definition depth))
    (quantifierFree : ∀ definition ∈ definitions,
      QuantifierFree definition.source) : Pattern :=
  match definitions with
  | [] => definitionsNil
  | head :: tail => definitionsCons
      (encodeDefinition head (quantifierFree head (by simp)))
      (encodeDefinitions tail (fun definition membership =>
        quantifierFree definition (by simp [membership])))

def encodeIntroducedPredicate (predicate : IntroducedPredicate) : Pattern :=
  introducedPredicate
    (TptpResolvedFofLanguageDef.encodeNatIndex predicate.id)
    (TptpResolvedFofLanguageDef.encodeNatIndex predicate.arity)

def encodeIntroduced : List IntroducedPredicate → Pattern
  | [] => introducedNil
  | head :: tail => introducedCons
      (encodeIntroducedPredicate head) (encodeIntroduced tail)

noncomputable def encodeNamedOutput {depth : Nat}
    (output : Output depth)
    (quantifierFree : ∀ definition ∈ output.definitions,
      QuantifierFree definition.source) : Pattern :=
  namedOutput (encodeReference output.root)
    (TptpResolvedFofLanguageDef.encodeNatIndex output.next)
    (encodeDefinitions output.definitions quantifierFree)
    (encodeIntroduced output.introduced)

noncomputable def encodeNameFrom {depth : Nat}
    (source : Source.Formula depth) (quantifierFree : QuantifierFree source)
    (frontier : Nat) : Pattern :=
  encodeNamedOutput (nameFrom source quantifierFree frontier)
    (fun definition membership =>
      nameFrom_definition_sources_quantifierFree source quantifierFree
        frontier definition membership)

noncomputable def encodeClause {depth : Nat}
    (clause : TptpFofDefinitionalCnfSemantics.Clause depth) : Pattern :=
  match clause with
  | [] => clauseNil
  | head :: tail => clauseCons (encodeReference head) (encodeClause tail)

noncomputable def encodeClauses {depth : Nat}
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) : Pattern :=
  match clauses with
  | [] => clausesNil
  | head :: tail => clausesCons (encodeClause head) (encodeClauses tail)

noncomputable def encodeCnfOutput {depth : Nat}
    (output : Output depth)
    (quantifierFree : ∀ definition ∈ output.definitions,
      QuantifierFree definition.source) : Pattern :=
  cnfOutput (encodeNamedOutput output quantifierFree)
    (encodeClauses
      (TptpFofDefinitionalCnfSemantics.clausesForOutput output))

theorem original_and_defined_references_are_distinct
    (relation arguments id : Pattern) :
    refOriginalPositive relation arguments ≠
      refDefinedPositive id arguments := by
  simp [refOriginalPositive, refDefinedPositive, a]

theorem empty_clause_is_represented_distinctly_from_empty_clause_list :
    clauseNil ≠ clausesNil := by
  simp [clauseNil, clausesNil, a]

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
#print axioms sourceInclusion
#print axioms theory_no_step
#print axioms original_and_defined_references_are_distinct
#print axioms empty_clause_is_represented_distinctly_from_empty_clause_list
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfLanguageDef
