import Mettapedia.GSLT.LanguageDef.TptpFofPrenexLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Canonical evidence-bearing Skolem FOF LanguageDef

This inert presentation is the target carrier for authored Skolemization.  It
keeps original and generated function symbols in distinct constructors,
excludes existential quantification from its formula sort, and carries the
fresh-symbol frontier and introduced-symbol list in the output itself.

The presentation structurally extends canonical prenex FOF so the later
transformation language can contain its source and target without a parallel
copy of either syntax.  It contains no evaluation policy or rewrite rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemLanguageDef

open LO FirstOrder
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

/-! ## Target constructors -/

def skolemTerms : List GrammarRule := [
  ctor "tptp-fof-skolem:term-variable" "TptpFofSkolem:Term"
    [("index", "TptpResolvedFof:Index")],
  ctor "tptp-fof-skolem:term-original" "TptpFofSkolem:Term"
    [("function", "TptpFofSymbol:FunctionHead"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem:term-generated" "TptpFofSkolem:Term"
    [("id", "TptpResolvedFof:Index"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem:terms-nil" "TptpFofSkolem:Terms" [],
  ctor "tptp-fof-skolem:terms-cons" "TptpFofSkolem:Terms"
    [("head", "TptpFofSkolem:Term"), ("tail", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem:verum" "TptpFofSkolem:Formula" [],
  ctor "tptp-fof-skolem:falsum" "TptpFofSkolem:Formula" [],
  ctor "tptp-fof-skolem:positive" "TptpFofSkolem:Formula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem:negative" "TptpFofSkolem:Formula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpFofSkolem:Terms")],
  ctor "tptp-fof-skolem:equal" "TptpFofSkolem:Formula"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")],
  ctor "tptp-fof-skolem:not-equal" "TptpFofSkolem:Formula"
    [("left", "TptpFofSkolem:Term"), ("right", "TptpFofSkolem:Term")],
  ctor "tptp-fof-skolem:and" "TptpFofSkolem:Formula"
    [("left", "TptpFofSkolem:Formula"),
     ("right", "TptpFofSkolem:Formula")],
  ctor "tptp-fof-skolem:or" "TptpFofSkolem:Formula"
    [("left", "TptpFofSkolem:Formula"),
     ("right", "TptpFofSkolem:Formula")],
  ctor "tptp-fof-skolem:all" "TptpFofSkolem:Formula"
    [("body", "TptpFofSkolem:Formula")],
  ctor "tptp-fof-skolem:introduced-symbol"
    "TptpFofSkolem:IntroducedSymbol"
    [("id", "TptpResolvedFof:Index"),
     ("arity", "TptpResolvedFof:Index")],
  ctor "tptp-fof-skolem:introduced-nil"
    "TptpFofSkolem:IntroducedList" [],
  ctor "tptp-fof-skolem:introduced-cons"
    "TptpFofSkolem:IntroducedList"
    [("head", "TptpFofSkolem:IntroducedSymbol"),
     ("tail", "TptpFofSkolem:IntroducedList")],
  ctor "tptp-fof-skolem:output" "TptpFofSkolem:Output"
    [("formula", "TptpFofSkolem:Formula"),
     ("next", "TptpResolvedFof:Index"),
     ("introduced", "TptpFofSkolem:IntroducedList")]
]

def language : LanguageDef := {
  name := "TptpFofSkolem"
  types := TptpFofPrenexLanguageDef.language.types ++ [
    ("TptpFofSkolem:Term" : TypeDecl),
    ("TptpFofSkolem:Terms" : TypeDecl),
    ("TptpFofSkolem:Formula" : TypeDecl),
    ("TptpFofSkolem:IntroducedSymbol" : TypeDecl),
    ("TptpFofSkolem:IntroducedList" : TypeDecl),
    ("TptpFofSkolem:Output" : TypeDecl)]
  terms := TptpFofPrenexLanguageDef.language.terms ++ skolemTerms
  equations := []
  rewrites := []
}

theorem source_types_are_exact_prefix :
    language.types = TptpFofPrenexLanguageDef.language.types ++ [
      ("TptpFofSkolem:Term" : TypeDecl),
      ("TptpFofSkolem:Terms" : TypeDecl),
      ("TptpFofSkolem:Formula" : TypeDecl),
      ("TptpFofSkolem:IntroducedSymbol" : TypeDecl),
      ("TptpFofSkolem:IntroducedList" : TypeDecl),
      ("TptpFofSkolem:Output" : TypeDecl)] := by
  rfl

theorem source_terms_are_exact_prefix :
    language.terms = TptpFofPrenexLanguageDef.language.terms ++
      skolemTerms := by
  rfl

/-! The exact public inventory lets later transformation languages validate
their own rows without unfolding this whole inherited carrier. -/

@[simp] theorem typeNames_exact : language.typeNames = [
    "String", "TptpFofSymbol:FunctionHead",
    "TptpFofSymbol:PredicateHead", "TptpResolvedFof:Index",
    "TptpResolvedFof:Term",
    "TptpResolvedFof:Terms", "TptpResolvedFof:Formula", "NNFFormula",
    "TptpFofPrenex:Matrix", "TptpFofPrenex:Form",
    "TptpFofSkolem:Term", "TptpFofSkolem:Terms",
    "TptpFofSkolem:Formula", "TptpFofSkolem:IntroducedSymbol",
    "TptpFofSkolem:IntroducedList", "TptpFofSkolem:Output"] := by
  rfl

@[simp] theorem constructorSignatures_exact :
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
      ("tptp-fof-prenex:matrix-verum", 0),
      ("tptp-fof-prenex:matrix-falsum", 0),
      ("tptp-fof-prenex:matrix-positive", 2),
      ("tptp-fof-prenex:matrix-negative", 2),
      ("tptp-fof-prenex:matrix-equal", 2),
      ("tptp-fof-prenex:matrix-not-equal", 2),
      ("tptp-fof-prenex:matrix-and", 2),
      ("tptp-fof-prenex:matrix-or", 2),
      ("tptp-fof-prenex:matrix", 1),
      ("tptp-fof-prenex:all", 1),
      ("tptp-fof-prenex:ex", 1),
      ("tptp-fof-skolem:term-variable", 1),
      ("tptp-fof-skolem:term-original", 2),
      ("tptp-fof-skolem:term-generated", 2),
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
      ("tptp-fof-skolem:introduced-symbol", 2),
      ("tptp-fof-skolem:introduced-nil", 0),
      ("tptp-fof-skolem:introduced-cons", 2),
      ("tptp-fof-skolem:output", 3)] := by
  rfl

@[simp] theorem constructorLabels_exact :
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
      "tptp-fof-resolved:ex", "tptp-fof-nnf:verum",
      "tptp-fof-nnf:falsum", "tptp-fof-nnf:positive",
      "tptp-fof-nnf:negative", "tptp-fof-nnf:equal",
      "tptp-fof-nnf:not-equal", "tptp-fof-nnf:and",
      "tptp-fof-nnf:or", "tptp-fof-nnf:all", "tptp-fof-nnf:ex",
      "tptp-fof-prenex:matrix-verum", "tptp-fof-prenex:matrix-falsum",
      "tptp-fof-prenex:matrix-positive", "tptp-fof-prenex:matrix-negative",
      "tptp-fof-prenex:matrix-equal", "tptp-fof-prenex:matrix-not-equal",
      "tptp-fof-prenex:matrix-and", "tptp-fof-prenex:matrix-or",
      "tptp-fof-prenex:matrix", "tptp-fof-prenex:all",
      "tptp-fof-prenex:ex", "tptp-fof-skolem:term-variable",
      "tptp-fof-skolem:term-original", "tptp-fof-skolem:term-generated",
      "tptp-fof-skolem:terms-nil", "tptp-fof-skolem:terms-cons",
      "tptp-fof-skolem:verum", "tptp-fof-skolem:falsum",
      "tptp-fof-skolem:positive", "tptp-fof-skolem:negative",
      "tptp-fof-skolem:equal", "tptp-fof-skolem:not-equal",
      "tptp-fof-skolem:and", "tptp-fof-skolem:or",
      "tptp-fof-skolem:all", "tptp-fof-skolem:introduced-symbol",
      "tptp-fof-skolem:introduced-nil", "tptp-fof-skolem:introduced-cons",
      "tptp-fof-skolem:output"] := by
  rfl

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def sourceInclusion :
    StructuralMorphism TptpFofPrenexLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈ TptpFofPrenexLanguageDef.language.equations at membership
    simp [TptpFofPrenexLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈ TptpFofPrenexLanguageDef.language.rewrites at membership
    simp [TptpFofPrenexLanguageDef.no_rewrites] at membership

theorem every_constructor_is_inert :
    language.terms.all (fun term => term.evalPolicy? = none) = true := by
  decide +kernel

theorem no_equations : language.equations = [] := rfl
theorem no_rewrites : language.rewrites = [] := rfl

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_equation_free rfl)

theorem theory_no_step (source target : Pattern) :
    ¬ theory.Step source target := by
  intro reduction
  unfold theory at reduction
  rw [languageGSLT_step] at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

/-! ## Canonical semantic encoding -/

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def termVariable (index : Pattern) : Pattern :=
  a "tptp-fof-skolem:term-variable" [index]
def termOriginal (function arguments : Pattern) : Pattern :=
  a "tptp-fof-skolem:term-original" [function, arguments]
def termGenerated (id arguments : Pattern) : Pattern :=
  a "tptp-fof-skolem:term-generated" [id, arguments]
def termsNil : Pattern := a "tptp-fof-skolem:terms-nil"
def termsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-skolem:terms-cons" [head, tail]

def verum : Pattern := a "tptp-fof-skolem:verum"
def falsum : Pattern := a "tptp-fof-skolem:falsum"
def positive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-skolem:positive" [relation, arguments]
def negative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-skolem:negative" [relation, arguments]
def equal (left right : Pattern) : Pattern :=
  a "tptp-fof-skolem:equal" [left, right]
def notEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-skolem:not-equal" [left, right]
def and (left right : Pattern) : Pattern :=
  a "tptp-fof-skolem:and" [left, right]
def or (left right : Pattern) : Pattern :=
  a "tptp-fof-skolem:or" [left, right]
def all (body : Pattern) : Pattern := a "tptp-fof-skolem:all" [body]

def introducedSymbol (id arity : Pattern) : Pattern :=
  a "tptp-fof-skolem:introduced-symbol" [id, arity]
def introducedNil : Pattern := a "tptp-fof-skolem:introduced-nil"
def introducedCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-skolem:introduced-cons" [head, tail]
def output (formula next introduced : Pattern) : Pattern :=
  a "tptp-fof-skolem:output" [formula, next, introduced]

def encodeTermPatterns : List Pattern -> Pattern
  | [] => termsNil
  | head :: tail => termsCons head (encodeTermPatterns tail)

noncomputable def encodeTerm {depth : Nat}
    (term : TptpFofSkolemizationSemantics.Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index => termVariable
      (TptpResolvedFofLanguageDef.encodeIndex index))
    (fun impossible => nomatch impossible)
    (fun {arity}
      (function : TptpFofSkolemizationSemantics.FunctionSymbol arity)
      _ encodedArguments =>
      match function with
      | .original sourceFunction =>
          termOriginal
            (TptpFofSymbolLanguageDef.encodeFunctionHead
              ⟨sourceFunction.kind, sourceFunction.name⟩)
            (encodeTermPatterns (List.ofFn encodedArguments))
      | .generated id =>
          termGenerated
            (TptpResolvedFofLanguageDef.encodeNatIndex id)
            (encodeTermPatterns (List.ofFn encodedArguments)))
    term

noncomputable def encodeTerms {depth : Nat}
    (terms : List (TptpFofSkolemizationSemantics.Term depth)) : Pattern :=
  encodeTermPatterns (terms.map encodeTerm)

noncomputable def encodeFormula : {depth : Nat} ->
    (formula : TptpFofSkolemizationSemantics.Formula depth) ->
    TptpFofSkolemizationSemantics.ExistentialFree formula -> Pattern
  | _, .verum, _ => verum
  | _, .falsum, _ => falsum
  | _, .rel (.predicate predicate) arguments, _ =>
      positive
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (encodeTerms (List.ofFn arguments))
  | _, .rel .equality arguments, _ =>
      equal (encodeTerm (arguments 0)) (encodeTerm (arguments 1))
  | _, .nrel (.predicate predicate) arguments, _ =>
      negative
        (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
        (encodeTerms (List.ofFn arguments))
  | _, .nrel .equality arguments, _ =>
      notEqual (encodeTerm (arguments 0)) (encodeTerm (arguments 1))
  | _, .and left right, free =>
      and (encodeFormula left free.1) (encodeFormula right free.2)
  | _, .or left right, free =>
      or (encodeFormula left free.1) (encodeFormula right free.2)
  | _, .all body, free => all (encodeFormula body free)
  | _, .ex _, impossible => False.elim impossible

def encodeIntroducedSymbol
    (symbol : TptpFofSkolemizationSemantics.IntroducedSymbol) : Pattern :=
  introducedSymbol
    (TptpResolvedFofLanguageDef.encodeNatIndex symbol.id)
    (TptpResolvedFofLanguageDef.encodeNatIndex symbol.arity)

def encodeIntroduced :
    List TptpFofSkolemizationSemantics.IntroducedSymbol -> Pattern
  | [] => introducedNil
  | head :: tail => introducedCons
      (encodeIntroducedSymbol head) (encodeIntroduced tail)

noncomputable def encodeOutput {depth : Nat}
    (result : TptpFofSkolemizationSemantics.Output depth)
    (free : TptpFofSkolemizationSemantics.ExistentialFree result.formula) :
    Pattern :=
  output (encodeFormula result.formula free)
    (TptpResolvedFofLanguageDef.encodeNatIndex result.next)
    (encodeIntroduced result.introduced)

namespace Canary

open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics

noncomputable def sourceEncoded : Pattern :=
  encodeOutput (skolemize Canary.source)
    (skolemize_existentialFree Canary.source)

def expected : Pattern :=
  output
    (all (positive
      (TptpFofSymbolLanguageDef.encodePredicateHead ⟨.plain, "p"⟩)
      (termsCons (termVariable
          (TptpResolvedFofLanguageDef.encodeNatIndex 0))
        (termsCons
          (termGenerated
            (TptpResolvedFofLanguageDef.encodeNatIndex 0)
            (termsCons (termVariable
                (TptpResolvedFofLanguageDef.encodeNatIndex 0)) termsNil))
          termsNil))))
    (TptpResolvedFofLanguageDef.encodeNatIndex 1)
    (introducedCons
      (introducedSymbol
        (TptpResolvedFofLanguageDef.encodeNatIndex 0)
        (TptpResolvedFofLanguageDef.encodeNatIndex 1))
      introducedNil)

theorem semantic_output_encoding_is_exact : sourceEncoded = expected := by
  simp [sourceEncoded, expected, encodeOutput, encodeFormula, encodeTerm,
    encodeTerms, encodeTermPatterns, encodeIntroduced, encodeIntroducedSymbol,
    skolemize, Canary.source, skolemizeFrom, underUniversal,
    underExistential, generatedApplication, translateTerm,
    Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Canary.p,
    TptpResolvedFofLanguageDef.encodeIndex,
    TptpResolvedFofLanguageDef.encodeNatIndex,
    TptpFofSymbolLanguageDef.encodePredicateHead,
    output, all, positive, termsCons, termsNil, termVariable,
    termGenerated, introducedCons, introducedNil, introducedSymbol, a]

theorem original_and_generated_symbols_are_distinct (name : Pattern)
    (arguments : Pattern) (id : Pattern) :
    termOriginal name arguments ≠ termGenerated id arguments := by
  simp [termOriginal, termGenerated, a]

theorem existential_constructor_is_absent :
    "tptp-fof-skolem:ex" ∉ skolemTerms.map (·.label) := by
  decide +kernel

theorem introduced_order_is_preserved :
    encodeIntroduced [⟨0, 1⟩, ⟨1, 2⟩] =
      introducedCons
        (introducedSymbol
          (TptpResolvedFofLanguageDef.encodeNatIndex 0)
          (TptpResolvedFofLanguageDef.encodeNatIndex 1))
        (introducedCons
          (introducedSymbol
            (TptpResolvedFofLanguageDef.encodeNatIndex 1)
            (TptpResolvedFofLanguageDef.encodeNatIndex 2))
          introducedNil) := by
  rfl

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
#print axioms sourceInclusion
#print axioms every_constructor_is_inert
#print axioms theory_no_step
#print axioms Canary.semantic_output_encoding_is_exact
#print axioms Canary.original_and_generated_symbols_are_distinct
#print axioms Canary.existential_constructor_is_absent
#print axioms Canary.introduced_order_is_preserved
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemLanguageDef
