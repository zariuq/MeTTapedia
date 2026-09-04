import Mettapedia.GSLT.LanguageDef.TptpResolvedFofLanguageDef
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Binder-resolved first-order negation-normal-form LanguageDef

This inert, validated language is the literal target carrier of FOF
normalization and the literal source carrier of the following clausification
stages.  Its formula sort has only signed atoms, equality/disequality,
conjunction, disjunction, and quantifiers.  Consequently every inhabitant of
`NNFFormula` is in negation normal form by construction.

The presentation extends the binder-resolved FOF carrier so that terms,
indices, strings, and their encodings have one owner.  It introduces no
rewrites: normalization belongs to the preceding authored transformation,
while rectification and Skolemization belong to later transformations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofNnfLanguageDef

open LO FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

/-- The constructors owned specifically by the NNF formula carrier. -/
def nnfTerms : List GrammarRule := [
  ctor "tptp-fof-nnf:verum" "NNFFormula" [],
  ctor "tptp-fof-nnf:falsum" "NNFFormula" [],
  ctor "tptp-fof-nnf:positive" "NNFFormula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-nnf:negative" "NNFFormula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-nnf:equal" "NNFFormula"
    [("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term")],
  ctor "tptp-fof-nnf:not-equal" "NNFFormula"
    [("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term")],
  ctor "tptp-fof-nnf:and" "NNFFormula"
    [("left", "NNFFormula"), ("right", "NNFFormula")],
  ctor "tptp-fof-nnf:or" "NNFFormula"
    [("left", "NNFFormula"), ("right", "NNFFormula")],
  ctor "tptp-fof-nnf:all" "NNFFormula" [("body", "NNFFormula")],
  ctor "tptp-fof-nnf:ex" "NNFFormula" [("body", "NNFFormula")]
]

def language : LanguageDef := {
  name := "TptpFofNnf"
  types := TptpResolvedFofLanguageDef.language.types ++
    [("NNFFormula" : TypeDecl)]
  terms := TptpResolvedFofLanguageDef.language.terms ++ nnfTerms
  equations := []
  rewrites := []
}

theorem resolved_types_are_exact_prefix :
    language.types = TptpResolvedFofLanguageDef.language.types ++
      [("NNFFormula" : TypeDecl)] := by
  rfl

theorem resolved_terms_are_exact_prefix :
    language.terms = TptpResolvedFofLanguageDef.language.terms ++ nnfTerms := by
  rfl

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef :=
  ⟨language, language_validate⟩

/-- Literal inclusion of the shared binder-resolved term and formula carrier. -/
def resolvedInclusion :
    StructuralMorphism TptpResolvedFofLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈ TptpResolvedFofLanguageDef.language.equations at membership
    simp [TptpResolvedFofLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈ TptpResolvedFofLanguageDef.language.rewrites at membership
    simp [TptpResolvedFofLanguageDef.no_rewrites] at membership

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

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-- The canonical encoder reuses the exact term representation owned by the
binder-resolved carrier. -/
noncomputable def encodeFormula {depth : Nat} :
    LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty depth -> Pattern
  | .verum => a "tptp-fof-nnf:verum"
  | .falsum => a "tptp-fof-nnf:falsum"
  | .rel relation arguments =>
      match relation with
      | .predicate predicate =>
          a "tptp-fof-nnf:positive"
            [TptpFofSymbolLanguageDef.encodePredicateHead
                ⟨predicate.kind, predicate.name⟩,
             TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)]
      | .equality =>
          a "tptp-fof-nnf:equal"
            [TptpResolvedFofLanguageDef.encodeTerm (arguments 0),
             TptpResolvedFofLanguageDef.encodeTerm (arguments 1)]
  | .nrel relation arguments =>
      match relation with
      | .predicate predicate =>
          a "tptp-fof-nnf:negative"
            [TptpFofSymbolLanguageDef.encodePredicateHead
                ⟨predicate.kind, predicate.name⟩,
             TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)]
      | .equality =>
          a "tptp-fof-nnf:not-equal"
            [TptpResolvedFofLanguageDef.encodeTerm (arguments 0),
             TptpResolvedFofLanguageDef.encodeTerm (arguments 1)]
  | .and left right =>
      a "tptp-fof-nnf:and" [encodeFormula left, encodeFormula right]
  | .or left right =>
      a "tptp-fof-nnf:or" [encodeFormula left, encodeFormula right]
  | .all body => a "tptp-fof-nnf:all" [encodeFormula body]
  | .ex body => a "tptp-fof-nnf:ex" [encodeFormula body]

namespace Canary

def normalizedSource :
    LO.FirstOrder.Semiformula
      TptpFofNormalizationSemantics.language Empty 0 :=
  TptpFofNormalizationSemantics.normalizePositive
    TptpFofNormalizationSemantics.Canary.source

def normalizedEncoded : Pattern :=
  a "tptp-fof-nnf:and" [
    a "tptp-fof-nnf:positive" [
      a "tptp-fof-symbol:predicate-plain" [a "p"],
      a "tptp-fof-resolved:terms-nil"],
    a "tptp-fof-nnf:negative" [
      a "tptp-fof-symbol:predicate-plain" [a "q"],
      a "tptp-fof-resolved:terms-nil"]]

theorem normalization_image_encoding_is_exact :
    encodeFormula normalizedSource = normalizedEncoded := by
  rfl

/-- Compound negation is not a constructor of the NNF formula sort. -/
theorem compound_negation_constructor_is_absent :
    "tptp-fof-nnf:not" ∉ language.terms.map (·.label) := by
  decide +kernel

theorem invented_computation_is_absent : language.rewrites = [] := by
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
#print axioms resolvedInclusion
#print axioms every_constructor_is_inert
#print axioms theory_no_step
#print axioms Canary.normalization_image_encoding_is_exact
#print axioms Canary.compound_negation_constructor_is_absent
#print axioms Canary.invented_computation_is_absent
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofNnfLanguageDef
