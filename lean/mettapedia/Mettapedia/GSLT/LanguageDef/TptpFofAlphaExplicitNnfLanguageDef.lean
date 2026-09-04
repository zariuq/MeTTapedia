import Mettapedia.GSLT.LanguageDef.TptpFofAlphaExplicitNnf
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Alpha-explicit NNF presentation for TPTP interchange

This inert, validated language is an optional presentation refinement of the
canonical binder-resolved NNF language.  It adds a structurally encoded,
globally fresh binder identity to every quantifier.  De Bruijn indices remain
the internal binding authority; binder identities exist for stable TPTP/TSTP
serialization and provenance.

The NNF source is a literal prefix.  Label generation belongs to a following
authored transformation, not to this carrier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofAlphaExplicitNnfLanguageDef

open LO FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.TotalGSLT

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

def alphaTerms : List GrammarRule := [
  ctor "tptp-fof-alpha:binder-zero" "TptpFofAlpha:BinderId" [],
  ctor "tptp-fof-alpha:binder-succ" "TptpFofAlpha:BinderId"
    [("predecessor", "TptpFofAlpha:BinderId")],
  ctor "tptp-fof-alpha:verum" "TptpFofAlpha:Formula" [],
  ctor "tptp-fof-alpha:falsum" "TptpFofAlpha:Formula" [],
  ctor "tptp-fof-alpha:positive" "TptpFofAlpha:Formula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-alpha:negative" "TptpFofAlpha:Formula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-alpha:equal" "TptpFofAlpha:Formula"
    [("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term")],
  ctor "tptp-fof-alpha:not-equal" "TptpFofAlpha:Formula"
    [("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term")],
  ctor "tptp-fof-alpha:and" "TptpFofAlpha:Formula"
    [("left", "TptpFofAlpha:Formula"), ("right", "TptpFofAlpha:Formula")],
  ctor "tptp-fof-alpha:or" "TptpFofAlpha:Formula"
    [("left", "TptpFofAlpha:Formula"), ("right", "TptpFofAlpha:Formula")],
  ctor "tptp-fof-alpha:all" "TptpFofAlpha:Formula"
    [("binder", "TptpFofAlpha:BinderId"), ("body", "TptpFofAlpha:Formula")],
  ctor "tptp-fof-alpha:ex" "TptpFofAlpha:Formula"
    [("binder", "TptpFofAlpha:BinderId"), ("body", "TptpFofAlpha:Formula")]
]

def language : LanguageDef := {
  name := "TptpFofAlphaExplicitNnf"
  types := TptpFofNnfLanguageDef.language.types ++
    [("TptpFofAlpha:BinderId" : TypeDecl),
     ("TptpFofAlpha:Formula" : TypeDecl)]
  terms := TptpFofNnfLanguageDef.language.terms ++ alphaTerms
  equations := []
  rewrites := []
}

theorem nnf_types_are_exact_prefix :
    language.types = TptpFofNnfLanguageDef.language.types ++
      [("TptpFofAlpha:BinderId" : TypeDecl),
       ("TptpFofAlpha:Formula" : TypeDecl)] := by
  rfl

theorem nnf_terms_are_exact_prefix :
    language.terms = TptpFofNnfLanguageDef.language.terms ++ alphaTerms := by
  rfl

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def nnfInclusion :
    StructuralMorphism TptpFofNnfLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈ TptpFofNnfLanguageDef.language.equations at membership
    simp [TptpFofNnfLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈ TptpFofNnfLanguageDef.language.rewrites at membership
    simp [TptpFofNnfLanguageDef.no_rewrites] at membership

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

def encodeBinderId : Nat -> Pattern
  | 0 => a "tptp-fof-alpha:binder-zero"
  | binder + 1 =>
      a "tptp-fof-alpha:binder-succ" [encodeBinderId binder]

noncomputable def encodeFormula {depth : Nat} :
    TptpFofAlphaExplicitNnf.Formula depth -> Pattern
  | .verum => a "tptp-fof-alpha:verum"
  | .falsum => a "tptp-fof-alpha:falsum"
  | .rel relation arguments =>
      match relation with
      | .predicate predicate =>
          a "tptp-fof-alpha:positive"
            [TptpFofSymbolLanguageDef.encodePredicateHead
              ⟨predicate.kind, predicate.name⟩,
             TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)]
      | .equality =>
          a "tptp-fof-alpha:equal"
            [TptpResolvedFofLanguageDef.encodeTerm (arguments 0),
             TptpResolvedFofLanguageDef.encodeTerm (arguments 1)]
  | .nrel relation arguments =>
      match relation with
      | .predicate predicate =>
          a "tptp-fof-alpha:negative"
            [TptpFofSymbolLanguageDef.encodePredicateHead
              ⟨predicate.kind, predicate.name⟩,
             TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments)]
      | .equality =>
          a "tptp-fof-alpha:not-equal"
            [TptpResolvedFofLanguageDef.encodeTerm (arguments 0),
             TptpResolvedFofLanguageDef.encodeTerm (arguments 1)]
  | .and left right =>
      a "tptp-fof-alpha:and" [encodeFormula left, encodeFormula right]
  | .or left right =>
      a "tptp-fof-alpha:or" [encodeFormula left, encodeFormula right]
  | .all binder body =>
      a "tptp-fof-alpha:all" [encodeBinderId binder, encodeFormula body]
  | .ex binder body =>
      a "tptp-fof-alpha:ex" [encodeBinderId binder, encodeFormula body]

namespace Canary

def zeroVariable : Pattern :=
  a "tptp-fof-resolved:term-variable" [
    a "tptp-fof-resolved:index-zero"]

def nestedEncoded : Pattern :=
  a "tptp-fof-alpha:all" [encodeBinderId 0,
    a "tptp-fof-alpha:and" [
      a "tptp-fof-alpha:equal" [
        zeroVariable, zeroVariable],
      a "tptp-fof-alpha:ex" [encodeBinderId 1,
        a "tptp-fof-alpha:not-equal" [
          zeroVariable, zeroVariable]]]]

theorem canonical_nested_encoding_is_exact :
    encodeFormula
        (TptpFofAlphaExplicitNnf.label
          TptpFofAlphaExplicitNnf.Canary.nestedSource) = nestedEncoded := by
  decide +kernel

theorem binder_ids_are_not_debruijn_indices :
    encodeBinderId 0 ≠ TptpResolvedFofLanguageDef.encodeNatIndex 0 := by
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
#print axioms nnfInclusion
#print axioms every_constructor_is_inert
#print axioms theory_no_step
#print axioms Canary.canonical_nested_encoding_is_exact
#print axioms Canary.binder_ids_are_not_debruijn_indices
#print axioms Canary.invented_computation_is_absent
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofAlphaExplicitNnfLanguageDef
