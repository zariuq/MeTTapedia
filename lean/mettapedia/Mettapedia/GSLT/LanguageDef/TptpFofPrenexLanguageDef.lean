import Mettapedia.GSLT.LanguageDef.TptpFofNnfLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Canonical prenex FOF LanguageDef

This inert presentation is the target carrier for authored prenex
normalization.  It separates a quantifier-free matrix sort from a prefix sort,
so every inhabitant of `TptpFofPrenex:Form` has a quantifier prefix followed by
one quantifier-free matrix by construction.

The presentation structurally extends canonical NNF and reuses its exact term,
index, relation-name, and source-formula representation.  Prenex conversion is
defined in a separate transformation language; this carrier contains no
evaluation policy, equation, or rewrite.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofPrenexLanguageDef

open LO FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics
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

/-! ## Quantifier-free matrix and prenex-prefix constructors -/

def matrixTerms : List GrammarRule := [
  ctor "tptp-fof-prenex:matrix-verum" "TptpFofPrenex:Matrix" [],
  ctor "tptp-fof-prenex:matrix-falsum" "TptpFofPrenex:Matrix" [],
  ctor "tptp-fof-prenex:matrix-positive" "TptpFofPrenex:Matrix"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-prenex:matrix-negative" "TptpFofPrenex:Matrix"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-prenex:matrix-equal" "TptpFofPrenex:Matrix"
    [("left", "TptpResolvedFof:Term"),
     ("right", "TptpResolvedFof:Term")],
  ctor "tptp-fof-prenex:matrix-not-equal" "TptpFofPrenex:Matrix"
    [("left", "TptpResolvedFof:Term"),
     ("right", "TptpResolvedFof:Term")],
  ctor "tptp-fof-prenex:matrix-and" "TptpFofPrenex:Matrix"
    [("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix")],
  ctor "tptp-fof-prenex:matrix-or" "TptpFofPrenex:Matrix"
    [("left", "TptpFofPrenex:Matrix"),
     ("right", "TptpFofPrenex:Matrix")]
]

def prenexTerms : List GrammarRule := [
  ctor "tptp-fof-prenex:matrix" "TptpFofPrenex:Form"
    [("body", "TptpFofPrenex:Matrix")],
  ctor "tptp-fof-prenex:all" "TptpFofPrenex:Form"
    [("body", "TptpFofPrenex:Form")],
  ctor "tptp-fof-prenex:ex" "TptpFofPrenex:Form"
    [("body", "TptpFofPrenex:Form")]
]

def language : LanguageDef := {
  name := "TptpFofPrenex"
  types := TptpFofNnfLanguageDef.language.types ++ [
    ("TptpFofPrenex:Matrix" : TypeDecl),
    ("TptpFofPrenex:Form" : TypeDecl)]
  terms := TptpFofNnfLanguageDef.language.terms ++ matrixTerms ++ prenexTerms
  equations := []
  rewrites := []
}

theorem source_types_are_exact_prefix :
    language.types = TptpFofNnfLanguageDef.language.types ++ [
      ("TptpFofPrenex:Matrix" : TypeDecl),
      ("TptpFofPrenex:Form" : TypeDecl)] := by
  rfl

theorem source_terms_are_exact_prefix :
    language.terms = TptpFofNnfLanguageDef.language.terms ++
      matrixTerms ++ prenexTerms := by
  rfl

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def sourceInclusion :
    StructuralMorphism TptpFofNnfLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ (List.mem_append_left _ membership)
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

/-! ## Canonical semantic encoding -/

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def matrixVerum : Pattern := a "tptp-fof-prenex:matrix-verum"
def matrixFalsum : Pattern := a "tptp-fof-prenex:matrix-falsum"
def matrixPositive (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-positive" [relation, arguments]
def matrixNegative (relation arguments : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-negative" [relation, arguments]
def matrixEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-equal" [left, right]
def matrixNotEqual (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-not-equal" [left, right]
def matrixAnd (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-and" [left, right]
def matrixOr (left right : Pattern) : Pattern :=
  a "tptp-fof-prenex:matrix-or" [left, right]

def matrix (body : Pattern) : Pattern := a "tptp-fof-prenex:matrix" [body]
def all (body : Pattern) : Pattern := a "tptp-fof-prenex:all" [body]
def ex (body : Pattern) : Pattern := a "tptp-fof-prenex:ex" [body]

/-- Encode a quantifier-free formula into the matrix sort.  The impossible
quantifier branches consume the actual `QuantifierFree` evidence rather than
silently accepting a wider formula language. -/
noncomputable def encodeMatrix : {depth : Nat} ->
    (formula : Formula depth) -> QuantifierFree formula -> Pattern
  | _, .verum, _ => matrixVerum
  | _, .falsum, _ => matrixFalsum
  | _, .rel relation arguments, _ =>
      match relation with
      | .predicate predicate =>
          matrixPositive
            (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
            (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments))
      | .equality =>
          matrixEqual
            (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
            (TptpResolvedFofLanguageDef.encodeTerm (arguments 1))
  | _, .nrel relation arguments, _ =>
      match relation with
      | .predicate predicate =>
          matrixNegative
            (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
            (TptpResolvedFofLanguageDef.encodeTerms (List.ofFn arguments))
      | .equality =>
          matrixNotEqual
            (TptpResolvedFofLanguageDef.encodeTerm (arguments 0))
            (TptpResolvedFofLanguageDef.encodeTerm (arguments 1))
  | _, .and left right, quantifierFree =>
      matrixAnd
        (encodeMatrix left quantifierFree.1)
        (encodeMatrix right quantifierFree.2)
  | _, .or left right, quantifierFree =>
      matrixOr
        (encodeMatrix left quantifierFree.1)
        (encodeMatrix right quantifierFree.2)
  | _, .all _, impossible => False.elim impossible
  | _, .ex _, impossible => False.elim impossible

noncomputable def encodePrenex : {depth : Nat} -> PrenexForm depth -> Pattern
  | _, .matrix formula quantifierFree =>
      matrix (encodeMatrix formula quantifierFree)
  | _, .all body => all (encodePrenex body)
  | _, .ex body => ex (encodePrenex body)

namespace Canary

def p : TptpFofNormalizationSemantics.PredicateSymbol 1 := ⟨"p", .plain⟩
def q : TptpFofNormalizationSemantics.PredicateSymbol 1 := ⟨"q", .plain⟩

def source : Formula 0 :=
  .or
    (.ex (.rel (.predicate p) ![.bvar 0]))
    (.all (.rel (.predicate q) ![.bvar 0]))

noncomputable def unaryArguments {depth : Nat} (index : Fin depth) : Pattern :=
  TptpResolvedFofLanguageDef.encodeTerms
    [(show TptpFofNormalizationSemantics.Term depth from .bvar index)]

noncomputable def expected : Pattern :=
  ex <| all <| matrix <| matrixOr
    (matrixPositive (TptpFofSymbolLanguageDef.encodePredicateHead
        ⟨.plain, "p"⟩)
      (unaryArguments (1 : Fin 2)))
    (matrixPositive (TptpFofSymbolLanguageDef.encodePredicateHead
        ⟨.plain, "q"⟩)
      (unaryArguments (0 : Fin 2)))

theorem semantic_prenex_encoding_is_exact :
    encodePrenex (TptpFofPrenexSemantics.prenex source) = expected := by
  simp [p, q, source, expected, TptpFofPrenexSemantics.prenex,
    TptpFofPrenexSemantics.combine,
    TptpFofPrenexSemantics.Connective.apply,
    TptpFofPrenexSemantics.PrenexForm.rew, encodePrenex, encodeMatrix,
    TptpFofSymbolLanguageDef.encodePredicateHead,
    TptpResolvedFofLanguageDef.encodeTerms,
    TptpResolvedFofLanguageDef.encodeTermPatterns,
    TptpResolvedFofLanguageDef.encodeTerm,
    TptpResolvedFofLanguageDef.encodeIndex,
    TptpResolvedFofLanguageDef.encodeNatIndex,
    LO.FirstOrder.Semiformula.rew_rel, Matrix.constant_eq_singleton,
    unaryArguments, matrix, all, ex, matrixOr, matrixPositive, a]

/-- A quantifier cannot be smuggled into the structurally separate matrix
constructor family. -/
theorem quantifier_matrix_constructors_are_absent :
    "tptp-fof-prenex:matrix-all" ∉ matrixTerms.map (·.label) ∧
      "tptp-fof-prenex:matrix-ex" ∉ matrixTerms.map (·.label) := by
  decide +kernel

/-- Omitting the capture-avoiding increment changes the concrete target. -/
theorem unshifted_left_occurrence_is_not_expected :
    expected ≠
      ex (all (matrix (matrixOr
        (matrixPositive (TptpFofSymbolLanguageDef.encodePredicateHead
            ⟨.plain, "p"⟩)
          (unaryArguments (0 : Fin 2)))
        (matrixPositive (TptpFofSymbolLanguageDef.encodePredicateHead
            ⟨.plain, "q"⟩)
          (unaryArguments (0 : Fin 2)))))) := by
  decide +kernel

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
#print axioms Canary.semantic_prenex_encoding_is_exact
#print axioms Canary.quantifier_matrix_constructors_are_absent
#print axioms Canary.unshifted_left_occurrence_is_not_expected
#print axioms language_supported
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofPrenexLanguageDef
