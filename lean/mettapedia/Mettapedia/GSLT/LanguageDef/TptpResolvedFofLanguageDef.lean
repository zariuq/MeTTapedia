import Mettapedia.GSLT.LanguageDef.TptpFofBinderResolution
import Mettapedia.GSLT.LanguageDef.TptpFofSymbolLanguageDef
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Binder-resolved semantic FOF LanguageDef

This inert, validated language is the semantic target of named-variable
resolution and the source of connective normalization. Bound variables use a
structural natural-number index, so the representation is independent of any
host integer primitive. Function and predicate heads retain their semantic
TPTP symbol classes through the shared inert symbol carrier.

The carrier performs no computation. Nearest-binder lookup belongs to the
preceding authored transformation; connective normalization belongs to the
following authored transformation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpResolvedFofLanguageDef

open LO FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics
open Mettapedia.GSLT.LanguageDef.TptpFofSymbolLanguageDef

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

def ownTerms : List GrammarRule := [
  ctor "tptp-fof-resolved:index-zero" "TptpResolvedFof:Index" [],
  ctor "tptp-fof-resolved:index-succ" "TptpResolvedFof:Index"
    [("predecessor", "TptpResolvedFof:Index")],
  ctor "tptp-fof-resolved:term-variable" "TptpResolvedFof:Term"
    [("index", "TptpResolvedFof:Index")],
  ctor "tptp-fof-resolved:term-function" "TptpResolvedFof:Term"
    [("function", "TptpFofSymbol:FunctionHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-resolved:terms-nil" "TptpResolvedFof:Terms" [],
  ctor "tptp-fof-resolved:terms-cons" "TptpResolvedFof:Terms"
    [("head", "TptpResolvedFof:Term"), ("tail", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-resolved:verum" "TptpResolvedFof:Formula" [],
  ctor "tptp-fof-resolved:falsum" "TptpResolvedFof:Formula" [],
  ctor "tptp-fof-resolved:predicate" "TptpResolvedFof:Formula"
    [("relation", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpResolvedFof:Terms")],
  ctor "tptp-fof-resolved:equal" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Term"), ("right", "TptpResolvedFof:Term")],
  ctor "tptp-fof-resolved:not" "TptpResolvedFof:Formula"
    [("body", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:and" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:or" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:iff" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:implies" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:reverse-implies" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:xor" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:nor" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:nand" "TptpResolvedFof:Formula"
    [("left", "TptpResolvedFof:Formula"),
     ("right", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:all" "TptpResolvedFof:Formula"
    [("body", "TptpResolvedFof:Formula")],
  ctor "tptp-fof-resolved:ex" "TptpResolvedFof:Formula"
    [("body", "TptpResolvedFof:Formula")]
]

def terms : List GrammarRule :=
  TptpFofSymbolLanguageDef.terms ++ ownTerms

def ownTypes : List TypeDecl := [
  "TptpResolvedFof:Index", "TptpResolvedFof:Term",
  "TptpResolvedFof:Terms", "TptpResolvedFof:Formula"]

def language : LanguageDef := {
  name := "TptpResolvedFof"
  types := TptpFofSymbolLanguageDef.language.types ++ ownTypes
  terms
  equations := []
  rewrites := []
}

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef :=
  ⟨language, language_validate⟩

theorem every_constructor_is_inert :
    terms.all (fun term => term.evalPolicy? = none) = true := by
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

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def encodeString (value : String) : Pattern :=
  a value

def encodeNatIndex : Nat → Pattern
  | 0 => a "tptp-fof-resolved:index-zero"
  | index + 1 =>
      a "tptp-fof-resolved:index-succ" [encodeNatIndex index]

def encodeIndex {depth : Nat} (index : Fin depth) : Pattern :=
  encodeNatIndex index.val

def encodeTermPatterns : List Pattern → Pattern
  | [] => a "tptp-fof-resolved:terms-nil"
  | term :: terms =>
      a "tptp-fof-resolved:terms-cons" [term, encodeTermPatterns terms]

noncomputable def encodeTerm {depth : Nat} (term : Term depth) : Pattern :=
  LO.FirstOrder.Semiterm.rec (motive := fun _ => Pattern)
    (fun index =>
      a "tptp-fof-resolved:term-variable" [encodeIndex index])
    (fun impossible => nomatch impossible)
    (fun {arity} (function : FunctionSymbol arity) _ encodedArguments =>
      a "tptp-fof-resolved:term-function"
        [encodeFunctionHead ⟨function.kind, function.name⟩,
         encodeTermPatterns (List.ofFn encodedArguments)])
    term

noncomputable def encodeTerms {depth : Nat}
    (terms : List (Term depth)) : Pattern :=
  encodeTermPatterns (terms.map encodeTerm)

noncomputable def encodeFormula {depth : Nat} : Formula depth → Pattern
  | .verum => a "tptp-fof-resolved:verum"
  | .falsum => a "tptp-fof-resolved:falsum"
  | .predicate predicate arguments =>
      a "tptp-fof-resolved:predicate"
        [encodePredicateHead ⟨predicate.kind, predicate.name⟩,
         encodeTerms (List.ofFn arguments)]
  | .equal left right =>
      a "tptp-fof-resolved:equal" [encodeTerm left, encodeTerm right]
  | .not body => a "tptp-fof-resolved:not" [encodeFormula body]
  | .and left right =>
      a "tptp-fof-resolved:and" [encodeFormula left, encodeFormula right]
  | .or left right =>
      a "tptp-fof-resolved:or" [encodeFormula left, encodeFormula right]
  | .iff left right =>
      a "tptp-fof-resolved:iff" [encodeFormula left, encodeFormula right]
  | .implies left right =>
      a "tptp-fof-resolved:implies" [encodeFormula left, encodeFormula right]
  | .reverseImplies left right =>
      a "tptp-fof-resolved:reverse-implies"
        [encodeFormula left, encodeFormula right]
  | .xor left right =>
      a "tptp-fof-resolved:xor" [encodeFormula left, encodeFormula right]
  | .nor left right =>
      a "tptp-fof-resolved:nor" [encodeFormula left, encodeFormula right]
  | .nand left right =>
      a "tptp-fof-resolved:nand" [encodeFormula left, encodeFormula right]
  | .all body => a "tptp-fof-resolved:all" [encodeFormula body]
  | .ex body => a "tptp-fof-resolved:ex" [encodeFormula body]

namespace Canary

def shadowingTarget : Formula 0 :=
  .all <| .and
    (.equal (.bvar 0) (.bvar 0))
    (.ex (.equal (.bvar 0) (.bvar 0)))

def shadowingEncoded : Pattern :=
  a "tptp-fof-resolved:all" [
    a "tptp-fof-resolved:and" [
      a "tptp-fof-resolved:equal" [
        a "tptp-fof-resolved:term-variable" [
          a "tptp-fof-resolved:index-zero"],
        a "tptp-fof-resolved:term-variable" [
          a "tptp-fof-resolved:index-zero"]],
      a "tptp-fof-resolved:ex" [
        a "tptp-fof-resolved:equal" [
          a "tptp-fof-resolved:term-variable" [
            a "tptp-fof-resolved:index-zero"],
          a "tptp-fof-resolved:term-variable" [
          a "tptp-fof-resolved:index-zero"]]]]]

theorem shadowing_encoding_is_exact :
    encodeFormula shadowingTarget = shadowingEncoded := by
  rfl

theorem distinct_indices_are_distinct :
    encodeNatIndex 0 ≠ encodeNatIndex 1 := by
  decide

theorem invented_computation_is_absent :
    language.rewrites = [] := by
  rfl

end Canary

#print axioms language_validate
#print axioms every_constructor_is_inert
#print axioms theory_no_step
#print axioms language_supported
#print axioms wire_isSome
#print axioms Canary.shadowing_encoding_is_exact
#print axioms Canary.distinct_indices_are_distinct
#print axioms Canary.invented_computation_is_absent

end Mettapedia.GSLT.LanguageDef.TptpResolvedFofLanguageDef
