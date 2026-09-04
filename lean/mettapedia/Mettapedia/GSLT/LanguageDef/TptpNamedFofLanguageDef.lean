import Mettapedia.GSLT.LanguageDef.TptpFofBinderResolution
import Mettapedia.GSLT.LanguageDef.TptpFofSymbolLanguageDef
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Named semantic FOF LanguageDef

This inert, validated LanguageDef is the semantic target between the official
grammar-shaped FOF AST and capture-avoiding binder resolution.  Its
constructors retain variable spellings and lossless semantic symbol heads but
do not assign occurrence identities to binders.  Binder resolution is a
subsequent transformation.

Because every constructor is inert and the language has no equations or
rewrites, adjoining these carriers cannot introduce hidden computation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.TptpFofBinderResolution
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
  ctor "tptp-fof-named:name" "TptpNamedFof:Name"
    [("value", "String")],
  ctor "tptp-fof-named:term-variable" "TptpNamedFof:Term"
    [("name", "TptpNamedFof:Name")],
  ctor "tptp-fof-named:term-function" "TptpNamedFof:Term"
    [("head", "TptpFofSymbol:FunctionHead"),
     ("arguments", "TptpNamedFof:Terms")],
  ctor "tptp-fof-named:terms-nil" "TptpNamedFof:Terms" [],
  ctor "tptp-fof-named:terms-cons" "TptpNamedFof:Terms"
    [("head", "TptpNamedFof:Term"), ("tail", "TptpNamedFof:Terms")],
  ctor "tptp-fof-named:verum" "TptpNamedFof:Formula" [],
  ctor "tptp-fof-named:falsum" "TptpNamedFof:Formula" [],
  ctor "tptp-fof-named:predicate" "TptpNamedFof:Formula"
    [("head", "TptpFofSymbol:PredicateHead"),
     ("arguments", "TptpNamedFof:Terms")],
  ctor "tptp-fof-named:equal" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Term"), ("right", "TptpNamedFof:Term")],
  ctor "tptp-fof-named:not" "TptpNamedFof:Formula"
    [("body", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:and" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:or" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:iff" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:implies" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:reverse-implies" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:xor" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:nor" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:nand" "TptpNamedFof:Formula"
    [("left", "TptpNamedFof:Formula"), ("right", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:all" "TptpNamedFof:Formula"
    [("binder", "TptpNamedFof:Name"), ("body", "TptpNamedFof:Formula")],
  ctor "tptp-fof-named:ex" "TptpNamedFof:Formula"
    [("binder", "TptpNamedFof:Name"), ("body", "TptpNamedFof:Formula")]
]

def terms : List GrammarRule :=
  TptpFofSymbolLanguageDef.terms ++ ownTerms

def ownTypes : List TypeDecl := [
  "TptpNamedFof:Name", "TptpNamedFof:Term", "TptpNamedFof:Terms",
  "TptpNamedFof:Formula"]

def language : LanguageDef := {
  name := "TptpNamedFof"
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

def encodeName (name : String) : Pattern :=
  a "tptp-fof-named:name" [a name]

mutual
  def encodeTerm : NamedTerm -> Pattern
    | .variable name =>
        a "tptp-fof-named:term-variable" [encodeName name]
    | .function head arguments =>
        a "tptp-fof-named:term-function"
          [encodeFunctionHead head, encodeTerms arguments]

  def encodeTerms : List NamedTerm -> Pattern
    | [] => a "tptp-fof-named:terms-nil"
    | term :: terms =>
        a "tptp-fof-named:terms-cons" [encodeTerm term, encodeTerms terms]
end

def encodeFormula : NamedFormula -> Pattern
  | .verum => a "tptp-fof-named:verum"
  | .falsum => a "tptp-fof-named:falsum"
  | .predicate head arguments =>
      a "tptp-fof-named:predicate"
        [encodePredicateHead head, encodeTerms arguments]
  | .equal left right =>
      a "tptp-fof-named:equal" [encodeTerm left, encodeTerm right]
  | .not body => a "tptp-fof-named:not" [encodeFormula body]
  | .and left right =>
      a "tptp-fof-named:and" [encodeFormula left, encodeFormula right]
  | .or left right =>
      a "tptp-fof-named:or" [encodeFormula left, encodeFormula right]
  | .iff left right =>
      a "tptp-fof-named:iff" [encodeFormula left, encodeFormula right]
  | .implies left right =>
      a "tptp-fof-named:implies" [encodeFormula left, encodeFormula right]
  | .reverseImplies left right =>
      a "tptp-fof-named:reverse-implies"
        [encodeFormula left, encodeFormula right]
  | .xor left right =>
      a "tptp-fof-named:xor" [encodeFormula left, encodeFormula right]
  | .nor left right =>
      a "tptp-fof-named:nor" [encodeFormula left, encodeFormula right]
  | .nand left right =>
      a "tptp-fof-named:nand" [encodeFormula left, encodeFormula right]
  | .all binder body =>
      a "tptp-fof-named:all" [encodeName binder, encodeFormula body]
  | .ex binder body =>
      a "tptp-fof-named:ex" [encodeName binder, encodeFormula body]

namespace Canary

def source : NamedFormula :=
  .all "X" (.ex "X" (.equal (.variable "X") (.variable "X")))

def encoded : Pattern :=
  a "tptp-fof-named:all" [encodeName "X",
    a "tptp-fof-named:ex" [encodeName "X",
      a "tptp-fof-named:equal" [
        a "tptp-fof-named:term-variable" [encodeName "X"],
        a "tptp-fof-named:term-variable" [encodeName "X"]]]]

theorem encoding_is_exact : encodeFormula source = encoded := by
  rfl

theorem invented_computation_is_absent :
    language.rewrites = [] := by
  rfl

end Canary

#print axioms language_validate
#print axioms every_constructor_is_inert
#print axioms theory_no_step
#print axioms language_supported
#print axioms wire_isSome
#print axioms Canary.encoding_is_exact
#print axioms Canary.invented_computation_is_absent

end Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef
