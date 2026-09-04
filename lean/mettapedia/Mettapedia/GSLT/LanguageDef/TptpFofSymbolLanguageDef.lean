import Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Inert semantic symbol carrier for TPTP FOF

This carrier makes the official TPTP symbol class part of an internal symbol's
identity.  Plain atomic-word spelling alternatives intentionally share one
constructor; defined words, system words, the three number classes, and
distinct objects remain separate.

All constructors are inert.  The carrier can therefore be shared by the named
and binder-resolved FOF languages without adding a second operational
authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSymbolLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity

private def ctor (label category : String) : GrammarRule := {
  label
  category
  params := [.simple "lexeme" (.base "String")]
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

def terms : List GrammarRule := [
  ctor "tptp-fof-symbol:function-plain" "TptpFofSymbol:FunctionHead",
  ctor "tptp-fof-symbol:function-defined" "TptpFofSymbol:FunctionHead",
  ctor "tptp-fof-symbol:function-system" "TptpFofSymbol:FunctionHead",
  ctor "tptp-fof-symbol:function-integer" "TptpFofSymbol:FunctionHead",
  ctor "tptp-fof-symbol:function-rational" "TptpFofSymbol:FunctionHead",
  ctor "tptp-fof-symbol:function-real" "TptpFofSymbol:FunctionHead",
  ctor "tptp-fof-symbol:function-distinct-object"
    "TptpFofSymbol:FunctionHead",
  ctor "tptp-fof-symbol:predicate-plain" "TptpFofSymbol:PredicateHead",
  ctor "tptp-fof-symbol:predicate-defined" "TptpFofSymbol:PredicateHead",
  ctor "tptp-fof-symbol:predicate-system" "TptpFofSymbol:PredicateHead"
]

def language : LanguageDef := {
  name := "TptpFofSymbol"
  types := [
    { name := "String", carrier := .builtinString },
    "TptpFofSymbol:FunctionHead", "TptpFofSymbol:PredicateHead"]
  terms
  equations := []
  rewrites := []
}

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

theorem every_constructor_is_inert :
    terms.all (fun term => term.evalPolicy? = none) = true := by
  decide +kernel

theorem no_equations : language.equations = [] := rfl
theorem no_rewrites : language.rewrites = [] := rfl

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_equation_free rfl)

theorem theory_no_step (source target : Pattern) :
    Not (theory.Step source target) := by
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

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def encodeFunctionHead (head : FunctionHead) : Pattern :=
  let constructor := match head.kind with
    | .plain => "tptp-fof-symbol:function-plain"
    | .defined => "tptp-fof-symbol:function-defined"
    | .system => "tptp-fof-symbol:function-system"
    | .integer => "tptp-fof-symbol:function-integer"
    | .rational => "tptp-fof-symbol:function-rational"
    | .real => "tptp-fof-symbol:function-real"
    | .distinctObject => "tptp-fof-symbol:function-distinct-object"
  a constructor [a head.lexeme]

def encodePredicateHead (head : PredicateHead) : Pattern :=
  let constructor := match head.kind with
    | .plain => "tptp-fof-symbol:predicate-plain"
    | .defined => "tptp-fof-symbol:predicate-defined"
    | .system => "tptp-fof-symbol:predicate-system"
  a constructor [a head.lexeme]

def decodeFunctionHead? : Pattern -> Option FunctionHead
  | .apply "tptp-fof-symbol:function-plain" [.apply lexeme []] =>
      some ⟨.plain, lexeme⟩
  | .apply "tptp-fof-symbol:function-defined" [.apply lexeme []] =>
      some ⟨.defined, lexeme⟩
  | .apply "tptp-fof-symbol:function-system" [.apply lexeme []] =>
      some ⟨.system, lexeme⟩
  | .apply "tptp-fof-symbol:function-integer" [.apply lexeme []] =>
      some ⟨.integer, lexeme⟩
  | .apply "tptp-fof-symbol:function-rational" [.apply lexeme []] =>
      some ⟨.rational, lexeme⟩
  | .apply "tptp-fof-symbol:function-real" [.apply lexeme []] =>
      some ⟨.real, lexeme⟩
  | .apply "tptp-fof-symbol:function-distinct-object" [.apply lexeme []] =>
      some ⟨.distinctObject, lexeme⟩
  | _ => none

def decodePredicateHead? : Pattern -> Option PredicateHead
  | .apply "tptp-fof-symbol:predicate-plain" [.apply lexeme []] =>
      some ⟨.plain, lexeme⟩
  | .apply "tptp-fof-symbol:predicate-defined" [.apply lexeme []] =>
      some ⟨.defined, lexeme⟩
  | .apply "tptp-fof-symbol:predicate-system" [.apply lexeme []] =>
      some ⟨.system, lexeme⟩
  | _ => none

theorem decode_encodeFunctionHead (head : FunctionHead) :
    decodeFunctionHead? (encodeFunctionHead head) = some head := by
  cases head with
  | mk kind lexeme => cases kind <;> rfl

theorem decode_encodePredicateHead (head : PredicateHead) :
    decodePredicateHead? (encodePredicateHead head) = some head := by
  cases head with
  | mk kind lexeme => cases kind <;> rfl

namespace Canary

theorem same_lexeme_different_function_classes_encode_differently :
    encodeFunctionHead ⟨.plain, "2"⟩ !=
      encodeFunctionHead ⟨.integer, "2"⟩ := by
  decide

theorem malformed_symbol_fails_closed :
    decodeFunctionHead? (a "tptp-fof-symbol:function-plain") = none := by
  rfl

end Canary

#print axioms language_validate
#print axioms theory_no_step
#print axioms decode_encodeFunctionHead
#print axioms decode_encodePredicateHead
#print axioms Canary.same_lexeme_different_function_classes_encode_differently
#print axioms Canary.malformed_symbol_fails_closed

end Mettapedia.GSLT.LanguageDef.TptpFofSymbolLanguageDef
