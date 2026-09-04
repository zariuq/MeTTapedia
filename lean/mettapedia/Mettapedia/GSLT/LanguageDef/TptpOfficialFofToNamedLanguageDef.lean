import Mettapedia.GSLT.LanguageDef.TptpOfficialFofElaboration
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Official TPTP FOF to named FOF

This language is the authored transformation from the official TPTP 9.2 FOF
abstract syntax to the named semantic FOF carrier.  The official and named
languages share the builtin `String` interface; all other named carriers and
constructors remain namespaced.  The original parser-produced constructor
identities are retained exactly.

The first completed layer is term elaboration.  Every accepted official FOF
term form is covered: variables, plain, defined, system, numeric, distinct,
nullary, and applied terms.  Recursive argument traversal is expressed only
with authored congruence premises.  Formula elaboration extends this same
language rather than introducing another term decoder.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

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

def translateTerm (source : Pattern) : Pattern :=
  a "tptp-fof-elab:term" [source]

def translateArguments (source : Pattern) : Pattern :=
  a "tptp-fof-elab:arguments" [source]

def targetName (lexeme : Pattern) : Pattern :=
  a "tptp-fof-named:name" [lexeme]

def targetVariable (lexeme : Pattern) : Pattern :=
  a "tptp-fof-named:term-variable" [targetName lexeme]

def targetFunctionHead (constructor : String) (lexeme : Pattern) : Pattern :=
  a constructor [lexeme]

def targetFunction (head arguments : Pattern) : Pattern :=
  a "tptp-fof-named:term-function" [head, arguments]

def targetTermsNil : Pattern :=
  a "tptp-fof-named:terms-nil"

def targetTermsCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-named:terms-cons" [head, tail]

def sourceToken (label : String) (lexeme : Pattern) : Pattern :=
  a label [lexeme]

def sourceAtomicWord (alternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  a alternative [sourceToken tokenLabel lexeme]

def sourcePlainTerm (body : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-1" [body]]

def sourceDefinedTerm (body : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [body]]

def sourceSystemTerm (body : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-3" [body]]

def variableRule : RewriteRule :=
  mkRule "tptp-fof-elab:term-variable" [("lexeme", "String")] []
    (translateTerm <| a "tptp92-ast:fof-term:alt-2" [
      a "tptp92-ast:variable:alt-1" [
        sourceToken "tptp92-ast:token:upper-word" (v "lexeme")]])
    (targetVariable (v "lexeme"))

def plainNullaryRule (name atomicAlternative tokenLabel : String) :
    RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (translateTerm <| sourcePlainTerm <|
      a "tptp92-ast:fof-plain-term:alt-1" [
        a "tptp92-ast:constant:alt-1" [
          a "tptp92-ast:functor:alt-1" [
            sourceAtomicWord atomicAlternative tokenLabel (v "lexeme")]]])
    (targetFunction
      (targetFunctionHead "tptp-fof-symbol:function-plain" (v "lexeme"))
      targetTermsNil)

def plainAppliedRule (name atomicAlternative tokenLabel : String) :
    RewriteRule :=
  mkRule name
    [("lexeme", "String"),
     ("arguments", "Tptp92Ast:fof-arguments"),
     ("argumentsResult", "TptpNamedFof:Terms")]
    [congruence (translateArguments (v "arguments")) (v "argumentsResult")]
    (translateTerm <| sourcePlainTerm <|
      a "tptp92-ast:fof-plain-term:alt-2" [
        a "tptp92-ast:functor:alt-1" [
          sourceAtomicWord atomicAlternative tokenLabel (v "lexeme")],
        v "arguments"])
    (targetFunction
      (targetFunctionHead "tptp-fof-symbol:function-plain" (v "lexeme"))
      (v "argumentsResult"))

def numberRule (name numberAlternative tokenLabel targetHead : String) : RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (translateTerm <| sourceDefinedTerm <|
      a "tptp92-ast:fof-defined-term:alt-1" [
        a "tptp92-ast:defined-term:alt-1" [
          a numberAlternative [sourceToken tokenLabel (v "lexeme")]]])
    (targetFunction (targetFunctionHead targetHead (v "lexeme")) targetTermsNil)

def distinctRule : RewriteRule :=
  mkRule "tptp-fof-elab:term-distinct" [("lexeme", "String")] []
    (translateTerm <| sourceDefinedTerm <|
      a "tptp92-ast:fof-defined-term:alt-1" [
        a "tptp92-ast:defined-term:alt-2" [
          sourceToken "tptp92-ast:token:distinct-object" (v "lexeme")]])
    (targetFunction
      (targetFunctionHead "tptp-fof-symbol:function-distinct-object"
        (v "lexeme"))
      targetTermsNil)

def sourceDefinedFunctor (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:defined-functor:alt-1" [
    a "tptp92-ast:atomic-defined-word:alt-1" [
      sourceToken "tptp92-ast:token:dollar-word" lexeme]]

def definedNullaryRule : RewriteRule :=
  mkRule "tptp-fof-elab:term-defined-nullary" [("lexeme", "String")] []
    (translateTerm <| sourceDefinedTerm <|
      a "tptp92-ast:fof-defined-term:alt-2" [
        a "tptp92-ast:fof-defined-atomic-term:alt-1" [
          a "tptp92-ast:fof-defined-plain-term:alt-1" [
            a "tptp92-ast:defined-constant:alt-1" [
              sourceDefinedFunctor (v "lexeme")]]]])
    (targetFunction
      (targetFunctionHead "tptp-fof-symbol:function-defined" (v "lexeme"))
      targetTermsNil)

def definedAppliedRule : RewriteRule :=
  mkRule "tptp-fof-elab:term-defined-applied"
    [("lexeme", "String"),
     ("arguments", "Tptp92Ast:fof-arguments"),
     ("argumentsResult", "TptpNamedFof:Terms")]
    [congruence (translateArguments (v "arguments")) (v "argumentsResult")]
    (translateTerm <| sourceDefinedTerm <|
      a "tptp92-ast:fof-defined-term:alt-2" [
        a "tptp92-ast:fof-defined-atomic-term:alt-1" [
          a "tptp92-ast:fof-defined-plain-term:alt-2" [
            sourceDefinedFunctor (v "lexeme"), v "arguments"]]])
    (targetFunction
      (targetFunctionHead "tptp-fof-symbol:function-defined" (v "lexeme"))
      (v "argumentsResult"))

def sourceSystemFunctor (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:system-functor:alt-1" [
    a "tptp92-ast:atomic-system-word:alt-1" [
      sourceToken "tptp92-ast:token:dollar-dollar-word" lexeme]]

def systemNullaryRule : RewriteRule :=
  mkRule "tptp-fof-elab:term-system-nullary" [("lexeme", "String")] []
    (translateTerm <| sourceSystemTerm <|
      a "tptp92-ast:fof-system-term:alt-1" [
        a "tptp92-ast:system-constant:alt-1" [
          sourceSystemFunctor (v "lexeme")]])
    (targetFunction
      (targetFunctionHead "tptp-fof-symbol:function-system" (v "lexeme"))
      targetTermsNil)

def systemAppliedRule : RewriteRule :=
  mkRule "tptp-fof-elab:term-system-applied"
    [("lexeme", "String"),
     ("arguments", "Tptp92Ast:fof-arguments"),
     ("argumentsResult", "TptpNamedFof:Terms")]
    [congruence (translateArguments (v "arguments")) (v "argumentsResult")]
    (translateTerm <| sourceSystemTerm <|
      a "tptp92-ast:fof-system-term:alt-2" [
        sourceSystemFunctor (v "lexeme"), v "arguments"])
    (targetFunction
      (targetFunctionHead "tptp-fof-symbol:function-system" (v "lexeme"))
      (v "argumentsResult"))

def argumentsOneRule : RewriteRule :=
  mkRule "tptp-fof-elab:arguments-one"
    [("term", "Tptp92Ast:fof-term"),
     ("termResult", "TptpNamedFof:Term")]
    [congruence (translateTerm (v "term")) (v "termResult")]
    (translateArguments <|
      a "tptp92-ast:fof-arguments:alt-1" [v "term"])
    (targetTermsCons (v "termResult") targetTermsNil)

def argumentsMoreRule : RewriteRule :=
  mkRule "tptp-fof-elab:arguments-more"
    [("term", "Tptp92Ast:fof-term"),
     ("arguments", "Tptp92Ast:fof-arguments"),
     ("termResult", "TptpNamedFof:Term"),
     ("argumentsResult", "TptpNamedFof:Terms")]
    [congruence (translateTerm (v "term")) (v "termResult"),
     congruence (translateArguments (v "arguments")) (v "argumentsResult")]
    (translateArguments <|
      a "tptp92-ast:fof-arguments:alt-2" [v "term", v "arguments"])
    (targetTermsCons (v "termResult") (v "argumentsResult"))

def termRewrites : List RewriteRule := [
  variableRule,
  plainNullaryRule "tptp-fof-elab:term-plain-lower-nullary"
    "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word",
  plainNullaryRule "tptp-fof-elab:term-plain-quoted-nullary"
    "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
  plainNullaryRule "tptp-fof-elab:term-plain-backquoted-nullary"
    "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted",
  plainAppliedRule "tptp-fof-elab:term-plain-lower-applied"
    "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word",
  plainAppliedRule "tptp-fof-elab:term-plain-quoted-applied"
    "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
  plainAppliedRule "tptp-fof-elab:term-plain-backquoted-applied"
    "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted",
  numberRule "tptp-fof-elab:term-integer"
    "tptp92-ast:number:alt-1" "tptp92-ast:token:integer"
    "tptp-fof-symbol:function-integer",
  numberRule "tptp-fof-elab:term-rational"
    "tptp92-ast:number:alt-2" "tptp92-ast:token:rational"
    "tptp-fof-symbol:function-rational",
  numberRule "tptp-fof-elab:term-real"
    "tptp92-ast:number:alt-3" "tptp92-ast:token:real"
    "tptp-fof-symbol:function-real",
  distinctRule,
  definedNullaryRule,
  definedAppliedRule,
  systemNullaryRule,
  systemAppliedRule,
  argumentsOneRule,
  argumentsMoreRule
]

def unaryRequest (label target source : String) : GrammarRule :=
  ctor label target [("source", source)] (some .rewrite)

def bodyRequest (label source : String) : GrammarRule :=
  ctor label "TptpNamedFof:Formula"
    [("source", source), ("body", "TptpNamedFof:Formula")]
    (some .rewrite)

/-- The official TPTP semantic production has exactly two nullary defined
propositions.  They are values of the shared builtin `String` carrier, made
explicit here so formula rules can match them without an external string
oracle. -/
def definedPropositionLexemes : List GrammarRule := [
  ctor "$true" "String" [],
  ctor "$false" "String" []
]

def requestTerms : List GrammarRule := [
  unaryRequest "tptp-fof-elab:term" "TptpNamedFof:Term"
    "Tptp92Ast:fof-term",
  unaryRequest "tptp-fof-elab:arguments" "TptpNamedFof:Terms"
    "Tptp92Ast:fof-arguments",
  unaryRequest "tptp-fof-elab:formula" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-formula",
  unaryRequest "tptp-fof-elab:logic" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-logic-formula",
  unaryRequest "tptp-fof-elab:binary" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-binary-formula",
  unaryRequest "tptp-fof-elab:binary-nonassoc" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-binary-nonassoc",
  unaryRequest "tptp-fof-elab:binary-assoc" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-binary-assoc",
  unaryRequest "tptp-fof-elab:or" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-or-formula",
  unaryRequest "tptp-fof-elab:and" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-and-formula",
  unaryRequest "tptp-fof-elab:unary" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-unary-formula",
  unaryRequest "tptp-fof-elab:unit" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-unit-formula",
  unaryRequest "tptp-fof-elab:unitary" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-unitary-formula",
  unaryRequest "tptp-fof-elab:quantified" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-quantified-formula",
  unaryRequest "tptp-fof-elab:atomic" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-atomic-formula",
  unaryRequest "tptp-fof-elab:plain-atomic" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-plain-atomic-formula",
  unaryRequest "tptp-fof-elab:defined-atomic" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-defined-atomic-formula",
  unaryRequest "tptp-fof-elab:defined-plain" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-defined-plain-formula",
  unaryRequest "tptp-fof-elab:defined-infix" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-defined-infix-formula",
  unaryRequest "tptp-fof-elab:system-atomic" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-system-atomic-formula",
  unaryRequest "tptp-fof-elab:infix-unary" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-infix-unary",
  unaryRequest "tptp-fof-elab:sequent" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-sequent",
  bodyRequest "tptp-fof-elab:bind-all" "Tptp92Ast:fof-variable-list",
  bodyRequest "tptp-fof-elab:bind-ex" "Tptp92Ast:fof-variable-list",
  unaryRequest "tptp-fof-elab:tuple-conjunction" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-formula-tuple",
  bodyRequest "tptp-fof-elab:comma-conjunction"
    "Tptp92AstList:tptp92ast-comma-fof-logic-formula",
  unaryRequest "tptp-fof-elab:tuple-disjunction" "TptpNamedFof:Formula"
    "Tptp92Ast:fof-formula-tuple",
  bodyRequest "tptp-fof-elab:comma-disjunction"
    "Tptp92AstList:tptp92ast-comma-fof-logic-formula"
]

/-- The official AST and named FOF share only the builtin `String` row. -/
def namedAdditionalTypes : List TypeDecl :=
  TptpNamedFofLanguageDef.language.types.drop 1

def officialDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpOfficialAbstractSyntax.language {}

def syntaxExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists namedAdditionalTypes
    (TptpNamedFofLanguageDef.language.terms ++
      definedPropositionLexemes ++ requestTerms)
    (some "TptpOfficialFofToNamed")

def syntaxDefinition : CalculusLanguageDef :=
  syntaxExtension.apply officialDefinition

def syntaxLanguage : LanguageDef := syntaxDefinition.toLanguageDef

def language : LanguageDef := {
  syntaxLanguage with rewrites := termRewrites
}

private theorem namedAdditionalTypes_disjoint :
    List.Disjoint officialDefinition.typeNames
      (namedAdditionalTypes.map (·.name)) := by
  rw [List.disjoint_left]
  intro name sourceMembership targetMembership
  simp [namedAdditionalTypes, TptpNamedFofLanguageDef.language,
    TptpNamedFofLanguageDef.ownTypes,
    TptpFofSymbolLanguageDef.language]
      at targetMembership
  rcases targetMembership with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change _ ∈ TptpOfficialAbstractSyntax.language.typeNames at sourceMembership
    revert sourceMembership
    decide +kernel

private theorem addedTermLabels_disjoint :
    List.Disjoint (officialDefinition.terms.map (·.label))
      ((TptpNamedFofLanguageDef.language.terms ++
        definedPropositionLexemes ++ requestTerms).map (·.label)) := by
  have namespaced :
      (officialDefinition.terms.map (·.label)).all
        (fun label => label.startsWith "tptp92-ast:") = true := by
    decide +kernel
  have addedNotNamespaced :
      ((TptpNamedFofLanguageDef.language.terms ++
        definedPropositionLexemes ++ requestTerms).map (·.label)).all
        (fun label => !(label.startsWith "tptp92-ast:")) = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label sourceMembership targetMembership
  have sourceNamespaced :=
    (List.all_eq_true.mp namespaced) label sourceMembership
  have targetNotNamespaced :=
    (List.all_eq_true.mp addedNotNamespaced) label targetMembership
  simp [sourceNamespaced] at targetNotNamespaced

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

private theorem syntaxLanguage_typeNames :
    syntaxLanguage.typeNames =
      TptpOfficialAbstractSyntax.language.typeNames ++
        namedAdditionalTypes.map (·.name) := by
  simp [syntaxLanguage, syntaxDefinition, syntaxExtension,
    officialDefinition, ConstructorSignatureExtension.ofLists,
    LanguageDef.typeNames]

private theorem namedTypeName_mem_syntaxLanguage
    (name : String)
    (membership : name ∈ TptpNamedFofLanguageDef.language.typeNames) :
    name ∈ syntaxLanguage.typeNames := by
  rw [syntaxLanguage_typeNames]
  have sharedOrAdditional :
      name = "String" ∨ name ∈ namedAdditionalTypes.map (·.name) := by
    simpa [namedAdditionalTypes, TptpNamedFofLanguageDef.language,
      TptpNamedFofLanguageDef.ownTypes,
      TptpFofSymbolLanguageDef.language, LanguageDef.typeNames]
      using membership
  rcases sharedOrAdditional with rfl | additional
  · exact List.mem_append_left _ (by decide +kernel)
  · exact List.mem_append_right _ additional

private theorem officialTypeName_mem_syntaxLanguage
    (name : String)
    (membership : name ∈ TptpOfficialAbstractSyntax.language.typeNames) :
    name ∈ syntaxLanguage.typeNames := by
  rw [syntaxLanguage_typeNames]
  exact List.mem_append_left _ membership

private theorem unaryRequest_validate
    (label target source : String)
    (targetMembership : target ∈ syntaxLanguage.typeNames)
    (sourceMembership : source ∈ syntaxLanguage.typeNames) :
    syntaxLanguage.validateTerm (unaryRequest label target source) = [] := by
  simp only [LanguageDef.validateTerm, unaryRequest, ctor,
    List.map_cons, List.map_nil, List.append_eq_nil_iff]
  refine ⟨⟨?_, ?_⟩, by simp⟩
  · simp [targetMembership]
  · rw [List.flatMap_eq_nil_iff]
    intro parameter parameterMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMembership
    simp only [List.mem_singleton] at parameterMembership
    subst parameter
    simp only [TermParam.typeExpr, TypeExpr.baseNames,
      List.mem_singleton] at nameMembership
    subst name
    exact sourceMembership

private theorem bodyRequest_validate
    (label source : String)
    (sourceMembership : source ∈ syntaxLanguage.typeNames)
    (formulaMembership :
      "TptpNamedFof:Formula" ∈ syntaxLanguage.typeNames) :
    syntaxLanguage.validateTerm (bodyRequest label source) = [] := by
  simp only [LanguageDef.validateTerm, bodyRequest, ctor,
    List.map_cons, List.map_nil, List.append_eq_nil_iff]
  refine ⟨⟨?_, ?_⟩, by simp⟩
  · simp [formulaMembership]
  · rw [List.flatMap_eq_nil_iff]
    intro parameter parameterMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMembership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at parameterMembership
    rcases parameterMembership with rfl | rfl
    · simp only [TermParam.typeExpr, TypeExpr.baseNames,
        List.mem_singleton] at nameMembership
      simpa [nameMembership] using sourceMembership
    · simp only [TermParam.typeExpr, TypeExpr.baseNames,
        List.mem_singleton] at nameMembership
      simpa [nameMembership] using formulaMembership

theorem syntaxLanguage_validate : syntaxLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    officialDefinition namedAdditionalTypes
    (TptpNamedFofLanguageDef.language.terms ++
      definedPropositionLexemes ++ requestTerms)
    (some "TptpOfficialFofToNamed")
  · exact TptpOfficialAbstractSyntax.language_validate
  · rfl
  · rfl
  · decide +kernel
  · exact namedAdditionalTypes_disjoint
  · decide +kernel
  · exact addedTermLabels_disjoint
  · intro term membership
    simp only [List.mem_append] at membership
    rcases membership with namedOrLexeme | requestMembership
    · rcases namedOrLexeme with namedMembership | lexemeMembership
      · have clean := LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
          TptpNamedFofLanguageDef.language
          TptpNamedFofLanguageDef.language_validate term namedMembership
        exact validateTerm_mono TptpNamedFofLanguageDef.language
          syntaxLanguage term clean namedTypeName_mem_syntaxLanguage
      · simp only [definedPropositionLexemes, List.mem_cons,
          List.mem_nil_iff, or_false] at lexemeMembership
        rcases lexemeMembership with rfl | rfl
        all_goals decide +kernel
    · simp only [requestTerms, List.mem_cons, List.mem_nil_iff,
        or_false] at requestMembership
      rcases requestMembership with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
        | apply unaryRequest_validate
        | apply bodyRequest_validate
      all_goals
        first
        | apply namedTypeName_mem_syntaxLanguage; decide +kernel
        | apply officialTypeName_mem_syntaxLanguage; decide +kernel

theorem source_types_are_prefix :
    TptpOfficialAbstractSyntax.language.types.IsPrefix language.types := by
  simp [language, syntaxLanguage, syntaxDefinition, syntaxExtension,
    officialDefinition, ConstructorSignatureExtension.ofLists]

theorem source_terms_are_prefix :
    TptpOfficialAbstractSyntax.language.terms.IsPrefix language.terms := by
  simp [language, syntaxLanguage, syntaxDefinition, syntaxExtension,
    officialDefinition, ConstructorSignatureExtension.ofLists]

theorem named_string_is_shared :
    TptpNamedFofLanguageDef.language.types.head? =
      TptpOfficialAbstractSyntax.language.types[1]? := by
  rfl

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  simpa [language] using
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil syntaxLanguage
      syntaxLanguage_validate

private def constructorLabelNamespaced (label : String) : Bool :=
  label.startsWith "tptp92-ast:" ||
    label.startsWith "tptp-fof-named:" ||
      label.startsWith "tptp-fof-symbol:" ||
        label.startsWith "tptp-fof-elab:" ||
        label = "$true" || label = "$false"

private theorem constructorLabels_namespaced :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelNamespaced = true := by
  decide +kernel

private theorem plainName_not_constructor (name : String)
    (plain : constructorLabelNamespaced name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have colon := (List.all_eq_true.mp constructorLabels_namespaced)
    name membership
  simp [plain] at colon

private theorem lexeme_not_constructor :
    "lexeme" ∉ RewriteValidationCertificate.constructorLabels language :=
  plainName_not_constructor "lexeme" (by simp [constructorLabelNamespaced])

private theorem arguments_not_constructor :
    "arguments" ∉ RewriteValidationCertificate.constructorLabels language :=
  plainName_not_constructor "arguments" (by simp [constructorLabelNamespaced])

private theorem argumentsResult_not_constructor :
    "argumentsResult" ∉
      RewriteValidationCertificate.constructorLabels language :=
  plainName_not_constructor "argumentsResult"
    (by simp [constructorLabelNamespaced])

private theorem term_not_constructor :
    "term" ∉ RewriteValidationCertificate.constructorLabels language :=
  plainName_not_constructor "term" (by simp [constructorLabelNamespaced])

private theorem termResult_not_constructor :
    "termResult" ∉ RewriteValidationCertificate.constructorLabels language :=
  plainName_not_constructor "termResult" (by simp [constructorLabelNamespaced])

local macro "certify_elaboration_row" : tactic =>
  `(tactic|
    (simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      variableRule, plainNullaryRule, plainAppliedRule, numberRule,
      distinctRule, definedNullaryRule, definedAppliedRule,
      systemNullaryRule, systemAppliedRule, argumentsOneRule,
      argumentsMoreRule, mkRule, typed, congruence, translateTerm,
      translateArguments, targetVariable, targetName, targetFunctionHead,
      targetFunction,
      targetTermsNil, targetTermsCons, sourcePlainTerm, sourceDefinedTerm,
      sourceSystemTerm, sourceDefinedFunctor, sourceSystemFunctor,
      sourceToken, sourceAtomicWord, a, v,
      RewriteValidationCertificate.constructorSignatures,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      lexeme_not_constructor, arguments_not_constructor,
      argumentsResult_not_constructor, term_not_constructor,
      termResult_not_constructor] <;> decide +kernel))

private theorem variableRule_checked :
    RewriteValidationCertificate.check language variableRule = true := by
  certify_elaboration_row

private theorem plainLowerNullaryRule_checked :
    RewriteValidationCertificate.check language
      (plainNullaryRule "tptp-fof-elab:term-plain-lower-nullary"
        "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word") =
      true := by
  certify_elaboration_row

private theorem plainQuotedNullaryRule_checked :
    RewriteValidationCertificate.check language
      (plainNullaryRule "tptp-fof-elab:term-plain-quoted-nullary"
        "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted") =
      true := by
  certify_elaboration_row

private theorem plainBackquotedNullaryRule_checked :
    RewriteValidationCertificate.check language
      (plainNullaryRule "tptp-fof-elab:term-plain-backquoted-nullary"
        "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted") =
      true := by
  certify_elaboration_row

private theorem plainLowerAppliedRule_checked :
    RewriteValidationCertificate.check language
      (plainAppliedRule "tptp-fof-elab:term-plain-lower-applied"
        "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word") =
      true := by
  certify_elaboration_row

private theorem plainQuotedAppliedRule_checked :
    RewriteValidationCertificate.check language
      (plainAppliedRule "tptp-fof-elab:term-plain-quoted-applied"
        "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted") =
      true := by
  certify_elaboration_row

private theorem plainBackquotedAppliedRule_checked :
    RewriteValidationCertificate.check language
      (plainAppliedRule "tptp-fof-elab:term-plain-backquoted-applied"
        "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted") =
      true := by
  certify_elaboration_row

private theorem integerRule_checked :
    RewriteValidationCertificate.check language
      (numberRule "tptp-fof-elab:term-integer"
        "tptp92-ast:number:alt-1" "tptp92-ast:token:integer"
        "tptp-fof-symbol:function-integer") = true := by
  certify_elaboration_row

private theorem rationalRule_checked :
    RewriteValidationCertificate.check language
      (numberRule "tptp-fof-elab:term-rational"
        "tptp92-ast:number:alt-2" "tptp92-ast:token:rational"
        "tptp-fof-symbol:function-rational") = true := by
  certify_elaboration_row

private theorem realRule_checked :
    RewriteValidationCertificate.check language
      (numberRule "tptp-fof-elab:term-real"
        "tptp92-ast:number:alt-3" "tptp92-ast:token:real"
        "tptp-fof-symbol:function-real") = true := by
  certify_elaboration_row

private theorem distinctRule_checked :
    RewriteValidationCertificate.check language distinctRule = true := by
  certify_elaboration_row

private theorem definedNullaryRule_checked :
    RewriteValidationCertificate.check language definedNullaryRule = true := by
  certify_elaboration_row

private theorem definedAppliedRule_checked :
    RewriteValidationCertificate.check language definedAppliedRule = true := by
  certify_elaboration_row

private theorem systemNullaryRule_checked :
    RewriteValidationCertificate.check language systemNullaryRule = true := by
  certify_elaboration_row

private theorem systemAppliedRule_checked :
    RewriteValidationCertificate.check language systemAppliedRule = true := by
  certify_elaboration_row

private theorem argumentsOneRule_checked :
    RewriteValidationCertificate.check language argumentsOneRule = true := by
  certify_elaboration_row

private theorem argumentsMoreRule_checked :
    RewriteValidationCertificate.check language argumentsMoreRule = true := by
  certify_elaboration_row

local macro "validate_elaboration_row" : tactic =>
  `(tactic|
    apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup <;>
    first
    | exact variableRule_checked
    | exact plainLowerNullaryRule_checked
    | exact plainQuotedNullaryRule_checked
    | exact plainBackquotedNullaryRule_checked
    | exact plainLowerAppliedRule_checked
    | exact plainQuotedAppliedRule_checked
    | exact plainBackquotedAppliedRule_checked
    | exact integerRule_checked
    | exact rationalRule_checked
    | exact realRule_checked
    | exact distinctRule_checked
    | exact definedNullaryRule_checked
    | exact definedAppliedRule_checked
    | exact systemNullaryRule_checked
    | exact systemAppliedRule_checked
    | exact argumentsOneRule_checked
    | exact argumentsMoreRule_checked)

/-- Every term-elaboration row remains valid for any later layer that retains
this exact source/target constructor signature. -/
theorem termRewrite_validate (rewrite : RewriteRule)
    (membership : rewrite ∈ termRewrites) :
    language.validateRewrite rewrite = [] := by
  simp only [termRewrites, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup variableRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup plainLowerNullaryRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup plainQuotedNullaryRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup plainBackquotedNullaryRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup plainLowerAppliedRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup plainQuotedAppliedRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup plainBackquotedAppliedRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup integerRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup rationalRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup realRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup distinctRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup definedNullaryRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup definedAppliedRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup systemNullaryRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup systemAppliedRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup argumentsOneRule_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      constructorLabels_nodup argumentsMoreRule_checked

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · simpa [language, LanguageDef.typeNames] using
      LanguageDef.typeNames_nodup_of_validate_eq_nil syntaxLanguage
        syntaxLanguage_validate
  · simpa [language] using
      LanguageDef.constructorLabels_nodup_of_validate_eq_nil syntaxLanguage
        syntaxLanguage_validate
  · change syntaxLanguage.equations.map (·.name) |>.Nodup
    exact LanguageDef.equationNames_nodup_of_validate_eq_nil syntaxLanguage
      syntaxLanguage_validate
  · decide +kernel
  · intro term membership
    have clean := LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      syntaxLanguage syntaxLanguage_validate term membership
    exact clean
  · intro equation membership
    change equation ∈ syntaxLanguage.equations at membership
    have noEquations : syntaxLanguage.equations = [] := rfl
    simp [noEquations] at membership
  · intro rewrite membership
    exact termRewrite_validate rewrite membership

theorem term_rewrite_count : termRewrites.length = 17 := by
  decide

private theorem official_language_supported :
    CanonicalWire.languageSupported TptpOfficialAbstractSyntax.language := by
  rw [← CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact TptpOfficialAbstractSyntax.wire_isSome

private theorem language_terms : language.terms =
    TptpOfficialAbstractSyntax.language.terms ++
      TptpNamedFofLanguageDef.language.terms ++
        definedPropositionLexemes ++ requestTerms := by
  simp [language, syntaxLanguage, syntaxDefinition, syntaxExtension,
    officialDefinition, ConstructorSignatureExtension.ofLists]

private theorem language_rewrites : language.rewrites = termRewrites := by
  rfl

private theorem terms_supported :
    language.terms.all CanonicalWire.grammarRuleSupported = true := by
  have source := official_language_supported
  have target := TptpNamedFofLanguageDef.language_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at source target
  rw [language_terms, List.all_append, List.all_append, List.all_append]
  simp [source.1.2, target.1.2, requestTerms, unaryRequest, bodyRequest, ctor,
    definedPropositionLexemes,
    CanonicalWire.grammarRuleSupported,
    CanonicalWire.termParamSupported, CanonicalWire.typeExprSupported]

private theorem rewrites_supported :
    language.rewrites.all CanonicalWire.rewriteSupported = true := by
  rw [language_rewrites]
  simp [termRewrites, variableRule, plainNullaryRule, plainAppliedRule,
    numberRule, distinctRule, definedNullaryRule, definedAppliedRule,
    systemNullaryRule, systemAppliedRule, argumentsOneRule,
    argumentsMoreRule, mkRule, typed, congruence, translateTerm,
    translateArguments, targetVariable, targetName, targetFunctionHead,
    targetFunction,
    targetTermsNil, targetTermsCons, sourcePlainTerm, sourceDefinedTerm,
    sourceSystemTerm, sourceDefinedFunctor, sourceSystemFunctor,
    sourceToken, sourceAtomicWord, a, v, CanonicalWire.rewriteSupported,
    CanonicalWire.typeBindingSupported, CanonicalWire.typeExprSupported,
    CanonicalWire.premiseSupported, CanonicalWire.patternSupported,
    CanonicalWire.patternListSupported]

theorem language_supported : CanonicalWire.languageSupported language := by
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, terms_supported⟩, rewrites_supported⟩

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

namespace Canary

def officialVariable : Pattern :=
  a "tptp92-ast:fof-term:alt-2" [
    a "tptp92-ast:variable:alt-1" [
      sourceToken "tptp92-ast:token:upper-word" (a "X")]]

theorem variable_semantics_agrees :
    TptpOfficialFofElaboration.decodeTerm? officialVariable =
      some (.variable "X") := by
  rfl

theorem variable_rewrite_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTerm officialVariable) =
      [TptpNamedFofLanguageDef.encodeTerm (.variable "X")] := by
  simp [rewriteAt, language, termRewrites, variableRule, plainNullaryRule,
    plainAppliedRule, numberRule, distinctRule, definedNullaryRule,
    definedAppliedRule, systemNullaryRule, systemAppliedRule,
    argumentsOneRule, argumentsMoreRule, mkRule, congruence, translateTerm,
    translateArguments, targetVariable, targetName, targetFunctionHead,
    targetFunction,
    targetTermsNil, targetTermsCons, sourcePlainTerm, sourceDefinedTerm,
    sourceSystemTerm, sourceDefinedFunctor, sourceSystemFunctor, sourceToken,
    sourceAtomicWord, officialVariable, a, v, TptpNamedFofLanguageDef.encodeTerm,
    TptpNamedFofLanguageDef.encodeName,
    applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
    premiseStepUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]
  rfl

def malformed : Pattern :=
  a "tptp92-ast:fof-term:alt-2" [a "invented-variable"]

theorem malformed_semantics_fails :
    TptpOfficialFofElaboration.decodeTerm? malformed = none := by
  rfl

theorem malformed_has_no_reduct (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (translateTerm malformed) = [] := by
  simp [rewriteAt, language, termRewrites, variableRule, plainNullaryRule,
    plainAppliedRule, numberRule, distinctRule, definedNullaryRule,
    definedAppliedRule, systemNullaryRule, systemAppliedRule,
    argumentsOneRule, argumentsMoreRule, mkRule, congruence, translateTerm,
    translateArguments, targetVariable, targetName, targetFunctionHead,
    targetFunction,
    targetTermsNil, targetTermsCons, sourcePlainTerm, sourceDefinedTerm,
    sourceSystemTerm, sourceDefinedFunctor, sourceSystemFunctor, sourceToken,
    sourceAtomicWord, malformed, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]

end Canary

#print axioms language_validate
#print axioms source_types_are_prefix
#print axioms source_terms_are_prefix
#print axioms named_string_is_shared
#print axioms termRewrite_validate
#print axioms language_supported
#print axioms Canary.variable_semantics_agrees
#print axioms Canary.variable_rewrite_exact
#print axioms Canary.malformed_semantics_fails
#print axioms Canary.malformed_has_no_reduct

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedLanguageDef
