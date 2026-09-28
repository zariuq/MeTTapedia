import Mettapedia.GSLT.LanguageDef.RestAwareChecker
import Mettapedia.GSLT.LanguageDef.TypedOccurrenceAddress
import Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression

/-!
# A sorted conditional premise-output regression

The original premise-output capture regression has a `Term` left side and an
arrow-typed right side. This instance keeps its equality premise and produced
metavariable but puts the same binder around both sides, so schema-side
typing can be checked. The open target keeps its ambient variable after the
premise produces the right-hand metavariable.
-/

namespace Mettapedia.GSLT.Examples.TypedPremiseOutput

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
open Mettapedia.OSLF.MeTTaIL.Engine

set_option autoImplicit false

private abbrev term : TypeExpr := .base "Term"

/-- The original raw capture regression has mismatched side types: its
constructor left side has a base sort, while its lambda right side has an
arrow sort. It remains a valid raw binding regression, not a sorted rule. -/
theorem originalPremiseRuleNotSchemaTyped :
    ¬ Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewriteHasType
      Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage
      Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule := by
  intro typed
  obtain ⟨_, leftTyped, rightTyped⟩ := typed
  cases rightTyped with
  | lambda _ =>
      obtain ⟨_, _, _, impossible⟩ :=
        declared_constructor_of_hasType_apply leftTyped.forget
      cases impossible

def sortedPremiseRule : RewriteRule :=
  { Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule with
    name := "sorted-premise-output-under-binder"
    left := .lambda none (.apply "f" [.fvar "X"])
    right := .lambda none (.fvar "Y") }

def sortedPremiseLanguage : LanguageDef :=
  { Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage with
    rewrites := [sortedPremiseRule] }

theorem sortedPremiseLanguage_validates :
    sortedPremiseLanguage.validate = [] := by
  simp [LanguageDef.validate, sortedPremiseLanguage, sortedPremiseRule,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputLanguage,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputRule,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTerm, LanguageDef.validateRewrite,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.term, TypeExpr.baseType,
    TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]
  decide +kernel

theorem sortedPremiseBindingsValid :
    bindingDeclarationsValid sortedPremiseLanguage = true := by
  unfold bindingDeclarationsValid
  rw [sortedPremiseLanguage_validates]
  decide +kernel

theorem sortedPremiseExecutable :
    scopedRewritesExecutable sortedPremiseLanguage = true := by
  unfold scopedRewritesExecutable
  rw [sortedPremiseBindingsValid]
  decide +kernel

theorem sortedPremiseSchemaTyped :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewriteHasType
      sortedPremiseLanguage sortedPremiseRule := by
  refine ⟨.arrow term term, ?_, ?_⟩
  · exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)
  · exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)

/-- The premise-produced `Y` is addressed under exactly the right-hand
lambda. The actual executable depth reader agrees with the typed zipper. -/
theorem producedOutputAddressSummary :
    (termZipperAt? sortedPremiseRule.right [0]).map
      (fun entry => (entry.1, binderCount entry.2)) =
        some ("Y", 1) := by
  decide +kernel

theorem producedOutputAddressTyped :
    ∃ context focusBound result binderPrefix,
      termZipperAt? sortedPremiseRule.right [0] =
        some ("Y", context) ∧
      TypedAt sortedPremiseLanguage
        (FreeTypeContext.ofList sortedPremiseRule.typeContext)
        (.fvar "Y") context [] (.arrow term term)
        focusBound result ∧
      FreeTypeContext.ofList sortedPremiseRule.typeContext "Y" =
        some result ∧
      focusBound = binderPrefix ∧ binderPrefix.length = 1 ∧
      occurrenceDepthAt? sortedPremiseRule.right [0] 0 = some 1 := by
  have rightTyped :
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
        sortedPremiseLanguage
        (FreeTypeContext.ofList sortedPremiseRule.typeContext) []
        sortedPremiseRule.right (.arrow term term) :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)
  obtain ⟨context, focusBound, result, binderPrefix, decoded, selected,
      lookup, prefixEq, prefixLength, runtimeDepth⟩ :=
    rightTyped.typedAtAddress_of_summary producedOutputAddressSummary
  exact ⟨context, focusBound, result, binderPrefix, decoded, selected,
    lookup, by simpa using prefixEq, prefixLength, runtimeDepth⟩

def openInput : Pattern :=
  .lambda none (.apply "f" [.bvar 1])

def openOutput : Pattern :=
  .lambda none (.bvar 1)

theorem openInputTyped :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      sortedPremiseLanguage FreeTypeContext.empty [term] openInput
      (.arrow term term) :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
    (by decide +kernel)

theorem openOutputTyped :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      sortedPremiseLanguage FreeTypeContext.empty [term] openOutput
      (.arrow term term) :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
    (by decide +kernel)

/-- A top-level equality premise produces `Y` from the ambient value of
`X`; instantiation below the right-hand binder preserves that ambient value. -/
theorem openPremiseOutputKeepsAmbientVariable :
    applyRuleAt RelationEnv.empty sortedPremiseLanguage 1
      sortedPremiseRule openInput = [openOutput] := by
  decide +kernel

theorem closedPremiseOutputStaysClosed :
    applyRuleAt RelationEnv.empty sortedPremiseLanguage 0
      sortedPremiseRule
      (.lambda none (.apply "f" [.apply "a" []])) =
      [.lambda none (.apply "a" [])] := by
  decide +kernel

end Mettapedia.GSLT.Examples.TypedPremiseOutput
