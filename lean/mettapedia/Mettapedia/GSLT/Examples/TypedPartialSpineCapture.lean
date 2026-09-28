import Mettapedia.GSLT.LanguageDef.TypedPartialSpineRecovery
import Mettapedia.GSLT.Examples.ScopedPremiseAuthoring

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.TypedPartialSpineCapture

open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.Examples.ScopedPremiseAuthoring
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

private def term : TypeExpr := .base "Term"

/-- A nested-binder rule captures X using the inner binder, leaving the
outer binder outside X's declared dependency context. -/
def partialRule : RewriteRule :=
  { «name» := "KeepInner",
    typeContext := [("X", term)], premises := [],
    left := .apply "Lam" [.lambda none
      (.apply "Lam" [.lambda none (.fvar "X")])],
    right := .apply "Lam" [.lambda none
      (.apply "Lam" [.lambda none (.bvar 0)])],
    bindings := some
      { dependencies := [("X", [term])],
        occurrences :=
          [{ «name» := "X", site := .left, path := [0, 0, 0, 0],
             arguments := [.bvar 0] }] } }

def partialLanguage : LanguageDef :=
  { lambdaScoped with «rewrites» := [partialRule] }

private def spec : RuleBindingSpec :=
  partialRule.bindings.getD { dependencies := [] }

private def free : FreeTypeContext :=
  FreeTypeContext.ofList partialRule.typeContext

private def captured : ContextualValue :=
  ContextualValue.mk [term] 0 (.bvar 0)

private def completed : Assignment := [("X", captured)]

theorem authored_language_valid : partialLanguage.validate = [] := by
  simp [LanguageDef.validate, partialLanguage, lambdaScoped,
    LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith,
    LanguageDef.nullaryLabels, LanguageDef.ofCore,
    RewriteRule.resolveNullary, Premise.resolveNullary,
    Pattern.resolveNullary, Pattern.resolveNullaryList,
    Pattern.eraseBinderMetadata,
    LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, LanguageDef.typeNames,
    TypeExpr.baseNames, TermParam.bodyName, TermParam.binderNames,
    TermParam.typeExpr, partialRule, term]
  decide +kernel

theorem authored_binding_admitted : admittedFor partialRule spec = true := by
  decide +kernel

theorem authored_site :
    dependencies? spec "X" = some [term] ∧
    arguments? partialRule spec "X" .left [0, 0, 0, 0] =
      some [.bvar 0] ∧
    occurrenceDepthAtSite? partialRule .left [0, 0, 0, 0] = some 2 := by
  decide +kernel

theorem selected_spine :
    PartialSortedSpine [term] [term, term] [0] := by
  refine ⟨by decide, ?_, ?_⟩
  · intro index member
    simp at member
    subst index
    decide
  · intro index member
    simp at member
    subst index
    decide

theorem selected_target :
    UsesOnlySelectedLocals [term, term] [0] (.bvar 0) := by
  intro index used bounded
  cases used with
  | bvar => simp

theorem open_target_typed :
    HasType partialLanguage free [term, term] (.bvar 0) term := by
  exact .bvar (by decide)

theorem exact_capture :
    capture? partialRule spec 0 2 .left [0, 0, 0, 0]
      [] "X" (.bvar 0) = some completed := by
  decide +kernel

private theorem empty_typed :
    AssignmentHasTypes partialLanguage free spec [] [] := by
  intro capturedName capturedValue membership
  cases membership

theorem capture_keeps_type :
    AssignmentHasTypes partialLanguage free spec [] completed := by
  obtain ⟨declared, atSite, _⟩ := authored_site
  exact capture?_partialSortedSpine_preserves_types_from_success
    partialLanguage free partialRule spec [] [term] [term, term]
    .left [0, 0, 0, 0] [] completed "X" (.bvar 0) term
    [.bvar 0] [0]
    empty_typed
    declared atSite (by decide) selected_spine
    (by decide) open_target_typed exact_capture

theorem omitted_binder_rejected :
    capture? partialRule spec 0 2 .left [0, 0, 0, 0]
      [] "X" (.bvar 1) = none := by
  decide +kernel

#print axioms capture_keeps_type
#print axioms omitted_binder_rejected

end Mettapedia.GSLT.Examples.TypedPartialSpineCapture
