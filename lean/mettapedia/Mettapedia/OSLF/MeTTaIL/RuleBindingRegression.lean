import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# Rule binding regression checks

These checks characterize the current rule executor and the existing syntax
validator. They do not define an additional class of admissible languages.
In particular, variable availability does not establish capture avoidance,
and the output of a quantified premise is local to that premise.

The open premise-output example records an unresolved executor defect. Its
closed instance is a positive control. A repair must change the former
behavior while retaining the latter, rather than merely accepting a rule
because its variable names pass a finite scan.
-/

namespace Mettapedia.OSLF.MeTTaIL.RuleBindingRegression

open Syntax Match Engine

set_option autoImplicit false

def premiseOutputRule : RewriteRule where
  name := "premise-output-under-binder"
  typeContext := []
  premises := [.relationQuery "eq" [.fvar "X", .fvar "Y"]]
  left := .apply "f" [.fvar "X"]
  right := .lambda none (.fvar "Y")

def premiseOutputLanguage : LanguageDef where
  name := "premise-output-regression"
  types := []
  terms := []
  equations := []
  rewrites := [premiseOutputRule]

/-- Name availability passes the existing syntax check; this is not a
capture-avoidance certificate. -/
theorem premise_output_passes_pattern_validation :
    LanguageDef.validateRulePatterns "test" [] premiseOutputRule.typeContext
      premiseOutputRule.premises premiseOutputRule.left premiseOutputRule.right = [] := by
  simp [premiseOutputRule, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    LanguageDef.premiseLocallyScoped,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

theorem premise_output_has_no_lhs_origin :
    captureDepth "Y" 0 premiseOutputRule.left = none := by decide +kernel

/-- The built-in equality query produces Y from X. The current applier
incorrectly inserts its open value without weakening under the new binder. -/
theorem open_premise_output_is_captured :
    applyRuleWithPremisesUsing RelationEnv.empty premiseOutputLanguage
      premiseOutputRule (.apply "f" [.bvar 0])
      = [.lambda none (.bvar 0)] := by decide +kernel

theorem open_premise_output_is_not_weakened :
    applyRuleWithPremisesUsing RelationEnv.empty premiseOutputLanguage
      premiseOutputRule (.apply "f" [.bvar 0])
      ≠ [.lambda none (.bvar 1)] := by decide +kernel

/-- A closed value takes the same route without a capture discrepancy. -/
theorem closed_premise_output_is_preserved :
    applyRuleWithPremisesUsing RelationEnv.empty premiseOutputLanguage
      premiseOutputRule (.apply "f" [.apply "a" []])
      = [.lambda none (.apply "a" [])] := by decide +kernel

def localPremise : Premise :=
  .forAll "items" "x" (.congruence (.fvar "x") (.fvar "Y"))

/-- The established premise analysis does not export local bindings. -/
theorem quantified_premise_exports_no_bindings
    (bound : List String) (collection parameter : String) (body : Premise) :
    LanguageDef.premiseProducedFvarNames bound
      (.forAll collection parameter body) = [] := rfl

/-- In contrast, a top-level congruence can produce its target bindings. -/
theorem top_level_congruence_exports_target :
    LanguageDef.premiseProducedFvarNames []
      (.congruence (.fvar "x") (.fvar "Y")) = ["Y"] := by
  simp [LanguageDef.premiseProducedFvarNames, LanguageDef.patternFvarNames,
    Pattern.freeFvarNames]

/-- The actual validator rejects an attempted escape from a quantified premise. -/
theorem quantified_local_escape_is_rejected :
    (LanguageDef.validateRulePatterns "test" [] [] [localPremise]
      (.apply "f" []) (.fvar "Y")).isEmpty = false := by
  simp [localPremise, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

/-- No new variable collector is needed: syntax already counts collection rests. -/
theorem rest_is_in_syntactic_support :
    (Pattern.collection .hashBag [.fvar "S"] (some "rest")).freeFvarNames
      = ["S", "rest"] := by simp [Pattern.freeFvarNames]

end Mettapedia.OSLF.MeTTaIL.RuleBindingRegression
