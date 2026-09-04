import Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-!
# Grounding boundary for selected-native hypothetical elimination

The generated eliminator calls one ordinary rule metavariable
`generic-focus`, but ordinary `RuleInstance` arguments must be ground.  This
module records that boundary with an executable nontrivial generated fixture.

The positive control supplies a closed term at the `generic-focus` argument
position.  It passes both generic local gates: argument validity and authored
side conditions.  The negative control supplies a free schema variable at the
same position; it fails argument validity.

This does not assign a semantics to hypothetical elimination.  It proves that
the current generic checker does not manufacture eigenvariable authority from
the spelling `generic-focus` or from a nested `variableClaim`.  A sound and
usable eliminator must therefore represent binding in closed syntax or extend
the rule-application boundary with explicit freshness authority.
-/

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeEliminationFreshnessBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus.Canary

private abbrev demand := middleDemand .star

private abbrev slot : Occurrence demand :=
  ⟨0, by simp [middleDemand]⟩

private def atom (name : String) : Pattern :=
  .apply name []

/-- A deliberately closed value placed in the argument position named
`generic-focus`. -/
def groundGenericFocus : Pattern :=
  atom "$canary:ground-generic-focus"

/-- Complete closed argument vector for the two-rely elimination fixture. -/
def groundArguments : List Pattern :=
  [ atom "gamma", atom "delta", atom "family", atom "predicate"
  , groundGenericFocus, atom "reduct", atom "member"
  , atom "left-type", atom "left-value"
  , atom "right-type", atom "right-value" ]

/-- The same vector with a free schema variable at `generic-focus`. -/
def openArguments : List Pattern :=
  [ atom "gamma", atom "delta", atom "family", atom "predicate"
  , .fvar "would-be-eigenvariable", atom "reduct", atom "member"
  , atom "left-type", atom "left-value"
  , atom "right-type", atom "right-value" ]

/-- A closed argument vector in which the purportedly generic focus is the
same occurrence as the conclusion member. -/
def collidingMemberArguments : List Pattern :=
  [ atom "gamma", atom "delta", atom "family", atom "predicate"
  , groundGenericFocus, atom "reduct", groundGenericFocus
  , atom "left-type", atom "left-value"
  , atom "right-type", atom "right-value" ]

/-- A closed argument vector in which the purportedly generic focus occurs
inside the predicate supplied to the elimination rule. -/
def capturedPredicateArguments : List Pattern :=
  [ atom "gamma", atom "delta", atom "family"
  , .apply "$canary:predicate-containing-focus" [groundGenericFocus]
  , groundGenericFocus, atom "reduct", atom "member"
  , atom "left-type", atom "left-value"
  , atom "right-type", atom "right-value" ]

def eliminationSchema : RuleSchema :=
  lowerRule (eliminationRule demand slot)

/-- The fifth argument of the generated schema is exactly the ordinary
depth-zero metavariable called `generic-focus`. -/
theorem elimination_metavariables_exact :
    eliminationSchema.metavariables =
      [("Gamma", 0), ("Delta", 0), ("result-family", 0), ("predicate", 0),
       ("generic-focus", 0), ("reduct", 0), ("member", 0),
       (relyTypeName 0, 0), (relyValueName 0, 0),
       (relyTypeName 1, 0), (relyValueName 1, 0)] := by
  simp [eliminationSchema, ContextualInference.lowerRule, eliminationRule,
    relyMetavariables, middle_bindingsAt, slot]

theorem ground_generic_focus_is_closed :
    groundGenericFocus.isGround = true := by
  rfl

/-- The generic local checker accepts a ground value in the position called
`generic-focus`; the generated rule declares no compensating freshness side
condition. -/
theorem ground_generic_focus_passes_local_contract :
    argumentsValidAt eliminationSchema.metavariables groundArguments = true ∧
      RuleSchema.sideConditionsHold eliminationSchema groundArguments = true := by
  constructor
  · simp [eliminationSchema, groundArguments, groundGenericFocus, atom,
      ContextualInference.lowerRule, eliminationRule, relyMetavariables,
      middle_bindingsAt, slot, argumentsValidAt, argumentValidAt,
      Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]
  · simp [eliminationSchema, ContextualInference.lowerRule, eliminationRule,
      RuleSchema.sideConditionsHold]

/-- Conversely, a free pattern metavariable cannot serve as an eigenvariable
argument because ordinary rule instances require closed arguments. -/
theorem open_generic_focus_fails_argument_contract :
    argumentsValidAt eliminationSchema.metavariables openArguments = false := by
  simp [eliminationSchema, openArguments, atom,
    ContextualInference.lowerRule, eliminationRule, relyMetavariables,
    middle_bindingsAt, slot, argumentsValidAt, argumentValidAt,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- Groundness alone does not enforce eigenvariable separation: the generic
focus may currently be instantiated by the very same term as the conclusion
member. -/
theorem colliding_member_passes_local_contract :
    argumentsValidAt eliminationSchema.metavariables
        collidingMemberArguments = true ∧
      RuleSchema.sideConditionsHold eliminationSchema
        collidingMemberArguments = true := by
  constructor
  · simp [eliminationSchema, collidingMemberArguments, groundGenericFocus,
      atom, ContextualInference.lowerRule, eliminationRule,
      relyMetavariables, middle_bindingsAt, slot, argumentsValidAt,
      argumentValidAt, Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]
  · simp [eliminationSchema, ContextualInference.lowerRule,
      eliminationRule, RuleSchema.sideConditionsHold]

/-- Nor does the current local contract prevent the purportedly generic focus
from occurring in the predicate that is transported to the conclusion. -/
theorem captured_predicate_passes_local_contract :
    argumentsValidAt eliminationSchema.metavariables
        capturedPredicateArguments = true ∧
      RuleSchema.sideConditionsHold eliminationSchema
        capturedPredicateArguments = true := by
  constructor
  · simp [eliminationSchema, capturedPredicateArguments,
      groundGenericFocus, atom, ContextualInference.lowerRule,
      eliminationRule, relyMetavariables, middle_bindingsAt, slot,
      argumentsValidAt, argumentValidAt, Pattern.isGroundAt,
      Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]
  · simp [eliminationSchema, ContextualInference.lowerRule,
      eliminationRule, RuleSchema.sideConditionsHold]

#print axioms elimination_metavariables_exact
#print axioms ground_generic_focus_is_closed
#print axioms ground_generic_focus_passes_local_contract
#print axioms open_generic_focus_fails_argument_contract
#print axioms colliding_member_passes_local_contract
#print axioms captured_predicate_passes_local_contract

end Mettapedia.OSLF.Framework.SelectedNativeTypeEliminationFreshnessBoundary
