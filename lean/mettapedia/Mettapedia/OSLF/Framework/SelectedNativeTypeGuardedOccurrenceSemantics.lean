import Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics

/-!
# Guarded selected-occurrence semantics

This module factors an exact selected-occurrence step into two independently
visible pieces:

1. activation evidence, consisting of a rule-local match followed by ordered
   evidence for every authored premise; and
2. structural reconstruction of the authored right-hand side from the final
   bindings.

The factorization is exact.  In particular, matching the left-hand side does
not grant premise evidence, and a missing relation query cannot be treated as
an enabled rewrite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedOccurrenceSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics

/-- Evidence that one exact authored rewrite occurrence is enabled at a source
state.  The target remains a computed projection of the final bindings. -/
structure SelectedOccurrenceActivation
    {source : ValidatedLanguageDef}
    (relations : RelationEnv) (typing : DisplayedRewriteTyping source)
    (before : Pattern) where
  premiseFuel : Nat
  initialBindings : Bindings
  finalBindings : Bindings
  matched : initialBindings ∈
    matchPatternForRule source.language typing.site.rewrite before
  premises : PremisesAt (engineBasePremises relations) source.language
    premiseFuel initialBindings typing.site.rewrite.premises finalBindings

namespace SelectedOccurrenceActivation

/-- The target reconstructed by the exact authored rewrite occurrence. -/
def target {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before : Pattern}
    (activation : SelectedOccurrenceActivation relations typing before) : Pattern :=
  applyBindingsForRule source.language typing.site.rewrite
    activation.finalBindings

/-- Activation evidence yields the exact occurrence step to its computed
target, without consulting an external transition result. -/
def toSelectedOccurrenceStep
    {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before : Pattern}
    (activation : SelectedOccurrenceActivation relations typing before) :
    SelectedOccurrenceStep relations typing before activation.target where
  premiseFuel := activation.premiseFuel
  initialBindings := activation.initialBindings
  finalBindings := activation.finalBindings
  matched := activation.matched
  premises := activation.premises
  result := rfl

/-- A premise-free authored row is enabled exactly from a successful match. -/
def ofPremiseFree
    {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before : Pattern}
    {bindings : Bindings}
    (premisesEmpty : typing.site.rewrite.premises = [])
    (matched : bindings ∈
      matchPatternForRule source.language typing.site.rewrite before) :
    SelectedOccurrenceActivation relations typing before where
  premiseFuel := 0
  initialBindings := bindings
  finalBindings := bindings
  matched := matched
  premises := by
    rw [premisesEmpty]
    exact .nil bindings

end SelectedOccurrenceActivation

/-- Forget only the reconstructed target equation, retaining all match and
ordered-premise evidence. -/
def activationOfStep
    {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before after : Pattern}
    (step : SelectedOccurrenceStep relations typing before after) :
    SelectedOccurrenceActivation relations typing before where
  premiseFuel := step.premiseFuel
  initialBindings := step.initialBindings
  finalBindings := step.finalBindings
  matched := step.matched
  premises := step.premises

@[simp] theorem activationOfStep_target
    {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before after : Pattern}
    (step : SelectedOccurrenceStep relations typing before after) :
    (activationOfStep step).target = after :=
  step.result

/-- Exact occurrence execution factors into activation evidence followed by
structural target reconstruction. -/
theorem occursAt_iff_exists_activation
    {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before after : Pattern} :
    OccursAt relations typing before after ↔
      ∃ activation : SelectedOccurrenceActivation relations typing before,
        activation.target = after := by
  constructor
  · rintro ⟨step⟩
    exact ⟨activationOfStep step, activationOfStep_target step⟩
  · rintro ⟨activation, targetEq⟩
    rw [← targetEq]
    exact ⟨activation.toSelectedOccurrenceStep⟩

/-- Propositional existence of exact match and ordered-premise evidence. -/
def CanActivate
    {source : ValidatedLanguageDef} (relations : RelationEnv)
    (typing : DisplayedRewriteTyping source) (before : Pattern) : Prop :=
  Nonempty (SelectedOccurrenceActivation relations typing before)

/-- A successful match activates a premise-free selected occurrence. -/
theorem canActivate_of_premiseFree
    {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before : Pattern}
    {bindings : Bindings}
    (premisesEmpty : typing.site.rewrite.premises = [])
    (matched : bindings ∈
      matchPatternForRule source.language typing.site.rewrite before) :
    CanActivate relations typing before :=
  ⟨SelectedOccurrenceActivation.ofPremiseFree premisesEmpty matched⟩

/-- If the ordered premises have no evidence after any successful match, the
selected occurrence cannot activate. -/
theorem not_canActivate_of_no_premise_evidence
    {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before : Pattern}
    (blocked : ∀ fuel initial final,
      initial ∈ matchPatternForRule source.language typing.site.rewrite before →
      ¬ PremisesAt (engineBasePremises relations) source.language fuel initial
        typing.site.rewrite.premises final) :
    ¬ CanActivate relations typing before := by
  rintro ⟨activation⟩
  exact blocked activation.premiseFuel activation.initialBindings
    activation.finalBindings activation.matched activation.premises

namespace Canary

private def language : LanguageDef := LanguageDef.empty "activation-canary"

private def missing : Premise :=
  .relationQuery "activation-canary:missing" []

/-- A relation premise absent from the explicit environment has no evidence.
Syntactic matching alone therefore cannot manufacture an activation. -/
theorem empty_relations_cannot_discharge_missing_query
    (fuel : Nat) (initial final : Bindings) :
    ¬ PremisesAt (engineBasePremises RelationEnv.empty) language
      fuel initial [missing] final := by
  intro evidence
  cases evidence with
  | cons head _tail =>
      cases head with
      | relationQuery member =>
        simp [engineBasePremises, premiseStepWithEnv, relationQueryStep,
          RelationEnv.empty, builtinRelationTuples] at member

end Canary

end Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedOccurrenceSemantics
