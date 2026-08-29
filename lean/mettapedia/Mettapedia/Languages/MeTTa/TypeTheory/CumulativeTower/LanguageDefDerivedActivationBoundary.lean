import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SpaceActivationPolicyBoundary

/-!
# LanguageDef-derived rewrite activation

The authored `LanguageDef` already determines the exact rewrite successor
family of a pattern.  A space policy separately determines whether a resident
occurrence may request that rewrite.  This module connects the two without
conflating them.

For the generated unary rewrite fragment, a singleton resident occurrence can
fire exactly when `rewriteAt` returns a nonempty successor family.  Every
transition receipt retains that exact family.  The construction grants no
binary communication, scheduling, resource, or external-effect authority.
Fold and oracle declarations therefore still require independently checked
backend capabilities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace LanguageDefDerivedActivationBoundary

open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.GSLT.LanguageDef.DialectGluing
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open ReductionChoiceNormalFormBoundary
open SpaceActivationPolicyBoundary
open SpaceOperationalViewBoundary

/-- The generic one-cell rewrite view satisfies the resident-source
obligation required by the activation-policy interface. -/
theorem rewriteTriggered_residentSound
    (language : LanguageDef) (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    ResidentSound (rewriteTriggeredView language reduction environment depth) := by
  intro store occurrence next receipt step
  rw [step.1]
  simp [rewriteTriggeredView]

/-- The unary rewrite capability generated from one checked language
presentation.  It exposes only explicit requested activation. -/
def generatedRewritePolicy
    (language : LanguageDef) (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat) :=
  ofOperationalView (rewriteTriggeredView language reduction environment depth)
    (rewriteTriggered_residentSound language reduction environment depth)

/-- Firing the generated policy returns exactly the successor family computed
from the authored `LanguageDef` and relation environment. -/
theorem fired_is_exact_language_rewrite
    {language : LanguageDef}
    {reduction : ReductionViewIndexedModalities.ReductionView language}
    {environment : RelationEnv} {depth : Nat}
    {source : Pattern} {next : List Pattern}
    {receipt : RewriteReceipt language environment depth}
    (fired :
      (generatedRewritePolicy language reduction environment depth).step
        [source] (.requested () source) next receipt) :
    receipt.source = source ∧
      next = rewriteAt (engineBasePremises environment) language depth source := by
  have receiptExact := receipt.exact
  rw [fired.2.1] at receiptExact
  exact ⟨fired.2.1, fired.2.2.1.trans receiptExact⟩

/-- On a singleton store, explicit rewrite activation exists exactly when the
presentation-derived successor family is nonempty. -/
theorem canFire_singleton_iff_rewriteAt_nonempty
    (language : LanguageDef)
    (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat) (source : Pattern) :
    (generatedRewritePolicy language reduction environment depth).CanFire
        [source] (.requested () source) ↔
      rewriteAt (engineBasePremises environment) language depth source ≠ [] := by
  constructor
  · rintro ⟨next, receipt, fired⟩
    intro successorsEmpty
    have receiptExact := receipt.exact
    rw [fired.2.1] at receiptExact
    exact fired.2.2.2 (receiptExact.trans successorsEmpty)
  · intro successorsNonempty
    let successors :=
      rewriteAt (engineBasePremises environment) language depth source
    let receipt : RewriteReceipt language environment depth := {
      source := source
      successors := successors
      exact := rfl }
    exact ⟨successors, receipt, rfl, rfl, rfl, successorsNonempty⟩

/-- The presentation-derived unary fragment does not gain rho-style
communication merely because its rewrite relation is executable. -/
theorem generatedRewritePolicy_no_communication
    (language : LanguageDef)
    (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat)
    (store : List Pattern) (sender receiver : Pattern) :
    ¬ (generatedRewritePolicy language reduction environment depth).CanFire
        store (.communication sender receiver) :=
  no_communication_fire
    (rewriteTriggeredView language reduction environment depth)
    (rewriteTriggered_residentSound language reduction environment depth)
    store sender receiver

namespace PrimeCanary

open SpaceOperationalViewBoundary.PrimeCanary

def policy := generatedRewritePolicy quoteAndChoice processReductionView
  choiceEnvironment 1

/-- Positive control: the authored choice rewrite generates activation. -/
theorem choice_requested_can_fire :
    policy.CanFire [choiceDemo] (.requested () choiceDemo) := by
  have exactSuccessors :
      rewriteAt (engineBasePremises choiceEnvironment) quoteAndChoice 1
          choiceDemo = [leftDemo, rightDemo] := by
    simpa [choiceEnvironment, validatedChoiceLanguage, successors] using
      choice_successors_exact
  apply (canFire_singleton_iff_rewriteAt_nonempty quoteAndChoice
    processReductionView choiceEnvironment 1 choiceDemo).2
  simp [exactSuccessors]

/-- Every generated receipt for the choice occurrence returns its two exact
authored successors. -/
theorem choice_firing_returns_exact_family
    {next : List Pattern}
    {receipt : RewriteReceipt quoteAndChoice choiceEnvironment 1}
    (fired : policy.step [choiceDemo] (.requested () choiceDemo) next receipt) :
    next = [leftDemo, rightDemo] := by
  have exactRewrite :=
    (fired_is_exact_language_rewrite (fired := fired)).2
  have exactSuccessors :
      rewriteAt (engineBasePremises choiceEnvironment) quoteAndChoice 1
          choiceDemo = [leftDemo, rightDemo] := by
    simpa [choiceEnvironment, validatedChoiceLanguage, successors] using
      choice_successors_exact
  have exactRewrite' :
      next = rewriteAt (engineBasePremises choiceEnvironment) quoteAndChoice 1
        choiceDemo := by
    simpa [policy, choiceEnvironment] using exactRewrite
  exact exactRewrite'.trans exactSuccessors

/-- Negative control: a normal resident term is still inert in the generated
rewrite fragment.  Residency is not a fabricated transition. -/
theorem normal_left_requested_cannot_fire :
    ¬ policy.CanFire [leftDemo] (.requested () leftDemo) := by
  have exactSuccessors :
      rewriteAt (engineBasePremises choiceEnvironment) quoteAndChoice 1
          leftDemo = [] := by
    simpa [IsNormal, choiceEnvironment, validatedChoiceLanguage, successors] using
      left_normal
  intro fires
  have nonempty :=
    (canFire_singleton_iff_rewriteAt_nonempty quoteAndChoice
      processReductionView choiceEnvironment 1 leftDemo).1
      (by simpa [policy] using fires)
  exact nonempty exactSuccessors

theorem generated_boundary_has_both_controls :
    policy.CanFire [choiceDemo] (.requested () choiceDemo) ∧
      ¬ policy.CanFire [leftDemo] (.requested () leftDemo) ∧
      ¬ policy.CanFire [choiceDemo] (.communication choiceDemo leftDemo) :=
  ⟨choice_requested_can_fire, normal_left_requested_cannot_fire,
    generatedRewritePolicy_no_communication quoteAndChoice processReductionView
      choiceEnvironment 1 [choiceDemo] choiceDemo leftDemo⟩

end PrimeCanary

#print axioms rewriteTriggered_residentSound
#print axioms fired_is_exact_language_rewrite
#print axioms canFire_singleton_iff_rewriteAt_nonempty
#print axioms generatedRewritePolicy_no_communication
#print axioms PrimeCanary.choice_requested_can_fire
#print axioms PrimeCanary.choice_firing_returns_exact_family
#print axioms PrimeCanary.normal_left_requested_cannot_fire
#print axioms PrimeCanary.generated_boundary_has_both_controls

end LanguageDefDerivedActivationBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
