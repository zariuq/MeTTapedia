import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.LanguageDefDerivedActivationBoundary
import Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceOperationalViewCanary

/-!
# Presentation-derived activation for the quotation/choice workload

The selected choice occurrence can request its authored rewrite, and every
generated firing returns exactly the two declared successors.  A normal
resident occurrence cannot fire, and the unary generated fragment supplies
no binary communication.
-/


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDefDerivedActivationCanary

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluing
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open ReductionChoiceNormalFormBoundary
open SpaceActivationPolicyBoundary
open SpaceOperationalViewBoundary
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.LanguageDefDerivedActivationBoundary

open Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceOperationalViewCanary

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


#print axioms choice_requested_can_fire
#print axioms choice_firing_returns_exact_family
#print axioms normal_left_requested_cannot_fire
#print axioms generated_boundary_has_both_controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDefDerivedActivationCanary
