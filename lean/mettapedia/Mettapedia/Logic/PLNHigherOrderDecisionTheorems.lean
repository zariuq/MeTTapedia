import Mettapedia.Logic.PLNHigherOrderChainBounds
import Mettapedia.Logic.PLNRegimeMixtureBenchmarkBridge

/-!
# Higher-Order Decision Theorems

This module turns certified 2nd/3rd-order summaries into theorem-facing action
conditions for a higher-order PLN chain engine.

The point is not to formalize Python planner thresholds. The point is to prove
that finite certified summaries are sufficient for action selection:

- continue when the certified chain bound is within tolerance,
- reveal when reveal cost is below certified variance,
- fallback when direct continuation is not certified but local exact recovery is,
- abstain when none of the available actions are certified.
-/

namespace Mettapedia.Logic

open scoped BigOperators
open Mettapedia.Logic.PLNRegimeMixtureTheorems

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Certified variance summary for one higher-order chain step. -/
def certifiedVariance (step : CertifiedChainStep R) : ℝ :=
  mixtureVariance step.posterior.weights step.branchValues

theorem certifiedVariance_nonneg
    (step : CertifiedChainStep R) :
    0 ≤ certifiedVariance step := by
  unfold certifiedVariance mixtureVariance expectedSquaredLoss
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg
      (CertifiedRegimePosterior.weights_nonneg step.posterior r)
      (sq_nonneg _)

/-- Planner-level actions derived from finite certified summaries. -/
inductive HigherOrderDecision where
  | continue
  | reveal
  | fallback
  | abstain
  deriving DecidableEq, Repr

/-- Finite summaries consumed by the theorem-facing decision procedure. -/
structure CertifiedActionSummary where
  continueBound : ℝ
  tolerance : ℝ
  revealCost : ℝ
  revealVariance : ℝ
  fallbackBound : ℝ
  fallbackTolerance : ℝ

/-- Flatten higher-order certified summaries to one planner action. -/
noncomputable def chooseHigherOrderAction
    (summary : CertifiedActionSummary) : HigherOrderDecision :=
  if summary.continueBound ≤ summary.tolerance then
    .continue
  else if summary.revealCost < summary.revealVariance then
    .reveal
  else if summary.fallbackBound ≤ summary.fallbackTolerance then
    .fallback
  else
    .abstain

/-- Summary induced by one certified chain and one fallback bound. -/
def actionSummaryOfCertifiedChain
    (steps : List (CertifiedChainStep R))
    (tolerance : ℝ)
    (revealCost : ℝ)
    (fallbackBound fallbackTolerance : ℝ) : CertifiedActionSummary where
  continueBound := chainCertifiedErrorBound steps
  tolerance := tolerance
  revealCost := revealCost
  revealVariance :=
    match steps with
    | [] => 0
    | step :: _ => certifiedVariance step
  fallbackBound := fallbackBound
  fallbackTolerance := fallbackTolerance

theorem continueSound_if_chainBound_le_tolerance
    (steps : List (RealizedCertifiedChainStep R))
    {tolerance : ℝ}
    (hbound : chainCertifiedErrorBoundFromRealized steps ≤ tolerance) :
    chainActualError steps ≤ tolerance := by
  exact le_trans (chainError_le_sum_certifiedBounds steps) hbound

theorem continuePreferred_if_chainBound_le_tolerance
    (summary : CertifiedActionSummary)
    (hcontinue : summary.continueBound ≤ summary.tolerance) :
    chooseHigherOrderAction summary = .continue := by
  simp [chooseHigherOrderAction, hcontinue]

theorem revealPreferred_if_cost_lt_certifiedVariance
    (summary : CertifiedActionSummary)
    (hcontinue : ¬ summary.continueBound ≤ summary.tolerance)
    (hreveal : summary.revealCost < summary.revealVariance) :
    chooseHigherOrderAction summary = .reveal := by
  simp [chooseHigherOrderAction, hcontinue, hreveal]

theorem fallbackPreferred_if_continueBound_gt_fallbackThreshold
    (summary : CertifiedActionSummary)
    (hcontinue : ¬ summary.continueBound ≤ summary.tolerance)
    (hreveal : ¬ summary.revealCost < summary.revealVariance)
    (hfallback : summary.fallbackBound ≤ summary.fallbackTolerance) :
    chooseHigherOrderAction summary = .fallback := by
  simp [chooseHigherOrderAction, hcontinue, hreveal, hfallback]

theorem abstainPreferred_if_no_action_certified
    (summary : CertifiedActionSummary)
    (hcontinue : ¬ summary.continueBound ≤ summary.tolerance)
    (hreveal : ¬ summary.revealCost < summary.revealVariance)
    (hfallback : ¬ summary.fallbackBound ≤ summary.fallbackTolerance) :
    chooseHigherOrderAction summary = .abstain := by
  simp [chooseHigherOrderAction, hcontinue, hreveal, hfallback]

theorem revealVarianceSummary_eq_certifiedVariance_head
    (step : CertifiedChainStep R)
    (rest : List (CertifiedChainStep R))
    (tolerance revealCost fallbackBound fallbackTolerance : ℝ) :
    (actionSummaryOfCertifiedChain (step :: rest)
      tolerance revealCost fallbackBound fallbackTolerance).revealVariance =
      certifiedVariance step := by
  simp [actionSummaryOfCertifiedChain]

theorem revealPreferred_if_cost_lt_headCertifiedVariance
    (step : CertifiedChainStep R)
    (rest : List (CertifiedChainStep R))
    (tolerance revealCost fallbackBound fallbackTolerance : ℝ)
    (hcontinue :
      ¬ chainCertifiedErrorBound (step :: rest) ≤ tolerance)
    (hreveal : revealCost < certifiedVariance step) :
    chooseHigherOrderAction
      (actionSummaryOfCertifiedChain (step :: rest)
        tolerance revealCost fallbackBound fallbackTolerance) = .reveal := by
  have hsummary :
      revealCost <
        (actionSummaryOfCertifiedChain (step :: rest)
          tolerance revealCost fallbackBound fallbackTolerance).revealVariance := by
    simpa [revealVarianceSummary_eq_certifiedVariance_head]
      using hreveal
  exact revealPreferred_if_cost_lt_certifiedVariance
    (actionSummaryOfCertifiedChain (step :: rest)
      tolerance revealCost fallbackBound fallbackTolerance)
    hcontinue
    hsummary

theorem revealGain_positive_of_cost_lt_certifiedVariance
    (step : CertifiedChainStep R)
    (hc : c < certifiedVariance step) :
    0 < revealGain step.posterior.weights step.branchValues c := by
  simpa [certifiedVariance] using
    revealPreferred_if_cost_lt_variance
      (w := step.posterior.weights)
      (q := step.branchValues)
      hc

theorem higherOrder_action_flattening_sound
    {s₁ s₂ : CertifiedActionSummary}
    (hcontinue : s₁.continueBound = s₂.continueBound)
    (htol : s₁.tolerance = s₂.tolerance)
    (hcost : s₁.revealCost = s₂.revealCost)
    (hvar : s₁.revealVariance = s₂.revealVariance)
    (hfallback : s₁.fallbackBound = s₂.fallbackBound)
    (hfallbackTol : s₁.fallbackTolerance = s₂.fallbackTolerance) :
    chooseHigherOrderAction s₁ = chooseHigherOrderAction s₂ := by
  cases s₁
  cases s₂
  simp at hcontinue htol hcost hvar hfallback hfallbackTol
  subst hcontinue
  subst htol
  subst hcost
  subst hvar
  subst hfallback
  subst hfallbackTol
  rfl

/-! ## End-to-end: soundness implies continue is both safe and preferred -/

/-- The certified error bound of a mapped chain equals that of the realized chain. -/
lemma chainCertifiedErrorBound_map_eq_fromRealized :
    ∀ steps : List (RealizedCertifiedChainStep R),
      chainCertifiedErrorBound (steps.map (·.toCertifiedChainStep)) =
        chainCertifiedErrorBoundFromRealized steps
  | [] => by simp [chainCertifiedErrorBound, chainCertifiedErrorBoundFromRealized]
  | step :: rest => by
      simp only [List.map, chainCertifiedErrorBound, chainCertifiedErrorBoundFromRealized]
      congr 1
      exact chainCertifiedErrorBound_map_eq_fromRealized rest

/-- **End-to-end certified continue**: if the realized chain error bound is within
tolerance, then (1) the actual chain error is within tolerance, and (2) the action
chooser selects `.continue` from the corresponding certified summary.

This joins the two previously separate guarantees:
- `continueSound_if_chainBound_le_tolerance` (error safety)
- `continuePreferred_if_chainBound_le_tolerance` (action selection)
into one statement that can be applied atomically. -/
theorem certifiedChain_continue_sound_and_preferred
    (steps : List (RealizedCertifiedChainStep R))
    (tolerance revealCost fallbackBound fallbackTolerance : ℝ)
    (hbound : chainCertifiedErrorBoundFromRealized steps ≤ tolerance) :
    chainActualError steps ≤ tolerance ∧
    chooseHigherOrderAction
      (actionSummaryOfCertifiedChain
        (steps.map (·.toCertifiedChainStep))
        tolerance revealCost fallbackBound fallbackTolerance) = .continue := by
  refine ⟨continueSound_if_chainBound_le_tolerance steps hbound,
          continuePreferred_if_chainBound_le_tolerance _ ?_⟩
  simp only [actionSummaryOfCertifiedChain]
  rw [chainCertifiedErrorBound_map_eq_fromRealized]
  exact hbound

end Mettapedia.Logic
