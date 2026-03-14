import Mettapedia.Logic.PLNHigherOrderCertifiedEstimates
import Mettapedia.Logic.PLNMixedModeChainComposition

/-!
# Higher-Order Chain Bounds

This module turns certified 2nd/3rd-order summaries into compositional bounds
for PLN-style chaining.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNMixedModeChainComposition
open Mettapedia.Logic.PLNGuardedHigherOrderSemantics

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The theorem-facing information carried by one higher-order chain step. -/
structure CertifiedChainStep (R : Type*) [Fintype R] [DecidableEq R] where
  admissibility : CertifiedAdmissibilityEstimate
  trust : CertifiedTrustEstimate
  posterior : CertifiedRegimePosterior R
  branchValues : R → ℝ

/-- Trust-discounted lower bound on step admissibility. -/
def CertifiedChainStep.trustAdjustedLower
    (step : CertifiedChainStep R) : ℝ :=
  trustAdjustedLowerBound step.admissibility step.trust

/-- Coverage-discounted lower bound used by a stricter trust-sensitive
composition law. -/
def CertifiedChainStep.coverageAdjustedLower
    (step : CertifiedChainStep R) : ℝ :=
  step.trustAdjustedLower * step.trust.coverage

/-- Conservative certified error bound for one step, widened by disagreement and
fragility penalties. -/
def CertifiedChainStep.effectiveErrorBound
    (step : CertifiedChainStep R) : ℝ :=
  step.admissibility.errorBound +
    step.trust.disagreementPenalty +
    step.trust.fragilityPenalty

/-- Independent-step lower bound obtained by multiplying trust-discounted
admissibility bounds. -/
def chainAdmissibilityIndependent : List (CertifiedChainStep R) → ℝ
  | [] => 1
  | step :: rest => step.trustAdjustedLower * chainAdmissibilityIndependent rest

/-- Bottleneck lower bound: the weakest trust-discounted step dominates the
chain certificate. -/
def chainAdmissibilityBottleneck : List (CertifiedChainStep R) → ℝ
  | [] => 1
  | step :: rest => min step.trustAdjustedLower (chainAdmissibilityBottleneck rest)

/-- Stricter trust-sensitive lower bound, discounting by confidence/coverage as
well as by trust itself. -/
def chainAdmissibilityTrustWeighted : List (CertifiedChainStep R) → ℝ
  | [] => 1
  | step :: rest => min step.coverageAdjustedLower (chainAdmissibilityTrustWeighted rest)

/-- Conservative certified chain-error bound. -/
def chainCertifiedErrorBound : List (CertifiedChainStep R) → ℝ
  | [] => 0
  | step :: rest => step.effectiveErrorBound + chainCertifiedErrorBound rest

/-- Realized step used to prove that the certified error bound really bounds an
actual chain-error aggregate. -/
structure RealizedCertifiedChainStep (R : Type*) [Fintype R] [DecidableEq R]
    extends CertifiedChainStep R where
  actualError : ℝ
  actualError_nonneg : 0 ≤ actualError
  actualError_le_effectiveBound :
    actualError ≤ toCertifiedChainStep.effectiveErrorBound

/-- Aggregated realized chain error. -/
def chainActualError : List (RealizedCertifiedChainStep R) → ℝ
  | [] => 0
  | step :: rest => step.actualError + chainActualError rest

/-- The certified bound associated to a realized chain. -/
def chainCertifiedErrorBoundFromRealized :
    List (RealizedCertifiedChainStep R) → ℝ
  | [] => 0
  | step :: rest =>
      step.toCertifiedChainStep.effectiveErrorBound +
        chainCertifiedErrorBoundFromRealized rest

theorem CertifiedChainStep.coverageAdjustedLower_nonneg
    (step : CertifiedChainStep R) :
    0 ≤ step.coverageAdjustedLower := by
  unfold CertifiedChainStep.coverageAdjustedLower
  exact mul_nonneg
    (trustAdjustedLowerBound_nonneg step.admissibility step.trust)
    step.trust.coverage_nonneg

theorem CertifiedChainStep.coverageAdjustedLower_le_trustAdjustedLower
    (step : CertifiedChainStep R) :
    step.coverageAdjustedLower ≤ step.trustAdjustedLower := by
  unfold CertifiedChainStep.coverageAdjustedLower
  have hcov : step.trust.coverage ≤ 1 := step.trust.coverage_le_one
  calc
    step.trustAdjustedLower * step.trust.coverage ≤
        step.trustAdjustedLower * 1 := by
          exact mul_le_mul_of_nonneg_left hcov
            (trustAdjustedLowerBound_nonneg step.admissibility step.trust)
    _ = step.trustAdjustedLower := by ring

theorem CertifiedChainStep.effectiveErrorBound_nonneg
    (step : CertifiedChainStep R) :
    0 ≤ step.effectiveErrorBound := by
  unfold CertifiedChainStep.effectiveErrorBound
  exact add_nonneg
    (add_nonneg step.admissibility.errorBound_nonneg
      step.trust.disagreementPenalty_nonneg)
    step.trust.fragilityPenalty_nonneg

theorem chainAdmissibilityIndependent_nonneg :
    ∀ steps : List (CertifiedChainStep R), 0 ≤ chainAdmissibilityIndependent steps
  | [] => by simp [chainAdmissibilityIndependent]
  | step :: rest => by
      calc
        0 ≤ step.trustAdjustedLower * chainAdmissibilityIndependent rest := by
          exact mul_nonneg
            (trustAdjustedLowerBound_nonneg step.admissibility step.trust)
            (chainAdmissibilityIndependent_nonneg rest)
        _ = chainAdmissibilityIndependent (step :: rest) := by
          simp [chainAdmissibilityIndependent]

theorem chainAdmissibilityIndependent_le_one :
    ∀ steps : List (CertifiedChainStep R), chainAdmissibilityIndependent steps ≤ 1
  | [] => by simp [chainAdmissibilityIndependent]
  | step :: rest => by
      have hstep :
          step.trustAdjustedLower ≤ 1 := by
        exact le_trans
          (trustAdjustedLowerBound_le_admissibilityLower step.admissibility step.trust)
          step.admissibility.lower_le_one
      have hrest := chainAdmissibilityIndependent_le_one rest
      have hrest_nonneg := chainAdmissibilityIndependent_nonneg rest
      have hstep_nonneg := trustAdjustedLowerBound_nonneg step.admissibility step.trust
      calc
        chainAdmissibilityIndependent (step :: rest)
            = step.trustAdjustedLower * chainAdmissibilityIndependent rest := by
                simp [chainAdmissibilityIndependent]
        _ ≤ 1 := by
              nlinarith

theorem chainAdmissibilityIndependent_le_bottleneck :
    ∀ steps : List (CertifiedChainStep R),
      chainAdmissibilityIndependent steps ≤ chainAdmissibilityBottleneck steps
  | [] => by simp [chainAdmissibilityIndependent, chainAdmissibilityBottleneck]
  | step :: rest => by
      have hstep_nonneg := trustAdjustedLowerBound_nonneg step.admissibility step.trust
      have hstep_le_one :
          step.trustAdjustedLower ≤ 1 := by
        exact le_trans
          (trustAdjustedLowerBound_le_admissibilityLower step.admissibility step.trust)
          step.admissibility.lower_le_one
      have hrest_nonneg := chainAdmissibilityIndependent_nonneg rest
      have hrest_le_one := chainAdmissibilityIndependent_le_one rest
      have hprod_le_left :
          step.trustAdjustedLower * chainAdmissibilityIndependent rest ≤
            step.trustAdjustedLower := by
        calc
          step.trustAdjustedLower * chainAdmissibilityIndependent rest ≤
              step.trustAdjustedLower * 1 := by
                exact mul_le_mul_of_nonneg_left hrest_le_one hstep_nonneg
          _ = step.trustAdjustedLower := by ring
      have hprod_le_right :
          step.trustAdjustedLower * chainAdmissibilityIndependent rest ≤
            chainAdmissibilityBottleneck rest := by
        have hrest_ind := chainAdmissibilityIndependent_le_bottleneck rest
        calc
          step.trustAdjustedLower * chainAdmissibilityIndependent rest ≤
              1 * chainAdmissibilityIndependent rest := by
                exact mul_le_mul_of_nonneg_right hstep_le_one hrest_nonneg
          _ = chainAdmissibilityIndependent rest := by ring
          _ ≤ chainAdmissibilityBottleneck rest := hrest_ind
      calc
        chainAdmissibilityIndependent (step :: rest)
            = step.trustAdjustedLower * chainAdmissibilityIndependent rest := by
                simp [chainAdmissibilityIndependent]
        _ ≤ min step.trustAdjustedLower (chainAdmissibilityBottleneck rest) := by
              exact le_min hprod_le_left hprod_le_right
        _ = chainAdmissibilityBottleneck (step :: rest) := by
              simp [chainAdmissibilityBottleneck]

theorem chainAdmissibilityTrustWeighted_le_bottleneck :
    ∀ steps : List (CertifiedChainStep R),
      chainAdmissibilityTrustWeighted steps ≤ chainAdmissibilityBottleneck steps
  | [] => by simp [chainAdmissibilityTrustWeighted, chainAdmissibilityBottleneck]
  | step :: rest => by
      have hstep :
          step.coverageAdjustedLower ≤ step.trustAdjustedLower :=
        step.coverageAdjustedLower_le_trustAdjustedLower
      have hrest := chainAdmissibilityTrustWeighted_le_bottleneck rest
      calc
        chainAdmissibilityTrustWeighted (step :: rest)
            = min step.coverageAdjustedLower (chainAdmissibilityTrustWeighted rest) := by
                simp [chainAdmissibilityTrustWeighted]
        _ ≤ min step.trustAdjustedLower (chainAdmissibilityBottleneck rest) := by
              exact min_le_min hstep hrest
        _ = chainAdmissibilityBottleneck (step :: rest) := by
              simp [chainAdmissibilityBottleneck]

theorem chainCertifiedErrorBound_nonneg :
    ∀ steps : List (CertifiedChainStep R), 0 ≤ chainCertifiedErrorBound steps
  | [] => by simp [chainCertifiedErrorBound]
  | step :: rest => by
      calc
        0 ≤ step.effectiveErrorBound + chainCertifiedErrorBound rest := by
          exact add_nonneg step.effectiveErrorBound_nonneg
            (chainCertifiedErrorBound_nonneg rest)
        _ = chainCertifiedErrorBound (step :: rest) := by
          simp [chainCertifiedErrorBound]

theorem chainError_le_sum_certifiedBounds :
    ∀ steps : List (RealizedCertifiedChainStep R),
      chainActualError steps ≤ chainCertifiedErrorBoundFromRealized steps
  | [] => by simp [chainActualError, chainCertifiedErrorBoundFromRealized]
  | step :: rest => by
      have hrest := chainError_le_sum_certifiedBounds rest
      calc
        chainActualError (step :: rest)
            = step.actualError + chainActualError rest := by
                simp [chainActualError]
        _ ≤ step.toCertifiedChainStep.effectiveErrorBound +
              chainCertifiedErrorBoundFromRealized rest := by
              exact add_le_add step.actualError_le_effectiveBound hrest
        _ = chainCertifiedErrorBoundFromRealized (step :: rest) := by
              simp [chainCertifiedErrorBoundFromRealized]

/-- Repeated higher-order continuation over a list of semantic guarded steps. -/
def applyHigherOrderSemanticChain
    (prev : MixedModePlan)
    (steps : List SemanticProbGuardedQuery) : MixedModePlan :=
  steps.foldl (fun plan step => applyStep plan .applyHigherOrderSemantic step) prev

theorem applyHigherOrderSemanticChain_accumulatedBound_eq
    (prev : MixedModePlan)
    (steps : List SemanticProbGuardedQuery) :
    (applyHigherOrderSemanticChain prev steps).accumulatedBound =
      steps.foldl (fun acc step => combineBounds acc step.violationBound)
        prev.accumulatedBound := by
  induction steps generalizing prev with
  | nil =>
      simp [applyHigherOrderSemanticChain]
  | cons step rest ih =>
      have htail := ih (applyStep prev .applyHigherOrderSemantic step)
      simpa [applyHigherOrderSemanticChain, applyStep] using htail

theorem applyHigherOrderSemanticChain_keeps_queryChanged
    (prev : MixedModePlan)
    (steps : List SemanticProbGuardedQuery) :
    (applyHigherOrderSemanticChain prev steps).queryChanged = prev.queryChanged := by
  induction steps generalizing prev with
  | nil =>
      simp [applyHigherOrderSemanticChain]
  | cons step rest ih =>
      have hstep :
          (applyStep prev .applyHigherOrderSemantic step).queryChanged = prev.queryChanged := by
        simp [applyStep, actionChangesQuery]
      calc
        (applyHigherOrderSemanticChain prev (step :: rest)).queryChanged
            = (applyHigherOrderSemanticChain
                (applyStep prev .applyHigherOrderSemantic step) rest).queryChanged := by
                  simp [applyHigherOrderSemanticChain]
        _ = (applyStep prev .applyHigherOrderSemantic step).queryChanged := by
              exact ih (applyStep prev .applyHigherOrderSemantic step)
        _ = prev.queryChanged := hstep

theorem applyHigherOrderSemanticChain_status_of_higherOrder_start
    (prev : MixedModePlan)
    (hprev : prev.current.semanticStatus = .higherOrderSemanticGuarded)
    (steps : List SemanticProbGuardedQuery)
    (hsteps : ∀ step ∈ steps, step.semanticStatus = .higherOrderSemanticGuarded) :
    (applyHigherOrderSemanticChain prev steps).current.semanticStatus =
      .higherOrderSemanticGuarded := by
  induction steps generalizing prev with
  | nil =>
      simp [applyHigherOrderSemanticChain, hprev]
  | cons step rest ih =>
      have hstep : step.semanticStatus = .higherOrderSemanticGuarded := by
        exact hsteps step (by simp)
      have hnext :
          (applyStep prev .applyHigherOrderSemantic step).current.semanticStatus =
            .higherOrderSemanticGuarded := by
        simp [applyStep, hprev, hstep, composeSemanticStatus]
      have hrest : ∀ next ∈ rest, next.semanticStatus = .higherOrderSemanticGuarded := by
        intro next hmem
        exact hsteps next (by simp [hmem])
      have htail :=
        ih (applyStep prev .applyHigherOrderSemantic step) hnext hrest
      simpa [applyHigherOrderSemanticChain] using htail

theorem higherOrder_chain_continue_sound
    (prev : MixedModePlan)
    (hprev : prev.current.semanticStatus = .theoremCertifiedExact)
    (steps : List SemanticProbGuardedQuery)
    (hne : steps ≠ [])
    (hsteps : ∀ step ∈ steps, step.semanticStatus = .higherOrderSemanticGuarded) :
    (applyHigherOrderSemanticChain prev steps).current.semanticStatus =
      .higherOrderSemanticGuarded ∧
    (applyHigherOrderSemanticChain prev steps).queryChanged = prev.queryChanged := by
  cases steps with
  | nil =>
      contradiction
  | cons first rest =>
      have hfirst : first.semanticStatus = .higherOrderSemanticGuarded := by
        exact hsteps first (by simp)
      have hstart :
          (applyStep prev .applyHigherOrderSemantic first).current.semanticStatus =
            .higherOrderSemanticGuarded := by
        simp [applyStep, hprev, hfirst, composeSemanticStatus]
      have hrest : ∀ step ∈ rest, step.semanticStatus = .higherOrderSemanticGuarded := by
        intro step hmem
        exact hsteps step (by simp [hmem])
      constructor
      · simpa [applyHigherOrderSemanticChain]
          using applyHigherOrderSemanticChain_status_of_higherOrder_start
            (applyStep prev .applyHigherOrderSemantic first) hstart rest hrest
      · simpa [applyHigherOrderSemanticChain, applyStep, actionChangesQuery]
          using applyHigherOrderSemanticChain_keeps_queryChanged
            (applyStep prev .applyHigherOrderSemantic first) rest

end Mettapedia.Logic
