import Mettapedia.Logic.PLNWorldModelExperimentStochastic
import Mettapedia.Logic.PLNBayesNetInference

/-!
# WM Stochastic Experiment Regression Fixture

Finite fixture for stochastic Blackwell/utility endpoints:

- explicit finite prior (`PMF Bool`)
- stochastic strong channel (`Bool → PMF Bool`)
- stochastic garbling kernel (`Bool → PMF Bool`)
- weak channel via composition (`weak = strong ≫ κ`)
- theorem-level regression for utility equality and optimal-value monotonicity.
-/

namespace Mettapedia.Logic.PLNWorldModelExperimentStochasticRegression

open Mettapedia.Logic.PLNWorldModelExperimentStochastic
open scoped ENNReal

abbrev H := Bool
abbrev O := Bool
abbrev A := Bool

noncomputable def pHalf : ℝ≥0∞ := (1 / 2 : ℝ≥0∞)

theorem pHalf_le_one : pHalf ≤ (1 : ℝ≥0∞) := by
  simp [pHalf]

/-- Stochastic strong channel over Bool hypotheses. -/
noncomputable def strongChannel : StochasticChannel H O
  | false => Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF pHalf pHalf_le_one
  | true => Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF pHalf pHalf_le_one

/-- Nontrivial stochastic garbling kernel on observations. -/
noncomputable def garbling : StochasticChannel O O
  | false => Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF pHalf pHalf_le_one
  | true => Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF pHalf pHalf_le_one

/-- Weak channel obtained by garbling the strong channel. -/
noncomputable def weakChannel : StochasticChannel H O :=
  stochasticComp strongChannel garbling

theorem weak_factors_through_strong :
    BlackwellFactorsThrough strongChannel weakChannel garbling := by
  rfl

/-- Explicit finite prior on hypotheses. -/
noncomputable def prior : Prior H :=
  Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF pHalf pHalf_le_one

/-- Weak-side decision rule: pick action equal to observed bit. -/
noncomputable def weakDecision : DecisionRule O A :=
  fun o => PMF.pure o

/-- Utility: reward exact action-hypothesis match. -/
def utility : H → A → ℝ≥0∞
  | h, a => if a = h then 1 else 0

/-- Base source weights for a trusted-source policy fixture. -/
def baseWeight : SourceWeight H
  | false => 1
  | true => 3

/-- Trusted-source gate for the weighted policy fixture. -/
def trustedSource : H → Bool
  | false => false
  | true => true

/-- Weighted/trusted-source experiment policy fixture. -/
def trustedPolicy : WeightedSourcePolicy H :=
  ⟨baseWeight, trustedSource⟩

/-- Finite fixture endpoint: expected utility is preserved by Blackwell lifting. -/
theorem fixture_expectedUtility_eq_lifted :
    expectedUtility prior weakChannel weakDecision utility =
      expectedUtility prior strongChannel (liftDecision garbling weakDecision) utility := by
  exact
    expectedUtility_eq_of_blackwellFactor
      prior strongChannel weakChannel garbling weak_factors_through_strong weakDecision utility

/-- Finite fixture endpoint: optimal value is monotone under Blackwell factorization. -/
theorem fixture_optimalValue_mono :
    optimalValue prior weakChannel utility ≤
      optimalValue prior strongChannel utility := by
  exact
    optimalValue_mono_of_blackwellFactor
      prior strongChannel weakChannel garbling weak_factors_through_strong utility

/-- Weighted/trusted-source fixture endpoint:
policy-level optimal utility remains monotone under Blackwell factorization. -/
theorem fixture_trustedPolicy_optimalValue_mono :
    optimalValuePolicy trustedPolicy weakChannel utility ≤
      optimalValuePolicy trustedPolicy strongChannel utility := by
  exact
    optimalValuePolicy_mono_of_blackwellFactor
      (policy := trustedPolicy)
      strongChannel weakChannel garbling weak_factors_through_strong utility

end Mettapedia.Logic.PLNWorldModelExperimentStochasticRegression
