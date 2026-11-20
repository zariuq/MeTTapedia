import Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive
import Mathlib.Probability.Distributions.Beta

/-!
# Beta normalizers for exact rational prediction

The executable mass agrees with the Beta normalizer for the counts with
unit prior shape parameters. Ratios therefore integrate the repeated
Bernoulli outcomes against the updated Beta law.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive

open Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning (BooleanCPTEntry)

theorem wordMass_eq_beta (counts : BooleanCPTEntry) :
    (wordMass counts : ℝ) = _root_.ProbabilityTheory.beta
      ((counts.n_pos : ℝ) + 1) ((counts.n_neg : ℝ) + 1) := by
  unfold wordMass _root_.ProbabilityTheory.beta
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  have den : (counts.n_pos : ℝ) + 1 + (counts.n_neg + 1) =
      ((counts.n_pos + counts.n_neg + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [den, Real.Gamma_nat_eq_factorial]
  push_cast
  rfl

theorem sequenceMass_eq_beta_ratio (counts : BooleanCPTEntry) (outcomes : List Bool) :
    let after := outcomes.foldl addOutcome counts
    (sequenceMass counts outcomes : ℝ) =
      _root_.ProbabilityTheory.beta ((after.n_pos : ℝ) + 1) ((after.n_neg : ℝ) + 1) /
      _root_.ProbabilityTheory.beta ((counts.n_pos : ℝ) + 1) ((counts.n_neg : ℝ) + 1) := by
  dsimp only
  rw [← wordMass_eq_beta, ← wordMass_eq_beta, ← Rat.cast_div]
  congr 1
  rw [← sequenceMass_exact, mul_comm (wordMass counts), mul_div_cancel_right₀ _
    (wordMass_positive counts).ne']

end Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive
