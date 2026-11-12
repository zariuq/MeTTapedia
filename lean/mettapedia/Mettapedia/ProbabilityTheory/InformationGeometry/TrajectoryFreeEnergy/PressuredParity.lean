import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.NoisyParity
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The noisy parity family is the optimizer of its declared task

The reference is fixed uniform independent input/output. The utility is the
sum of the three signed update relations, specified independently of the
probability law. Its Gibbs optimizer is exactly the noisy parity law with
correlation `tanh pressure`. Both endpoint laws stay uniform.

The resulting past/future mutual information is nondecreasing at nonnegative
task pressure, while every pair of individual coordinates stays independent.
This concerns a finite one-step model, not an implementation of causal
control on a physical system.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.PressuredParity

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference
open Parity (Bits sign initial)
open NoisyParity (History errors mass)

def reference : Prob History := productLaw initial initial

def utility (history : History) : ℝ :=
  sign history.2.1 * sign history.1.2.1 * sign history.1.2.2 +
    sign history.2.2.1 * sign history.1.1 * sign history.1.2.2 +
      sign history.2.2.2 * sign history.1.1 * sign history.1.2.1 * sign history.1.2.2

theorem utility_eq_errors (history : History) :
    utility history = sign (errors history).1 + sign (errors history).2.1 + sign (errors history).2.2 := by
  rcases history with ⟨⟨a, b, c⟩, ⟨x, y, z⟩⟩
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;>
    norm_num [utility, errors, Parity.transition, sign]

theorem sign_weight (pressure : ℝ) (bit : Bool) :
    Real.exp (pressure * sign bit) / Real.cosh pressure = 1 + Real.tanh pressure * sign bit := by
  have positive := Real.cosh_pos pressure
  have plus : Real.exp pressure / Real.cosh pressure = 1 + Real.tanh pressure := by
    rw [Real.tanh_eq_sinh_div_cosh, div_eq_iff positive.ne', add_mul, one_mul,
      div_mul_cancel₀ _ positive.ne']
    exact (Real.cosh_add_sinh pressure).symm
  have minus : Real.exp (-pressure) / Real.cosh pressure = 1 - Real.tanh pressure := by
    rw [Real.tanh_eq_sinh_div_cosh, div_eq_iff positive.ne', sub_mul, one_mul,
      div_mul_cancel₀ _ positive.ne']
    exact (Real.cosh_sub_sinh pressure).symm
  cases bit
  · simpa [sign] using plus
  · simpa [sign, sub_eq_add_neg] using minus

theorem weight_product (pressure : ℝ) (history : History) :
    weight (fun history => -pressure * utility history) 1 history =
      Real.exp (pressure * sign (errors history).1) *
        Real.exp (pressure * sign (errors history).2.1) *
          Real.exp (pressure * sign (errors history).2.2) := by
  have exponent : -(-pressure * utility history) / 1 =
      pressure * sign (errors history).1 + pressure * sign (errors history).2.1 +
        pressure * sign (errors history).2.2 := by rw [utility_eq_errors]; ring
  rw [weight, exponent, Real.exp_add, Real.exp_add]

theorem normalized_weight (pressure : ℝ) (history : History) :
    weight (fun history => -pressure * utility history) 1 history / (Real.cosh pressure) ^ 3 =
      64 * mass (Real.tanh pressure) history := by
  rw [weight_product]
  have fractions (a b c d : ℝ) : a * b * c / d ^ 3 = (a / d) * (b / d) * (c / d) := by ring
  rw [fractions, sign_weight, sign_weight, sign_weight]
  unfold mass
  ring

theorem partition_cosh (pressure : ℝ) :
    partition reference (fun history => -pressure * utility history) 1 = (Real.cosh pressure) ^ 3 := by
  have pointwise (history : History) :
      reference.1 history * weight (fun history => -pressure * utility history) 1 history =
        (Real.cosh pressure) ^ 3 * mass (Real.tanh pressure) history := by
    have weightEq := (div_eq_iff (pow_ne_zero 3 (Real.cosh_pos pressure).ne')).mp
      (normalized_weight pressure history)
    rw [reference, productLaw_apply, weightEq]
    norm_num [initial]
    ring
  unfold partition evidence
  rw [Finset.sum_congr rfl (fun history _ => pointwise history), ← Finset.mul_sum,
    NoisyParity.total_mass, mul_one]

theorem tanh_nonnegative (pressure : ℝ) (nonnegative : 0 ≤ pressure) : 0 ≤ Real.tanh pressure := by
  rw [Real.tanh_eq]
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

theorem optimizer_eq_noisy (pressure : ℝ) (nonnegative : 0 ≤ pressure) :
    pressureGibbs reference utility pressure =
      NoisyParity.law (Real.tanh pressure) (tanh_nonnegative pressure nonnegative)
        (Real.tanh_lt_one pressure).le := by
  apply Subtype.ext
  funext history
  change (gibbs reference (fun history => -pressure * utility history) 1 (by norm_num)).1 history = _
  rw [gibbs_apply, partition_cosh]
  change reference.1 history * weight (fun history => -pressure * utility history) 1 history /
    (Real.cosh pressure) ^ 3 = mass (Real.tanh pressure) history
  rw [reference, productLaw_apply]
  change (1 / 8 : ℝ) * (1 / 8) * weight _ _ _ / _ = _
  have fractions : (1 / 8 : ℝ) * (1 / 8) * weight (fun history => -pressure * utility history) 1 history /
      (Real.cosh pressure) ^ 3 =
        (weight (fun history => -pressure * utility history) 1 history / (Real.cosh pressure) ^ 3) / 64 := by ring
  rw [fractions, normalized_weight]
  ring

theorem optimizer_fixed_marginals (pressure : ℝ) (nonnegative : 0 ≤ pressure) :
    pressureGibbs reference utility pressure ∈ fixedMarginals initial initial := by
  rw [optimizer_eq_noisy pressure nonnegative]
  exact ⟨NoisyParity.initial_uniform _ _ _, NoisyParity.final_uniform _ _ _⟩

theorem utility_mean (correlation : ℝ) :
    (∑ history, mass correlation history * utility history) = 3 * correlation := by
  norm_num [mass, errors, Parity.transition, sign, utility, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem optimizer_utility (pressure : ℝ) (nonnegative : 0 ≤ pressure) :
    expectedCost (pressureGibbs reference utility pressure) utility = 3 * Real.tanh pressure := by
  rw [optimizer_eq_noisy pressure nonnegative]
  exact utility_mean _

theorem optimizer_divergence (pressure : ℝ) (nonnegative : 0 ≤ pressure) :
    klSum (pressureGibbs reference utility pressure).1 reference.1 =
      3 * pressure * Real.tanh pressure - 3 * Real.log (Real.cosh pressure) := by
  have minimum := gibbs_value reference (fun history => -pressure * utility history) 1 (by norm_num)
  change freeEnergy reference (fun history => -pressure * utility history) 1
    (pressureGibbs reference utility pressure) = _ at minimum
  rw [← pressure_objective_eq reference _ utility pressure, pressureObjective,
    partition_cosh, Real.log_pow, optimizer_utility pressure nonnegative] at minimum
  norm_num at minimum
  nlinarith

theorem history_information_formula (pressure : ℝ) (nonnegative : 0 ≤ pressure) :
    mutualInfo (pressureGibbs reference utility pressure).1 Prod.fst Prod.snd =
      3 * pressure * Real.tanh pressure - 3 * Real.log (Real.cosh pressure) := by
  rw [← fixed_marginal_kl_eq_mutualInfo initial initial _ (optimizer_fixed_marginals pressure nonnegative)]
  exact optimizer_divergence pressure nonnegative

theorem history_information_mono (low high : ℝ) (nonnegative : 0 ≤ low) (increase : low < high) :
    mutualInfo (pressureGibbs reference utility low).1 Prod.fst Prod.snd ≤
      mutualInfo (pressureGibbs reference utility high).1 Prod.fst Prod.snd := by
  rw [← fixed_marginal_kl_eq_mutualInfo initial initial _ (optimizer_fixed_marginals low nonnegative),
    ← fixed_marginal_kl_eq_mutualInfo initial initial _
      (optimizer_fixed_marginals high (nonnegative.trans increase.le))]
  exact pressureGibbs_divergence_mono reference utility low high nonnegative increase

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.PressuredParity
