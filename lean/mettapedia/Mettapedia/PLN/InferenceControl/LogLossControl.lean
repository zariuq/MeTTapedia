import Mettapedia.InformationTheory.PredictiveLogLoss
import Mettapedia.ProbabilityTheory.BayesianInference.Information

/-!
# Valuing computations by their gain on a target prediction

A computation is modeled by its result channel as seen by the controller.
The hidden variable in this calculation is the target to be predicted.
A policy that issues approximate answers pays a posterior KL penalty,
in addition to its computation cost.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.InferenceControl.LogLossControl

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

variable {Target Result : Type*} [Fintype Target] [Fintype Result]

noncomputable def posteriorLaw (prior : Prob Target) (result : Target → Prob Result)
    (supported : ∀ r, 0 < (observationLaw prior result).1 r) (r : Result) : Prob Target :=
  posterior prior (fun target => (result target).1 r) (fun target => (result target).2.1 r)
    (supported r)

/-- Gain against the best prediction before the computation, using the
forecasts actually issued after each result. Cost is in the same units. -/
noncomputable def value (prior : Prob Target) (result : Target → Prob Result)
    (supported : ∀ r, 0 < (observationLaw prior result).1 r)
    (forecast : Result → Prob Target) (cost : ℝ) : ℝ :=
  crossEntropy prior prior -
    (∑ r, (observationLaw prior result).1 r *
      crossEntropy (posteriorLaw prior result supported r) (forecast r)) - cost

theorem value_eq_information_sub_error (prior : Prob Target) (result : Target → Prob Result)
    (supported : ∀ r, 0 < (observationLaw prior result).1 r)
    (forecast : Result → Prob Target) (cost : ℝ)
    (forecastSupport : ∀ r target, 0 < (posteriorLaw prior result supported r).1 target →
      0 < (forecast r).1 target) :
    value prior result supported forecast cost =
      expectedInformationGain prior result -
        (∑ r, (observationLaw prior result).1 r *
          klSum (posteriorLaw prior result supported r).1 (forecast r).1) - cost := by
  unfold value
  rw [crossEntropy_self, expectedInformationGain_eq_entropy_sub,
    expectedPosteriorEntropy_eq prior result supported]
  simp_rw [crossEntropy_eq_entropy_add_kl _ _ (forecastSupport _), mul_add, Finset.sum_add_distrib]
  unfold posteriorLaw
  ring

theorem exact_value (prior : Prob Target) (result : Target → Prob Result)
    (supported : ∀ r, 0 < (observationLaw prior result).1 r) (cost : ℝ) :
    value prior result supported (posteriorLaw prior result supported) cost =
      expectedInformationGain prior result - cost := by
  rw [value_eq_information_sub_error _ _ _ _ _ (fun _ _ h => h)]
  simp [klSum_self_eq_zero _ (fun target =>
    (posteriorLaw prior result supported _).2.1 target)]

theorem forecast_value_le_exact (prior : Prob Target) (result : Target → Prob Result)
    (supported : ∀ r, 0 < (observationLaw prior result).1 r)
    (forecast : Result → Prob Target) (cost : ℝ)
    (forecastSupport : ∀ r target, 0 < (posteriorLaw prior result supported r).1 target →
      0 < (forecast r).1 target) :
    value prior result supported forecast cost ≤
      value prior result supported (posteriorLaw prior result supported) cost := by
  rw [value_eq_information_sub_error _ _ _ _ _ forecastSupport, exact_value]
  have error_nonneg : 0 ≤ ∑ r, (observationLaw prior result).1 r *
      klSum (posteriorLaw prior result supported r).1 (forecast r).1 := by
    apply Finset.sum_nonneg
    intro r _
    let target := posteriorLaw prior result supported r
    have bound : 0 ≤ klSum target.1 (forecast r).1 :=
      klSumOn_nonneg Finset.univ target.1 (forecast r).1
        (fun t _ => target.2.1 t) (fun t _ => (forecast r).2.1 t)
        (fun t _ => forecastSupport r t) (by rw [target.2.2, (forecast r).2.2])
    exact mul_nonneg ((observationLaw prior result).2.1 r) bound
  linarith

/-- A result independent of the target earns zero log-loss benefit, even
if it is informative about other quantities in the controller's state. -/
theorem independent_result_costs (prior : Prob Target) (noise : Prob Result)
    (supported : ∀ r, 0 < (observationLaw prior (fun _ => noise)).1 r) (cost : ℝ) :
    value prior (fun _ => noise) supported (posteriorLaw prior (fun _ => noise) supported) cost =
      -cost := by
  rw [exact_value, expectedInformationGain_eq_joint_divergence]
  have marginal : ∀ r, (observationLaw prior (fun _ => noise)).1 r = noise.1 r := by
    intro r
    rw [observationLaw_apply, evidence, ← Finset.sum_mul, prior.2.2, one_mul]
  simp only [marginal]
  change klSum (joint prior (fun _ => noise)).1 (joint prior (fun _ => noise)).1 - cost = _
  rw [klSum_self_eq_zero _ (joint prior (fun _ => noise)).2.1, zero_sub]

end Mettapedia.PLN.InferenceControl.LogLossControl
