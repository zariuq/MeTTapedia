import Mettapedia.PLN.WorldModel.BayesianObservationLedger
import Mettapedia.ProbabilityTheory.BayesianInference.InformationLaws
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Replay, dependent reports, and continuous observations -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.PLN.WorldModel.BayesianObservationLedger.Controls

open MeasureTheory
open scoped ENNReal

def report (state : Bool) : ℝ≥0∞ := if state then 3 / 4 else 1 / 4

def independent : ObservationModel Bool Nat where
  likelihood _ _ := report
  measurable _ _ := measurable_of_countable _

/-- A second distinct event can be a perfect echo of an already known
report. Its conditional likelihood is one, despite its distinct ID. -/
def echo : ObservationModel Bool Nat where
  likelihood history _ := if history.isEmpty then report else fun _ => 1
  measurable _ _ := measurable_of_countable _

theorem once : independent.density [0] true = 3 / 4 := by
  norm_num [ObservationModel.density, independent, report]

theorem fresh_independent : independent.density [1, 0] true = 9 / 16 := by
  norm_num [ObservationModel.density, independent, report]
  have cast := congrArg (fun value : NNReal => (value : ℝ≥0∞))
    (show (3 : NNReal) / 4 * (3 / 4) = 9 / 16 by norm_num)
  simpa [ENNReal.coe_mul, ENNReal.coe_div] using cast

theorem replay_once :
    independent.density (ObservationModel.record [0] 0) true = 3 / 4 := by
  norm_num [ObservationModel.record, once]

theorem distinct_not_independent : (1 : Nat) ≠ 0 ∧
    echo.density [1, 0] true ≠ independent.density [1, 0] true := by
  constructor
  · decide
  · norm_num [ObservationModel.density, echo, independent, report]
    have cast := (ENNReal.coe_injective.ne
      (show (3 : NNReal) / 4 ≠ 3 / 4 * (3 / 4) by norm_num))
    simpa [ENNReal.coe_mul, ENNReal.coe_div] using cast

def continuousObservation (state : Bool) : Measure ℝ :=
  if state then volume.restrict (Set.Icc 0 1)
  else (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc 0 2)

/-- Both hypotheses give normalized continuous observation laws. -/
theorem continuousObservation_probability (state : Bool) :
    IsProbabilityMeasure (continuousObservation state) := by
  constructor
  cases state <;>
    norm_num [continuousObservation, Measure.smul_apply, Measure.restrict_apply,
      Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

def continuousKernel : ProbabilityTheory.Kernel Bool ℝ where
  toFun := continuousObservation
  measurable' := measurable_of_countable _

instance : ProbabilityTheory.IsMarkovKernel continuousKernel where
  isProbabilityMeasure state := continuousObservation_probability state

def observationDensity (state : Bool) (value : ℝ) : ℝ≥0∞ :=
  if state then (Set.Icc (0 : ℝ) 1).indicator (fun _ => 1) value
  else (Set.Icc (0 : ℝ) 2).indicator (fun _ => 1 / 2) value

theorem continuousKernel_density (state : Bool) :
    continuousKernel state = volume.withDensity (observationDensity state) := by
  change continuousObservation state = _
  cases state
  · change (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (0 : ℝ) 2) =
      volume.withDensity ((Set.Icc (0 : ℝ) 2).indicator (fun _ => 1 / 2))
    rw [withDensity_indicator measurableSet_Icc, withDensity_const]
  · change volume.restrict (Set.Icc (0 : ℝ) 1) =
      volume.withDensity ((Set.Icc (0 : ℝ) 1).indicator (fun _ => 1))
    rw [withDensity_indicator measurableSet_Icc, withDensity_const, one_smul]

theorem singleton_zero (state : Bool) : continuousKernel state {(1 / 2 : ℝ)} = 0 := by
  change continuousObservation state {(1 / 2 : ℝ)} = 0
  cases state <;> simp [continuousObservation]

/-- Density updating at a null singleton is informative: the two hypotheses
give likelihoods 1 and 1/2 at the actual observation. -/
theorem positive_density_at_null_observation :
    observationDensity true (1 / 2) = 1 ∧ observationDensity false (1 / 2) = 1 / 2 := by
  norm_num [observationDensity, Set.indicator_apply]

open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference

def prior : Prob Bool := ⟨fun _ => 1 / 2, (fun _ => by norm_num), by norm_num [Fintype.sum_bool]⟩

def likelihood (state : Bool) : ℝ := if state then 1 else 1 / 2

/-- The likelihood passed to finite Bayes is the actual continuous kernel
density, evaluated at the observed real value, rather than a proxy score. -/
theorem likelihood_is_kernel_density (state : Bool) :
    likelihood state = (observationDensity state (1 / 2)).toReal := by
  cases state <;> norm_num [likelihood, observationDensity, Set.indicator_apply]

theorem density_evidence : evidence prior likelihood = 3 / 4 := by
  norm_num [evidence, prior, likelihood, Fintype.sum_bool]

def afterContinuousObservation : Prob Bool :=
  posterior prior likelihood (by intro state; cases state <;> norm_num [likelihood])
    (by rw [density_evidence]; norm_num)

theorem informative_continuous_posterior : afterContinuousObservation.1 true = 2 / 3 := by
  norm_num [afterContinuousObservation, posterior_apply, evidence, prior, likelihood, Fintype.sum_bool]

/-- Use the actual kernel density, not only its evaluated proxy, in the
posterior construction at a zero-singleton-mass continuous observation. -/
theorem kernel_density_posterior :
    (posterior prior (fun state => (observationDensity state (1 / 2)).toReal)
      (by intro state; exact ENNReal.toReal_nonneg)
      (by simpa only [← likelihood_is_kernel_density] using
        (show 0 < evidence prior likelihood by rw [density_evidence]; norm_num))).1 true = 2 / 3 := by
  simpa only [← likelihood_is_kernel_density, afterContinuousObservation] using informative_continuous_posterior

#print axioms continuousKernel_density
#print axioms informative_continuous_posterior
#print axioms distinct_not_independent

end Mettapedia.PLN.WorldModel.BayesianObservationLedger.Controls
