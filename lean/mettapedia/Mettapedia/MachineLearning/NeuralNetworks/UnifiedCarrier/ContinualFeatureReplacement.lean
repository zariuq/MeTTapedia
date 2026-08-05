import Mathlib

/-!
# Continual feature replacement

Dohare, Sutton, and Mahmood, *Continual Backprop: Stochastic Gradient
Descent with Persistent Randomness* (arXiv:2108.06325), Section 4 and
Algorithm 1, continually replace mature low-utility features.  A replacement
draws new incoming weights, zeros the feature's outgoing weights, and resets
its utility, activation average, and age.  Their mean-corrected contribution
utility is proportional to

`|activation - average activation| * sum |outgoing weight|`.

This file isolates the exact local algebra behind those choices.  Once the
outgoing row is zero, the newly sampled feature is immediately invisible to
the readout, independently of its activation.  The readout disturbance caused
by removing the old feature is exactly its raw outgoing contribution.  If the
mean contribution is already represented by the bias/base path, the remaining
disturbance is exactly the source's mean-corrected contribution utility.

The distinction is essential: without the mean-transfer premise, centered
utility can be zero while immediate removal still changes the readout.  The
file also formalizes the source's strict maturity gate and represents
bias-correction at age zero as unavailable rather than silently dividing by
zero.

No theorem here claims that replacement improves optimization, prevents
plasticity loss, preserves the complete pre-replacement network function, or
establishes the source's empirical results.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace ContinualFeatureReplacement

noncomputable section

variable {Output : Type*}

/-- A single feature's contribution to a downstream readout.  `base` contains
the bias and every other feature's contribution. -/
structure FeatureReadout (Output : Type*) where
  base : Output → ℝ
  activation : ℝ
  outgoing : Output → ℝ

/-- The downstream readout decomposed into the base path and one feature. -/
def readout (feature : FeatureReadout Output) (output : Output) : ℝ :=
  feature.base output + feature.outgoing output * feature.activation

/-- The source replacement endpoint: the new feature may have an arbitrary
activation, but every outgoing weight is reset to zero. -/
def resetOutgoing
    (feature : FeatureReadout Output) (newActivation : ℝ) :
    FeatureReadout Output where
  base := feature.base
  activation := newActivation
  outgoing := fun _ => 0

/-- A replacement with the old mean contribution already transferred to the
base/bias path.  This is the explicit premise under which the source's
mean-corrected utility exactly measures removal disturbance. -/
def resetOutgoingWithMeanTransfer
    (feature : FeatureReadout Output) (meanActivation newActivation : ℝ) :
    FeatureReadout Output where
  base := fun output =>
    feature.base output + feature.outgoing output * meanActivation
  activation := newActivation
  outgoing := fun _ => 0

/-- Zero outgoing weights make the newly sampled feature immediately
invisible to the downstream readout. -/
@[simp] theorem readout_resetOutgoing
    (feature : FeatureReadout Output) (newActivation : ℝ)
    (output : Output) :
    readout (resetOutgoing feature newActivation) output =
      feature.base output := by
  simp [readout, resetOutgoing]

/-- The immediate readout after replacement is independent of the random
incoming initialization, represented here by the resulting activation. -/
theorem resetOutgoing_randomness_invisible
    (feature : FeatureReadout Output) (first second : ℝ) :
    readout (resetOutgoing feature first) =
      readout (resetOutgoing feature second) := by
  funext output
  simp

/-- Without a mean-transfer premise, the exact immediate disturbance is the
old feature's raw outgoing contribution. -/
theorem resetOutgoing_difference
    (feature : FeatureReadout Output) (newActivation : ℝ)
    (output : Output) :
    readout feature output -
        readout (resetOutgoing feature newActivation) output =
      feature.outgoing output * feature.activation := by
  simp [readout, resetOutgoing]

/-- With the mean contribution represented by the base path, the exact
disturbance is the outgoing weight times centered activation. -/
theorem resetOutgoingWithMeanTransfer_difference
    (feature : FeatureReadout Output)
    (meanActivation newActivation : ℝ) (output : Output) :
    readout feature output -
        readout
          (resetOutgoingWithMeanTransfer
            feature meanActivation newActivation) output =
      feature.outgoing output *
        (feature.activation - meanActivation) := by
  simp [readout, resetOutgoingWithMeanTransfer]
  ring

/-- Total entrywise readout disturbance. -/
def totalDisturbance [Fintype Output]
    (before after : FeatureReadout Output) : ℝ :=
  ∑ output, |readout before output - readout after output|

/-- The raw contribution utility associated with immediate removal. -/
def rawContributionUtility [Fintype Output]
    (feature : FeatureReadout Output) : ℝ :=
  (∑ output, |feature.outgoing output|) * |feature.activation|

/-- The mean-corrected contribution term from Section 4, Equation (4). -/
def meanCorrectedContributionUtility [Fintype Output]
    (feature : FeatureReadout Output) (meanActivation : ℝ) : ℝ :=
  (∑ output, |feature.outgoing output|) *
    |feature.activation - meanActivation|

/-- Immediate reset disturbance is exactly the raw contribution utility. -/
theorem totalDisturbance_resetOutgoing [Fintype Output]
    (feature : FeatureReadout Output) (newActivation : ℝ) :
    totalDisturbance feature (resetOutgoing feature newActivation) =
      rawContributionUtility feature := by
  classical
  simp only [totalDisturbance, resetOutgoing_difference, abs_mul,
    rawContributionUtility]
  rw [Finset.sum_mul]

/-- Under explicit mean transfer, total reset disturbance is exactly the
source's mean-corrected contribution term. -/
theorem totalDisturbance_resetOutgoingWithMeanTransfer [Fintype Output]
    (feature : FeatureReadout Output)
    (meanActivation newActivation : ℝ) :
    totalDisturbance feature
        (resetOutgoingWithMeanTransfer
          feature meanActivation newActivation) =
      meanCorrectedContributionUtility feature meanActivation := by
  classical
  simp only [totalDisturbance,
    resetOutgoingWithMeanTransfer_difference, abs_mul,
    meanCorrectedContributionUtility]
  rw [Finset.sum_mul]

/-- Selecting a feature below a declared mean-corrected contribution budget
therefore bounds the complete entrywise disturbance, provided mean transfer
has been established. -/
theorem totalDisturbance_le_of_meanCorrectedContributionUtility_le
    [Fintype Output]
    (feature : FeatureReadout Output)
    (meanActivation newActivation budget : ℝ)
    (utilityBound :
      meanCorrectedContributionUtility feature meanActivation ≤ budget) :
    totalDisturbance feature
        (resetOutgoingWithMeanTransfer
          feature meanActivation newActivation) ≤ budget := by
  rw [totalDisturbance_resetOutgoingWithMeanTransfer]
  exact utilityBound

/-! ## Maturity and bias correction -/

/-- Algorithm 1 makes a feature eligible only when its age is strictly greater
than the maturity threshold. -/
def eligible (maturity age : ℕ) : Prop :=
  maturity < age

/-- Age after a reset followed by the given number of updates. -/
def ageAfterReset (updates : ℕ) : ℕ :=
  updates

/-- A reset feature remains protected through the maturity threshold. -/
theorem not_eligible_through_maturity
    {maturity updates : ℕ} (notMature : updates ≤ maturity) :
    ¬ eligible maturity (ageAfterReset updates) := by
  exact not_lt_of_ge notMature

/-- The first age after the protected interval is eligible. -/
@[simp] theorem eligible_first_step_after_maturity (maturity : ℕ) :
    eligible maturity (ageAfterReset (maturity + 1)) := by
  simp [eligible, ageAfterReset]

/-- Replacing strict eligibility by `≤` would expose a fresh feature
immediately when the threshold is zero. -/
def nonstrictEligible (maturity age : ℕ) : Prop :=
  maturity ≤ age

theorem nonstrict_zero_threshold_exposes_fresh_feature :
    nonstrictEligible 0 (ageAfterReset 0) := by
  simp [nonstrictEligible, ageAfterReset]

/-- Bias correction from Equation (7), made partial at a zero denominator. -/
def biasCorrectedUtility?
    (decay rawUtility : ℝ) (age : ℕ) : Option ℝ :=
  if 1 - decay ^ age = 0 then
    none
  else
    some (rawUtility / (1 - decay ^ age))

/-- At reset age zero, bias correction is unavailable. -/
@[simp] theorem biasCorrectedUtility?_age_zero
    (decay rawUtility : ℝ) :
    biasCorrectedUtility? decay rawUtility 0 = none := by
  simp [biasCorrectedUtility?]

/-- Whenever the correction denominator is nonzero, the partial definition
recovers Equation (7) exactly. -/
theorem biasCorrectedUtility?_eq_some
    (decay rawUtility : ℝ) (age : ℕ)
    (denominatorNonzero : 1 - decay ^ age ≠ 0) :
    biasCorrectedUtility? decay rawUtility age =
      some (rawUtility / (1 - decay ^ age)) := by
  simp [biasCorrectedUtility?, denominatorNonzero]

/-! ## Executable positive and negative fixtures -/

def twoOutputFeature : FeatureReadout (Fin 2) where
  base
    | 0 => 10
    | 1 => 20
  activation := 3
  outgoing
    | 0 => 2
    | 1 => -1

theorem raw_replacement :
    readout twoOutputFeature 0 = 16 ∧
      readout twoOutputFeature 1 = 17 ∧
      readout (resetOutgoing twoOutputFeature 100) 0 = 10 ∧
      readout (resetOutgoing twoOutputFeature (-100)) 1 = 20 ∧
      totalDisturbance twoOutputFeature
        (resetOutgoing twoOutputFeature 100) = 9 := by
  norm_num [readout, resetOutgoing, totalDisturbance, twoOutputFeature]

/-- Mean transfer of `2` leaves only the centered activation `3 - 2`, so the
two-output disturbance is exactly `|2| + |-1| = 3`. -/
theorem mean_transferred_replacement :
    totalDisturbance twoOutputFeature
        (resetOutgoingWithMeanTransfer twoOutputFeature 2 100) = 3 ∧
      meanCorrectedContributionUtility twoOutputFeature 2 = 3 := by
  norm_num [totalDisturbance, readout, resetOutgoingWithMeanTransfer,
    meanCorrectedContributionUtility, twoOutputFeature]

/-- The mean-corrected term is not an unconditional bound on immediate
replacement.  If the mean contribution has not moved to the base path, it can
be zero even though zeroing outgoing weights changes the readout. -/
theorem centered_utility_without_mean_transfer_is_insufficient :
    meanCorrectedContributionUtility twoOutputFeature 3 = 0 ∧
      0 <
        totalDisturbance twoOutputFeature
          (resetOutgoing twoOutputFeature 100) := by
  norm_num [meanCorrectedContributionUtility, totalDisturbance, readout,
    resetOutgoing, twoOutputFeature]

theorem half_decay_bias_correction :
    biasCorrectedUtility? (1 / 2) 3 1 = some 6 := by
  norm_num [biasCorrectedUtility?]

#print axioms readout_resetOutgoing
#print axioms resetOutgoing_randomness_invisible
#print axioms resetOutgoing_difference
#print axioms resetOutgoingWithMeanTransfer_difference
#print axioms totalDisturbance_resetOutgoing
#print axioms totalDisturbance_resetOutgoingWithMeanTransfer
#print axioms totalDisturbance_le_of_meanCorrectedContributionUtility_le
#print axioms not_eligible_through_maturity
#print axioms eligible_first_step_after_maturity
#print axioms nonstrict_zero_threshold_exposes_fresh_feature
#print axioms biasCorrectedUtility?_age_zero
#print axioms biasCorrectedUtility?_eq_some
#print axioms raw_replacement
#print axioms mean_transferred_replacement
#print axioms centered_utility_without_mean_transfer_is_insufficient
#print axioms half_decay_bias_correction

end

end ContinualFeatureReplacement

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
