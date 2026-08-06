import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.Core
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FusionBoundaryProvenance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.SequentialSelectivity

/-!
# Belief-policy frontier

This file joins the existing scalar linear-Gaussian boundary theorems to a new
finite multimodality boundary.  The modeled policies are selected by proved
regime conditions rather than architecture names:

* independent stationary Gaussian evidence uses additive natural coordinates;
* positive process drift requires statistically derived fading;
* known overlap requires discounted addition;
* fixed linear distortion is repaired in the measurement map;
* changing observation noise requires a selective gain schedule; and
* a genuinely bimodal finite posterior requires at least two atomic slots when
  actions are chosen by represented modes rather than a single Gaussian mean.

The multimodality statement is deliberately finite and narrow.  It concerns a
single Gaussian moment slot followed by nearest-mean action selection; it is
not a claim that every one-vector neural representation has Gaussian semantics.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open scoped BigOperators
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## A finite two-mode decision boundary -/

/-- Three legal completions, located at `-1`, `0`, and `1`. -/
abbrev Completion := Fin 3

/-- Scalar location chart for the three completion actions. -/
def completionLocation (action : Completion) : ℝ :=
  match action.1 with
  | 0 => -1
  | 1 => 0
  | _ => 1

/-- Equal posterior mass on the two outer completions and none at the mean. -/
noncomputable def bimodalCompletionMass (action : Completion) : ℝ :=
  match action.1 with
  | 0 => 1 / 2
  | 1 => 0
  | _ => 1 / 2

theorem bimodalCompletionMass_nonnegative (action : Completion) :
    0 ≤ bimodalCompletionMass action := by
  fin_cases action <;> norm_num [bimodalCompletionMass]

theorem bimodalCompletionMass_normalized :
    ∑ action : Completion, bimodalCompletionMass action = 1 := by
  norm_num [bimodalCompletionMass, Fin.sum_univ_succ]

/-- Mean of the declared finite posterior. -/
noncomputable def bimodalCompletionMean : ℝ :=
  ∑ action : Completion,
    bimodalCompletionMass action * completionLocation action

/-- Variance about the declared posterior mean. -/
noncomputable def bimodalCompletionVariance : ℝ :=
  ∑ action : Completion,
    bimodalCompletionMass action *
      (completionLocation action - bimodalCompletionMean) ^ 2

/-- The single-Gaussian moment projection retains only a mean and variance. -/
structure ScalarGaussianMomentSlot where
  mean : ℝ
  variance : ℝ
  variance_nonnegative : 0 ≤ variance

theorem bimodalCompletionMean_eq_zero : bimodalCompletionMean = 0 := by
  norm_num [bimodalCompletionMean, bimodalCompletionMass,
    completionLocation, Fin.sum_univ_succ]

theorem bimodalCompletionVariance_eq_one : bimodalCompletionVariance = 1 := by
  norm_num [bimodalCompletionVariance, bimodalCompletionMean,
    bimodalCompletionMass, completionLocation, Fin.sum_univ_succ]

/-- Moment-matched single Gaussian for the finite posterior. -/
noncomputable def bimodalSingleGaussianSlot : ScalarGaussianMomentSlot where
  mean := bimodalCompletionMean
  variance := bimodalCompletionVariance
  variance_nonnegative := by rw [bimodalCompletionVariance_eq_one]; norm_num

/-- Squared distance used by nearest-mean action selection. -/
noncomputable def meanDecisionDistance
    (slot : ScalarGaussianMomentSlot) (action : Completion) : ℝ :=
  (completionLocation action - slot.mean) ^ 2

/-- The center completion is the unique action nearest the projected mean. -/
theorem bimodalSingleGaussian_center_uniqueNearest :
    ∀ action : Completion,
      meanDecisionDistance bimodalSingleGaussianSlot 1 ≤
          meanDecisionDistance bimodalSingleGaussianSlot action ∧
        (meanDecisionDistance bimodalSingleGaussianSlot action =
            meanDecisionDistance bimodalSingleGaussianSlot 1 ↔ action = 1) := by
  intro action
  fin_cases action <;>
    norm_num [meanDecisionDistance, bimodalSingleGaussianSlot,
      bimodalCompletionMean_eq_zero, completionLocation]

/-- Nearest-mean selection from the single Gaussian chooses a zero-mass action. -/
theorem bimodalSingleGaussian_nearestMean_zeroProbability :
    bimodalCompletionMass 1 = 0 := by
  norm_num [bimodalCompletionMass]

/-! ## Exact atomic representations and their minimum width -/

/-- A width-`k` finite atomic belief register.  Zero-weight spare components
are permitted, so `k` is capacity rather than necessarily active support. -/
structure AtomicMixture (Action : Type*) (width : ℕ) where
  atom : Fin width → Action
  weight : Fin width → ℝ
  weight_nonnegative : ∀ index, 0 ≤ weight index
  weight_sum_one : ∑ index, weight index = 1

/-- Probability mass assigned to an action by an atomic mixture. -/
noncomputable def AtomicMixture.mass
    {Action : Type*} [DecidableEq Action] {width : ℕ}
    (mixture : AtomicMixture Action width) (action : Action) : ℝ :=
  ∑ index, if mixture.atom index = action then mixture.weight index else 0

/-- Exact representation of a finite mass function. -/
def AtomicMixture.Represents
    {Action : Type*} [Fintype Action] [DecidableEq Action] {width : ℕ}
    (mixture : AtomicMixture Action width) (probability : Action → ℝ) : Prop :=
  ∀ action, mixture.mass action = probability action

/-- The two-component register stores precisely the two supported modes. -/
noncomputable def bimodalTwoComponentMixture : AtomicMixture Completion 2 where
  atom := fun index => match index.1 with | 0 => 0 | _ => 2
  weight := fun _index => 1 / 2
  weight_nonnegative := by intro; norm_num
  weight_sum_one := by norm_num [Fin.sum_univ_succ]

theorem bimodalTwoComponentMixture_represents :
    bimodalTwoComponentMixture.Represents bimodalCompletionMass := by
  intro action
  fin_cases action <;>
    norm_num [AtomicMixture.Represents, AtomicMixture.mass,
      bimodalTwoComponentMixture, bimodalCompletionMass, Fin.sum_univ_succ] <;>
    decide

/-- No empty atomic register represents a normalized posterior. -/
theorem noWidthZero_represents_bimodal :
    ¬ ∃ mixture : AtomicMixture Completion 0,
      mixture.Represents bimodalCompletionMass := by
  rintro ⟨mixture, hrepresents⟩
  have hleft := hrepresents (0 : Completion)
  norm_num [AtomicMixture.Represents, AtomicMixture.mass,
    bimodalCompletionMass] at hleft

/-- One atom cannot place positive mass on both distinct outer actions. -/
theorem noWidthOne_represents_bimodal :
    ¬ ∃ mixture : AtomicMixture Completion 1,
      mixture.Represents bimodalCompletionMass := by
  rintro ⟨mixture, hrepresents⟩
  have hleft := hrepresents (0 : Completion)
  have hright := hrepresents (2 : Completion)
  generalize hatom : mixture.atom 0 = action at hleft hright
  fin_cases action
  · have hne : (0 : Completion) ≠ 2 := by decide
    simp [AtomicMixture.mass, bimodalCompletionMass,
      hatom, hne] at hright
  · have hne : (1 : Completion) ≠ 0 := by decide
    simp [AtomicMixture.mass, bimodalCompletionMass,
      hatom, hne] at hleft
  · have hne : (2 : Completion) ≠ 0 := by decide
    simp [AtomicMixture.mass, bimodalCompletionMass,
      hatom, hne] at hleft

/-- Width `k` is the smallest exact capacity when it represents the posterior
and every smaller capacity fails to represent it. -/
def IsMinimumAtomicWidth
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (probability : Action → ℝ) (width : ℕ) : Prop :=
  (∃ mixture : AtomicMixture Action width,
      mixture.Represents probability) ∧
    ∀ smaller < width,
      ¬ ∃ mixture : AtomicMixture Action smaller,
        mixture.Represents probability

/-- Multimodality representation crown: the smallest exact atomic capacity is
two, with explicit failures at widths zero and one. -/
theorem bimodalCompletion_minimumAtomicWidth_two :
    IsMinimumAtomicWidth bimodalCompletionMass 2 := by
  constructor
  · exact ⟨bimodalTwoComponentMixture,
      bimodalTwoComponentMixture_represents⟩
  · intro smaller hsmaller
    have hcases : smaller = 0 ∨ smaller = 1 := by omega
    rcases hcases with rfl | rfl
    · exact noWidthZero_represents_bimodal
    · exact noWidthOne_represents_bimodal

/-- A mode-aware two-component policy may choose the left represented mode. -/
def bimodalMixtureChoice : Completion := 0

/-- The mixture-aware legal action has positive posterior mass. -/
theorem bimodalMixtureChoice_positiveProbability :
    0 < bimodalCompletionMass bimodalMixtureChoice := by
  norm_num [bimodalMixtureChoice, bimodalCompletionMass]

/-- Exact decision-probability advantage over the nearest-mean Gaussian
projection in the fixture. -/
noncomputable def bimodalDecisionGap : ℝ :=
  bimodalCompletionMass bimodalMixtureChoice - bimodalCompletionMass 1

theorem bimodalDecisionGap_eq_half : bimodalDecisionGap = 1 / 2 := by
  norm_num [bimodalDecisionGap, bimodalMixtureChoice,
    bimodalCompletionMass]

/-! ## One proof-bearing policy map for all six regimes -/

/-- Scalar Gaussian natural coordinates `(information, precision) = (Λμ, Λ)`.
They are stored without normalization. -/
noncomputable def scalarGaussianNatural
    (mean precision : ℝ) : ℝ × ℝ :=
  (precision * mean, precision)

/-- Independent scalar Gaussian packets fuse by literal componentwise
addition in natural coordinates. -/
theorem scalarGaussianNatural_add_exact
    (firstMean secondMean firstPrecision secondPrecision : ℝ) :
    scalarGaussianNatural firstMean firstPrecision +
        scalarGaussianNatural secondMean secondPrecision =
      (firstPrecision * firstMean + secondPrecision * secondMean,
        firstPrecision + secondPrecision) := by
  rfl

/-- The six modeled belief regimes. -/
inductive BeliefRegime where
  | stationaryIndependentGaussian
  | positiveProcessDrift
  | knownObservationOverlap
  | fixedLinearDistortion
  | varyingObservationNoise
  | finiteBimodalDecision
  deriving DecidableEq, Fintype, Repr

/-- Belief policies licensed by the regime theory. -/
inductive BeliefPolicy where
  | additiveNatural
  | fadingNatural
  | discountedNatural
  | calibratedMeasurement
  | selectiveGain
  | finiteMixture (width : ℕ)
  deriving DecidableEq, Repr

/-- Policy selected for each modeled regime. -/
def recommendedBeliefPolicy : BeliefRegime → BeliefPolicy
  | .stationaryIndependentGaussian => .additiveNatural
  | .positiveProcessDrift => .fadingNatural
  | .knownObservationOverlap => .discountedNatural
  | .fixedLinearDistortion => .calibratedMeasurement
  | .varyingObservationNoise => .selectiveGain
  | .finiteBimodalDecision => .finiteMixture 2

/-- Mathematical guarantee attached to a regime/policy pair.  Nonmatching
pairs are unlicensed, and the matching cases expose the actual risk,
calibration, or representation statement rather than a policy label. -/
def BeliefPolicyGuarantee : BeliefRegime → BeliefPolicy → Prop
  | .stationaryIndependentGaussian, .additiveNatural =>
      (∀ firstMean secondMean firstPrecision secondPrecision : ℝ,
        scalarGaussianNatural firstMean firstPrecision +
            scalarGaussianNatural secondMean secondPrecision =
          (firstPrecision * firstMean + secondPrecision * secondMean,
            firstPrecision + secondPrecision)) ∧
      (∀ priorVariance noiseVariance : ℝ,
        0 < priorVariance → 0 < noiseVariance →
            (∀ gate,
              varianceGateRisk priorVariance noiseVariance
                  (varianceKalmanGain priorVariance noiseVariance) ≤
                varianceGateRisk priorVariance noiseVariance gate) ∧
            (∀ gate,
              varianceGateRisk priorVariance noiseVariance gate =
                  varianceGateRisk priorVariance noiseVariance
                    (varianceKalmanGain priorVariance noiseVariance) ↔
                gate = varianceKalmanGain priorVariance noiseVariance))
  | .positiveProcessDrift, .fadingNatural =>
      ∀ oldVariance jumpVariance noiseVariance retainedVariance : ℝ,
        0 < oldVariance → 0 < jumpVariance → 0 < noiseVariance →
          MonotoneAccumulatorVariance oldVariance retainedVariance →
            varianceGateRisk
                (jumpPredictiveVariance oldVariance jumpVariance)
                noiseVariance
                (jumpOptimalGain oldVariance jumpVariance noiseVariance) <
            varianceGateRisk
                (jumpPredictiveVariance oldVariance jumpVariance)
                noiseVariance
                (varianceKalmanGain retainedVariance noiseVariance) ∧
            (jumpPredictiveVariance oldVariance jumpVariance)⁻¹ =
              jumpInformationRetention oldVariance jumpVariance *
                oldVariance⁻¹ ∧
            jumpInformationRetention oldVariance jumpVariance ∈
              Set.Ioo (0 : ℝ) 1
  | .knownObservationOverlap, .discountedNatural =>
      ∀ priorPrecision firstPrecision secondPrecision overlap : ℝ,
        0 < priorPrecision →
          ValidPrecisionOverlap firstPrecision secondPrecision overlap →
          secondPrecision ≠ 0 →
          naiveOverlappingPrecision priorPrecision firstPrecision
                secondPrecision -
              overlapCalibratedPrecision priorPrecision firstPrecision
                secondPrecision overlap = overlap ∧
            1 / overlapCalibratedPrecision priorPrecision firstPrecision
                  secondPrecision overlap -
                1 / naiveOverlappingPrecision priorPrecision firstPrecision
                  secondPrecision =
              overlap /
                (overlapCalibratedPrecision priorPrecision firstPrecision
                    secondPrecision overlap *
                  naiveOverlappingPrecision priorPrecision firstPrecision
                    secondPrecision) ∧
            overlapCalibratedPrecision priorPrecision firstPrecision
                secondPrecision overlap =
              priorPrecision + firstPrecision +
                secondPrecision * overlapRetention secondPrecision overlap
  | .fixedLinearDistortion, .calibratedMeasurement =>
      ∀ priorVariance noiseVariance distortion : ℝ,
        0 < priorVariance → 0 < noiseVariance → distortion ≠ 0 →
          (unitModelHardwiredMix priorVariance noiseVariance =
                distortedOptimalMix priorVariance noiseVariance distortion ↔
              (distortion - 1) *
                (priorVariance * distortion - noiseVariance) = 0) ∧
          ((distortion - 1) *
              (priorVariance * distortion - noiseVariance) ≠ 0 →
            distortedMeasurementRisk priorVariance noiseVariance distortion
                (distortedOptimalMix priorVariance noiseVariance distortion) <
              distortedMeasurementRisk priorVariance noiseVariance distortion
                (unitModelHardwiredMix priorVariance noiseVariance)) ∧
          recalibratedHardwiredRawCoefficient
                priorVariance noiseVariance distortion =
              distortedOptimalMix priorVariance noiseVariance distortion
  | .varyingObservationNoise, .selectiveGain =>
      (∀ priorVariance firstNoise secondNoise gate : ℝ,
        0 < priorVariance → 0 < firstNoise → 0 < secondNoise →
          firstNoise ≠ secondNoise →
            twoRegimeSelectiveRisk priorVariance firstNoise secondNoise <
              twoRegimeConstantGateRisk priorVariance firstNoise secondNoise gate) ∧
      (∀ priorVariance noiseVariance : ℝ,
        twoRegimeConstantGateRisk priorVariance noiseVariance noiseVariance
            (varianceKalmanGain priorVariance noiseVariance) =
          twoRegimeSelectiveRisk priorVariance noiseVariance noiseVariance)
  | .finiteBimodalDecision, .finiteMixture 2 =>
      IsMinimumAtomicWidth bimodalCompletionMass 2 ∧
        bimodalCompletionMass 1 = 0 ∧
        0 < bimodalCompletionMass bimodalMixtureChoice
  | _, _ => False

/-- T2 policy crown: every modeled regime selects a policy carrying its full
boundary proof. -/
theorem beliefPolicy_frontier (regime : BeliefRegime) :
    BeliefPolicyGuarantee regime (recommendedBeliefPolicy regime) := by
  cases regime with
  | stationaryIndependentGaussian =>
      exact ⟨scalarGaussianNatural_add_exact,
        fun priorVariance noiseVariance hprior hnoise =>
          varianceKalmanGain_uniqueMinimizer
            priorVariance noiseVariance hprior hnoise⟩
  | positiveProcessDrift =>
      intro oldVariance jumpVariance noiseVariance retainedVariance
        hold hjump hnoise hretained
      exact ⟨monotoneEvidenceAccumulator_strictlySuboptimalAfterJump
          oldVariance jumpVariance noiseVariance retainedVariance
          hold hjump hnoise hretained,
        jumpPredictivePrecision_eq_decayedOldPrecision
          oldVariance jumpVariance hold hjump.le,
        jumpInformationRetention_mem_Ioo oldVariance jumpVariance hold hjump⟩
  | knownObservationOverlap =>
      intro priorPrecision firstPrecision secondPrecision overlap
        hprior hvalid hsecond
      exact ⟨naivePrecision_sub_calibrated_eq_overlap
          priorPrecision firstPrecision secondPrecision overlap,
        overlapVarianceGap_exact priorPrecision firstPrecision secondPrecision
          overlap hprior hvalid,
        overlapCalibratedPrecision_eq_discountedAddition
          priorPrecision firstPrecision secondPrecision overlap hsecond⟩
  | fixedLinearDistortion =>
      intro priorVariance noiseVariance distortion hprior hnoise
        hdistortion
      exact ⟨unitModelHardwiredMix_eq_distortedOptimalMix_iff
          priorVariance noiseVariance distortion hprior hnoise,
        learnedMix_strictlyOutperforms_uncorrectedHardwiredFusion
          priorVariance noiseVariance distortion hprior hnoise,
        recalibratedHardwiredRawCoefficient_eq_distortedOptimalMix
          priorVariance noiseVariance distortion hprior hnoise hdistortion⟩
  | varyingObservationNoise =>
      exact ⟨fun priorVariance firstNoise secondNoise gate hprior hfirst
          hsecond hnoise =>
        everyConstantGate_strictlySuboptimal priorVariance firstNoise
          secondNoise gate hprior hfirst hsecond hnoise,
        constantNoise_no_selectivitySeparation⟩
  | finiteBimodalDecision =>
      exact ⟨bimodalCompletion_minimumAtomicWidth_two,
        bimodalSingleGaussian_nearestMean_zeroProbability,
        bimodalMixtureChoice_positiveProbability⟩

#print axioms bimodalSingleGaussian_center_uniqueNearest
#print axioms bimodalCompletion_minimumAtomicWidth_two
#print axioms bimodalDecisionGap_eq_half
#print axioms scalarGaussianNatural_add_exact
#print axioms beliefPolicy_frontier

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
