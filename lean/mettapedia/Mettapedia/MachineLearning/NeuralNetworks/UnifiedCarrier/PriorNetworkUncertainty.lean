import Mathlib.Tactic
import Mettapedia.InformationTheory.ShannonEntropy.Properties
import KnuthSkilling.Information.InformationEntropy

/-!
# Predictive uncertainty decomposition for finite prior-network ensembles

Malinin and Gales, *Predictive Uncertainty Estimation via Prior Networks*
(2018, arXiv:1802.10501), Equations (16)--(17), separate total predictive
uncertainty into expected data uncertainty and a mutual-information gap.
For a distribution over categorical predictors, that gap is the entropy of
the mean prediction minus the mean entropy of the predictors.

This file proves a finite weighted version of the decomposition.

* The mean of finitely many categorical predictors is a categorical
  predictor.
* The entropy gap is exactly the weighted average divergence of each
  predictor from the mean and is therefore nonnegative.
* It is bounded above by total predictive entropy.
* Duplicate predictors have zero distributional information.
* Two executable binary ensembles have the same uniform mean prediction:
  an ensemble of opposite point masses has zero expected data uncertainty
  and distributional information `log 2`, while duplicate uniform
  predictors have expected data uncertainty `log 2` and zero distributional
  information.

The result is a theorem about declared finite probability vectors. It does
not identify an input as out of distribution, prove calibration, derive the
Dirichlet digamma formula, or establish the empirical performance of a prior
network.

Source artifact SHA-256:
`a40b4de097f80d9c8577776f4fa8c84f6f10c88be24f4ee67cd28b149566cc16`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace PriorNetworkUncertainty

open scoped BigOperators
open Finset Real
open Mettapedia.InformationTheory

noncomputable section

/-- A finite distribution over finite categorical predictors. -/
structure PredictiveEnsemble (MemberCount ClassCount : ℕ) where
  weights : ProbVec MemberCount
  prediction : Fin MemberCount → ProbVec ClassCount

variable {MemberCount ClassCount : ℕ}

/-- The categorical prediction obtained by averaging the ensemble. -/
def ensembleMean
    (ensemble : PredictiveEnsemble MemberCount ClassCount) :
    ProbVec ClassCount where
  val classIndex :=
    ∑ memberIndex,
      ensemble.weights.1 memberIndex *
        (ensemble.prediction memberIndex).1 classIndex
  property := by
    constructor
    · intro classIndex
      exact Finset.sum_nonneg fun memberIndex _ =>
        mul_nonneg
          (ensemble.weights.nonneg memberIndex)
          ((ensemble.prediction memberIndex).nonneg classIndex)
    · rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      simp [ProbVec.sum_eq_one]

/-- Expected categorical entropy of an ensemble member. -/
def expectedDataUncertainty
    (ensemble : PredictiveEnsemble MemberCount ClassCount) : ℝ :=
  ∑ memberIndex,
    ensemble.weights.1 memberIndex *
      shannonEntropy (ensemble.prediction memberIndex)

/-- Entropy of the mean prediction minus expected member entropy. -/
def distributionalInformation
    (ensemble : PredictiveEnsemble MemberCount ClassCount) : ℝ :=
  shannonEntropy (ensembleMean ensemble) -
    expectedDataUncertainty ensemble

/-- Finite categorical divergence in natural logarithm units. -/
def categoricalDivergence
    (prediction reference : ProbVec ClassCount) : ℝ :=
  ∑ classIndex,
    prediction.1 classIndex *
      log (prediction.1 classIndex / reference.1 classIndex)

/-- Explicit bridge from the mathlib-simplex probability vector used here to
the finite distribution used by the standalone Knuth--Skilling development. -/
def toKSDist (prediction : ProbVec ClassCount) :
    KnuthSkilling.Information.InformationEntropy.ProbDist ClassCount where
  p := prediction.1
  nonneg := prediction.nonneg
  sum_one := prediction.sum_eq_one

@[simp]
theorem toKSDist_apply
    (prediction : ProbVec ClassCount) (classIndex : Fin ClassCount) :
    (toKSDist prediction).p classIndex = prediction.1 classIndex :=
  rfl

theorem categoricalDivergence_eq_ksKLDivergence
    (prediction reference : ProbVec ClassCount)
    (hreference :
      ∀ classIndex,
        prediction.1 classIndex ≠ 0 →
          0 < reference.1 classIndex) :
    categoricalDivergence prediction reference =
      KnuthSkilling.Information.InformationEntropy.klDivergence
        (toKSDist prediction) (toKSDist reference) hreference := by
  rfl

theorem categoricalDivergence_nonneg
    (prediction reference : ProbVec ClassCount)
    (hreference :
      ∀ classIndex,
        prediction.1 classIndex ≠ 0 →
          0 < reference.1 classIndex) :
    0 ≤ categoricalDivergence prediction reference := by
  rw [categoricalDivergence_eq_ksKLDivergence
    prediction reference hreference]
  exact
    KnuthSkilling.Information.InformationEntropy.klDivergence_nonneg'
      (toKSDist prediction) (toKSDist reference) hreference

/-- Weighted average divergence from the ensemble mean. -/
def averageDivergenceFromMean
    (ensemble : PredictiveEnsemble MemberCount ClassCount) : ℝ :=
  ∑ memberIndex,
    ensemble.weights.1 memberIndex *
      categoricalDivergence
        (ensemble.prediction memberIndex)
        (ensembleMean ensemble)

theorem ensembleMean_coordinate
    (ensemble : PredictiveEnsemble MemberCount ClassCount)
    (classIndex : Fin ClassCount) :
    ∑ memberIndex,
        ensemble.weights.1 memberIndex *
          (ensemble.prediction memberIndex).1 classIndex =
      (ensembleMean ensemble).1 classIndex :=
  rfl

/-- Coordinate form of the entropy-gap/divergence identity. -/
theorem coordinate_entropyGap_eq_averageDivergence
    (ensemble : PredictiveEnsemble MemberCount ClassCount)
    (classIndex : Fin ClassCount)
    (hmean : 0 < (ensembleMean ensemble).1 classIndex) :
    negMulLog ((ensembleMean ensemble).1 classIndex) -
        ∑ memberIndex,
          ensemble.weights.1 memberIndex *
            negMulLog
              ((ensemble.prediction memberIndex).1 classIndex) =
      ∑ memberIndex,
        ensemble.weights.1 memberIndex *
          ((ensemble.prediction memberIndex).1 classIndex *
            log
              ((ensemble.prediction memberIndex).1 classIndex /
                (ensembleMean ensemble).1 classIndex)) := by
  have hmeanNe : (ensembleMean ensemble).1 classIndex ≠ 0 :=
    ne_of_gt hmean
  rw [negMulLog]
  simp_rw [negMulLog]
  have hdata :
      ∑ memberIndex,
          ensemble.weights.1 memberIndex *
            (-((ensemble.prediction memberIndex).1 classIndex) *
              log ((ensemble.prediction memberIndex).1 classIndex)) =
        -(∑ memberIndex,
          ensemble.weights.1 memberIndex *
            ((ensemble.prediction memberIndex).1 classIndex *
              log ((ensemble.prediction memberIndex).1 classIndex))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro memberIndex _
    ring
  have hcoordinate :
      ∑ memberIndex,
          ensemble.weights.1 memberIndex *
            ((ensemble.prediction memberIndex).1 classIndex *
              log
                ((ensemble.prediction memberIndex).1 classIndex /
                  (ensembleMean ensemble).1 classIndex)) =
        ∑ memberIndex,
          (ensemble.weights.1 memberIndex *
              ((ensemble.prediction memberIndex).1 classIndex *
                log ((ensemble.prediction memberIndex).1 classIndex)) -
            ensemble.weights.1 memberIndex *
              (ensemble.prediction memberIndex).1 classIndex *
                log ((ensembleMean ensemble).1 classIndex)) := by
    apply Finset.sum_congr rfl
    intro memberIndex _
    by_cases hprediction :
        (ensemble.prediction memberIndex).1 classIndex = 0
    · simp [hprediction]
    · rw [Real.log_div hprediction hmeanNe]
      ring
  rw [hdata, hcoordinate, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [ensembleMean_coordinate]
  ring

/-- The source entropy difference is exactly average categorical divergence
from the mean prediction. -/
theorem distributionalInformation_eq_averageDivergenceFromMean
    (ensemble : PredictiveEnsemble MemberCount ClassCount)
    (hmean :
      ∀ classIndex, 0 < (ensembleMean ensemble).1 classIndex) :
    distributionalInformation ensemble =
      averageDivergenceFromMean ensemble := by
  have hexpected :
      expectedDataUncertainty ensemble =
        ∑ classIndex,
          ∑ memberIndex,
            ensemble.weights.1 memberIndex *
              negMulLog
                ((ensemble.prediction memberIndex).1 classIndex) := by
    unfold expectedDataUncertainty
    simp_rw [shannonEntropy, Finset.mul_sum]
    rw [Finset.sum_comm]
  have haverage :
      averageDivergenceFromMean ensemble =
        ∑ classIndex,
          ∑ memberIndex,
            ensemble.weights.1 memberIndex *
              ((ensemble.prediction memberIndex).1 classIndex *
                log
                  ((ensemble.prediction memberIndex).1 classIndex /
                    (ensembleMean ensemble).1 classIndex)) := by
    unfold averageDivergenceFromMean categoricalDivergence
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [distributionalInformation, hexpected, shannonEntropy,
    ← Finset.sum_sub_distrib, haverage]
  apply Finset.sum_congr rfl
  intro classIndex _
  exact coordinate_entropyGap_eq_averageDivergence
    ensemble classIndex (hmean classIndex)

/-- Distributional information is nonnegative whenever the mean prediction
has full support. -/
theorem distributionalInformation_nonneg
    (ensemble : PredictiveEnsemble MemberCount ClassCount)
    (hmean :
      ∀ classIndex, 0 < (ensembleMean ensemble).1 classIndex) :
    0 ≤ distributionalInformation ensemble := by
  rw [distributionalInformation_eq_averageDivergenceFromMean ensemble hmean]
  exact Finset.sum_nonneg fun memberIndex _ =>
    mul_nonneg
      (ensemble.weights.nonneg memberIndex)
      (categoricalDivergence_nonneg
        (ensemble.prediction memberIndex)
        (ensembleMean ensemble)
        (fun classIndex _ => hmean classIndex))

theorem expectedDataUncertainty_nonneg
    (ensemble : PredictiveEnsemble MemberCount ClassCount) :
    0 ≤ expectedDataUncertainty ensemble :=
  Finset.sum_nonneg fun memberIndex _ =>
    mul_nonneg
      (ensemble.weights.nonneg memberIndex)
      (shannonEntropy_nonneg (ensemble.prediction memberIndex))

/-- The distributional component cannot exceed total predictive entropy. -/
theorem distributionalInformation_le_totalUncertainty
    (ensemble : PredictiveEnsemble MemberCount ClassCount) :
    distributionalInformation ensemble ≤
      shannonEntropy (ensembleMean ensemble) := by
  unfold distributionalInformation
  linarith [expectedDataUncertainty_nonneg ensemble]

/-! ## Exact duplicate and binary separation boundaries -/

/-- An ensemble whose every member makes the same prediction. -/
def duplicateEnsemble
    (weights : ProbVec MemberCount)
    (prediction : ProbVec ClassCount) :
    PredictiveEnsemble MemberCount ClassCount where
  weights := weights
  prediction := fun _ => prediction

@[simp]
theorem duplicateEnsemble_mean
    (weights : ProbVec MemberCount)
    (prediction : ProbVec ClassCount) :
    ensembleMean (duplicateEnsemble weights prediction) = prediction := by
  ext classIndex
  simp [ensembleMean, duplicateEnsemble, ← Finset.sum_mul,
    ProbVec.sum_eq_one]

theorem duplicateEnsemble_expectedDataUncertainty
    (weights : ProbVec MemberCount)
    (prediction : ProbVec ClassCount) :
    expectedDataUncertainty (duplicateEnsemble weights prediction) =
      shannonEntropy prediction := by
  simp [expectedDataUncertainty, duplicateEnsemble, ← Finset.sum_mul,
    ProbVec.sum_eq_one]

/-- Mere multiplicity of an identical predictor carries no distributional
information. -/
theorem duplicateEnsemble_distributionalInformation_eq_zero
    (weights : ProbVec MemberCount)
    (prediction : ProbVec ClassCount) :
    distributionalInformation (duplicateEnsemble weights prediction) = 0 := by
  rw [distributionalInformation, duplicateEnsemble_mean,
    duplicateEnsemble_expectedDataUncertainty]
  ring

/-- Equal-weight binary ensemble of opposite point predictions. -/
def binarySeparatedEnsemble : PredictiveEnsemble 2 2 where
  weights := binaryUniform
  prediction := fun memberIndex =>
    if memberIndex = 0 then pointMass 0 else pointMass 1

/-- Equal-weight binary ensemble whose members are both maximally ambiguous. -/
def binaryAmbiguousEnsemble : PredictiveEnsemble 2 2 :=
  duplicateEnsemble binaryUniform binaryUniform

@[simp]
theorem binarySeparatedEnsemble_mean :
    ensembleMean binarySeparatedEnsemble = binaryUniform := by
  apply Subtype.ext
  funext classIndex
  fin_cases classIndex <;>
    simp [ensembleMean, binarySeparatedEnsemble, binaryUniform,
      binaryDist, pointMass]

@[simp]
theorem binaryAmbiguousEnsemble_mean :
    ensembleMean binaryAmbiguousEnsemble = binaryUniform := by
  exact duplicateEnsemble_mean binaryUniform binaryUniform

theorem binarySeparated_expectedDataUncertainty :
    expectedDataUncertainty binarySeparatedEnsemble = 0 := by
  norm_num [expectedDataUncertainty, binarySeparatedEnsemble,
    shannonEntropy_pointMass, binaryUniform, binaryDist]

theorem binaryAmbiguous_expectedDataUncertainty :
    expectedDataUncertainty binaryAmbiguousEnsemble = log 2 := by
  rw [binaryAmbiguousEnsemble, duplicateEnsemble_expectedDataUncertainty,
    shannonEntropy_binaryUniform]

theorem binarySeparated_distributionalInformation :
    distributionalInformation binarySeparatedEnsemble = log 2 := by
  rw [distributionalInformation, binarySeparatedEnsemble_mean,
    binarySeparated_expectedDataUncertainty,
    shannonEntropy_binaryUniform]
  ring

theorem binaryAmbiguous_distributionalInformation :
    distributionalInformation binaryAmbiguousEnsemble = 0 := by
  exact duplicateEnsemble_distributionalInformation_eq_zero
    binaryUniform binaryUniform

/-- Equal mean prediction does not identify whether uncertainty comes from
member ambiguity or member disagreement. -/
theorem sameMean_oppositeUncertaintyDecomposition :
    ensembleMean binarySeparatedEnsemble =
        ensembleMean binaryAmbiguousEnsemble ∧
      expectedDataUncertainty binarySeparatedEnsemble = 0 ∧
      distributionalInformation binarySeparatedEnsemble = log 2 ∧
      expectedDataUncertainty binaryAmbiguousEnsemble = log 2 ∧
      distributionalInformation binaryAmbiguousEnsemble = 0 := by
  constructor
  · rw [binarySeparatedEnsemble_mean, binaryAmbiguousEnsemble_mean]
  · exact ⟨
      binarySeparated_expectedDataUncertainty,
      binarySeparated_distributionalInformation,
      binaryAmbiguous_expectedDataUncertainty,
      binaryAmbiguous_distributionalInformation
    ⟩

end

end PriorNetworkUncertainty

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
