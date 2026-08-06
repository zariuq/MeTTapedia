import Mathlib.Tactic
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LearnedPrecisionDynamics

/-!
# Information and residual-uncertainty boundaries

A deterministic cap applied only to a frozen representation cannot distinguish
worlds that the frozen representation identifies.  Additional temporal,
sensor, or evidential input can refine that partition, but post-processing
alone cannot.  This is an access-to-information statement: it does not claim
that every learner makes equally effective use of the information it receives.

Squared prediction residual has a second, independent ambiguity.  Its finite
bias--variance decomposition contains both observation variability and
systematic prediction bias.  Two explicit samples have the same residual
second moment, and therefore the same optimal scalar Gaussian precision, while
one is entirely variable and the other entirely biased.  Residual magnitude or
an inverse-residual penalty therefore does not identify aleatoric, epistemic,
or distributional uncertainty without an additional statistical model and a
calibration argument.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

namespace ResidualUncertaintyIdentifiability

open scoped BigOperators

noncomputable section

/-! ## Deterministic information access -/

/-- A representation identifies a target when target values are constant on
every representation fibre. -/
def Identifies {World Representation Target : Type*}
    (representation : World → Representation)
    (target : World → Target) : Prop :=
  ∀ ⦃left right⦄,
    representation left = representation right → target left = target right

/-- Deterministic post-processing cannot split a fibre of its input
representation. -/
theorem postprocess_preserves_indistinguishability
    {World Trunk Cap : Type*}
    (trunk : World → Trunk) (cap : Trunk → Cap)
    {left right : World}
    (sameTrunk : trunk left = trunk right) :
    cap (trunk left) = cap (trunk right) := by
  rw [sameTrunk]

/-- If a deterministic cap identifies a target, the representation supplied
to that cap already identifies the target. -/
theorem identifies_of_identifies_postprocess
    {World Trunk Cap Target : Type*}
    (trunk : World → Trunk) (cap : Trunk → Cap) (target : World → Target)
    (capIdentifies : Identifies (fun world => cap (trunk world)) target) :
    Identifies trunk target := by
  intro left right sameTrunk
  exact capIdentifies (postprocess_preserves_indistinguishability
    trunk cap sameTrunk)

/-- A constant frozen representation cannot identify a nonconstant Boolean
world state. -/
theorem constantRepresentation_does_not_identify_boolean :
    ¬ Identifies (fun _ : Bool => Unit.unit) (fun world : Bool => world) := by
  intro identifies
  have impossible := identifies (left := false) (right := true) rfl
  simp at impossible

/-- An additional evidence channel can distinguish the worlds collapsed by
the constant frozen representation. -/
theorem sideEvidence_can_identify_boolean :
    Identifies
      (fun world : Bool => (Unit.unit, world))
      (fun world : Bool => world) := by
  intro left right sameObservation
  exact congrArg Prod.snd sameObservation

/-- The Boolean fixture exhibits the exact boundary: deterministic
post-processing of the frozen representation cannot identify the world, while
the product of that representation with side evidence can. -/
theorem additionalEvidence_strictly_refines_information :
    (¬ Identifies (fun _ : Bool => Unit.unit) (fun world : Bool => world)) ∧
      Identifies
        (fun world : Bool => (Unit.unit, world))
        (fun world : Bool => world) := by
  exact ⟨constantRepresentation_does_not_identify_boolean,
    sideEvidence_can_identify_boolean⟩

/-! ## Finite residual decomposition -/

/-- Squared scalar prediction residual. -/
def squaredResidual (observation prediction : ℝ) : ℝ :=
  (observation - prediction) ^ 2

/-- Arithmetic mean of a nonempty finite observation family. -/
def empiricalMean {n : ℕ} (observation : Fin n → ℝ) : ℝ :=
  (∑ index, observation index) / n

/-- Mean squared prediction residual. -/
def residualSecondMoment {n : ℕ}
    (observation : Fin n → ℝ) (prediction : ℝ) : ℝ :=
  (∑ index, squaredResidual (observation index) prediction) / n

/-- Empirical observation variance around the sample mean. -/
def empiricalVariance {n : ℕ} (observation : Fin n → ℝ) : ℝ :=
  (∑ index, (observation index - empiricalMean observation) ^ 2) / n

/-- Squared systematic offset between a constant predictor and the sample
mean. -/
def squaredBias {n : ℕ}
    (observation : Fin n → ℝ) (prediction : ℝ) : ℝ :=
  (empiricalMean observation - prediction) ^ 2

theorem sum_sub_empiricalMean_eq_zero
    {n : ℕ} (observation : Fin n → ℝ) (hn : n ≠ 0) :
    ∑ index, (observation index - empiricalMean observation) = 0 := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  unfold empiricalMean
  field_simp [hn]
  ring

/-- Finite bias--variance decomposition for a constant scalar prediction. -/
theorem residualSecondMoment_eq_variance_add_squaredBias
    {n : ℕ} (observation : Fin n → ℝ) (prediction : ℝ) (hn : n ≠ 0) :
    residualSecondMoment observation prediction =
      empiricalVariance observation + squaredBias observation prediction := by
  have centered := sum_sub_empiricalMean_eq_zero observation hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have middleSum :
      (∑ index,
          2 * (observation index - empiricalMean observation) *
            (empiricalMean observation - prediction)) =
        2 * (empiricalMean observation - prediction) *
          ∑ index, (observation index - empiricalMean observation) := by
    calc
      (∑ index,
          2 * (observation index - empiricalMean observation) *
            (empiricalMean observation - prediction)) =
          ∑ index,
            (2 * (empiricalMean observation - prediction)) *
              (observation index - empiricalMean observation) := by
            apply Finset.sum_congr rfl
            intro index _
            ring
      _ = 2 * (empiricalMean observation - prediction) *
          ∑ index, (observation index - empiricalMean observation) := by
            rw [Finset.mul_sum]
  have constantSum :
      (∑ _index : Fin n,
          (empiricalMean observation - prediction) ^ 2) =
        (n : ℝ) * (empiricalMean observation - prediction) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have sumDecomposition :
      (∑ index, squaredResidual (observation index) prediction) =
        (∑ index, (observation index - empiricalMean observation) ^ 2) +
          (n : ℝ) * (empiricalMean observation - prediction) ^ 2 := by
    calc
      (∑ index, squaredResidual (observation index) prediction) =
          ∑ index,
            ((observation index - empiricalMean observation) ^ 2 +
              2 * (observation index - empiricalMean observation) *
                (empiricalMean observation - prediction) +
              (empiricalMean observation - prediction) ^ 2) := by
            apply Finset.sum_congr rfl
            intro index _
            simp only [squaredResidual]
            ring
      _ = (∑ index,
              (observation index - empiricalMean observation) ^ 2) +
            (∑ index,
              2 * (observation index - empiricalMean observation) *
                (empiricalMean observation - prediction)) +
            (∑ _index : Fin n,
              (empiricalMean observation - prediction) ^ 2) := by
            simp only [Finset.sum_add_distrib]
      _ = (∑ index,
              (observation index - empiricalMean observation) ^ 2) +
            (n : ℝ) * (empiricalMean observation - prediction) ^ 2 := by
            rw [middleSum, centered, mul_zero, add_zero, constantSum]
  unfold residualSecondMoment empiricalVariance squaredBias
  rw [sumDecomposition]
  field_simp [hnReal]

/-! ## Exact ambiguity fixtures -/

/-- A two-point sample with unit empirical variance and zero bias for the zero
predictor. -/
def variableSample : Fin 2 → ℝ
  | 0 => -1
  | 1 => 1

/-- A constant sample with zero empirical variance and unit bias for the zero
predictor. -/
def biasedSample : Fin 2 → ℝ := fun _ => 1

theorem variableSample_decomposition :
    empiricalMean variableSample = 0 ∧
      empiricalVariance variableSample = 1 ∧
      squaredBias variableSample 0 = 0 ∧
      residualSecondMoment variableSample 0 = 1 := by
  norm_num [empiricalMean, empiricalVariance, squaredBias,
    residualSecondMoment, squaredResidual, variableSample, Fin.sum_univ_two]

theorem biasedSample_decomposition :
    empiricalMean biasedSample = 1 ∧
      empiricalVariance biasedSample = 0 ∧
      squaredBias biasedSample 0 = 1 ∧
      residualSecondMoment biasedSample 0 = 1 := by
  norm_num [empiricalMean, empiricalVariance, squaredBias,
    residualSecondMoment, squaredResidual, biasedSample, Fin.sum_univ_two]

/-- Residual second moment alone cannot identify whether the observed error is
sample variability or systematic prediction bias. -/
theorem sameResidual_oppositeBiasVarianceDecomposition :
    residualSecondMoment variableSample 0 =
        residualSecondMoment biasedSample 0 ∧
      empiricalVariance variableSample ≠ empiricalVariance biasedSample ∧
      squaredBias variableSample 0 ≠ squaredBias biasedSample 0 := by
  norm_num [variableSample_decomposition, biasedSample_decomposition,
    empiricalMean, empiricalVariance, squaredBias, residualSecondMoment,
    squaredResidual, variableSample, biasedSample, Fin.sum_univ_two]

/-- Since scalar Gaussian precision learns inverse residual second moment, the
two causally different fixtures receive exactly the same optimal precision. -/
theorem optimalPrecision_cannot_separate_variability_from_bias :
    1 / residualSecondMoment variableSample 0 =
        1 / residualSecondMoment biasedSample 0 ∧
      1 / residualSecondMoment variableSample 0 = 1 := by
  norm_num [residualSecondMoment, squaredResidual, variableSample,
    biasedSample, Fin.sum_univ_two]

/-! ## Pointwise OOD non-identifiability -/

/-- Minimal record separating an observed residual from an externally defined
distribution-membership label. -/
structure LabeledObservation where
  observation : ℝ
  prediction : ℝ
  isOOD : Bool

def observedSquaredResidual (sample : LabeledObservation) : ℝ :=
  squaredResidual sample.observation sample.prediction

/-- An in-distribution noisy observation and a perfectly predicted OOD
observation refute both directions of the proposed residual/OOD equivalence. -/
theorem residual_threshold_does_not_characterize_OOD :
    let inDistribution : LabeledObservation := ⟨2, 0, false⟩
    let outOfDistribution : LabeledObservation := ⟨1, 1, true⟩
    observedSquaredResidual inDistribution = 4 ∧
      observedSquaredResidual outOfDistribution = 0 ∧
      inDistribution.isOOD = false ∧
      outOfDistribution.isOOD = true := by
  norm_num [observedSquaredResidual, squaredResidual]

#print axioms postprocess_preserves_indistinguishability
#print axioms identifies_of_identifies_postprocess
#print axioms additionalEvidence_strictly_refines_information
#print axioms residualSecondMoment_eq_variance_add_squaredBias
#print axioms sameResidual_oppositeBiasVarianceDecomposition
#print axioms optimalPrecision_cannot_separate_variability_from_bias
#print axioms residual_threshold_does_not_characterize_OOD

end

end ResidualUncertaintyIdentifiability

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
