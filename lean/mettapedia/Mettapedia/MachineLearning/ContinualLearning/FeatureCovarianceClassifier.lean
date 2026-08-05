import Mettapedia.MachineLearning.ContinualLearning.ApproximateCovarianceRetention
import Mettapedia.MachineLearning.ContinualLearning.StreamingLDACovariance

/-!
# Feature-covariance classifiers

Goswami, Liu, Twardowski, and van de Weijer,
*FeCAM: Exploiting the Heterogeneity of Class Distributions in
Exemplar-Free Continual Learning* (NeurIPS 2023, arXiv:2309.14062),
Equations (1)--(10), classify frozen features by class prototypes and
covariance-aware distances.

This file isolates the exact classifier geometry:

* a positive-semidefinite precision gives a nonnegative Mahalanobis
  quadratic;
* identity precision recovers squared Euclidean distance;
* with a common positive precision and common prior, Gaussian-density
  ordering is exactly the reverse of Mahalanobis-distance ordering;
* with class-dependent precision, the Gaussian normalization factor is
  load-bearing.  A concrete scalar example makes the Mahalanobis-only rule
  choose the opposite class from the normalized Gaussian score;
* setting every covariance diagonal to one does not equalize determinants:
  two positive-definite correlation matrices have the same diagonal and
  different Gaussian normalizers.

Thus a shared-covariance FeCAM score has the advertised Bayes reduction under
equal priors.  A per-class Mahalanobis-only score is not, in general, the
complete Gaussian Bayes classifier unless the omitted normalization factors
are equal.  The development does not claim feature Gaussianity, covariance
estimation consistency, task accuracy, or any empirical result from the
source.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace FeatureCovarianceClassifier

noncomputable section

open Matrix
open scoped Matrix
open ApproximateCovarianceRetention

variable {Feature : Type*} [Fintype Feature]

/-- Squared Mahalanobis distance represented by a precision matrix. -/
def mahalanobisSquared
    (precision : Matrix Feature Feature ℝ)
    (feature mean : Feature → ℝ) : ℝ :=
  (feature - mean) ⬝ᵥ precision.mulVec (feature - mean)

/-- Positive-semidefinite precision makes every represented squared distance
nonnegative. -/
theorem mahalanobisSquared_nonnegative
    (precision : Matrix Feature Feature ℝ)
    (feature mean : Feature → ℝ)
    (precision_posSemidef : Matrix.PosSemidef precision) :
    0 ≤ mahalanobisSquared precision feature mean := by
  simpa [mahalanobisSquared] using
    precision_posSemidef.dotProduct_mulVec_nonneg (feature - mean)

/-- Equation (2) is the identity-precision specialization of Equation (1). -/
theorem mahalanobisSquared_identity
    [DecidableEq Feature]
    (feature mean : Feature → ℝ) :
    mahalanobisSquared (1 : Matrix Feature Feature ℝ) feature mean =
      squaredL2 (feature - mean) := by
  simp [mahalanobisSquared, squaredL2]

/-- Scalar squared Mahalanobis distance.  Here `precision` is inverse
variance. -/
def scalarMahalanobisSquared
    (precision x mean : ℝ) : ℝ :=
  precision * (x - mean) ^ 2

/-- A scalar Gaussian density with the class-independent factor
`1 / sqrt (2 * pi)` removed.  Unlike the Mahalanobis-only kernel, this keeps
both the prior and the precision-dependent normalization. -/
def scalarGaussianRelativeDensity
    (prior precision x mean : ℝ) : ℝ :=
  prior * Real.sqrt precision *
    Real.exp (-(scalarMahalanobisSquared precision x mean) / 2)

theorem scalarMahalanobisSquared_nonnegative
    (precision x mean : ℝ) (precision_nonnegative : 0 ≤ precision) :
    0 ≤ scalarMahalanobisSquared precision x mean := by
  exact mul_nonneg precision_nonnegative (sq_nonneg _)

/-- With equal priors and one shared positive precision, maximizing the
Gaussian score is exactly minimizing squared Mahalanobis distance. -/
theorem same_precision_density_gt_iff_mahalanobis_lt
    (precision x firstMean secondMean : ℝ)
    (precision_pos : 0 < precision) :
    scalarGaussianRelativeDensity 1 precision x secondMean <
        scalarGaussianRelativeDensity 1 precision x firstMean ↔
      scalarMahalanobisSquared precision x firstMean <
        scalarMahalanobisSquared precision x secondMean := by
  have sqrt_pos : 0 < Real.sqrt precision :=
    Real.sqrt_pos.2 precision_pos
  unfold scalarGaussianRelativeDensity
  simp only [one_mul]
  constructor
  · intro density_lt
    have exponent_lt :=
      Real.exp_lt_exp.mp
        (lt_of_mul_lt_mul_left density_lt sqrt_pos.le)
    linarith
  · intro distance_lt
    apply mul_lt_mul_of_pos_left _ sqrt_pos
    apply Real.exp_lt_exp.mpr
    linarith

/-- Equal class-dependent Mahalanobis costs need not give equal Gaussian
density.  The missing normalization already matters at the common mean. -/
theorem heterogeneous_precision_equal_distance_unequal_density :
    scalarMahalanobisSquared 1 0 0 =
        scalarMahalanobisSquared 4 0 0 ∧
      scalarGaussianRelativeDensity 1 1 0 0 <
        scalarGaussianRelativeDensity 1 4 0 0 := by
  norm_num [scalarMahalanobisSquared, scalarGaussianRelativeDensity]

/-- Stronger negative fixture: a Mahalanobis-only decision can reverse the
normalized Gaussian decision.  At `x = 0`, the first class has mean zero and
unit precision; the second has mean `1/3` and precision nine. -/
theorem heterogeneous_precisions_reverse_distance_decision :
    scalarMahalanobisSquared 1 0 0 <
        scalarMahalanobisSquared 9 0 (1 / 3) ∧
      scalarGaussianRelativeDensity 1 1 0 0 <
        scalarGaussianRelativeDensity 1 9 0 (1 / 3) := by
  constructor
  · norm_num [scalarMahalanobisSquared]
  · have exp_lower :
        (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      have bound := Real.add_one_le_exp (-(1 / 2 : ℝ))
      norm_num at bound ⊢
      exact bound
    norm_num [scalarGaussianRelativeDensity, scalarMahalanobisSquared]
    nlinarith

/-! ## Correlation normalization does not normalize determinants -/

def twoOnes : Fin 2 → ℝ := fun _ => 1

def identityCorrelation : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 1]

def correlatedCorrelation : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / 2; 1 / 2, 1]

theorem identityCorrelation_eq_one :
    identityCorrelation = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [identityCorrelation, Matrix.one_apply]

theorem correlatedCorrelation_decomposition :
    correlatedCorrelation =
      (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (1 / 2 : ℝ) • Matrix.vecMulVec twoOnes twoOnes := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [correlatedCorrelation, twoOnes, Matrix.one_apply,
      Matrix.vecMulVec]

theorem identityCorrelation_posDef :
    Matrix.PosDef identityCorrelation := by
  rw [identityCorrelation_eq_one]
  exact Matrix.PosDef.one

theorem correlatedCorrelation_posDef :
    Matrix.PosDef correlatedCorrelation := by
  rw [correlatedCorrelation_decomposition]
  have rankOne_posSemidef :
      Matrix.PosSemidef (Matrix.vecMulVec twoOnes twoOnes) := by
    simpa using Matrix.posSemidef_vecMulVec_self_star twoOnes
  have identityRidge_posDef :
      Matrix.PosDef
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Matrix.PosDef.one.smul (by norm_num)
  have rankOneHalf_posSemidef :
      Matrix.PosSemidef
        ((1 / 2 : ℝ) • Matrix.vecMulVec twoOnes twoOnes) :=
    rankOne_posSemidef.smul (by norm_num)
  simpa [add_comm] using
    Matrix.PosDef.posSemidef_add
      rankOneHalf_posSemidef identityRidge_posDef

/-- Both matrices satisfy the source's unit-diagonal correlation
normalization, but their determinants differ.  Therefore that normalization
does not make the class-dependent Gaussian normalizers equal. -/
theorem same_unit_diagonal_different_determinant :
    (∀ i, identityCorrelation i i = correlatedCorrelation i i) ∧
      Matrix.det identityCorrelation ≠
        Matrix.det correlatedCorrelation := by
  constructor
  · intro i
    fin_cases i <;>
      norm_num [identityCorrelation, correlatedCorrelation]
  · norm_num [identityCorrelation, correlatedCorrelation,
      Matrix.det_fin_two]

/-- Positive and negative boundary combined: both unit-diagonal matrices are
valid positive-definite covariance shapes, yet determinant equality still
fails. -/
theorem correlation_normalization_does_not_equalize_gaussian_normalizer :
    Matrix.PosDef identityCorrelation ∧
      Matrix.PosDef correlatedCorrelation ∧
      (∀ i, identityCorrelation i i =
        correlatedCorrelation i i) ∧
      Matrix.det identityCorrelation ≠
        Matrix.det correlatedCorrelation := by
  exact ⟨identityCorrelation_posDef, correlatedCorrelation_posDef,
    same_unit_diagonal_different_determinant⟩

#print axioms mahalanobisSquared_nonnegative
#print axioms mahalanobisSquared_identity
#print axioms same_precision_density_gt_iff_mahalanobis_lt
#print axioms heterogeneous_precision_equal_distance_unequal_density
#print axioms heterogeneous_precisions_reverse_distance_decision
#print axioms identityCorrelation_eq_one
#print axioms identityCorrelation_posDef
#print axioms correlatedCorrelation_posDef
#print axioms same_unit_diagonal_different_determinant
#print axioms correlation_normalization_does_not_equalize_gaussian_normalizer

end

end FeatureCovarianceClassifier

end Mettapedia.MachineLearning.ContinualLearning
