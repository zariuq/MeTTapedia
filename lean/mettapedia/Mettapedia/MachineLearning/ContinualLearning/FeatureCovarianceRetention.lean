import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Exact retention from feature-covariance null spaces

Wang et al., *Training Networks in Null Space of Feature Covariance for
Continual Learning* (2021), Lemmas 1--2 and Condition 1, constrain each
layer's parameter update to the null space of the uncentered covariance of
stored features.  This file isolates the exact finite algebra behind that
condition.

For a finite real feature matrix `X`, the kernels of `X` and `XᵀX` agree.
Consequently, a weight update annihilated by the uncentered covariance also
annihilates every stored feature.  The result is lifted through an arbitrary
finite chain of square layers and arbitrary deterministic activation maps:
if each update is covariance-null along the stored forward trajectory, the
entire stored output is unchanged exactly.

The formal boundary is equally important.  Approximate covariance
annihilation alone gives no uniform output-drift bound without a conditioning
or spectral-gap hypothesis, and a full-rank stored feature matrix leaves no
nonzero covariance-null update.  Thus exact stability can consume all
plasticity, while approximate null spaces require a quantitative theorem
rather than being silently treated as exact.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace FeatureCovarianceRetention

noncomputable section

variable {Sample Feature Output : Type*}
  [Fintype Sample] [Fintype Feature]

/-- The unnormalized, uncentered feature covariance `XᵀX`.  Multiplication by
a positive sample-count normalization does not change its null space. -/
def uncenteredCovariance
    (features : Matrix Sample Feature ℝ) :
    Matrix Feature Feature ℝ :=
  features.transpose * features

/-- The load-bearing covariance fact: for every finite real feature matrix,
`XᵀX` and `X` have exactly the same vector kernel. -/
theorem uncenteredCovariance_mulVec_eq_zero_iff
    (features : Matrix Sample Feature ℝ)
    (direction : Feature → ℝ) :
    (uncenteredCovariance features).mulVec direction = 0 ↔
      features.mulVec direction = 0 := by
  change direction ∈
      LinearMap.ker ((features.transpose * features).mulVecLin) ↔
    direction ∈ LinearMap.ker features.mulVecLin
  rw [Matrix.ker_mulVecLin_transpose_mul_self]

/-- Columnwise generalization used by a whole weight update: covariance
annihilation is equivalent to annihilating all stored features. -/
theorem uncenteredCovariance_mul_eq_zero_iff
    (features : Matrix Sample Feature ℝ)
    (update : Matrix Feature Output ℝ) :
    uncenteredCovariance features * update = 0 ↔
      features * update = 0 := by
  constructor
  · intro covarianceNull
    ext sample output
    let direction : Feature → ℝ := fun feature => update feature output
    have covarianceColumn :
        (uncenteredCovariance features).mulVec direction = 0 := by
      funext feature
      simpa [direction, Matrix.mulVec, Matrix.mul_apply,
        dotProduct] using
        congr_fun (congr_fun covarianceNull feature) output
    have featureColumn :
        features.mulVec direction = 0 :=
      (uncenteredCovariance_mulVec_eq_zero_iff
        features direction).mp covarianceColumn
    simpa [direction, Matrix.mulVec, Matrix.mul_apply,
      dotProduct] using
      congr_fun featureColumn sample
  · intro featureNull
    rw [uncenteredCovariance, Matrix.mul_assoc, featureNull]
    simp

/-- An exact covariance-null update leaves the stored affine-free linear
layer output unchanged. -/
theorem linearLayer_add_covarianceNull
    (features : Matrix Sample Feature ℝ)
    (weight update : Matrix Feature Output ℝ)
    (covarianceNull : uncenteredCovariance features * update = 0) :
    features * (weight + update) = features * weight := by
  rw [Matrix.mul_add,
    (uncenteredCovariance_mul_eq_zero_iff features update).mp
      covarianceNull,
    add_zero]

/-- Sum a finite execution trace of updates to one layer. -/
def totalWeightUpdate : List (Matrix Feature Output ℝ) → Matrix Feature Output ℝ
  | [] => 0
  | update :: updates => update + totalWeightUpdate updates

/-- Exact covariance-nullity is closed under an arbitrary finite update
trace.  This is the step-level-to-task-level bridge used by the source. -/
theorem uncenteredCovariance_mul_totalWeightUpdate_eq_zero
    (features : Matrix Sample Feature ℝ) :
    ∀ updates : List (Matrix Feature Output ℝ),
      (∀ update ∈ updates,
        uncenteredCovariance features * update = 0) →
      uncenteredCovariance features * totalWeightUpdate updates = 0 := by
  intro updates covarianceNull
  induction updates with
  | nil =>
      simp [totalWeightUpdate]
  | cons update updates inductionHypothesis =>
      have headNull :
          uncenteredCovariance features * update = 0 :=
        covarianceNull update (by simp)
      have tailNull :
          ∀ later ∈ updates,
            uncenteredCovariance features * later = 0 := by
        intro later laterMem
        exact covarianceNull later (by simp [laterMem])
      rw [totalWeightUpdate, Matrix.mul_add, headNull,
        inductionHypothesis tailNull]
      simp

/-- One square layer together with the finite parameter change made while
learning later tasks. -/
structure SquareLayerChange (Feature : Type*) where
  base : Matrix Feature Feature ℝ
  update : Matrix Feature Feature ℝ

/-- Execute a finite sequence of square layers with an arbitrary deterministic
activation after every linear map. -/
def runSquareLayers
    (activation :
      Matrix Sample Feature ℝ → Matrix Sample Feature ℝ) :
    Matrix Sample Feature ℝ →
      List (Matrix Feature Feature ℝ) →
      Matrix Sample Feature ℝ
  | features, [] => features
  | features, weight :: weights =>
      runSquareLayers activation
        (activation (features * weight)) weights

/-- Execute the stored, pre-update version of a finite layer chain. -/
def runBaseChanges
    (activation :
      Matrix Sample Feature ℝ → Matrix Sample Feature ℝ) :
    Matrix Sample Feature ℝ →
      List (SquareLayerChange Feature) →
      Matrix Sample Feature ℝ
  | features, [] => features
  | features, change :: changes =>
      runBaseChanges activation
        (activation (features * change.base)) changes

/-- Execute the same finite chain after applying every declared update. -/
def runUpdatedChanges
    (activation :
      Matrix Sample Feature ℝ → Matrix Sample Feature ℝ) :
    Matrix Sample Feature ℝ →
      List (SquareLayerChange Feature) →
      Matrix Sample Feature ℝ
  | features, [] => features
  | features, change :: changes =>
      runUpdatedChanges activation
        (activation (features * (change.base + change.update))) changes

/-- Layerwise Condition 1 evaluated along the stored forward trajectory. -/
def CovarianceNullAlongBase
    (activation :
      Matrix Sample Feature ℝ → Matrix Sample Feature ℝ) :
    Matrix Sample Feature ℝ →
      List (SquareLayerChange Feature) → Prop
  | _, [] => True
  | features, change :: changes =>
      uncenteredCovariance features * change.update = 0 ∧
        CovarianceNullAlongBase activation
          (activation (features * change.base)) changes

/-- Source recovery and finite-depth generalization: arbitrary deterministic
nonlinearities do not disturb exact retention when every layer update is
covariance-null on the stored forward trajectory. -/
theorem runUpdatedChanges_eq_runBaseChanges
    (activation :
      Matrix Sample Feature ℝ → Matrix Sample Feature ℝ) :
    ∀ (features : Matrix Sample Feature ℝ)
      (changes : List (SquareLayerChange Feature)),
      CovarianceNullAlongBase activation features changes →
      runUpdatedChanges activation features changes =
        runBaseChanges activation features changes := by
  intro features changes covarianceNull
  induction changes generalizing features with
  | nil =>
      rfl
  | cons change changes inductionHypothesis =>
      have layerSame :
          features * (change.base + change.update) =
            features * change.base :=
        linearLayer_add_covarianceNull
          features change.base change.update covarianceNull.1
      rw [runUpdatedChanges, runBaseChanges, layerSame]
      exact inductionHypothesis
        (activation (features * change.base)) covarianceNull.2

/-! ## Positive and negative executable boundaries -/

/-- A nontrivial update supported on the unseen second feature is exactly
covariance-null for data occupying only the first feature. -/
theorem unseenSecondFeature_nontrivial_safeUpdate :
    let features : Matrix (Fin 1) (Fin 2) ℝ :=
      fun _ feature => if feature = 0 then 1 else 0
    let update : Matrix (Fin 2) (Fin 2) ℝ :=
      fun input output =>
        if input = 1 ∧ output = 1 then 3 else 0
    uncenteredCovariance features * update = 0 ∧
      features * update = 0 ∧ update ≠ 0 := by
  dsimp
  constructor
  · ext input output
    fin_cases input <;> fin_cases output <;>
      norm_num [uncenteredCovariance, Matrix.mul_apply,
        Fin.sum_univ_succ]
  · constructor
    · ext sample output
      fin_cases sample
      fin_cases output <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · intro updateZero
      have entryZero := congr_fun (congr_fun updateZero 1) 1
      norm_num at entryZero

/-- Full stored feature rank leaves no covariance-null plasticity. -/
theorem identityFeatures_covarianceNull_iff_zero
    [DecidableEq Feature]
    (update : Matrix Feature Output ℝ) :
    uncenteredCovariance (1 : Matrix Feature Feature ℝ) * update = 0 ↔
      update = 0 := by
  simp [uncenteredCovariance]

/-- Approximate covariance annihilation alone does not control feature-space
drift.  In one dimension, scaling the feature by `epsilon` and the update by
its reciprocal makes the covariance residual equal `epsilon` while the
actual output drift remains exactly one. -/
theorem scalar_covarianceResidual_small_but_outputDrift_one
    (epsilon : ℝ) (nonzero : epsilon ≠ 0) :
    let features : Matrix Unit Unit ℝ := fun _ _ => epsilon
    let update : Matrix Unit Unit ℝ := fun _ _ => epsilon⁻¹
    features * update = 1 ∧
      uncenteredCovariance features * update =
        fun _ _ => epsilon := by
  dsimp
  constructor
  · ext sample output
    cases sample
    cases output
    simp [Matrix.mul_apply, nonzero]
  · ext input output
    cases input
    cases output
    simp [uncenteredCovariance, Matrix.mul_apply, nonzero]

/-- Concrete form of the conditioning boundary: a covariance residual of
`1/100` coexists with unit output drift. -/
theorem hundredfold_scalar_conditioning :
    let features : Matrix Unit Unit ℝ := fun _ _ => 1 / 100
    let update : Matrix Unit Unit ℝ := fun _ _ => 100
    features * update = 1 ∧
      uncenteredCovariance features * update =
        fun _ _ => 1 / 100 := by
  simpa using
    scalar_covarianceResidual_small_but_outputDrift_one
      (1 / 100 : ℝ) (by norm_num)

#print axioms uncenteredCovariance_mul_eq_zero_iff
#print axioms runUpdatedChanges_eq_runBaseChanges
#print axioms unseenSecondFeature_nontrivial_safeUpdate
#print axioms scalar_covarianceResidual_small_but_outputDrift_one

end

end FeatureCovarianceRetention

end Mettapedia.MachineLearning.ContinualLearning
