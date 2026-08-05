import Mathlib

/-!
# Analytic incremental ridge regression

Zhuang et al.,
*ACIL: Analytic Class-Incremental Learning with Absolute Memorization and
Privacy Protection* (2022, arXiv:2205.14922), Theorem 1, update a frozen
feature head by a Woodbury inverse recursion and a residual correction.

This file proves the finite-dimensional matrix identity behind that result.
If `R` is a two-sided inverse of the accumulated ridge normal matrix and `S`
is a two-sided inverse of the new batch Schur matrix, the displayed Woodbury
update is a two-sided inverse of the enlarged normal matrix.  The recursive
head update is then exactly the head obtained by joint ridge regression on
the accumulated sufficient statistics.

The fixed-feature premise is load bearing.  Sufficient-statistic accumulation
is order independent in one feature coordinate system, while an executable
fixture shows that changing a position-indexed feature map destroys raw-order
invariance.  Further fixtures show that changing the ridge between phases
breaks joint equivalence and that singular normal matrices do not satisfy the
inverse contract.

No theorem here identifies a frozen analytic head with end-to-end training,
proves statistical generalization or accuracy, or upgrades exemplar-free
storage to a privacy theorem.  A scalar recovery lemma instead records that
an inverse normal statistic can reveal an exact feature-square statistic.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace AnalyticIncrementalRidge

noncomputable section

open Matrix
open scoped Matrix

universe uFeature uBatch uOutput

variable {Feature : Type uFeature}
variable {Batch : Type uBatch}
variable {Output : Type uOutput}

/-- An explicit inverse contract, avoiding any appeal to a totalized matrix
inverse at singular inputs. -/
def TwoSidedInverse
    [Fintype Feature] [DecidableEq Feature]
    (candidate target : Matrix Feature Feature ℝ) : Prop :=
  candidate * target = 1 ∧ target * candidate = 1

/-- The normal-matrix contribution of one frozen-feature batch. -/
def normalIncrement
    [Fintype Batch]
    (features : Matrix Batch Feature ℝ) :
    Matrix Feature Feature ℝ :=
  features.transpose * features

/-- The feature-target cross-statistic contributed by one batch. -/
def crossIncrement
    [Fintype Batch]
    (features : Matrix Batch Feature ℝ)
    (targets : Matrix Batch Output ℝ) :
    Matrix Feature Output ℝ :=
  features.transpose * targets

/-- Enlarged normal matrix after accepting one batch. -/
def updatedNormal
    [Fintype Batch]
    (normal : Matrix Feature Feature ℝ)
    (features : Matrix Batch Feature ℝ) :
    Matrix Feature Feature ℝ :=
  normal + normalIncrement features

/-- Enlarged feature-target statistic after accepting one batch. -/
def updatedCross
    [Fintype Batch]
    (cross : Matrix Feature Output ℝ)
    (features : Matrix Batch Feature ℝ)
    (targets : Matrix Batch Output ℝ) :
    Matrix Feature Output ℝ :=
  cross + crossIncrement features targets

/-- Batch-space Schur matrix in Equation (10). -/
def batchSchur
    [Fintype Feature] [DecidableEq Batch]
    (features : Matrix Batch Feature ℝ)
    (oldInverse : Matrix Feature Feature ℝ) :
    Matrix Batch Batch ℝ :=
  1 + features * oldInverse * features.transpose

/-- The batch gain factored out of the Woodbury decrement. -/
def batchGain
    [Fintype Feature]
    [Fintype Batch]
    (features : Matrix Batch Feature ℝ)
    (oldInverse : Matrix Feature Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ) :
    Matrix Feature Feature ℝ :=
  oldInverse * features.transpose * schurInverse * features

/-- Equation (10), written as `R - gain * R`. -/
def updatedInverse
    [Fintype Feature]
    [Fintype Batch]
    (features : Matrix Batch Feature ℝ)
    (oldInverse : Matrix Feature Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ) :
    Matrix Feature Feature ℝ :=
  oldInverse - batchGain features oldInverse schurInverse * oldInverse

/-- Ridge head reconstructed from an inverse normal matrix and cross
statistic. -/
def headFromStatistics
    [Fintype Feature]
    (inverseNormal : Matrix Feature Feature ℝ)
    (cross : Matrix Feature Output ℝ) :
    Matrix Feature Output ℝ :=
  inverseNormal * cross

/-- Equation (9), in residual-correction form. -/
def recursiveHeadUpdate
    [Fintype Feature]
    [Fintype Batch]
    (oldHead : Matrix Feature Output ℝ)
    (features : Matrix Batch Feature ℝ)
    (targets : Matrix Batch Output ℝ)
    (newInverse : Matrix Feature Feature ℝ) :
    Matrix Feature Output ℝ :=
  oldHead +
    newInverse * features.transpose * (targets - features * oldHead)

variable [Fintype Feature] [DecidableEq Feature]
variable [Fintype Batch] [DecidableEq Batch]

omit [DecidableEq Feature] in
/-- A left Schur inverse, applied to the incoming features. -/
theorem schurInverse_mul_features
    (features : Matrix Batch Feature ℝ)
    (oldInverse : Matrix Feature Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (inverse_left :
      schurInverse * batchSchur features oldInverse = 1) :
    schurInverse * features +
        schurInverse * features * oldInverse *
          features.transpose * features =
      features := by
  have applied := congrArg
    (fun matrix : Matrix Batch Batch ℝ => matrix * features)
    inverse_left
  simpa only [batchSchur, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc] using applied

/-- The Woodbury update is a right inverse of the enlarged normal matrix. -/
theorem updatedInverse_mul_updatedNormal
    (normal oldInverse : Matrix Feature Feature ℝ)
    (features : Matrix Batch Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (old_right : oldInverse * normal = 1)
    (schur_left :
      schurInverse * batchSchur features oldInverse = 1) :
    updatedInverse features oldInverse schurInverse *
        updatedNormal normal features =
      1 := by
  have schur_on_features :=
    schurInverse_mul_features features oldInverse schurInverse schur_left
  have left_applied := congrArg
    (fun matrix : Matrix Batch Feature ℝ =>
      (oldInverse * features.transpose) * matrix)
    schur_on_features
  have cancellation :
      batchGain features oldInverse schurInverse +
          batchGain features oldInverse schurInverse * oldInverse *
            (features.transpose * features) =
        oldInverse * (features.transpose * features) := by
    simpa only [batchGain, Matrix.mul_add, Matrix.mul_assoc] using
      left_applied
  unfold updatedInverse updatedNormal normalIncrement
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
  rw [Matrix.mul_assoc
    (batchGain features oldInverse schurInverse) oldInverse normal,
    old_right, Matrix.mul_one]
  rw [cancellation]
  abel

omit [DecidableEq Feature] in
/-- A right Schur inverse, sandwiched between the incoming feature maps. -/
theorem features_sandwich_schurInverse
    (features : Matrix Batch Feature ℝ)
    (oldInverse : Matrix Feature Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (inverse_right :
      batchSchur features oldInverse * schurInverse = 1) :
    features.transpose * schurInverse * features * oldInverse +
        features.transpose * features * oldInverse *
          features.transpose * schurInverse * features * oldInverse =
      features.transpose * features * oldInverse := by
  have applied := congrArg
    (fun matrix : Matrix Batch Batch ℝ =>
      features.transpose * matrix * (features * oldInverse))
    inverse_right
  simpa only [batchSchur, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc] using applied

omit [DecidableEq Batch] in
/-- The old normal matrix cancels the leading old inverse in the batch gain. -/
theorem normal_mul_batchGain
    (normal oldInverse : Matrix Feature Feature ℝ)
    (features : Matrix Batch Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (old_left : normal * oldInverse = 1) :
    normal * batchGain features oldInverse schurInverse =
      features.transpose * schurInverse * features := by
  unfold batchGain
  simp only [← Matrix.mul_assoc, old_left, Matrix.one_mul]

/-- The Woodbury update is a left inverse of the enlarged normal matrix. -/
theorem updatedNormal_mul_updatedInverse
    (normal oldInverse : Matrix Feature Feature ℝ)
    (features : Matrix Batch Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (old_left : normal * oldInverse = 1)
    (schur_right :
      batchSchur features oldInverse * schurInverse = 1) :
    updatedNormal normal features *
        updatedInverse features oldInverse schurInverse =
      1 := by
  have cancellation :=
    features_sandwich_schurInverse
      features oldInverse schurInverse schur_right
  have normal_gain :=
    normal_mul_batchGain
      normal oldInverse features schurInverse old_left
  have increment_gain :
      (features.transpose * features) *
          (batchGain features oldInverse schurInverse * oldInverse) =
        features.transpose * features * oldInverse *
          features.transpose * schurInverse * features * oldInverse := by
    simp only [batchGain, Matrix.mul_assoc]
  unfold updatedInverse updatedNormal normalIncrement
  rw [Matrix.mul_sub, Matrix.add_mul, Matrix.add_mul]
  rw [old_left]
  rw [← Matrix.mul_assoc
    normal (batchGain features oldInverse schurInverse) oldInverse,
    normal_gain]
  rw [increment_gain]
  rw [cancellation]
  abel

/-- Equation (10) preserves the complete inverse contract. -/
theorem updatedInverse_twoSided
    (normal oldInverse : Matrix Feature Feature ℝ)
    (features : Matrix Batch Feature ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (old_contract : TwoSidedInverse oldInverse normal)
    (schur_contract :
      TwoSidedInverse schurInverse (batchSchur features oldInverse)) :
    TwoSidedInverse
      (updatedInverse features oldInverse schurInverse)
      (updatedNormal normal features) := by
  constructor
  · exact updatedInverse_mul_updatedNormal
      normal oldInverse features schurInverse
      old_contract.1 schur_contract.1
  · exact updatedNormal_mul_updatedInverse
      normal oldInverse features schurInverse
      old_contract.2 schur_contract.2

omit [DecidableEq Batch] in
/-- A finite credit-error correction equals the enlarged joint head whenever
the old head solves its normal equation and the new inverse contract holds. -/
theorem recursiveHeadUpdate_eq_joint_of_normalEquation
    (normal newInverse : Matrix Feature Feature ℝ)
    (cross oldHead : Matrix Feature Output ℝ)
    (features : Matrix Batch Feature ℝ)
    (targets : Matrix Batch Output ℝ)
    (old_normal_equation : normal * oldHead = cross)
    (new_right_inverse :
      newInverse * updatedNormal normal features = 1) :
    recursiveHeadUpdate oldHead features targets newInverse =
      headFromStatistics newInverse
        (updatedCross cross features targets) := by
  have inverse_on_head := congrArg
    (fun matrix : Matrix Feature Feature ℝ => matrix * oldHead)
    new_right_inverse
  have decomposition :
      newInverse * cross +
          newInverse * (features.transpose * features) * oldHead =
        oldHead := by
    simpa only [updatedNormal, normalIncrement, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc,
      old_normal_equation] using inverse_on_head
  have cross_identity :
      newInverse * cross =
        oldHead -
          newInverse * (features.transpose * features) * oldHead :=
    eq_sub_of_add_eq decomposition
  unfold recursiveHeadUpdate headFromStatistics updatedCross crossIncrement
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
  rw [cross_identity]
  simp only [← Matrix.mul_assoc]
  abel

/-- The source's recursive ridge head is exactly the batch-joint ridge head.
The proof does not require the target columns to denote disjoint classes. -/
theorem recursiveHeadUpdate_eq_joint
    (normal oldInverse : Matrix Feature Feature ℝ)
    (cross : Matrix Feature Output ℝ)
    (features : Matrix Batch Feature ℝ)
    (targets : Matrix Batch Output ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (old_contract : TwoSidedInverse oldInverse normal)
    (schur_contract :
      TwoSidedInverse schurInverse (batchSchur features oldInverse)) :
    recursiveHeadUpdate
        (headFromStatistics oldInverse cross)
        features targets
        (updatedInverse features oldInverse schurInverse) =
      headFromStatistics
        (updatedInverse features oldInverse schurInverse)
        (updatedCross cross features targets) := by
  have old_normal_equation :
      normal * headFromStatistics oldInverse cross = cross := by
    unfold headFromStatistics
    rw [← Matrix.mul_assoc, old_contract.2, Matrix.one_mul]
  exact recursiveHeadUpdate_eq_joint_of_normalEquation
    normal (updatedInverse features oldInverse schurInverse)
    cross (headFromStatistics oldInverse cross)
    features targets old_normal_equation
    (updatedInverse_mul_updatedNormal
      normal oldInverse features schurInverse
      old_contract.1 schur_contract.1)

/-- The recursive result satisfies the enlarged joint normal equation. -/
theorem updatedNormal_mul_recursiveHeadUpdate
    (normal oldInverse : Matrix Feature Feature ℝ)
    (cross : Matrix Feature Output ℝ)
    (features : Matrix Batch Feature ℝ)
    (targets : Matrix Batch Output ℝ)
    (schurInverse : Matrix Batch Batch ℝ)
    (old_contract : TwoSidedInverse oldInverse normal)
    (schur_contract :
      TwoSidedInverse schurInverse (batchSchur features oldInverse)) :
    updatedNormal normal features *
        recursiveHeadUpdate
          (headFromStatistics oldInverse cross)
          features targets
          (updatedInverse features oldInverse schurInverse) =
      updatedCross cross features targets := by
  rw [recursiveHeadUpdate_eq_joint
    normal oldInverse cross features targets schurInverse
    old_contract schur_contract]
  unfold headFromStatistics
  rw [← Matrix.mul_assoc,
    (updatedInverse_twoSided
      normal oldInverse features schurInverse
      old_contract schur_contract).2,
    Matrix.one_mul]

/-! ## Fixed-coordinate order invariance -/

variable {Batch₁ : Type*} {Batch₂ : Type*}
variable [Fintype Batch₁] [Fintype Batch₂]

omit [Fintype Feature] [DecidableEq Feature] in
/-- Frozen-feature normal statistics commute across arbitrary batches. -/
theorem updatedNormal_order_independent
    (normal : Matrix Feature Feature ℝ)
    (first : Matrix Batch₁ Feature ℝ)
    (second : Matrix Batch₂ Feature ℝ) :
    updatedNormal (updatedNormal normal first) second =
      updatedNormal (updatedNormal normal second) first := by
  unfold updatedNormal
  abel

omit [Fintype Feature] [DecidableEq Feature] in
/-- Frozen-feature cross statistics commute across arbitrary batches. -/
theorem updatedCross_order_independent
    (cross : Matrix Feature Output ℝ)
    (firstFeatures : Matrix Batch₁ Feature ℝ)
    (firstTargets : Matrix Batch₁ Output ℝ)
    (secondFeatures : Matrix Batch₂ Feature ℝ)
    (secondTargets : Matrix Batch₂ Output ℝ) :
    updatedCross
        (updatedCross cross firstFeatures firstTargets)
        secondFeatures secondTargets =
      updatedCross
        (updatedCross cross secondFeatures secondTargets)
        firstFeatures firstTargets := by
  unfold updatedCross
  abel

/-! ## Positive and negative executable boundaries -/

/-- A one-by-one matrix used for exact executable fixtures. -/
def singletonMatrix (value : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => value

@[simp] theorem singletonMatrix_apply
    (value : ℝ)
    (row column : Fin 1) :
    singletonMatrix value row column = value := by
  rfl

/-- The old scalar normal matrix `2` and candidate inverse `1/2` satisfy the
complete inverse contract. -/
theorem scalar_old_inverse :
    TwoSidedInverse
      (singletonMatrix (1 / 2))
      (singletonMatrix 2) := by
  constructor <;>
    ext row column <;>
    fin_cases row <;>
    fin_cases column <;>
    norm_num [TwoSidedInverse, singletonMatrix, Matrix.mul_apply]

/-- For feature `3` and old inverse `1/2`, the Schur matrix is `11/2` and
`2/11` is its complete inverse. -/
theorem scalar_schur_inverse :
    TwoSidedInverse
      (singletonMatrix (2 / 11))
      (batchSchur
        (singletonMatrix 3)
        (singletonMatrix (1 / 2))) := by
  constructor <;>
    ext row column <;>
    fin_cases row <;>
    fin_cases column <;>
    norm_num [TwoSidedInverse, batchSchur, singletonMatrix,
      Matrix.mul_apply]

/-- A nonzero residual fixture: the recursive update and the joint ridge
solution both equal `31/11`. -/
theorem scalar_recursive_joint :
    recursiveHeadUpdate
        (headFromStatistics
          (singletonMatrix (1 / 2))
          (singletonMatrix 4))
        (singletonMatrix 3)
        (singletonMatrix 9)
        (updatedInverse
          (singletonMatrix 3)
          (singletonMatrix (1 / 2))
          (singletonMatrix (2 / 11))) =
      singletonMatrix (31 / 11) := by
  ext row column
  fin_cases row
  fin_cases column
  norm_num [recursiveHeadUpdate, headFromStatistics, updatedInverse,
    batchGain, singletonMatrix, Matrix.mul_apply]

/-- The same fixture reaches the joint head through the general theorem. -/
theorem scalar_recursive_eq_joint :
    recursiveHeadUpdate
        (headFromStatistics
          (singletonMatrix (1 / 2))
          (singletonMatrix 4))
        (singletonMatrix 3)
        (singletonMatrix 9)
        (updatedInverse
          (singletonMatrix 3)
          (singletonMatrix (1 / 2))
          (singletonMatrix (2 / 11))) =
      headFromStatistics
        (updatedInverse
          (singletonMatrix 3)
          (singletonMatrix (1 / 2))
          (singletonMatrix (2 / 11)))
        (updatedCross
          (singletonMatrix 4)
          (singletonMatrix 3)
          (singletonMatrix 9)) := by
  exact recursiveHeadUpdate_eq_joint
    (singletonMatrix 2)
    (singletonMatrix (1 / 2))
    (singletonMatrix 4)
    (singletonMatrix 3)
    (singletonMatrix 9)
    (singletonMatrix (2 / 11))
    scalar_old_inverse
    scalar_schur_inverse

/-- Replacing ridge `1` by ridge `2` in the joint comparator changes the
answer: the recursive same-ridge update is `1/3`, not `1/4`. -/
theorem changing_ridge_breaks_joint_equivalence :
    recursiveHeadUpdate
        (singletonMatrix (1 / 2))
        (singletonMatrix 1)
        (singletonMatrix 0)
        (singletonMatrix (1 / 3)) ≠
      headFromStatistics
        (singletonMatrix (1 / 4))
        (updatedCross
          (singletonMatrix 1)
          (singletonMatrix 1)
          (singletonMatrix 0)) := by
  intro claimed_equal
  have entry_equal :=
    congrFun (congrFun claimed_equal (0 : Fin 1)) (0 : Fin 1)
  norm_num [recursiveHeadUpdate, headFromStatistics, updatedCross,
    crossIncrement, singletonMatrix, Matrix.mul_apply] at entry_equal

/-- Position-indexed projectors break raw-order invariance: raw features
`1,2` become projected features `1,4`, while the swapped raw order becomes
`2,2` under the same two position projectors. -/
theorem changing_feature_map_breaks_raw_order_invariance :
    updatedNormal
        (updatedNormal
          (singletonMatrix 1)
          (singletonMatrix (1 * 1)))
        (singletonMatrix (2 * 2)) ≠
      updatedNormal
        (updatedNormal
          (singletonMatrix 1)
          (singletonMatrix (1 * 2)))
        (singletonMatrix (2 * 1)) := by
  intro claimed_equal
  have entry_equal :=
    congrFun (congrFun claimed_equal (0 : Fin 1)) (0 : Fin 1)
  norm_num [updatedNormal, normalIncrement, singletonMatrix,
    Matrix.mul_apply] at entry_equal

/-- A singular zero normal matrix has no zero two-sided inverse. -/
theorem zero_not_inverse_of_singular_normal :
    ¬ TwoSidedInverse
      (singletonMatrix 0)
      (singletonMatrix 0) := by
  intro contract
  have entry_equal :=
    congrFun (congrFun contract.1 (0 : Fin 1)) (0 : Fin 1)
  norm_num [singletonMatrix, Matrix.mul_apply] at entry_equal

/-- In the scalar singleton case, a cached inverse normal statistic
reveals the exact squared feature magnitude.  This is not full sample
reconstruction, but it prevents exemplar-free storage from being treated as
a privacy theorem without an additional threat model. -/
theorem featureSquare_recoverable_from_inverseNormal
    (feature ridge cachedInverse : ℝ)
    (cache_equation :
      cachedInverse = 1 / (feature ^ 2 + ridge)) :
    1 / cachedInverse - ridge = feature ^ 2 := by
  rw [cache_equation]
  simp only [one_div, inv_inv]
  ring

#print axioms updatedInverse_twoSided
#print axioms recursiveHeadUpdate_eq_joint
#print axioms updatedNormal_mul_recursiveHeadUpdate
#print axioms updatedNormal_order_independent
#print axioms changing_ridge_breaks_joint_equivalence
#print axioms changing_feature_map_breaks_raw_order_invariance
#print axioms featureSquare_recoverable_from_inverseNormal

end

end AnalyticIncrementalRidge

end Mettapedia.MachineLearning.ContinualLearning
