import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Feasibility and least squares after low-rank truncation

Low-rank analytic classifiers are often described in two different ways:

1. interpolate every target after truncating the feature SVD; or
2. minimize the residual against the truncated features.

These formulations are not equivalent without a compatibility condition.
The fitted rows produced by a truncated pseudoinverse lie in the preserved
right-singular subspace.  Exact interpolation is therefore possible exactly
when every target row already lies in that subspace.

This file isolates the reusable Hilbert-space statement.  An orthogonal
projector represents the retained right-singular subspace.  Projection is the
global least-squares solution among representable predictions, with an exact
Pythagorean loss decomposition.  The two-coordinate fixtures show both the
compatible and incompatible cases for a proper, nonzero retained subspace.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace LowRankTruncationFeasibility

open scoped BigOperators RealInnerProductSpace

variable {V Output : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The algebraic data used from a truncated SVD: an idempotent,
self-adjoint projection onto the retained right-singular subspace. -/
structure OrthogonalProjector (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  projection : V →ₗ[ℝ] V
  idempotent : ∀ vector, projection (projection vector) = projection vector
  selfAdjoint :
    ∀ left right,
      inner ℝ (projection left) right =
        inner ℝ left (projection right)

/-- A prediction is representable after truncation when every output row is
fixed by the retained-subspace projector. -/
def IsRepresentable
    (projector : OrthogonalProjector V)
    (prediction : Output → V) : Prop :=
  ∀ output, projector.projection (prediction output) = prediction output

/-- The prediction obtained by projecting every target row onto the retained
right-singular subspace. -/
noncomputable def projectedPrediction
    (projector : OrthogonalProjector V)
    (target : Output → V) : Output → V :=
  fun output ↦ projector.projection (target output)

/-- Finite squared error across output rows. -/
noncomputable def squaredLoss
    [Fintype Output]
    (prediction target : Output → V) : ℝ :=
  ∑ output, ‖prediction output - target output‖ ^ 2

omit [InnerProductSpace ℝ V] in
theorem squaredLoss_nonnegative
    [Fintype Output]
    (prediction target : Output → V) :
    0 ≤ squaredLoss prediction target := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [InnerProductSpace ℝ V] in
/-- Finite squared loss vanishes exactly when the two predictions agree.
This also covers an empty output type, where function extensionality makes
all predictions equal. -/
theorem squaredLoss_eq_zero_iff
    [Fintype Output]
    (prediction target : Output → V) :
    squaredLoss prediction target = 0 ↔ prediction = target := by
  constructor
  · intro hloss
    have hall :
        (fun output ↦ ‖prediction output - target output‖ ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun _ ↦ sq_nonneg _)).mp hloss
    funext output
    have hterm :
        ‖prediction output - target output‖ ^ 2 = 0 := by
      exact congrFun hall output
    have hnorm :
        ‖prediction output - target output‖ = 0 :=
      sq_eq_zero_iff.mp hterm
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · rintro rfl
    simp [squaredLoss]

/-- Projection always produces a representable prediction. -/
theorem projectedPrediction_isRepresentable
    (projector : OrthogonalProjector V)
    (target : Output → V) :
    IsRepresentable projector
      (projectedPrediction projector target) := by
  intro output
  exact projector.idempotent (target output)

/-- A representable displacement and the discarded target component are
orthogonal. -/
theorem fixed_sub_projected_orthogonal
    (projector : OrthogonalProjector V)
    (prediction target : V)
    (hprediction :
      projector.projection prediction = prediction) :
    inner ℝ
      (prediction - projector.projection target)
      (projector.projection target - target) = 0 := by
  have hleft :
      projector.projection
          (prediction - projector.projection target) =
        prediction - projector.projection target := by
    simp only [map_sub, hprediction, projector.idempotent]
  have hright :
      projector.projection
          (projector.projection target - target) = 0 := by
    simp only [map_sub, projector.idempotent, sub_self]
  calc
    inner ℝ
        (prediction - projector.projection target)
        (projector.projection target - target) =
      inner ℝ
        (projector.projection
          (prediction - projector.projection target))
        (projector.projection target - target) := by
          rw [hleft]
    _ =
      inner ℝ
        (prediction - projector.projection target)
        (projector.projection
          (projector.projection target - target)) :=
          projector.selfAdjoint _ _
    _ = 0 := by rw [hright, inner_zero_right]

/-- Exact one-row Pythagorean decomposition. -/
theorem pointwise_squaredLoss_decomposition
    (projector : OrthogonalProjector V)
    (prediction target : V)
    (hprediction :
      projector.projection prediction = prediction) :
    ‖prediction - target‖ ^ 2 =
      ‖prediction - projector.projection target‖ ^ 2 +
        ‖projector.projection target - target‖ ^ 2 := by
  have decomposition :
      prediction - target =
        (prediction - projector.projection target) +
          (projector.projection target - target) := by
    abel
  rw [decomposition]
  simpa [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_real
      (fixed_sub_projected_orthogonal
        projector prediction target hprediction)

/-- Exact finite-output loss decomposition.  The first term is avoidable
within the retained subspace; the second is the irreducible discarded-target
loss. -/
theorem squaredLoss_decomposition
    [Fintype Output]
    (projector : OrthogonalProjector V)
    (prediction target : Output → V)
    (hprediction : IsRepresentable projector prediction) :
    squaredLoss prediction target =
      squaredLoss prediction (projectedPrediction projector target) +
        squaredLoss (projectedPrediction projector target) target := by
  unfold squaredLoss
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro output _
  simpa [projectedPrediction] using
    pointwise_squaredLoss_decomposition
      projector (prediction output) (target output) (hprediction output)

/-- The projected target is a global least-squares minimizer among all
predictions representable after truncation. -/
theorem projectedPrediction_minimizes
    [Fintype Output]
    (projector : OrthogonalProjector V)
    (prediction target : Output → V)
    (hprediction : IsRepresentable projector prediction) :
    squaredLoss (projectedPrediction projector target) target ≤
      squaredLoss prediction target := by
  rw [squaredLoss_decomposition projector prediction target hprediction]
  exact le_add_of_nonneg_left
    (squaredLoss_nonnegative
      prediction (projectedPrediction projector target))

/-- The projected target is the unique least-squares minimizer in the
retained subspace.  Equality with its loss forces the avoidable component in
the Pythagorean decomposition to vanish. -/
theorem projectedPrediction_unique_minimizer
    [Fintype Output]
    (projector : OrthogonalProjector V)
    (prediction target : Output → V)
    (hprediction : IsRepresentable projector prediction)
    (hloss :
      squaredLoss prediction target =
        squaredLoss (projectedPrediction projector target) target) :
    prediction = projectedPrediction projector target := by
  have hdecomposition :=
    squaredLoss_decomposition projector prediction target hprediction
  have havoidable :
      squaredLoss prediction (projectedPrediction projector target) = 0 := by
    linarith
  exact
    (squaredLoss_eq_zero_iff
      prediction (projectedPrediction projector target)).mp havoidable

/-- The printed hard interpolation constraint is feasible exactly when every
target row survives the retained-subspace projection. -/
theorem exists_exact_representable_iff
    (projector : OrthogonalProjector V)
    (target : Output → V) :
    (∃ prediction,
      IsRepresentable projector prediction ∧ prediction = target) ↔
      IsRepresentable projector target := by
  constructor
  · rintro ⟨prediction, hprediction, rfl⟩
    exact hprediction
  · intro htarget
    exact ⟨target, htarget, rfl⟩

/-- Projection interpolates exactly under the compatibility condition. -/
theorem projectedPrediction_eq_target_of_representable
    (projector : OrthogonalProjector V)
    (target : Output → V)
    (htarget : IsRepresentable projector target) :
    projectedPrediction projector target = target := by
  funext output
  exact htarget output

/-- Conversely, exact projected interpolation forces the compatibility
condition; least-squares optimality alone cannot replace it. -/
theorem representable_of_projectedPrediction_eq_target
    (projector : OrthogonalProjector V)
    (target : Output → V)
    (hexact : projectedPrediction projector target = target) :
    IsRepresentable projector target := by
  intro output
  exact congrFun hexact output

/-! ## Proper retained-subspace fixtures -/

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A nonzero, nonidentity projection retaining the first coordinate. -/
noncomputable def keepFirstCoordinate : Plane →ₗ[ℝ] Plane where
  toFun vector := EuclideanSpace.single 0 (vector 0)
  map_add' left right := by
    ext coordinate
    fin_cases coordinate <;>
      simp
  map_smul' scalar vector := by
    ext coordinate
    fin_cases coordinate <;>
      simp

noncomputable def keepFirstProjector : OrthogonalProjector Plane where
  projection := keepFirstCoordinate
  idempotent vector := by
    ext coordinate
    fin_cases coordinate <;>
      simp [keepFirstCoordinate]
  selfAdjoint left right := by
    simp [keepFirstCoordinate, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, mul_comm]

noncomputable def retainedTarget : Fin 1 → Plane :=
  fun _ ↦ 2 • EuclideanSpace.single 0 1

noncomputable def discardedTarget : Fin 1 → Plane :=
  fun _ ↦ EuclideanSpace.single 1 1

/-- Positive fixture: a target in the retained first-coordinate subspace is
interpolated exactly. -/
theorem retainedTarget_projected_exact :
    projectedPrediction keepFirstProjector retainedTarget =
      retainedTarget := by
  funext output
  fin_cases output
  ext coordinate
  fin_cases coordinate <;>
    simp [projectedPrediction, keepFirstProjector,
      keepFirstCoordinate, retainedTarget]

/-- The discarded second-coordinate target is not representable by the
proper rank-one retained subspace. -/
theorem discardedTarget_not_representable :
    ¬ IsRepresentable keepFirstProjector discardedTarget := by
  intro representable
  have secondCoordinate := congrArg
    (fun vector : Plane ↦ vector 1)
    (representable 0)
  norm_num [keepFirstProjector, keepFirstCoordinate, discardedTarget,
    PiLp.single_apply] at secondCoordinate

/-- Negative fixture: the hard interpolation problem is infeasible even
though its projected least-squares solution exists. -/
theorem discardedTarget_no_exact_representable_prediction :
    ¬ ∃ prediction,
      IsRepresentable keepFirstProjector prediction ∧
        prediction = discardedTarget := by
  rw [exists_exact_representable_iff]
  exact discardedTarget_not_representable

/-- The projection is genuinely nontrivial: it preserves one nonzero axis
and removes another. -/
theorem keepFirstProjector_proper :
    keepFirstProjector.projection
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
        EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∧
      keepFirstProjector.projection
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = 0 := by
  constructor <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      simp [keepFirstProjector, keepFirstCoordinate]

#print axioms fixed_sub_projected_orthogonal
#print axioms squaredLoss_decomposition
#print axioms squaredLoss_eq_zero_iff
#print axioms projectedPrediction_minimizes
#print axioms projectedPrediction_unique_minimizer
#print axioms exists_exact_representable_iff
#print axioms discardedTarget_no_exact_representable_prediction
#print axioms keepFirstProjector_proper

end LowRankTruncationFeasibility

end Mettapedia.MachineLearning.ContinualLearning
