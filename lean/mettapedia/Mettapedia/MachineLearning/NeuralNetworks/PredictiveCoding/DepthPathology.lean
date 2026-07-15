import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.BacktrackingDescent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Depth-dependent settling on a predictive-coding path

This file isolates the slow mode of synchronous Jacobi relaxation on a unit
path with clamped endpoints.  At every interior site the update is exactly a
quarter-step along the negative gradient of the local unit-path energy.  The
first discrete sine mode is an exact eigenmode with rate
`cos (pi / segments)`, so the rate approaches one as the path grows.

The final adapter result deliberately keeps the frozen backbone in the model
while its analytic rate bound depends only on the trainable adapter path.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Filter

/-! ## Jacobi relaxation as an exact local gradient step -/

/-- Gradient contribution at an interior vertex of a unit-weight path. -/
noncomputable def unitPathEnergyGradient (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * (2 * v n - v (n - 1) - v (n + 1))

/-- Synchronous averaging with zero-valued clamped endpoints. -/
noncomputable def pathJacobiStep (segments : ℕ) (v : ℕ → ℝ) : ℕ → ℝ :=
  fun n =>
    if n = 0 then 0
    else if segments ≤ n then 0
    else (v (n - 1) + v (n + 1)) / 2

theorem pathJacobiStep_eq_quarter_gradientStep
    (segments : ℕ) (v : ℕ → ℝ) (n : ℕ)
    (hn0 : n ≠ 0) (hnsegments : n < segments) :
    pathJacobiStep segments v n =
      v n - (1 / 4) * unitPathEnergyGradient v n := by
  simp [pathJacobiStep, unitPathEnergyGradient, hn0, Nat.not_le.mpr hnsegments]
  ring

/-! ## Exact slow mode and depth-dependent rate -/

/-- Relaxation rate of the first sine mode on a path. -/
noncomputable def pathRelaxationRate (segments : ℕ) : ℝ :=
  Real.cos (Real.pi / (segments : ℝ))

/-- First discrete sine mode on the path vertices. -/
noncomputable def pathSlowMode (segments n : ℕ) : ℝ :=
  Real.sin ((n : ℝ) * (Real.pi / (segments : ℝ)))

theorem pathSlowMode_interior_eigenrelation
    (segments n : ℕ) (hn0 : n ≠ 0) :
    (pathSlowMode segments (n - 1) + pathSlowMode segments (n + 1)) / 2 =
      pathRelaxationRate segments * pathSlowMode segments n := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hcast_add : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    norm_num
  unfold pathSlowMode pathRelaxationRate
  rw [hcast_sub, hcast_add]
  rw [show ((n : ℝ) - 1) * (Real.pi / (segments : ℝ)) =
      (n : ℝ) * (Real.pi / (segments : ℝ)) -
        Real.pi / (segments : ℝ) by ring]
  rw [show ((n : ℝ) + 1) * (Real.pi / (segments : ℝ)) =
      (n : ℝ) * (Real.pi / (segments : ℝ)) +
        Real.pi / (segments : ℝ) by ring]
  rw [Real.sin_sub, Real.sin_add]
  ring

theorem pathSlowMode_boundary_zero
    (segments : ℕ) (hsegments : 0 < segments) :
    pathSlowMode segments 0 = 0 ∧ pathSlowMode segments segments = 0 := by
  constructor
  · simp [pathSlowMode]
  · unfold pathSlowMode
    have hseg : (segments : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hsegments
    rw [show (segments : ℝ) * (Real.pi / (segments : ℝ)) = Real.pi by
      field_simp]
    exact Real.sin_pi

theorem pathSlowMode_eigenrelation
    (segments n : ℕ) (hsegments : 0 < segments) (hn : n ≤ segments) :
    pathJacobiStep segments (pathSlowMode segments) n =
      pathRelaxationRate segments * pathSlowMode segments n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [pathJacobiStep, pathSlowMode]
  rcases eq_or_ne n segments with hnsegments | hnsegments
  · rw [hnsegments, (pathSlowMode_boundary_zero segments hsegments).2]
    simp [pathJacobiStep]
  · have hnlt : n < segments := lt_of_le_of_ne hn hnsegments
    simp only [pathJacobiStep, hn0, if_false, Nat.not_le.mpr hnlt]
    exact pathSlowMode_interior_eigenrelation segments n hn0

/-- Repeated synchronous path relaxation. -/
noncomputable def pathJacobiIterate
    (segments : ℕ) (v : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => v
  | t + 1 => pathJacobiStep segments (pathJacobiIterate segments v t)

/-- The first sine mode decays by exactly the depth-dependent
factor `pathRelaxationRate segments` at every settling step. -/
theorem pathSlowMode_iterate_exact
    (segments : ℕ) (hsegments : 0 < segments) :
    ∀ t n, n ≤ segments →
      pathJacobiIterate segments (pathSlowMode segments) t n =
        pathRelaxationRate segments ^ t * pathSlowMode segments n := by
  intro t
  induction t with
  | zero =>
      intro n _hn
      simp [pathJacobiIterate]
  | succ t ih =>
      intro n hn
      rw [pathJacobiIterate]
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [pathJacobiStep, pathSlowMode]
      rcases eq_or_ne n segments with hnsegments | hnsegments
      · rw [hnsegments, (pathSlowMode_boundary_zero segments hsegments).2]
        simp [pathJacobiStep]
      · have hnlt : n < segments := lt_of_le_of_ne hn hnsegments
        have hnsub : n - 1 ≤ segments := by omega
        have hnadd : n + 1 ≤ segments := by omega
        simp only [pathJacobiStep, hn0, if_false, Nat.not_le.mpr hnlt]
        rw [ih (n - 1) hnsub, ih (n + 1) hnadd]
        rw [← mul_add, div_eq_mul_inv, mul_assoc]
        rw [show (pathSlowMode segments (n - 1) +
              pathSlowMode segments (n + 1)) * (2 : ℝ)⁻¹ =
            pathRelaxationRate segments * pathSlowMode segments n by
          rw [← div_eq_mul_inv]
          exact pathSlowMode_interior_eigenrelation segments n hn0]
        rw [pow_succ]
        ring

/-- The first-mode spectral gap is at most quadratic in inverse path depth. -/
theorem pathRelaxationRate_gap_bound (segments : ℕ) :
    0 ≤ 1 - pathRelaxationRate segments ∧
      1 - pathRelaxationRate segments ≤
        (Real.pi / (segments : ℝ)) ^ 2 / 2 := by
  constructor
  · unfold pathRelaxationRate
    linarith [Real.cos_le_one (Real.pi / (segments : ℝ))]
  · have h := Real.one_sub_sq_div_two_le_cos
      (x := Real.pi / (segments : ℝ))
    unfold pathRelaxationRate
    linarith

/-- Increasing the path depth drives the exact slow-mode rate to one. -/
theorem pathRelaxationRate_tendsto_one :
    Tendsto (fun n : ℕ => pathRelaxationRate (n + 1)) atTop (nhds 1) := by
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hangle :
      Tendsto (fun n : ℕ => Real.pi * ((1 : ℝ) / ((n : ℝ) + 1)))
        atTop (nhds 0) := by
    simpa using hinv.const_mul Real.pi
  have hcos := (Real.continuous_cos.tendsto 0).comp hangle
  simpa [Function.comp_def, Real.cos_zero, pathRelaxationRate, Nat.cast_add,
    div_eq_mul_inv, mul_comm] using hcos

/-! ## Frozen-backbone adapter corollary -/

/-- A path-shaped trainable adapter attached to a backbone whose state remains
frozen during adapter settling. -/
structure FrozenAdapterPath where
  backboneDepth : ℕ
  adapterSegments : ℕ

/-- Freezing removes the backbone coordinates from the relaxation operator. -/
noncomputable def FrozenAdapterPath.relaxationRate
    (model : FrozenAdapterPath) : ℝ :=
  pathRelaxationRate model.adapterSegments

/-- The settling-rate bound for a frozen-backbone adapter depends only on the
adapter path depth, not on the stored backbone depth. -/
theorem FrozenAdapterPath.relaxationRate_gap_bound
    (model : FrozenAdapterPath) :
    0 ≤ 1 - model.relaxationRate ∧
      1 - model.relaxationRate ≤
        (Real.pi / (model.adapterSegments : ℝ)) ^ 2 / 2 := by
  exact pathRelaxationRate_gap_bound model.adapterSegments

/-! ## Positive and negative rate fixtures -/

theorem pathRelaxationRate_two_segments_positive_example :
    pathRelaxationRate 2 = 0 := by
  norm_num [pathRelaxationRate, Real.cos_pi_div_two]

theorem pathRelaxationRate_three_segments_positive_example :
    pathRelaxationRate 3 = 1 / 2 := by
  norm_num [pathRelaxationRate, Real.cos_pi_div_three]

/-- Adding an interior degree of freedom changes the relaxation rate; a
depth-invariant rate claim is false even in the smallest comparison. -/
theorem deeper_path_has_different_rate_negative_example :
    pathRelaxationRate 3 ≠ pathRelaxationRate 2 := by
  rw [pathRelaxationRate_three_segments_positive_example,
    pathRelaxationRate_two_segments_positive_example]
  norm_num

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
