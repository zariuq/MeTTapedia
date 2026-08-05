import Mettapedia.MachineLearning.NeuralNetworks.Architecture.DepthwiseResidualScaling

/-!
# Depthwise branch and update scaling

Yang, Yu, Zhu, and Hayou, *Tensor Programs VI: Feature Learning in Infinite
Depth Neural Networks* (arXiv:2310.02244), pair an inverse-square-root residual
branch multiplier with parameter updates of inverse-square-root size.  Their
finite-depth intuition separates two geometries: initialization contributions
are independent and therefore accumulate quadratically, whereas training
contributions are highly correlated and therefore accumulate coherently.

This file makes that finite two-scale geometry exact.  If both the branch
multiplier and the effective parameter update scale as `1 / sqrt depth`, then
the coherent training coefficient is depth independent, while the quadratic
budget of mutually orthogonal update directions decays as `1 / depth`.
Keeping the update scale constant instead makes the coherent squared
coefficient grow linearly with depth.  Conversely, once the branch amplitude
is nonzero, coherent invariance uniquely forces the inverse-square-root update
scale.

The source's infinite-width tensor-program limit, infinite-depth feature
diversity, optimizer-specific derivation of effective update size, stochastic
independence, and empirical hyperparameter transfer are not formalized here.
The exact theorems apply to an observed effective branch coefficient and
parameter-update coefficient; using them operationally therefore requires
those quantities and their cross-layer geometry to be measured.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace DepthwiseUpdateScaling

noncomputable section

open DepthwiseResidualScaling

/-- Scalar coefficient obtained when equal per-layer training contributions
are coherently aligned across a residual stack. -/
def coherentUpdateCoefficient
    (depth : ℕ) (branchScale parameterUpdateScale : ℝ) : ℝ :=
  (depth : ℝ) * branchScale * parameterUpdateScale

/-- Quadratic budget of equal per-layer training contributions.  This is the
relevant exact budget when their directions are orthonormal. -/
def updateQuadraticBudget
    (depth : ℕ) (branchScale parameterUpdateScale : ℝ) : ℝ :=
  residualQuadraticBudget
    (fun _ : Fin depth => branchScale * parameterUpdateScale)

@[simp] theorem updateQuadraticBudget_eq
    (depth : ℕ) (branchScale parameterUpdateScale : ℝ) :
    updateQuadraticBudget depth branchScale parameterUpdateScale =
      (depth : ℝ) * (branchScale * parameterUpdateScale) ^ 2 := by
  simp [updateQuadraticBudget, residualQuadraticBudget_const]

/-- Orthonormal update directions realize the update quadratic budget exactly
as squared state-space effect norm. -/
theorem orthonormal_updateEffect_norm_sq_eq
    {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    (direction : Fin depth → State)
    (branchScale parameterUpdateScale : ℝ)
    (horthonormal : Orthonormal ℝ direction) :
    ‖residualEffect direction
        (fun _ : Fin depth => branchScale * parameterUpdateScale)‖ ^ 2 =
      updateQuadraticBudget depth branchScale parameterUpdateScale := by
  exact orthonormal_residualEffect_norm_sq_eq
    direction _ horthonormal

/-- Fully aligned unit update directions realize the square of the coherent
coefficient. -/
theorem aligned_updateEffect_norm_sq_eq
    {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (direction : State) (branchScale parameterUpdateScale : ℝ)
    (hdirection : ‖direction‖ = 1) :
    ‖residualEffect (fun _ : Fin depth => direction)
        (fun _ : Fin depth => branchScale * parameterUpdateScale)‖ ^ 2 =
      coherentUpdateCoefficient depth branchScale parameterUpdateScale ^ 2 := by
  rw [aligned_residualEffect_eq, norm_smul, hdirection, mul_one,
    Real.norm_eq_abs, sq_abs]
  unfold coherentUpdateCoefficient
  ring

/-- The paired inverse-square-root scales give a depth-independent coherent
training coefficient at every positive depth. -/
theorem sqrtDepthScales_coherentUpdateCoefficient
    (depth : ℕ) (branchAmplitude updateAmplitude : ℝ)
    (hdepth : 0 < depth) :
    coherentUpdateCoefficient depth
        (sqrtDepthScale branchAmplitude depth)
        (sqrtDepthScale updateAmplitude depth) =
      branchAmplitude * updateAmplitude := by
  have hdepthReal : (0 : ℝ) < depth := by
    exact_mod_cast hdepth
  have hsqrt : Real.sqrt (depth : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdepthReal)
  unfold coherentUpdateCoefficient sqrtDepthScale
  have hsqrtSq :
      Real.sqrt (depth : ℝ) * Real.sqrt depth = depth := by
    nlinarith [Real.sq_sqrt (le_of_lt hdepthReal)]
  calc
    (depth : ℝ) * (branchAmplitude / Real.sqrt depth) *
        (updateAmplitude / Real.sqrt depth) =
        branchAmplitude * updateAmplitude *
          ((depth : ℝ) /
            (Real.sqrt depth * Real.sqrt depth)) := by ring
    _ = branchAmplitude * updateAmplitude := by
      rw [hsqrtSq]
      field_simp

/-- Under the same paired scaling, mutually orthogonal update directions have
an exact quadratic budget decaying as the reciprocal of depth. -/
theorem sqrtDepthScales_updateQuadraticBudget
    (depth : ℕ) (branchAmplitude updateAmplitude : ℝ)
    (hdepth : 0 < depth) :
    updateQuadraticBudget depth
        (sqrtDepthScale branchAmplitude depth)
        (sqrtDepthScale updateAmplitude depth) =
      (branchAmplitude * updateAmplitude) ^ 2 / depth := by
  have hdepthReal : (0 : ℝ) < depth := by
    exact_mod_cast hdepth
  have hsqrt : Real.sqrt (depth : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdepthReal)
  rw [updateQuadraticBudget_eq, sqrtDepthScale, sqrtDepthScale]
  have hsqrtSq :
      Real.sqrt (depth : ℝ) * Real.sqrt depth = depth := by
    nlinarith [Real.sq_sqrt (le_of_lt hdepthReal)]
  rw [div_mul_div_comm, hsqrtSq]
  field_simp

/-- If only the branch uses inverse-square-root scaling while the effective
parameter update remains constant, the coherent squared coefficient grows
linearly with depth. -/
theorem sqrtBranch_constantUpdate_coherent_sq
    (depth : ℕ) (branchAmplitude updateAmplitude : ℝ)
    (hdepth : 0 < depth) :
    coherentUpdateCoefficient depth
        (sqrtDepthScale branchAmplitude depth) updateAmplitude ^ 2 =
      (depth : ℝ) * (branchAmplitude * updateAmplitude) ^ 2 := by
  have hdepthReal : (0 : ℝ) < depth := by
    exact_mod_cast hdepth
  have hsqrt : Real.sqrt (depth : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdepthReal)
  unfold coherentUpdateCoefficient sqrtDepthScale
  have hdiv :
      (depth : ℝ) / Real.sqrt depth = Real.sqrt depth := by
    apply (div_eq_iff hsqrt).2
    nlinarith [Real.sq_sqrt (le_of_lt hdepthReal)]
  calc
    ((depth : ℝ) * (branchAmplitude / Real.sqrt depth) *
        updateAmplitude) ^ 2 =
        (branchAmplitude * updateAmplitude * Real.sqrt depth) ^ 2 := by
          rw [show (depth : ℝ) * (branchAmplitude / Real.sqrt depth) =
            branchAmplitude * ((depth : ℝ) / Real.sqrt depth) by ring,
            hdiv]
          ring
    _ = (depth : ℝ) * (branchAmplitude * updateAmplitude) ^ 2 := by
      nlinarith [Real.sq_sqrt (le_of_lt hdepthReal)]

/-- With a nonzero branch amplitude, coherent invariance uniquely determines
the paired inverse-square-root effective update scale. -/
theorem coherent_invariance_forces_sqrt_updateScale
    (depth : ℕ) (branchAmplitude updateAmplitude updateScale : ℝ)
    (hdepth : 0 < depth) (hbranch : branchAmplitude ≠ 0)
    (hinvariant :
      coherentUpdateCoefficient depth
          (sqrtDepthScale branchAmplitude depth) updateScale =
        branchAmplitude * updateAmplitude) :
    updateScale = sqrtDepthScale updateAmplitude depth := by
  have hdepthReal : (0 : ℝ) < depth := by
    exact_mod_cast hdepth
  have hsqrt : Real.sqrt (depth : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdepthReal)
  unfold coherentUpdateCoefficient at hinvariant
  unfold sqrtDepthScale at hinvariant ⊢
  have hdiv :
      (depth : ℝ) / Real.sqrt depth = Real.sqrt depth := by
    apply (div_eq_iff hsqrt).2
    nlinarith [Real.sq_sqrt (le_of_lt hdepthReal)]
  have hfactor :
      (depth : ℝ) * (branchAmplitude / Real.sqrt depth) =
        branchAmplitude * Real.sqrt depth := by
    calc
      (depth : ℝ) * (branchAmplitude / Real.sqrt depth) =
          branchAmplitude * ((depth : ℝ) / Real.sqrt depth) := by ring
      _ = branchAmplitude * Real.sqrt depth := by rw [hdiv]
  rw [hfactor] at hinvariant
  apply (eq_div_iff hsqrt).2
  have hcancel :
      Real.sqrt depth * updateScale = updateAmplitude := by
    apply (mul_left_cancel₀ hbranch)
    calc
      branchAmplitude * (Real.sqrt depth * updateScale) =
          (branchAmplitude * Real.sqrt depth) * updateScale := by ring
      _ = branchAmplitude * updateAmplitude := hinvariant
  simpa [mul_comm] using hcancel

/-- Paired scaling preserves the aligned unit-direction effect exactly. -/
theorem sqrtDepthScales_aligned_updateEffect
    {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (direction : State) (branchAmplitude updateAmplitude : ℝ)
    (hdepth : 0 < depth) (hdirection : ‖direction‖ = 1) :
    ‖residualEffect (fun _ : Fin depth => direction)
        (fun _ : Fin depth =>
          sqrtDepthScale branchAmplitude depth *
            sqrtDepthScale updateAmplitude depth)‖ ^ 2 =
      (branchAmplitude * updateAmplitude) ^ 2 := by
  rw [aligned_updateEffect_norm_sq_eq direction _ _ hdirection,
    sqrtDepthScales_coherentUpdateCoefficient depth _ _ hdepth]

/-- At depth four, paired half-scales give coherent coefficient one but
orthogonal quadratic budget one quarter. -/
theorem depthFour_pairedScale_geometry :
    coherentUpdateCoefficient 4
        (sqrtDepthScale 1 4) (sqrtDepthScale 1 4) = 1 ∧
      updateQuadraticBudget 4
        (sqrtDepthScale 1 4) (sqrtDepthScale 1 4) = 1 / 4 := by
  constructor
  · simpa using
      sqrtDepthScales_coherentUpdateCoefficient 4 1 1 (by norm_num)
  · simpa using
      sqrtDepthScales_updateQuadraticBudget 4 1 1 (by norm_num)

/-- At depth four, failing to scale the effective update makes the coherent
squared coefficient four rather than one. -/
theorem depthFour_constantUpdate_is_not_invariant :
    coherentUpdateCoefficient 4 (sqrtDepthScale 1 4) 1 ^ 2 = 4 ∧
      coherentUpdateCoefficient 4 (sqrtDepthScale 1 4) 1 ^ 2 ≠ 1 := by
  constructor
  · simpa using sqrtBranch_constantUpdate_coherent_sq 4 1 1 (by norm_num)
  · rw [sqrtBranch_constantUpdate_coherent_sq 4 1 1 (by norm_num)]
    norm_num

#print axioms updateQuadraticBudget_eq
#print axioms orthonormal_updateEffect_norm_sq_eq
#print axioms aligned_updateEffect_norm_sq_eq
#print axioms sqrtDepthScales_coherentUpdateCoefficient
#print axioms sqrtDepthScales_updateQuadraticBudget
#print axioms sqrtBranch_constantUpdate_coherent_sq
#print axioms coherent_invariance_forces_sqrt_updateScale
#print axioms sqrtDepthScales_aligned_updateEffect
#print axioms depthFour_pairedScale_geometry
#print axioms depthFour_constantUpdate_is_not_invariant

end

end DepthwiseUpdateScaling

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
