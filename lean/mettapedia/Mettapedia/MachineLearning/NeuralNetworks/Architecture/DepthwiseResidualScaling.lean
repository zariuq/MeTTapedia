import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Depthwise residual scaling: orthogonal and aligned branch geometries

Bordelon, Noci, Li, Hanin, and Pehlevan,
*Depthwise Hyperparameter Transfer in Residual Networks: Dynamics and
Scaling Limit* (arXiv:2309.16620), use residual-branch coefficients of order
`1 / sqrt depth` together with a maximal-update parameterization.  The
quadratic accumulation of these coefficients remains order one as depth
changes.

This file makes that finite coefficient law exact and separates the geometric
hypothesis that gives it operational meaning.  For orthonormal branch
directions, squared effect norm is exactly the coefficient quadratic budget,
so uniform `1 / sqrt depth` scaling preserves the budget.  For completely
aligned branch directions the same scaling produces squared norm proportional
to depth.  Conversely, uniform `1 / depth` scaling preserves aligned effect
but makes the orthogonal quadratic budget decay like `1 / depth`.  No scalar
coefficient can give both geometries unit budget once depth exceeds one.

The source's infinite-width/infinite-depth DMFT limit, feature-learning
dynamics, optimizer scaling, finite-size convergence rate, and empirical
hyperparameter transfer are not formalized here.  Runtime use requires a
trace of residual-branch scale and cross-branch geometry.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace DepthwiseResidualScaling

noncomputable section

open scoped BigOperators

/-- Quadratic accumulation budget for a finite residual schedule. -/
def residualQuadraticBudget {depth : ℕ}
    (coefficient : Fin depth → ℝ) : ℝ :=
  ∑ layer, coefficient layer ^ 2

/-- Residual effect in a real inner-product state space. -/
def residualEffect {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (direction : Fin depth → State) (coefficient : Fin depth → ℝ) : State :=
  ∑ layer, coefficient layer • direction layer

/-- Orthogonal residual directions turn geometric effect into the exact
coefficient quadratic budget. -/
theorem orthonormal_residualEffect_norm_sq_eq
    {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    (direction : Fin depth → State) (coefficient : Fin depth → ℝ)
    (horthonormal : Orthonormal ℝ direction) :
    ‖residualEffect direction coefficient‖ ^ 2 =
      residualQuadraticBudget coefficient := by
  rw [residualEffect, residualQuadraticBudget,
    ← real_inner_self_eq_norm_sq]
  simpa [pow_two] using
    horthonormal.inner_sum coefficient coefficient Finset.univ

/-- Uniform branch coefficient that preserves a quadratic accumulation
budget across positive depths. -/
def sqrtDepthScale (amplitude : ℝ) (depth : ℕ) : ℝ :=
  amplitude / Real.sqrt depth

/-- Uniform branch coefficient that preserves a completely aligned sum across
positive depths. -/
def inverseDepthScale (amplitude : ℝ) (depth : ℕ) : ℝ :=
  amplitude / depth

@[simp] theorem residualQuadraticBudget_const
    (depth : ℕ) (coefficient : ℝ) :
    residualQuadraticBudget (fun _ : Fin depth => coefficient) =
      (depth : ℝ) * coefficient ^ 2 := by
  simp [residualQuadraticBudget]

/-- The source's `1 / sqrt depth` law has exactly depth-independent quadratic
budget at every positive finite depth. -/
theorem sqrtDepthScale_quadraticBudget
    (depth : ℕ) (amplitude : ℝ) (hdepth : 0 < depth) :
    residualQuadraticBudget
      (fun _ : Fin depth => sqrtDepthScale amplitude depth) =
        amplitude ^ 2 := by
  have hdepthReal : (0 : ℝ) < depth := by
    exact_mod_cast hdepth
  have hsqrt : Real.sqrt (depth : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdepthReal)
  rw [residualQuadraticBudget_const, sqrtDepthScale, div_pow,
    Real.sq_sqrt (le_of_lt hdepthReal)]
  field_simp

/-- Uniform `1 / depth` coefficients have a quadratic budget that decays as
the reciprocal of depth. -/
theorem inverseDepthScale_quadraticBudget
    (depth : ℕ) (amplitude : ℝ) (hdepth : 0 < depth) :
    residualQuadraticBudget
      (fun _ : Fin depth => inverseDepthScale amplitude depth) =
        amplitude ^ 2 / depth := by
  have hdepthNe : (depth : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdepth)
  rw [residualQuadraticBudget_const, inverseDepthScale, div_pow]
  field_simp

/-- Completely aligned branch directions reduce to one scalar sum. -/
theorem aligned_residualEffect_eq
    {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (direction : State) (coefficient : ℝ) :
    residualEffect (fun _ : Fin depth => direction)
        (fun _ : Fin depth => coefficient) =
      ((depth : ℝ) * coefficient) • direction := by
  simp only [residualEffect, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

/-- Under `1 / sqrt depth` scaling, fully aligned unit directions have
squared effect norm proportional to depth rather than depth independent. -/
theorem sqrtDepthScale_aligned_norm_sq
    {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (direction : State) (amplitude : ℝ) (hdepth : 0 < depth)
    (hdirection : ‖direction‖ = 1) :
    ‖residualEffect (fun _ : Fin depth => direction)
        (fun _ : Fin depth => sqrtDepthScale amplitude depth)‖ ^ 2 =
      (depth : ℝ) * amplitude ^ 2 := by
  have hdepthReal : (0 : ℝ) < depth := by
    exact_mod_cast hdepth
  have hsqrt : Real.sqrt (depth : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdepthReal)
  have hcoefficient :
      (depth : ℝ) * sqrtDepthScale amplitude depth =
        amplitude * Real.sqrt depth := by
    unfold sqrtDepthScale
    have hdiv :
        (depth : ℝ) / Real.sqrt depth = Real.sqrt depth := by
      apply (div_eq_iff hsqrt).2
      nlinarith [Real.sq_sqrt (le_of_lt hdepthReal)]
    calc
      (depth : ℝ) * (amplitude / Real.sqrt depth) =
          amplitude * ((depth : ℝ) / Real.sqrt depth) := by ring
      _ = amplitude * Real.sqrt depth := by rw [hdiv]
  rw [aligned_residualEffect_eq, norm_smul, hdirection, mul_one,
    Real.norm_eq_abs, sq_abs, hcoefficient]
  nlinarith [Real.sq_sqrt (le_of_lt hdepthReal)]

/-- Under `1 / depth` scaling, fully aligned unit directions have exactly
depth-independent squared effect norm. -/
theorem inverseDepthScale_aligned_norm_sq
    {depth : ℕ} {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (direction : State) (amplitude : ℝ) (hdepth : 0 < depth)
    (hdirection : ‖direction‖ = 1) :
    ‖residualEffect (fun _ : Fin depth => direction)
        (fun _ : Fin depth => inverseDepthScale amplitude depth)‖ ^ 2 =
      amplitude ^ 2 := by
  have hdepthNe : (depth : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdepth)
  rw [aligned_residualEffect_eq, inverseDepthScale]
  have hcoefficient :
      (depth : ℝ) * (amplitude / depth) = amplitude := by
    field_simp
  rw [hcoefficient, norm_smul, hdirection, mul_one, Real.norm_eq_abs,
    sq_abs]

/-- Once depth exceeds one, no uniform scalar coefficient gives unit
quadratic budget and unit fully aligned squared coefficient simultaneously. -/
theorem no_scalar_depthScale_preserves_both_geometries
    {depth : ℕ} (hdepth : 1 < depth) :
    ¬ ∃ coefficient : ℝ,
      residualQuadraticBudget
          (fun _ : Fin depth => coefficient) = 1 ∧
        ((depth : ℝ) * coefficient) ^ 2 = 1 := by
  rintro ⟨coefficient, horthogonal, haligned⟩
  have hdepthReal : (1 : ℝ) < depth := by
    exact_mod_cast hdepth
  have horthogonal' :
      (depth : ℝ) * coefficient ^ 2 = 1 := by
    simpa using horthogonal
  nlinarith

/-- At depth four, unit-amplitude square-root scaling has unit orthogonal
budget but aligned squared coefficient four. -/
theorem depthFour_sqrtScale_geometry_separation :
    residualQuadraticBudget
        (fun _ : Fin 4 => sqrtDepthScale 1 4) = 1 ∧
      ((4 : ℝ) * sqrtDepthScale 1 4) ^ 2 = 4 := by
  constructor
  · simpa using sqrtDepthScale_quadraticBudget 4 1 (by norm_num)
  · have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    change ((4 : ℝ) * (1 / Real.sqrt (4 : ℝ))) ^ 2 = 4
    rw [hsqrt]
    norm_num

#print axioms orthonormal_residualEffect_norm_sq_eq
#print axioms sqrtDepthScale_quadraticBudget
#print axioms inverseDepthScale_quadraticBudget
#print axioms aligned_residualEffect_eq
#print axioms sqrtDepthScale_aligned_norm_sq
#print axioms inverseDepthScale_aligned_norm_sq
#print axioms no_scalar_depthScale_preserves_both_geometries
#print axioms depthFour_sqrtScale_geometry_separation

end

end DepthwiseResidualScaling

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
