import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualContinuation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.BroadcastProxy

/-!
# Directional task-descent certificates for approximate credit

A norm bound on credit error is a conservative route to task descent, but it
can reject useful directions whose error lies in a low-curvature subspace.
This file first derives the norm certificate from the existing four-part
credit-error budget, then states the sharper finite-step condition in terms of
the actual first-order margin and a directional second-order upper model.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace DirectionalTaskDescent

open scoped InnerProductSpace
open PrimalDualContinuation

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- A smooth task upper model along every declared direction. -/
def HasSmoothTaskUpperModelAt
    (loss : Parameter → ℝ) (parameter gradient : Parameter) (beta : ℝ) : Prop :=
  ∀ direction step, 0 ≤ step →
    loss (parameter - step • direction) ≤
      loss parameter - step * ⟪gradient, direction⟫_ℝ +
        beta * step ^ 2 * ‖direction‖ ^ 2 / 2

/-- A sharper upper model along one direction.  `curvature` bounds the
second-order coefficient only on this line; it need not be a global
smoothness constant times the squared direction norm. -/
def HasDirectionalTaskUpperModelAt
    (loss : Parameter → ℝ) (parameter gradient direction : Parameter)
    (curvature : ℝ) : Prop :=
  ∀ step, 0 ≤ step →
    loss (parameter - step • direction) ≤
      loss parameter - step * ⟪gradient, direction⟫_ℝ +
        step ^ 2 * curvature / 2

/-- Global smoothness supplies a directional curvature certificate with
coefficient `beta * ‖direction‖²`. -/
theorem HasSmoothTaskUpperModelAt.toDirectional
    {loss : Parameter → ℝ} {parameter gradient : Parameter} {beta : ℝ}
    (certificate : HasSmoothTaskUpperModelAt loss parameter gradient beta)
    (direction : Parameter) :
    HasDirectionalTaskUpperModelAt loss parameter gradient direction
      (beta * ‖direction‖ ^ 2) := by
  intro step hstep
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    certificate direction step hstep

/-- Algebraic heart of the trust-region certificate: the quadratic remainder
must be strictly smaller than the first-order task margin. -/
theorem strict_descent_of_directional_quadratic_upper
    {current next step alignment curvature : ℝ}
    (hupper :
      next ≤ current - step * alignment + step ^ 2 * curvature / 2)
    (hstep : 0 < step)
    (htrust : step * curvature / 2 < alignment) :
    next < current := by
  have hscaled := mul_lt_mul_of_pos_left htrust hstep
  nlinarith

/-- A positive directional task margin plus its finite-step curvature budget
gives strict task descent. -/
theorem directionalTask_strict_descent
    {loss : Parameter → ℝ} {parameter gradient direction : Parameter}
    {curvature step : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter gradient direction
        curvature)
    (hstep : 0 < step)
    (htrust : step * curvature / 2 < ⟪gradient, direction⟫_ℝ) :
    loss (parameter - step • direction) < loss parameter := by
  exact strict_descent_of_directional_quadratic_upper
    (certificate step hstep.le) hstep htrust

/-- For positive curvature, the familiar directional trust radius is
`2 * alignment / curvature`. -/
theorem directionalTask_strict_descent_of_step_lt_radius
    {loss : Parameter → ℝ} {parameter gradient direction : Parameter}
    {curvature step : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter gradient direction
        curvature)
    (hcurvature : 0 < curvature) (hstep : 0 < step)
    (hstepRadius :
      step < 2 * ⟪gradient, direction⟫_ℝ / curvature) :
    loss (parameter - step • direction) < loss parameter := by
  apply directionalTask_strict_descent certificate hstep
  have hscaled := (lt_div_iff₀ hcurvature).mp hstepRadius
  nlinarith

/-- A nonpositive directional curvature upper bound needs no finite upper
step radius once the first-order margin is positive. -/
theorem directionalTask_strict_descent_of_nonpos_curvature
    {loss : Parameter → ℝ} {parameter gradient direction : Parameter}
    {curvature step : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter gradient direction
        curvature)
    (hcurvature : curvature ≤ 0) (hstep : 0 < step)
    (halignment : 0 < ⟪gradient, direction⟫_ℝ) :
    loss (parameter - step • direction) < loss parameter := by
  apply directionalTask_strict_descent certificate hstep
  have hnonpos : step * curvature / 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hstep.le hcurvature) (by norm_num)
  linarith

/-! ## Conservative norm route -/

/-- An approximate direction's task alignment is bounded below by the exact
gradient norm and its norm error. -/
theorem approximateDirection_inner_lower
    (gradient approximate : Parameter) (error : ℝ)
    (herror : ‖approximate - gradient‖ ≤ error) :
    ‖gradient‖ * (‖gradient‖ - error) ≤
      ⟪gradient, approximate⟫_ℝ := by
  have hdecompose :
      approximate = gradient + (approximate - gradient) := by
    abel
  rw [hdecompose, inner_add_right, real_inner_self_eq_norm_sq]
  have hcauchy :
      -(‖gradient‖ * ‖approximate - gradient‖) ≤
        ⟪gradient, approximate - gradient⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hscaled :
      ‖gradient‖ * ‖approximate - gradient‖ ≤ ‖gradient‖ * error :=
    mul_le_mul_of_nonneg_left herror (norm_nonneg _)
  nlinarith

omit [InnerProductSpace ℝ Parameter] in
/-- The same norm-error certificate bounds the approximate direction's size. -/
theorem approximateDirection_norm_le
    (gradient approximate : Parameter) (error : ℝ)
    (herror : ‖approximate - gradient‖ ≤ error) :
    ‖approximate‖ ≤ ‖gradient‖ + error := by
  calc
    ‖approximate‖ = ‖(approximate - gradient) + gradient‖ := by
      congr 1
      abel
    _ ≤ ‖approximate - gradient‖ + ‖gradient‖ := norm_add_le _ _
    _ ≤ error + ‖gradient‖ := add_le_add_left herror _
    _ = ‖gradient‖ + error := by ring

/-- Conservative smooth-task certificate.  Its trust premise uses only the
exact-gradient norm, the credit-error budget, and a global smoothness bound. -/
theorem smoothTask_strict_descent_of_norm_error
    {loss : Parameter → ℝ} {parameter gradient approximate : Parameter}
    {beta error step : ℝ}
    (certificate : HasSmoothTaskUpperModelAt loss parameter gradient beta)
    (herror : ‖approximate - gradient‖ ≤ error)
    (hbeta : 0 ≤ beta) (hstep : 0 < step)
    (hrelative : error < ‖gradient‖)
    (htrust :
      beta * step * (‖gradient‖ + error) ^ 2 / 2 <
        ‖gradient‖ * (‖gradient‖ - error)) :
    loss (parameter - step • approximate) < loss parameter := by
  have herrorNonneg : 0 ≤ error :=
    le_trans (norm_nonneg (approximate - gradient)) herror
  have hsumNonneg : 0 ≤ ‖gradient‖ + error :=
    add_nonneg (norm_nonneg _) herrorNonneg
  have hgradientNormPositive : 0 < ‖gradient‖ :=
    lt_of_le_of_lt herrorNonneg hrelative
  have hmarginPositive :
      0 < ‖gradient‖ * (‖gradient‖ - error) :=
    mul_pos hgradientNormPositive (sub_pos.mpr hrelative)
  have hnorm := approximateDirection_norm_le gradient approximate error herror
  have hnormSq :
      ‖approximate‖ ^ 2 ≤ (‖gradient‖ + error) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsumNonneg).2 hnorm
  have hremainder :
      beta * step * ‖approximate‖ ^ 2 / 2 ≤
        beta * step * (‖gradient‖ + error) ^ 2 / 2 := by
    have hcoefficient : 0 ≤ beta * step / 2 := by positivity
    calc
      beta * step * ‖approximate‖ ^ 2 / 2 =
          (beta * step / 2) * ‖approximate‖ ^ 2 := by ring
      _ ≤ (beta * step / 2) * (‖gradient‖ + error) ^ 2 :=
        mul_le_mul_of_nonneg_left hnormSq hcoefficient
      _ = beta * step * (‖gradient‖ + error) ^ 2 / 2 := by ring
  have halignment :=
    approximateDirection_inner_lower gradient approximate error herror
  have hactualTrust :
      step * (beta * ‖approximate‖ ^ 2) / 2 <
        ⟪gradient, approximate⟫_ℝ := by
    nlinarith [hmarginPositive]
  exact directionalTask_strict_descent
    (certificate.toDirectional approximate) hstep hactualTrust

/-- The existing four-error decomposition directly feeds the conservative
task-descent certificate; no cosine proxy is introduced. -/
theorem smoothTask_strict_descent_of_four_error_budget
    {loss : Parameter → ℝ}
    (parameter finite settled released tracked reference : Parameter)
    (solveError biasError nonlinearError trackingError beta step : ℝ)
    (certificate : HasSmoothTaskUpperModelAt loss parameter reference beta)
    (hsolve : ‖finite - settled‖ ≤ solveError)
    (hbias : ‖settled - released‖ ≤ biasError)
    (hnonlinear : ‖released - tracked‖ ≤ nonlinearError)
    (htracking : ‖tracked - reference‖ ≤ trackingError)
    (hbeta : 0 ≤ beta) (hstep : 0 < step)
    (hrelative :
      solveError + biasError + nonlinearError + trackingError < ‖reference‖)
    (htrust :
      beta * step *
          (‖reference‖ +
            (solveError + biasError + nonlinearError + trackingError)) ^ 2 /
            2 <
        ‖reference‖ *
          (‖reference‖ -
            (solveError + biasError + nonlinearError + trackingError))) :
    loss (parameter - step • finite) < loss parameter := by
  have htotal := norm_gradientGap_le_four_errors finite settled released
    tracked reference solveError biasError nonlinearError trackingError
    hsolve hbias hnonlinear htracking
  exact smoothTask_strict_descent_of_norm_error certificate htotal hbeta hstep
    hrelative htrust

/-! ## Exact diagonal-Hessian fixtures -/

open Instances

/-- Two-coordinate quadratic with constant diagonal Hessian. -/
noncomputable def diagonalQuadratic
    (firstCurvature secondCurvature : ℝ) (parameter : CreditVec2) : ℝ :=
  (firstCurvature * parameter.first ^ 2 +
    secondCurvature * parameter.second ^ 2) / 2

def diagonalGradient
    (firstCurvature secondCurvature : ℝ) (parameter : CreditVec2) :
    CreditVec2 :=
  ⟨firstCurvature * parameter.first,
    secondCurvature * parameter.second⟩

def diagonalHessianApply
    (firstCurvature secondCurvature : ℝ) (direction : CreditVec2) :
    CreditVec2 :=
  ⟨firstCurvature * direction.first,
    secondCurvature * direction.second⟩

def diagonalDirectionalCurvature
    (firstCurvature secondCurvature : ℝ) (direction : CreditVec2) : ℝ :=
  direction.dot
    (diagonalHessianApply firstCurvature secondCurvature direction)

/-- The directional upper model is an equality for the declared constant
diagonal Hessian. -/
theorem diagonalQuadratic_step_expansion
    (firstCurvature secondCurvature : ℝ)
    (parameter direction : CreditVec2) (step : ℝ) :
    diagonalQuadratic firstCurvature secondCurvature
        (parameter.sub (CreditVec2.scale step direction)) =
      diagonalQuadratic firstCurvature secondCurvature parameter -
        step *
          (diagonalGradient firstCurvature secondCurvature parameter).dot
            direction +
        step ^ 2 *
          diagonalDirectionalCurvature firstCurvature secondCurvature
            direction / 2 := by
  simp [diagonalQuadratic, diagonalGradient, diagonalHessianApply,
    diagonalDirectionalCurvature, CreditVec2.sub, CreditVec2.scale,
    CreditVec2.dot]
  ring

/-- A large error in a Hessian-null coordinate defeats the conservative norm
gate but is harmless to the exact directional certificate. -/
theorem flatSecond_largeOrthogonal_direction_strictly_descends :
    diagonalQuadratic 1 0
        ((⟨1, 0⟩ : CreditVec2).sub
          (CreditVec2.scale 1 (⟨1, 10⟩ : CreditVec2))) <
      diagonalQuadratic 1 0 (⟨1, 0⟩ : CreditVec2) := by
  have hupper :
      diagonalQuadratic 1 0
          ((⟨1, 0⟩ : CreditVec2).sub
            (CreditVec2.scale 1 (⟨1, 10⟩ : CreditVec2))) ≤
        diagonalQuadratic 1 0 (⟨1, 0⟩ : CreditVec2) -
          1 *
            (diagonalGradient 1 0 (⟨1, 0⟩ : CreditVec2)).dot
              (⟨1, 10⟩ : CreditVec2) +
          1 ^ 2 * diagonalDirectionalCurvature 1 0
            (⟨1, 10⟩ : CreditVec2) / 2 := by
    exact (diagonalQuadratic_step_expansion 1 0
      (⟨1, 0⟩ : CreditVec2) (⟨1, 10⟩ : CreditVec2) 1).le
  apply strict_descent_of_directional_quadratic_upper hupper
  · norm_num
  · norm_num [diagonalGradient, diagonalHessianApply,
      diagonalDirectionalCurvature, CreditVec2.dot]

theorem flatSecond_largeOrthogonal_norm_gate_fails :
    ¬ (((⟨1, 10⟩ : CreditVec2).sub
          (diagonalGradient 1 0 (⟨1, 0⟩ : CreditVec2))).normSq <
        (diagonalGradient 1 0 (⟨1, 0⟩ : CreditVec2)).normSq) := by
  norm_num [diagonalGradient, CreditVec2.sub, CreditVec2.normSq,
    CreditVec2.dot]

/-- Positive first-order alignment alone is not a finite-step certificate:
the same exact quadratic ascends when the step crosses its curvature radius. -/
theorem positive_alignment_without_curvature_trust_can_ascend :
    (diagonalGradient 1 0 (⟨1, 0⟩ : CreditVec2)).dot
        (⟨1, 0⟩ : CreditVec2) = 1 ∧
      ¬ (3 * diagonalDirectionalCurvature 1 0
          (⟨1, 0⟩ : CreditVec2) / 2 < 1) ∧
      diagonalQuadratic 1 0
          ((⟨1, 0⟩ : CreditVec2).sub
            (CreditVec2.scale 3 (⟨1, 0⟩ : CreditVec2))) >
        diagonalQuadratic 1 0 (⟨1, 0⟩ : CreditVec2) := by
  norm_num [diagonalQuadratic, diagonalGradient, diagonalHessianApply,
    diagonalDirectionalCurvature, CreditVec2.sub, CreditVec2.scale,
    CreditVec2.dot]

#print axioms strict_descent_of_directional_quadratic_upper
#print axioms directionalTask_strict_descent
#print axioms directionalTask_strict_descent_of_step_lt_radius
#print axioms approximateDirection_inner_lower
#print axioms smoothTask_strict_descent_of_norm_error
#print axioms smoothTask_strict_descent_of_four_error_budget
#print axioms diagonalQuadratic_step_expansion
#print axioms flatSecond_largeOrthogonal_direction_strictly_descends
#print axioms flatSecond_largeOrthogonal_norm_gate_fails
#print axioms positive_alignment_without_curvature_trust_can_ascend

end DirectionalTaskDescent

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
