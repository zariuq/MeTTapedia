import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.EncoderEquivariance
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CompositionalJacobianBounds
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SpectralPolynomialAcceleration

/-!
# Regional derivative budgets for SiLU transitions

The registered deep residual adapter uses an affine layer followed by
coordinatewise SiLU at every hidden site.  This file proves the scalar
analytic core and then lifts it to finite Euclidean hidden states.  On a ball
of radius `a`, SiLU has derivative norm at most `1 + a / 4` and
derivative-variation rate at most `1 / 2 + a / 4`.  The final sections
transport those bounds through affine layers.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SiLUTransitionBounds

open Set
open Filter
open CompositionalJacobianBounds
open SpectralPolynomialAcceleration

noncomputable section

/-! ## Scalar SiLU and its two derivatives -/

/-- Exact scalar form of `torch.nn.functional.silu`. -/
def sourceSiLU (value : ℝ) : ℝ :=
  value * Real.sigmoid value

/-- The analytic first derivative of SiLU. -/
def sourceSiLUDerivative (value : ℝ) : ℝ :=
  Real.sigmoid value +
    value * (Real.sigmoid value * (1 - Real.sigmoid value))

/-- The analytic second derivative of SiLU. -/
def sourceSiLUSecondDerivative (value : ℝ) : ℝ :=
  (Real.sigmoid value * (1 - Real.sigmoid value)) *
    (2 + value * (1 - 2 * Real.sigmoid value))

/-- The source-shaped multiplicative form equals the encoder's existing
division form. -/
theorem sourceSiLU_eq_encoderSiLU (value : ℝ) :
    sourceSiLU value =
      Mettapedia.MachineLearning.NeuralNetworks.Architecture.silu value := by
  simp [sourceSiLU,
    Mettapedia.MachineLearning.NeuralNetworks.Architecture.silu,
    Real.sigmoid_def, div_eq_mul_inv]

theorem sourceSiLU_hasDerivAt (value : ℝ) :
    HasDerivAt sourceSiLU (sourceSiLUDerivative value) value := by
  have h := (hasDerivAt_id value).mul (Real.hasDerivAt_sigmoid value)
  have heq : (fun x : ℝ => x * Real.sigmoid x) =ᶠ[nhds value]
      (id * Real.sigmoid) := Eventually.of_forall fun _ => rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv
    (by simp [sourceSiLUDerivative])

theorem sourceSiLUDerivative_hasDerivAt (value : ℝ) :
    HasDerivAt sourceSiLUDerivative (sourceSiLUSecondDerivative value) value := by
  let sigmoidDerivative :=
    Real.sigmoid value * (1 - Real.sigmoid value)
  have hsigmoid := Real.hasDerivAt_sigmoid value
  have honeMinus : HasDerivAt (fun x : ℝ => 1 - Real.sigmoid x)
      (-sigmoidDerivative) value := by
    change HasDerivAt ((fun _ : ℝ => 1) - Real.sigmoid)
      (-sigmoidDerivative) value
    simpa [sigmoidDerivative] using
      (hasDerivAt_const value (1 : ℝ)).sub hsigmoid
  have hproduct : HasDerivAt
      (fun x : ℝ => Real.sigmoid x * (1 - Real.sigmoid x))
      (sigmoidDerivative * (1 - 2 * Real.sigmoid value)) value := by
    have hraw := hsigmoid.mul honeMinus
    have heq :
        (fun x : ℝ => Real.sigmoid x * (1 - Real.sigmoid x)) =ᶠ[nhds value]
          (Real.sigmoid * fun x : ℝ => 1 - Real.sigmoid x) :=
      Eventually.of_forall fun _ => rfl
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by
      dsimp [sigmoidDerivative]
      ring)
  have h := hsigmoid.add ((hasDerivAt_id value).mul hproduct)
  have heq :
      (fun x : ℝ => Real.sigmoid x +
        x * (Real.sigmoid x * (1 - Real.sigmoid x))) =ᶠ[nhds value]
        (Real.sigmoid + id *
          fun x : ℝ => Real.sigmoid x * (1 - Real.sigmoid x)) :=
    Eventually.of_forall fun _ => rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by
    dsimp [sigmoidDerivative]
    simp [sourceSiLUSecondDerivative]
    ring)

private theorem sigmoidProduct_nonneg (value : ℝ) :
    0 ≤ Real.sigmoid value * (1 - Real.sigmoid value) :=
  mul_nonneg (Real.sigmoid_nonneg value)
    (sub_nonneg.mpr (Real.sigmoid_le_one value))

private theorem sigmoidProduct_le_quarter (value : ℝ) :
    Real.sigmoid value * (1 - Real.sigmoid value) ≤ (1 / 4 : ℝ) := by
  nlinarith [sq_nonneg (Real.sigmoid value - (1 / 2 : ℝ))]

private theorem abs_one_sub_two_sigmoid_le_one (value : ℝ) :
    |1 - 2 * Real.sigmoid value| ≤ (1 : ℝ) := by
  rw [abs_le]
  constructor <;> nlinarith [Real.sigmoid_nonneg value,
    Real.sigmoid_le_one value]

/-! ## Regional scalar bounds -/

/-- On a symmetric interval, the absolute SiLU derivative is bounded by
`1 + radius / 4`. -/
theorem abs_sourceSiLUDerivative_le
    {radius value : ℝ} (hradius : 0 ≤ radius) (hvalue : |value| ≤ radius) :
    |sourceSiLUDerivative value| ≤ 1 + radius / 4 := by
  let d := Real.sigmoid value * (1 - Real.sigmoid value)
  have hd0 : 0 ≤ d := sigmoidProduct_nonneg value
  have hd4 : d ≤ (1 / 4 : ℝ) := sigmoidProduct_le_quarter value
  have hs0 : 0 ≤ Real.sigmoid value := Real.sigmoid_nonneg value
  have hs1 : Real.sigmoid value ≤ 1 := Real.sigmoid_le_one value
  calc
    |sourceSiLUDerivative value| = |Real.sigmoid value + value * d| := by
      rfl
    _ ≤ |Real.sigmoid value| + |value * d| := abs_add_le _ _
    _ = Real.sigmoid value + |value| * d := by
      rw [abs_of_nonneg hs0, abs_mul, abs_of_nonneg hd0]
    _ ≤ 1 + radius / 4 := by nlinarith

/-- On a symmetric interval, the absolute SiLU second derivative is bounded
by `1/2 + radius/4`. -/
theorem abs_sourceSiLUSecondDerivative_le
    {radius value : ℝ} (hradius : 0 ≤ radius) (hvalue : |value| ≤ radius) :
    |sourceSiLUSecondDerivative value| ≤ 1 / 2 + radius / 4 := by
  let d := Real.sigmoid value * (1 - Real.sigmoid value)
  have hd0 : 0 ≤ d := sigmoidProduct_nonneg value
  have hd4 : d ≤ (1 / 4 : ℝ) := sigmoidProduct_le_quarter value
  have hfactor : |1 - 2 * Real.sigmoid value| ≤ (1 : ℝ) :=
    abs_one_sub_two_sigmoid_le_one value
  have hinner : |2 + value * (1 - 2 * Real.sigmoid value)| ≤ 2 + radius := by
    calc
      |2 + value * (1 - 2 * Real.sigmoid value)| ≤
          |(2 : ℝ)| + |value * (1 - 2 * Real.sigmoid value)| := abs_add_le _ _
      _ = 2 + |value| * |1 - 2 * Real.sigmoid value| := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_mul]
      _ ≤ 2 + radius := by
        have hmul := mul_le_mul hvalue hfactor (abs_nonneg _) hradius
        nlinarith
  calc
    |sourceSiLUSecondDerivative value| =
        d * |2 + value * (1 - 2 * Real.sigmoid value)| := by
      rw [sourceSiLUSecondDerivative, abs_mul, abs_of_nonneg hd0]
    _ ≤ (1 / 4 : ℝ) * (2 + radius) := by
      exact mul_le_mul hd4 hinner (abs_nonneg _) (by positivity)
    _ = 1 / 2 + radius / 4 := by ring

/-- Symmetric scalar certification region. -/
def scalarRegion (radius value : ℝ) : Prop :=
  |value| ≤ radius

/-- The declared scalar Jacobian of SiLU. -/
def sourceSiLUJacobian (value : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (sourceSiLUDerivative value)

theorem sourceSiLUJacobian_hasFDerivAt (value : ℝ) :
    HasFDerivAt sourceSiLU (sourceSiLUJacobian value) value := by
  simpa [sourceSiLUJacobian] using (sourceSiLU_hasDerivAt value).hasFDerivAt

private theorem scalarRegion_mem_Icc
    {radius value : ℝ} (hvalue : scalarRegion radius value) :
    value ∈ Icc (-radius) radius := by
  simpa [scalarRegion, abs_le] using hvalue

/-- Complete scalar regional budget for SiLU. -/
def sourceSiLUBudget (radius : ℝ) (hradius : 0 ≤ radius) :
    RegionalJacobianBudget sourceSiLU sourceSiLUJacobian
      (scalarRegion radius) (1 + radius / 4) (1 + radius / 4)
      (1 / 2 + radius / 4) where
  rate_nonneg := by positivity
  operatorBound_nonneg := by positivity
  variation_nonneg := by positivity
  hasFDerivAt_on_domain := by
    intro value _
    exact sourceSiLUJacobian_hasFDerivAt value
  map_pair_bound := by
    intro left right hleft hright
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := sourceSiLU) (s := Icc (-radius) radius)
      (x := right) (y := left) (C := 1 + radius / 4)
      (fun value _ => (sourceSiLU_hasDerivAt value).differentiableAt)
      (fun value hvalue => by
        rw [(sourceSiLU_hasDerivAt value).deriv, Real.norm_eq_abs]
        exact abs_sourceSiLUDerivative_le hradius
          (by simpa [abs_le] using hvalue))
      (convex_Icc _ _) (scalarRegion_mem_Icc hright)
      (scalarRegion_mem_Icc hleft)
    exact h
  jacobian_norm_bound := by
    intro value hvalue
    rw [sourceSiLUJacobian, ContinuousLinearMap.norm_toSpanSingleton,
      Real.norm_eq_abs]
    exact abs_sourceSiLUDerivative_le hradius hvalue
  jacobian_pair_bound := by
    intro left right hleft hright
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := sourceSiLUDerivative) (s := Icc (-radius) radius)
      (x := right) (y := left) (C := 1 / 2 + radius / 4)
      (fun value _ => (sourceSiLUDerivative_hasDerivAt value).differentiableAt)
      (fun value hvalue => by
        rw [(sourceSiLUDerivative_hasDerivAt value).deriv, Real.norm_eq_abs]
        exact abs_sourceSiLUSecondDerivative_le hradius
          (by simpa [abs_le] using hvalue))
      (convex_Icc _ _) (scalarRegion_mem_Icc hright)
      (scalarRegion_mem_Icc hleft)
    have hjacobian :
        sourceSiLUJacobian left - sourceSiLUJacobian right =
          ContinuousLinearMap.toSpanSingleton ℝ
            (sourceSiLUDerivative left - sourceSiLUDerivative right) := by
      ext
      simp [sourceSiLUJacobian]
    rw [hjacobian, ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
    simpa [Real.norm_eq_abs] using h

/-! ## Scalar affine transition -/

/-- Scalar affine layer, written with the same linear-plus-bias decomposition
used by the source. -/
def scalarAffine (linear : ℝ →L[ℝ] ℝ) (bias input : ℝ) : ℝ :=
  linear input + bias

/-- A closed input ball maps into a certified symmetric preactivation
interval. -/
theorem scalarAffine_mem_region
    (linear : ℝ →L[ℝ] ℝ) (bias center radius input : ℝ)
    (hinput : ‖input - center‖ ≤ radius) :
    scalarRegion (‖linear‖ * (‖center‖ + radius) + ‖bias‖)
      (scalarAffine linear bias input) := by
  have hinputNorm : ‖input‖ ≤ ‖center‖ + radius := by
    calc
      ‖input‖ = ‖(input - center) + center‖ := by ring_nf
      _ ≤ ‖input - center‖ + ‖center‖ := norm_add_le _ _
      _ ≤ ‖center‖ + radius := by linarith
  have hlinear := linear.le_opNorm input
  rw [scalarRegion, ← Real.norm_eq_abs]
  calc
    ‖scalarAffine linear bias input‖ ≤ ‖linear input‖ + ‖bias‖ :=
      norm_add_le _ _
    _ ≤ ‖linear‖ * ‖input‖ + ‖bias‖ := by linarith
    _ ≤ ‖linear‖ * (‖center‖ + radius) + ‖bias‖ := by
      gcongr

/-- Regional `R/J/H` budget for a scalar affine-SiLU transition.  The bias
only determines the certified preactivation radius; the derivative bounds
depend on the affine linear part. -/
def scalarAffineSiLUBudget
    (linear : ℝ →L[ℝ] ℝ) (bias center radius : ℝ) (hradius : 0 ≤ radius) :
    RegionalJacobianBudget
      (composeMap sourceSiLU (scalarAffine linear bias))
      (composeJacobian sourceSiLUJacobian (scalarAffine linear bias)
        (fun _ => linear))
      (fun input => ‖input - center‖ ≤ radius)
      ((1 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) * ‖linear‖)
      ((1 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) * ‖linear‖)
      ((1 / 2 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) *
        ‖linear‖ * ‖linear‖) := by
  let preactivationRadius := ‖linear‖ * (‖center‖ + radius) + ‖bias‖
  have hpreactivationRadius : 0 ≤ preactivationRadius := by
    dsimp [preactivationRadius]
    positivity
  let affineBudget : RegionalJacobianBudget
      (scalarAffine linear bias) (fun _ => linear)
      (fun input : ℝ => ‖input - center‖ ≤ radius)
      ‖linear‖ ‖linear‖ 0 := {
    rate_nonneg := norm_nonneg _
    operatorBound_nonneg := norm_nonneg _
    variation_nonneg := by norm_num
    hasFDerivAt_on_domain := by
      intro input _
      have h := (linear.hasFDerivAt (x := input)).add_const bias
      have heq : scalarAffine linear bias =ᶠ[nhds input]
          (fun x => linear x + bias) := Eventually.of_forall fun _ => rfl
      exact h.congr_of_eventuallyEq heq
    map_pair_bound := by
      intro left right _ _
      rw [show scalarAffine linear bias left - scalarAffine linear bias right =
          linear (left - right) by simp [scalarAffine, map_sub]]
      exact linear.le_opNorm (left - right)
    jacobian_norm_bound := by simp
    jacobian_pair_bound := by simp
  }
  have hmapsInto : ∀ input, ‖input - center‖ ≤ radius →
      scalarRegion preactivationRadius (scalarAffine linear bias input) := by
    intro input hinput
    exact scalarAffine_mem_region linear bias center radius input hinput
  have composed :=
    (sourceSiLUBudget preactivationRadius hpreactivationRadius).comp
      affineBudget hmapsInto
  simpa only [preactivationRadius, affineBudget, mul_zero, zero_mul,
    add_zero] using composed

/-! ## Coordinatewise SiLU on finite Euclidean hidden states -/

variable {Index : Type*} [Fintype Index]

/-- The finite Euclidean hidden-state space used by the source adapter. -/
abbrev HiddenState (Index : Type*) [Fintype Index] :=
  EuclideanSpace ℝ Index

/-- Diagonal continuous linear map in Euclidean coordinates. -/
noncomputable def diagonalMap (coefficient : Index → ℝ) :
    HiddenState Index →L[ℝ] HiddenState Index :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Index => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun index =>
      ContinuousLinearMap.toSpanSingleton ℝ (coefficient index) ∘L
        PiLp.proj 2 (fun _ : Index => ℝ) index)

@[simp] theorem diagonalMap_apply
    (coefficient : Index → ℝ) (state : HiddenState Index) (index : Index) :
    diagonalMap coefficient state index = coefficient index * state index := by
  simp [diagonalMap, mul_comm]

/-- A pointwise multiplier bound is an operator-norm bound for the diagonal
map in Euclidean norm. -/
theorem diagonalMap_norm_le
    (coefficient : Index → ℝ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ index, |coefficient index| ≤ bound) :
    ‖diagonalMap coefficient‖ ≤ bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ hbound
  intro state
  have h := diagonalMultiplier_norm_le coefficient bound hbound
    hcoefficient state
  have heq :
      diagonalMap coefficient state =
        WithLp.toLp 2 (fun index => coefficient index * state index) := by
    ext index
    simp
  rw [heq]
  exact h

/-- Operator norm of a difference of diagonal maps. -/
theorem diagonalMap_sub_norm_le
    (left right : Index → ℝ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ index, |left index - right index| ≤ bound) :
    ‖diagonalMap left - diagonalMap right‖ ≤ bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ hbound
  intro state
  have h := diagonalMultiplier_norm_le (fun index => left index - right index)
    bound hbound hcoefficient state
  have heq :
      (diagonalMap left - diagonalMap right) state =
        WithLp.toLp 2 (fun index =>
          (left index - right index) * state index) := by
    ext index
    simp [sub_mul]
  rw [heq]
  exact h

/-- Coordinatewise SiLU on a finite Euclidean hidden state. -/
noncomputable def vectorSiLU (state : HiddenState Index) : HiddenState Index :=
  WithLp.toLp 2 fun index => sourceSiLU (state index)

/-- Exact diagonal Jacobian of coordinatewise SiLU. -/
noncomputable def vectorSiLUJacobian (state : HiddenState Index) :
    HiddenState Index →L[ℝ] HiddenState Index :=
  diagonalMap fun index => sourceSiLUDerivative (state index)

theorem vectorSiLU_hasFDerivAt (state : HiddenState Index) :
    HasFDerivAt vectorSiLU (vectorSiLUJacobian state) state := by
  unfold vectorSiLU vectorSiLUJacobian diagonalMap
  apply (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp state
  rw [hasFDerivAt_pi]
  intro index
  exact (sourceSiLU_hasDerivAt (state index)).hasFDerivAt.comp state
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 state index)

/-- Closed Euclidean ball used as a hidden-state certification region. -/
def vectorRegion (radius : ℝ) (state : HiddenState Index) : Prop :=
  ‖state‖ ≤ radius

private theorem coordinate_abs_le_norm
    (state : HiddenState Index) (index : Index) :
    |state index| ≤ ‖state‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le state index

private theorem abs_sourceSiLUDerivative_sub_le
    {radius left right : ℝ} (hradius : 0 ≤ radius)
    (hleft : |left| ≤ radius) (hright : |right| ≤ radius) :
    |sourceSiLUDerivative left - sourceSiLUDerivative right| ≤
      (1 / 2 + radius / 4) * |left - right| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := sourceSiLUDerivative) (s := Icc (-radius) radius)
    (x := right) (y := left) (C := 1 / 2 + radius / 4)
    (fun value _ => (sourceSiLUDerivative_hasDerivAt value).differentiableAt)
    (fun value hvalue => by
      rw [(sourceSiLUDerivative_hasDerivAt value).deriv, Real.norm_eq_abs]
      exact abs_sourceSiLUSecondDerivative_le hradius
        (by simpa [abs_le] using hvalue))
    (convex_Icc _ _) (by simpa [abs_le] using hright)
    (by simpa [abs_le] using hleft)
  simpa [Real.norm_eq_abs] using h

/-- Complete regional `R/J/H` budget for coordinatewise SiLU on a finite
Euclidean hidden state. -/
noncomputable def vectorSiLUBudget (radius : ℝ) (hradius : 0 ≤ radius) :
    RegionalJacobianBudget (vectorSiLU (Index := Index))
      (vectorSiLUJacobian (Index := Index))
      (vectorRegion radius) (1 + radius / 4) (1 + radius / 4)
      (1 / 2 + radius / 4) where
  rate_nonneg := by positivity
  operatorBound_nonneg := by positivity
  variation_nonneg := by positivity
  hasFDerivAt_on_domain := by
    intro state _
    exact vectorSiLU_hasFDerivAt state
  map_pair_bound := by
    intro left right hleft hright
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := vectorSiLU) (s := Metric.closedBall (0 : HiddenState Index) radius)
      (x := right) (y := left) (C := 1 + radius / 4)
      (fun state _ => (vectorSiLU_hasFDerivAt state).differentiableAt)
      (fun state hstate => by
        rw [(vectorSiLU_hasFDerivAt state).fderiv]
        apply diagonalMap_norm_le _ (by positivity)
        intro index
        apply abs_sourceSiLUDerivative_le hradius
        exact (coordinate_abs_le_norm state index).trans
          (by simpa [Metric.mem_closedBall, dist_zero_right] using hstate))
      (convex_closedBall _ _) (by
        simpa [vectorRegion, Metric.mem_closedBall, dist_zero_right] using hright)
      (by simpa [vectorRegion, Metric.mem_closedBall, dist_zero_right] using hleft)
    exact h
  jacobian_norm_bound := by
    intro state hstate
    apply diagonalMap_norm_le _ (by positivity)
    intro index
    exact abs_sourceSiLUDerivative_le hradius
      ((coordinate_abs_le_norm state index).trans hstate)
  jacobian_pair_bound := by
    intro left right hleft hright
    apply diagonalMap_sub_norm_le _ _ (mul_nonneg (by positivity) (norm_nonneg _))
    intro index
    have hcoordinate := abs_sourceSiLUDerivative_sub_le hradius
      ((coordinate_abs_le_norm left index).trans hleft)
      ((coordinate_abs_le_norm right index).trans hright)
    calc
      |sourceSiLUDerivative (left index) -
          sourceSiLUDerivative (right index)|
          ≤ (1 / 2 + radius / 4) * |left index - right index| := hcoordinate
      _ ≤ (1 / 2 + radius / 4) * ‖left - right‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.norm_eq_abs]
        simpa only [PiLp.sub_apply] using
          (PiLp.norm_apply_le (left - right) index)

/-! ## Affine-coordinatewise-SiLU hidden transitions -/

/-- Affine hidden-state transition before coordinatewise SiLU. -/
def vectorAffine
    (linear : HiddenState Index →L[ℝ] HiddenState Index)
    (bias input : HiddenState Index) : HiddenState Index :=
  linear input + bias

theorem vectorAffine_mem_region
    (linear : HiddenState Index →L[ℝ] HiddenState Index)
    (bias center : HiddenState Index) (radius : ℝ)
    (input : HiddenState Index) (hinput : ‖input - center‖ ≤ radius) :
    vectorRegion (‖linear‖ * (‖center‖ + radius) + ‖bias‖)
      (vectorAffine linear bias input) := by
  have hinputNorm : ‖input‖ ≤ ‖center‖ + radius := by
    calc
      ‖input‖ = ‖(input - center) + center‖ := by congr 1; abel
      _ ≤ ‖input - center‖ + ‖center‖ := norm_add_le _ _
      _ ≤ ‖center‖ + radius := by linarith
  have hlinear := linear.le_opNorm input
  rw [vectorRegion]
  calc
    ‖vectorAffine linear bias input‖ ≤ ‖linear input‖ + ‖bias‖ :=
      norm_add_le _ _
    _ ≤ ‖linear‖ * ‖input‖ + ‖bias‖ := by linarith
    _ ≤ ‖linear‖ * (‖center‖ + radius) + ‖bias‖ := by gcongr

/-- Regional `R/J/H` budget for the actual affine-coordinatewise-SiLU shape
of every hidden transition in the registered deep error-coordinate adapter. -/
noncomputable def vectorAffineSiLUBudget
    (linear : HiddenState Index →L[ℝ] HiddenState Index)
    (bias center : HiddenState Index) (radius : ℝ) (hradius : 0 ≤ radius) :
    RegionalJacobianBudget
      (composeMap (vectorSiLU (Index := Index)) (vectorAffine linear bias))
      (composeJacobian (vectorSiLUJacobian (Index := Index))
        (vectorAffine linear bias)
        (fun _ => linear))
      (fun input => ‖input - center‖ ≤ radius)
      ((1 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) * ‖linear‖)
      ((1 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) * ‖linear‖)
      ((1 / 2 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) *
        ‖linear‖ * ‖linear‖) := by
  let preactivationRadius :=
    ‖linear‖ * (‖center‖ + radius) + ‖bias‖
  have hpreactivationRadius : 0 ≤ preactivationRadius := by
    dsimp [preactivationRadius]
    positivity
  let affineBudget : RegionalJacobianBudget
      (vectorAffine linear bias) (fun _ => linear)
      (fun input : HiddenState Index => ‖input - center‖ ≤ radius)
      ‖linear‖ ‖linear‖ 0 := {
    rate_nonneg := norm_nonneg _
    operatorBound_nonneg := norm_nonneg _
    variation_nonneg := by norm_num
    hasFDerivAt_on_domain := by
      intro input _
      have h := (linear.hasFDerivAt (x := input)).add_const bias
      have heq : vectorAffine linear bias =ᶠ[nhds input]
          (fun x => linear x + bias) := Eventually.of_forall fun _ => rfl
      exact h.congr_of_eventuallyEq heq
    map_pair_bound := by
      intro left right _ _
      rw [show vectorAffine linear bias left - vectorAffine linear bias right =
          linear (left - right) by simp [vectorAffine, map_sub]]
      exact linear.le_opNorm (left - right)
    jacobian_norm_bound := by simp
    jacobian_pair_bound := by simp
  }
  have hmapsInto : ∀ input, ‖input - center‖ ≤ radius →
      vectorRegion preactivationRadius (vectorAffine linear bias input) := by
    intro input hinput
    exact vectorAffine_mem_region linear bias center radius input hinput
  have composed :=
    (vectorSiLUBudget (Index := Index) preactivationRadius
      hpreactivationRadius).comp
      affineBudget hmapsInto
  simpa only [preactivationRadius, affineBudget, mul_zero, zero_mul,
    add_zero] using composed

/-! ## Source-shaped node masks -/

/-- Coordinate projection induced by a Boolean-shaped node mask.  Flattening
node and feature axes makes the source multiplication by `node_mask` exactly
such a zero-one diagonal map. -/
noncomputable def maskProjection
    (mask : Index → Prop) [DecidablePred mask] :
    HiddenState Index →L[ℝ] HiddenState Index :=
  diagonalMap fun index => if mask index then 1 else 0

@[simp] theorem maskProjection_apply
    (mask : Index → Prop) [DecidablePred mask]
    (state : HiddenState Index) (index : Index) :
    maskProjection mask state index = if mask index then state index else 0 := by
  by_cases h : mask index <;> simp [maskProjection, h]

theorem maskProjection_norm_le_one
    (mask : Index → Prop) [DecidablePred mask] :
    ‖maskProjection mask‖ ≤ 1 := by
  apply diagonalMap_norm_le _ (by norm_num)
  intro index
  by_cases h : mask index <;> simp [h]

/-- Exact source-shaped hidden transition: affine layer, coordinatewise SiLU,
then zero-one node masking. -/
noncomputable def maskedAffineSiLU
    (mask : Index → Prop) [DecidablePred mask]
    (linear : HiddenState Index →L[ℝ] HiddenState Index)
    (bias : HiddenState Index) : HiddenState Index → HiddenState Index :=
  composeMap (maskProjection mask)
    (composeMap vectorSiLU (vectorAffine linear bias))

/-- Symbolic Jacobian of `maskedAffineSiLU`. -/
noncomputable def maskedAffineSiLUJacobian
    (mask : Index → Prop) [DecidablePred mask]
    (linear : HiddenState Index →L[ℝ] HiddenState Index)
    (bias : HiddenState Index) :
    HiddenState Index → (HiddenState Index →L[ℝ] HiddenState Index) :=
  composeJacobian (fun _ => maskProjection mask)
    (composeMap vectorSiLU (vectorAffine linear bias))
    (composeJacobian vectorSiLUJacobian (vectorAffine linear bias) (fun _ => linear))

/-- Masking is a nonexpansive affine-free transition with constant Jacobian. -/
noncomputable def maskProjectionBudget
    (mask : Index → Prop) [DecidablePred mask] :
    RegionalJacobianBudget (maskProjection mask) (fun _ => maskProjection mask)
      (fun _ : HiddenState Index => True) 1 1 0 where
  rate_nonneg := by norm_num
  operatorBound_nonneg := by norm_num
  variation_nonneg := by norm_num
  hasFDerivAt_on_domain := by
    intro state _
    exact (maskProjection mask).hasFDerivAt
  map_pair_bound := by
    intro left right _ _
    rw [← map_sub]
    calc
      ‖maskProjection mask (left - right)‖
          ≤ ‖maskProjection mask‖ * ‖left - right‖ :=
        (maskProjection mask).le_opNorm (left - right)
      _ ≤ 1 * ‖left - right‖ := by
        gcongr
        exact maskProjection_norm_le_one mask
  jacobian_norm_bound := by
    intro _ _
    exact maskProjection_norm_le_one mask
  jacobian_pair_bound := by simp

/-- Complete `R/J/H` budget for the source transition
`mask * silu(linear input + bias)`.  The zero-one mask does not increase any
of the affine-SiLU rates. -/
noncomputable def maskedAffineSiLUBudget
    (mask : Index → Prop) [DecidablePred mask]
    (linear : HiddenState Index →L[ℝ] HiddenState Index)
    (bias center : HiddenState Index) (radius : ℝ) (hradius : 0 ≤ radius) :
    RegionalJacobianBudget
      (maskedAffineSiLU mask linear bias)
      (maskedAffineSiLUJacobian mask linear bias)
      (fun input => ‖input - center‖ ≤ radius)
      ((1 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) * ‖linear‖)
      ((1 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) * ‖linear‖)
      ((1 / 2 + (‖linear‖ * (‖center‖ + radius) + ‖bias‖) / 4) *
        ‖linear‖ * ‖linear‖) := by
  have hmapsInto : ∀ output,
      ‖output - center‖ ≤ radius → True := by simp
  have composed := (maskProjectionBudget mask).comp
    (vectorAffineSiLUBudget linear bias center radius hradius) hmapsInto
  simpa only [maskedAffineSiLU, maskedAffineSiLUJacobian, composeMap,
    composeJacobian, one_mul, zero_mul, zero_add] using composed

/-! ## Positive and negative fixtures -/

/-- At zero preactivation the exact SiLU derivative is one half. -/
theorem sourceSiLUDerivative_zero :
    sourceSiLUDerivative 0 = 1 / 2 := by
  norm_num [sourceSiLUDerivative, Real.sigmoid_zero]

/-- Positive precision or a finite linear norm cannot make SiLU affine: the
derivative changes between zero and one. -/
theorem sourceSiLU_not_affine_derivative :
    sourceSiLUDerivative 0 ≠ sourceSiLUDerivative 1 := by
  intro h
  have hspos := Real.sigmoid_pos (1 : ℝ)
  have hslt := Real.sigmoid_lt_one (1 : ℝ)
  have hsHalf : (1 / 2 : ℝ) < Real.sigmoid 1 := by
    simpa [one_div] using
      (Real.sigmoid_strictMono (show (0 : ℝ) < 1 by norm_num))
  rw [sourceSiLUDerivative_zero] at h
  dsimp [sourceSiLUDerivative] at h
  nlinarith

#print axioms sourceSiLUBudget
#print axioms scalarAffineSiLUBudget
#print axioms vectorSiLUBudget
#print axioms vectorAffineSiLUBudget
#print axioms maskProjectionBudget
#print axioms maskedAffineSiLUBudget
#print axioms sourceSiLU_not_affine_derivative

end

end SiLUTransitionBounds

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
