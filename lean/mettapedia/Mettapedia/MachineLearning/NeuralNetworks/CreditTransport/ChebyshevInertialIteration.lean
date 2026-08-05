import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SpectralPolynomialAcceleration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Algebra.Polynomial.Splits

/-!
# Chebyshev inertial fixed-point iteration

Wadayama and Takabe, *Chebyshev Inertial Iteration for Accelerating
Fixed-Point Iterations* (2020), choose iteration-dependent relaxation factors
from the roots of a Chebyshev polynomial.  The primary PDF has SHA-256
`151cb775835deba7f68320cbb282e7cca1f2847a4e05c561855012960b1cf6aa`.

This file recovers the exact spectral-polynomial core of source Equations
(6)--(27).  Every nonzero relaxation preserves the fixed points of the
original map.  For a positive real spectral interval, the finite root
schedule is proved equal to the normalized Chebyshev residual polynomial.
That polynomial contracts every mode in the interval by one common factor,
yielding a finite-dimensional Hilbert-space contraction certificate and a
geometric cycle bound.

The exact theorem is deliberately restricted to a supplied real diagonal
spectral representation.  The source's nonlinear theorem is local and relies
on the Jacobian linearization remainder becoming negligible.  Two executable
boundaries keep that distinction visible: one Chebyshev factor can expand a
mode even though the complete cycle contracts it, and changing the order of
two inertial factors changes a nonlinear trajectory although it cannot change
the exact linear residual polynomial.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ChebyshevInertialIteration

open Polynomial Polynomial.Chebyshev Real
open AmortizedInitialization
open SpectralPolynomialAcceleration

noncomputable section

/-! ## Fixed-point semantics of inertial relaxation -/

/-- Source Equation (6): relax one fixed-point update by a scalar weight. -/
def inertialStep {State : Type*} [NormedAddCommGroup State]
    [NormedSpace ℝ State]
    (weight : ℝ) (solver : State → State) (state : State) : State :=
  (1 - weight) • state + weight • solver state

/-- Displacement of an inertial step from its input. -/
theorem inertialStep_sub_self {State : Type*} [NormedAddCommGroup State]
    [NormedSpace ℝ State]
    (weight : ℝ) (solver : State → State) (state : State) :
    inertialStep weight solver state - state =
      weight • (solver state - state) := by
  simp [inertialStep, smul_sub]
  module

/-- Source Equation (8): every original fixed point is preserved by every
inertial weight. -/
theorem inertialStep_fixedPoint {State : Type*} [NormedAddCommGroup State]
    [NormedSpace ℝ State]
    (weight : ℝ) (solver : State → State) {state : State}
    (fixed : solver state = state) :
    inertialStep weight solver state = state := by
  rw [← sub_eq_zero, inertialStep_sub_self, fixed, sub_self, smul_zero]

/-- A nonzero inertial weight introduces no additional fixed points. -/
theorem inertialStep_fixedPoint_iff_of_weight_ne_zero
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (weight : ℝ) (weightNonzero : weight ≠ 0)
    (solver : State → State) (state : State) :
    inertialStep weight solver state = state ↔ solver state = state := by
  rw [← sub_eq_zero, inertialStep_sub_self, smul_eq_zero]
  simp [weightNonzero, sub_eq_zero]

/-- The nonzero-weight premise is necessary: weight zero freezes even a
non-fixed state. -/
theorem zero_weight_can_mask_nonfixed :
    inertialStep 0 (fun state : ℝ => state + 1) 0 = 0 ∧
      (fun state : ℝ => state + 1) 0 ≠ 0 := by
  norm_num [inertialStep]

/-! ## The normalized Chebyshev residual polynomial -/

/-- Affine coordinate taking `[lower, upper]` to `[-1, 1]`. -/
def intervalCoordinate (lower upper value : ℝ) : ℝ :=
  (2 * value - upper - lower) / (upper - lower)

/-- Source Equations (24)--(25): the residual polynomial normalized to equal
one at spectral value zero. -/
def chebyshevCycleGain
    (degree : ℕ) (lower upper value : ℝ) : ℝ :=
  (T ℝ degree).eval (intervalCoordinate lower upper value) /
    (T ℝ degree).eval (intervalCoordinate lower upper 0)

/-- Uniform source bound before rewriting it as a hyperbolic secant. -/
def chebyshevCycleBound
    (degree : ℕ) (lower upper : ℝ) : ℝ :=
  1 / |(T ℝ degree).eval (intervalCoordinate lower upper 0)|

theorem intervalCoordinate_mem_Icc
    {lower upper value : ℝ}
    (lowerLtUpper : lower < upper)
    (lowerLeValue : lower ≤ value)
    (valueLeUpper : value ≤ upper) :
    intervalCoordinate lower upper value ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc]
  dsimp [intervalCoordinate]
  constructor
  · rw [le_div_iff₀ (sub_pos.mpr lowerLtUpper)]
    linarith
  · rw [div_le_iff₀ (sub_pos.mpr lowerLtUpper)]
    linarith

theorem intervalCoordinate_zero_lt_neg_one
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper) :
    intervalCoordinate lower upper 0 < -1 := by
  dsimp [intervalCoordinate]
  rw [div_lt_iff₀ (sub_pos.mpr lowerLtUpper)]
  linarith

/-- The real Chebyshev polynomial splits over its explicit cosine roots. -/
theorem chebyshevT_splits_real (degree : ℕ) :
    (T ℝ degree).Splits := by
  rw [Polynomial.splits_iff_card_roots, roots_T_real]
  change
    (Finset.image
        (fun index : ℕ =>
          cos ((2 * index + 1) * π / (2 * degree)))
        (Finset.range degree)).card =
      (T ℝ (degree : ℤ)).natDegree
  rw [Finset.card_image_of_injOn]
  · simp [natDegree_T]
  · exact
      Finset.nodup_map_iff_injOn.mp
        (roots_T_real_nodup degree)

/-- Evaluation of `T_degree` as its leading coefficient times the product of
its explicit real root factors. -/
theorem chebyshevT_eval_eq_leading_mul_rootProduct
    (degree : ℕ) (value : ℝ) :
    (T ℝ degree).eval value =
      (T ℝ degree).leadingCoeff *
        ∏ index ∈ Finset.range degree,
          (value -
            cos ((2 * index + 1) * π / (2 * degree))) := by
  rw [(chebyshevT_splits_real degree).eval_eq_prod_roots, roots_T_real]
  change
    (T ℝ degree).leadingCoeff *
        (∏ root ∈
          Finset.image
            (fun index : ℕ =>
              cos ((2 * index + 1) * π / (2 * degree)))
            (Finset.range degree),
          (value - root)) =
      _
  rw [Finset.prod_image]
  exact
    Finset.nodup_map_iff_injOn.mp
      (roots_T_real_nodup degree)

/-! ## The source root schedule -/

/-- Source Equation (21): one Chebyshev root transformed to the declared
spectral interval. -/
def chebyshevRoot
    (degree : ℕ) (lower upper : ℝ) (index : ℕ) : ℝ :=
  (upper + lower) / 2 +
    (upper - lower) / 2 *
      cos ((2 * index + 1) * π / (2 * degree))

/-- One scalar residual factor `1 - weight * eigenvalue`, with the source
weight equal to the inverse transformed root. -/
def chebyshevInertialFactor
    (degree : ℕ) (lower upper value : ℝ) (index : ℕ) : ℝ :=
  1 - value / chebyshevRoot degree lower upper index

/-- Residual gain of the complete finite root schedule. -/
def chebyshevScheduleGain
    (degree : ℕ) (lower upper value : ℝ) : ℝ :=
  ∏ index ∈ Finset.range degree,
    chebyshevInertialFactor degree lower upper value index

theorem chebyshevRoot_pos
    {degree : ℕ} {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    (index : ℕ) :
    0 < chebyshevRoot degree lower upper index := by
  have cosineLower :=
    neg_one_le_cos ((2 * index + 1) * π / (2 * degree))
  have cosineUpper :=
    cos_le_one ((2 * index + 1) * π / (2 * degree))
  dsimp [chebyshevRoot]
  nlinarith

/-- Each root factor is the ratio of the corresponding normalized-coordinate
root factors at the spectral value and at zero. -/
theorem chebyshevInertialFactor_eq_coordinateRatio
    {degree : ℕ} {lower upper value : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    (index : ℕ) :
    chebyshevInertialFactor degree lower upper value index =
      (intervalCoordinate lower upper value -
          cos ((2 * index + 1) * π / (2 * degree))) /
        (intervalCoordinate lower upper 0 -
          cos ((2 * index + 1) * π / (2 * degree))) := by
  have rootNonzero :=
    ne_of_gt
      (chebyshevRoot_pos (degree := degree)
        lowerPositive lowerLtUpper index)
  have gapNonzero : upper - lower ≠ 0 :=
    ne_of_gt (sub_pos.mpr lowerLtUpper)
  have coordinateNonzero :
      intervalCoordinate lower upper 0 -
          cos ((2 * index + 1) * π / (2 * degree)) ≠ 0 := by
    intro coordinateZero
    have rootZero :
        chebyshevRoot degree lower upper index = 0 := by
      dsimp [intervalCoordinate] at coordinateZero
      dsimp [chebyshevRoot]
      field_simp [gapNonzero] at coordinateZero ⊢
      linarith
    exact rootNonzero rootZero
  have numeratorIdentity :
      intervalCoordinate lower upper value -
          cos ((2 * index + 1) * π / (2 * degree)) =
        2 * (value - chebyshevRoot degree lower upper index) /
          (upper - lower) := by
    dsimp [intervalCoordinate, chebyshevRoot]
    field_simp [gapNonzero]
    ring
  have denominatorIdentity :
      intervalCoordinate lower upper 0 -
          cos ((2 * index + 1) * π / (2 * degree)) =
        -2 * chebyshevRoot degree lower upper index /
          (upper - lower) := by
    dsimp [intervalCoordinate, chebyshevRoot]
    field_simp [gapNonzero]
    ring
  rw [numeratorIdentity, denominatorIdentity]
  dsimp [chebyshevInertialFactor]
  field_simp [rootNonzero, gapNonzero]
  ring

theorem chebyshevDenominator_abs_gt_one
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper) :
    1 <
      |(T ℝ degree).eval (intervalCoordinate lower upper 0)| := by
  apply one_lt_abs_eval_T_real
  · exact_mod_cast degreeNonzero
  · have coordinateBelow :=
      intervalCoordinate_zero_lt_neg_one lowerPositive lowerLtUpper
    rw [abs_of_neg (coordinateBelow.trans (by norm_num))]
    linarith

/-- Source Equation (25), now proved from the explicit transformed roots:
the finite inertial schedule is exactly the normalized Chebyshev polynomial. -/
theorem chebyshevScheduleGain_eq_cycleGain
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper value : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper) :
    chebyshevScheduleGain degree lower upper value =
      chebyshevCycleGain degree lower upper value := by
  have leadingNonzero : (T ℝ degree).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_T]
    positivity
  have denominatorNonzero :
      (T ℝ degree).eval
          (intervalCoordinate lower upper 0) ≠ 0 := by
    have denominatorLarge :=
      chebyshevDenominator_abs_gt_one degreeNonzero
        lowerPositive lowerLtUpper
    exact fun denominatorZero => by
      norm_num [denominatorZero] at denominatorLarge
  rw [chebyshevScheduleGain]
  have factorEquality :
      ∀ index ∈ Finset.range degree,
        chebyshevInertialFactor degree lower upper value index =
          (intervalCoordinate lower upper value -
              cos ((2 * index + 1) * π / (2 * degree))) /
            (intervalCoordinate lower upper 0 -
              cos ((2 * index + 1) * π / (2 * degree))) := by
    intro index _
    exact
      chebyshevInertialFactor_eq_coordinateRatio
        lowerPositive lowerLtUpper index
  rw [Finset.prod_congr rfl factorEquality, Finset.prod_div_distrib]
  rw [chebyshevCycleGain,
    chebyshevT_eval_eq_leading_mul_rootProduct,
    chebyshevT_eval_eq_leading_mul_rootProduct]
  field_simp [leadingNonzero, denominatorNonzero]
  simp only [show ∀ index : ℕ,
    (2 * (index : ℝ) + 1) * π / (2 * (degree : ℝ)) =
      π * (2 * (index : ℝ) + 1) / (2 * (degree : ℝ)) by
        intro
        ring]

/-! ## Uniform spectral contraction -/

theorem abs_chebyshevCycleGain_le
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper value : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    (valueMem : value ∈ Set.Icc lower upper) :
    |chebyshevCycleGain degree lower upper value| ≤
      chebyshevCycleBound degree lower upper := by
  have numeratorBound :=
    abs_eval_T_real_le_one (degree : ℤ)
      (show |intervalCoordinate lower upper value| ≤ 1 by
        exact
          abs_le.mpr
            (intervalCoordinate_mem_Icc lowerLtUpper
              valueMem.1 valueMem.2))
  have denominatorLarge :=
    chebyshevDenominator_abs_gt_one degreeNonzero
      lowerPositive lowerLtUpper
  rw [chebyshevCycleGain, abs_div, chebyshevCycleBound]
  exact
    div_le_div_of_nonneg_right numeratorBound (abs_nonneg _)

theorem chebyshevCycleBound_nonneg
    (degree : ℕ) (lower upper : ℝ) :
    0 ≤ chebyshevCycleBound degree lower upper := by
  exact div_nonneg (by norm_num) (abs_nonneg _)

theorem chebyshevCycleBound_lt_one
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper) :
    chebyshevCycleBound degree lower upper < 1 := by
  have denominatorLarge :=
    chebyshevDenominator_abs_gt_one degreeNonzero
      lowerPositive lowerLtUpper
  rw [chebyshevCycleBound,
    div_lt_one (lt_trans (by norm_num) denominatorLarge)]
  exact denominatorLarge

/-- Degree one recovers the familiar optimal constant relaxation factor
`2 / (lower + upper)`. -/
theorem degreeOne_cycleGain
    (lower upper value : ℝ)
    (lowerNeUpper : lower ≠ upper)
    (sumNonzero : lower + upper ≠ 0) :
    chebyshevCycleGain 1 lower upper value =
      1 - (2 / (lower + upper)) * value := by
  change
    (T ℝ (1 : ℤ)).eval (intervalCoordinate lower upper value) /
        (T ℝ (1 : ℤ)).eval (intervalCoordinate lower upper 0) =
      _
  rw [T_one]
  simp only [eval_X]
  dsimp [intervalCoordinate]
  rw [show (2 * 0 - upper - lower) = -(lower + upper) by ring]
  field_simp [sumNonzero]
  ring

/-! ## Exact execution on a finite real spectrum -/

variable {Mode : Type*} [Fintype Mode]

/-- Execute the first `steps` factors of a degree-`degree` source schedule on
every diagonal spectral mode. -/
def runChebyshevPrefix
    (degree : ℕ) (lower upper : ℝ) (curvature : Mode → ℝ) :
    ℕ → ModalState Mode → ModalState Mode
  | 0, state => state
  | steps + 1, state =>
      diagonalStep
        (1 / chebyshevRoot degree lower upper steps)
        curvature
        (runChebyshevPrefix degree lower upper curvature steps state)

/-- Execute one complete source schedule. -/
def chebyshevCycleSweep
    (degree : ℕ) (lower upper : ℝ)
    (curvature : Mode → ℝ) (state : ModalState Mode) :
    ModalState Mode :=
  runChebyshevPrefix degree lower upper curvature degree state

@[simp] theorem runChebyshevPrefix_apply
    (degree steps : ℕ) (lower upper : ℝ)
    (curvature : Mode → ℝ) (state : ModalState Mode) (mode : Mode) :
    runChebyshevPrefix degree lower upper curvature steps state mode =
      (∏ index ∈ Finset.range steps,
        chebyshevInertialFactor degree lower upper
          (curvature mode) index) *
        state mode := by
  induction steps with
  | zero =>
      simp [runChebyshevPrefix]
  | succ steps inductionHypothesis =>
      rw [runChebyshevPrefix, diagonalStep_apply,
        inductionHypothesis, Finset.prod_range_succ]
      dsimp [chebyshevInertialFactor]
      ring

@[simp] theorem chebyshevCycleSweep_apply
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    (curvature : Mode → ℝ) (state : ModalState Mode) (mode : Mode) :
    chebyshevCycleSweep degree lower upper curvature state mode =
      chebyshevCycleGain degree lower upper (curvature mode) *
        state mode := by
  rw [chebyshevCycleSweep, runChebyshevPrefix_apply]
  change
    chebyshevScheduleGain degree lower upper (curvature mode) *
        state mode =
      _
  rw [chebyshevScheduleGain_eq_cycleGain degreeNonzero
    lowerPositive lowerLtUpper]

/-- One exact Chebyshev cycle contracts all declared real modes
simultaneously. -/
theorem chebyshevCycleSweep_norm_le
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    {curvature : Mode → ℝ}
    (curvatureMem :
      ∀ mode, curvature mode ∈ Set.Icc lower upper)
    (state : ModalState Mode) :
    ‖chebyshevCycleSweep degree lower upper curvature state‖ ≤
      chebyshevCycleBound degree lower upper * ‖state‖ := by
  have cycleAsMultiplier :
      chebyshevCycleSweep degree lower upper curvature state =
        WithLp.toLp 2 (fun mode =>
          chebyshevCycleGain degree lower upper (curvature mode) *
            state mode) := by
    ext mode
    rw [chebyshevCycleSweep_apply degreeNonzero
      lowerPositive lowerLtUpper]
  rw [cycleAsMultiplier]
  exact
    diagonalMultiplier_norm_le
      (fun mode =>
        chebyshevCycleGain degree lower upper (curvature mode))
      (chebyshevCycleBound degree lower upper)
      (chebyshevCycleBound_nonneg degree lower upper)
      (fun mode =>
        abs_chebyshevCycleGain_le degreeNonzero
          lowerPositive lowerLtUpper (curvatureMem mode))
      state

theorem chebyshevCycleSweep_distance_le
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    {curvature : Mode → ℝ}
    (curvatureMem :
      ∀ mode, curvature mode ∈ Set.Icc lower upper)
    (left right : ModalState Mode) :
    ‖chebyshevCycleSweep degree lower upper curvature left -
        chebyshevCycleSweep degree lower upper curvature right‖ ≤
      chebyshevCycleBound degree lower upper * ‖left - right‖ := by
  have cycleLinear :
      chebyshevCycleSweep degree lower upper curvature left -
          chebyshevCycleSweep degree lower upper curvature right =
        chebyshevCycleSweep degree lower upper curvature
          (left - right) := by
    ext mode
    change
      chebyshevCycleSweep degree lower upper curvature left mode -
          chebyshevCycleSweep degree lower upper curvature right mode =
        chebyshevCycleSweep degree lower upper curvature
          (left - right) mode
    rw [chebyshevCycleSweep_apply degreeNonzero
      lowerPositive lowerLtUpper]
    rw [chebyshevCycleSweep_apply degreeNonzero
      lowerPositive lowerLtUpper]
    rw [chebyshevCycleSweep_apply degreeNonzero
      lowerPositive lowerLtUpper]
    change
      chebyshevCycleGain degree lower upper (curvature mode) *
            left mode -
          chebyshevCycleGain degree lower upper (curvature mode) *
            right mode =
      chebyshevCycleGain degree lower upper (curvature mode) *
          (left mode - right mode)
    ring
  rw [cycleLinear]
  exact
    chebyshevCycleSweep_norm_le degreeNonzero
      lowerPositive lowerLtUpper curvatureMem (left - right)

/-- Proof-carrying exact source-cycle contraction certificate. -/
def chebyshevCycleContractionCertificate
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    {curvature : Mode → ℝ}
    (curvatureMem :
      ∀ mode, curvature mode ∈ Set.Icc lower upper) :
    ContractionCertificate
      (chebyshevCycleSweep degree lower upper curvature) where
  factor := chebyshevCycleBound degree lower upper
  factor_nonneg :=
    chebyshevCycleBound_nonneg degree lower upper
  factor_lt_one :=
    chebyshevCycleBound_lt_one degreeNonzero
      lowerPositive lowerLtUpper
  contracts :=
    chebyshevCycleSweep_distance_le degreeNonzero
      lowerPositive lowerLtUpper curvatureMem

@[simp] theorem chebyshevCycleSweep_zero
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    (curvature : Mode → ℝ) :
    chebyshevCycleSweep degree lower upper curvature 0 = 0 := by
  ext mode
  simp [chebyshevCycleSweep_apply degreeNonzero
    lowerPositive lowerLtUpper]

/-- Repeating complete cycles gives the exact geometric source-style
endpoint bound. -/
theorem iterate_chebyshevCycleSweep_norm_le
    {degree : ℕ} (degreeNonzero : degree ≠ 0)
    {lower upper : ℝ}
    (lowerPositive : 0 < lower)
    (lowerLtUpper : lower < upper)
    {curvature : Mode → ℝ}
    (curvatureMem :
      ∀ mode, curvature mode ∈ Set.Icc lower upper)
    (initial : ModalState Mode) (cycles : ℕ) :
    ‖(chebyshevCycleSweep degree lower upper curvature)^[cycles]
        initial‖ ≤
      chebyshevCycleBound degree lower upper ^ cycles *
        ‖initial‖ := by
  have fixedZero :
      chebyshevCycleSweep degree lower upper curvature
          (0 : ModalState Mode) =
        0 :=
    chebyshevCycleSweep_zero degreeNonzero
      lowerPositive lowerLtUpper curvature
  have bound :=
    iterate_initializer_to_fixedPoint_le
      (chebyshevCycleContractionCertificate degreeNonzero
        lowerPositive lowerLtUpper curvatureMem)
      (0 : ModalState Mode) initial fixedZero cycles
  simpa only [chebyshevCycleContractionCertificate, sub_zero] using bound

/-! ## Intermediate-sweep and nonlinear boundaries -/

theorem degreeTwo_unitNine_secondRoot :
    chebyshevRoot 2 1 9 1 = 5 - 2 * √2 := by
  norm_num [chebyshevRoot]
  rw [show 3 * π / 4 = π - π / 4 by ring]
  rw [cos_pi_sub, cos_pi_div_four]
  ring

/-- The second exact source factor expands the high `[1,9]` mode.  The
contraction guarantee is therefore a cycle-end guarantee, not a per-factor
monotonicity claim. -/
theorem degreeTwo_unitNine_secondFactor_expands_highMode :
    |chebyshevInertialFactor 2 1 9 9 1| > 1 := by
  rw [chebyshevInertialFactor, degreeTwo_unitNine_secondRoot]
  have sqrtLower : 1 < √2 := by
    rw [lt_sqrt (by norm_num)]
    norm_num
  have sqrtUpper : √2 < 2 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  have denominatorPositive : 0 < 5 - 2 * √2 := by
    linarith
  have ratioLarge : 2 < 9 / (5 - 2 * √2) := by
    rw [lt_div_iff₀ denominatorPositive]
    nlinarith
  have factorBelow : 1 - 9 / (5 - 2 * √2) < -1 := by
    linarith
  rw [abs_of_neg (factorBelow.trans (by norm_num))]
  linarith

theorem degreeTwo_unitNine_cycle_contracts :
    chebyshevCycleBound 2 1 9 < 1 := by
  exact chebyshevCycleBound_lt_one (by norm_num) (by norm_num)
    (by norm_num)

/-- A simple nonlinear fixed-point map used to separate exact linear
polynomial commutation from nonlinear execution order. -/
def squareSolver (state : ℝ) : ℝ :=
  state ^ 2

theorem nonlinear_inertial_order_matters :
    inertialStep 2 squareSolver
        (inertialStep (1 / 2) squareSolver 2) = 15 ∧
      inertialStep (1 / 2) squareSolver
        (inertialStep 2 squareSolver 2) = 21 := by
  norm_num [inertialStep, squareSolver]

#print axioms inertialStep_fixedPoint_iff_of_weight_ne_zero
#print axioms chebyshevT_eval_eq_leading_mul_rootProduct
#print axioms chebyshevScheduleGain_eq_cycleGain
#print axioms abs_chebyshevCycleGain_le
#print axioms degreeOne_cycleGain
#print axioms chebyshevCycleSweep_norm_le
#print axioms chebyshevCycleContractionCertificate
#print axioms iterate_chebyshevCycleSweep_norm_le
#print axioms degreeTwo_unitNine_secondFactor_expands_highMode
#print axioms nonlinear_inertial_order_matters

end

end ChebyshevInertialIteration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
