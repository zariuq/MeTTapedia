import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SettledCreditClosedForm

/-!
# Spectral geometry of settled credit

Diagonal affine settling scales each coordinate of the backpropagated credit
by a schedule coefficient.  This file quantifies the resulting angle.  The
sharp lower bound is the Kantorovich factor

`2 * sqrt (lower * upper) / (lower + upper)`.

The bound is attained by a two-coordinate endpoint spectrum.  A separate
perturbation theorem charges a nonlinear credit remainder in norm.  Finally,
an explicit diagonal field shows that two settling schedules can select
different directions once curvature is not scalar.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SettledCreditSpectralGeometry

open scoped BigOperators InnerProductSpace
open SettledCreditClosedForm
open ProspectiveResidualSemantics

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Euclidean coordinate inner product, written independently of a bundled
vector representation so it can be applied directly to logged coordinates. -/
def coordinateInner (left right : ι → ℝ) : ℝ :=
  ∑ index, left index * right index

/-- Squared Euclidean coordinate norm. -/
def coordinateNormSq (value : ι → ℝ) : ℝ :=
  coordinateInner value value

/-- Coordinatewise positive scaling. -/
def diagonalScale (scale value : ι → ℝ) : ι → ℝ :=
  fun index => scale index * value index

/-- Cosine computed from Euclidean coordinate sums.  The theorems using it
carry strict positivity hypotheses for both squared norms. -/
def coordinateCosine (left right : ι → ℝ) : ℝ :=
  coordinateInner left right /
    Real.sqrt (coordinateNormSq left * coordinateNormSq right)

/-- Positive scalar multiplication has cosine one with the original vector. -/
theorem coordinateCosine_pos_smul_self
    (value : ι → ℝ) (scale : ℝ) (scale_pos : 0 < scale)
    (normSq_pos : 0 < coordinateNormSq value) :
    coordinateCosine (scale • value) value = 1 := by
  have normSq_scaled :
      coordinateNormSq (scale • value) =
        scale ^ 2 * coordinateNormSq value := by
    simp [coordinateNormSq, coordinateInner, Finset.mul_sum, pow_two]
    ring_nf
  have inner_scaled :
      coordinateInner (scale • value) value =
        scale * coordinateNormSq value := by
    simp [coordinateNormSq, coordinateInner, Finset.mul_sum]
    ring_nf
  have product_eq :
      coordinateNormSq (scale • value) * coordinateNormSq value =
        (scale * coordinateNormSq value) ^ 2 := by
    rw [normSq_scaled]
    ring
  have product_pos : 0 < scale * coordinateNormSq value :=
    mul_pos scale_pos normSq_pos
  rw [coordinateCosine, inner_scaled, product_eq, Real.sqrt_sq_eq_abs,
    abs_of_pos product_pos]
  exact div_self (ne_of_gt product_pos)

@[simp] theorem coordinateInner_apply (left right : ι → ℝ) :
    coordinateInner left right = ∑ index, left index * right index := rfl

@[simp] theorem coordinateNormSq_apply (value : ι → ℝ) :
    coordinateNormSq value = ∑ index, value index ^ 2 := by
  simp [coordinateNormSq, coordinateInner, pow_two]

theorem coordinateNormSq_nonneg (value : ι → ℝ) :
    0 ≤ coordinateNormSq value := by
  rw [coordinateNormSq_apply]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype ι] in
@[simp] theorem diagonalScale_apply (scale value : ι → ℝ) (index : ι) :
    diagonalScale scale value index = scale index * value index := rfl

/-- The polynomial form of the sharp diagonal-scaling cosine bound. -/
theorem diagonalScale_kantorovich_squared
    (scale credit : ι → ℝ) {lower upper : ℝ}
    (lower_nonneg : 0 ≤ lower) (lower_le_upper : lower ≤ upper)
    (scale_mem : ∀ index, lower ≤ scale index ∧ scale index ≤ upper) :
    4 * lower * upper * coordinateNormSq credit *
        coordinateNormSq (diagonalScale scale credit) ≤
      (lower + upper) ^ 2 *
        coordinateInner (diagonalScale scale credit) credit ^ 2 := by
  let baseSq := coordinateNormSq credit
  let scaledSq := coordinateNormSq (diagonalScale scale credit)
  let mixed := coordinateInner (diagonalScale scale credit) credit
  have upper_nonneg : 0 ≤ upper := lower_nonneg.trans lower_le_upper
  have baseSq_nonneg : 0 ≤ baseSq := coordinateNormSq_nonneg credit
  have pointwise : ∀ index,
      scale index ^ 2 + lower * upper ≤
        (lower + upper) * scale index := by
    intro index
    obtain ⟨hlower, hupper⟩ := scale_mem index
    nlinarith [mul_nonneg (sub_nonneg.mpr hlower) (sub_nonneg.mpr hupper)]
  have summed : scaledSq + lower * upper * baseSq ≤
      (lower + upper) * mixed := by
    dsimp [scaledSq, baseSq, mixed]
    rw [coordinateNormSq_apply, coordinateNormSq_apply]
    calc
      (∑ index, (diagonalScale scale credit index) ^ 2) +
          lower * upper * ∑ index, credit index ^ 2 =
          ∑ index,
            (scale index ^ 2 + lower * upper) * credit index ^ 2 := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro index _
              simp [diagonalScale]
              ring
      _ ≤ ∑ index,
          ((lower + upper) * scale index) * credit index ^ 2 := by
            exact Finset.sum_le_sum fun index _ =>
              mul_le_mul_of_nonneg_right (pointwise index) (sq_nonneg _)
      _ = (lower + upper) *
          ∑ index, diagonalScale scale credit index * credit index := by
            simp [diagonalScale, Finset.mul_sum]
            ring_nf
  have coefficient_nonneg : 0 ≤ 4 * lower * upper * baseSq := by positivity
  have multiplied := mul_le_mul_of_nonneg_left summed coefficient_nonneg
  have square_nonneg :
      0 ≤ ((lower + upper) * mixed - 2 * lower * upper * baseSq) ^ 2 :=
    sq_nonneg _
  dsimp [baseSq, scaledSq, mixed] at multiplied square_nonneg ⊢
  nlinarith

/-- Sharp cosine lower bound for a positive diagonal scaling. -/
theorem kantorovichFactor_le_coordinateCosine_diagonalScale
    (scale credit : ι → ℝ) {lower upper : ℝ}
    (lower_pos : 0 < lower) (lower_le_upper : lower ≤ upper)
    (scale_mem : ∀ index, lower ≤ scale index ∧ scale index ≤ upper)
    (credit_normSq_pos : 0 < coordinateNormSq credit) :
    2 * Real.sqrt (lower * upper) / (lower + upper) ≤
      coordinateCosine (diagonalScale scale credit) credit := by
  have lower_nonneg : 0 ≤ lower := lower_pos.le
  have upper_pos : 0 < upper := lower_pos.trans_le lower_le_upper
  have upper_nonneg : 0 ≤ upper := upper_pos.le
  have sum_pos : 0 < lower + upper := add_pos lower_pos upper_pos
  have mixed_lower :
      lower * coordinateNormSq credit ≤
        coordinateInner (diagonalScale scale credit) credit := by
    rw [coordinateNormSq_apply, coordinateInner_apply]
    calc
      lower * ∑ index, credit index ^ 2 =
          ∑ index, lower * credit index ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ index,
          diagonalScale scale credit index * credit index := by
            exact Finset.sum_le_sum fun index _ => by
              have h := (scale_mem index).1
              simp only [diagonalScale, pow_two]
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_right h
                  (mul_self_nonneg (credit index))
  have mixed_pos :
      0 < coordinateInner (diagonalScale scale credit) credit := by
    exact lt_of_lt_of_le (mul_pos lower_pos credit_normSq_pos) mixed_lower
  have scaled_lower :
      lower ^ 2 * coordinateNormSq credit ≤
        coordinateNormSq (diagonalScale scale credit) := by
    rw [coordinateNormSq_apply, coordinateNormSq_apply]
    calc
      lower ^ 2 * ∑ index, credit index ^ 2 =
          ∑ index, lower ^ 2 * credit index ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ index, diagonalScale scale credit index ^ 2 := by
            exact Finset.sum_le_sum fun index _ => by
              have h := (scale_mem index).1
              have hsquare : lower ^ 2 ≤ scale index ^ 2 := by
                nlinarith [lower_nonneg, h]
              simpa [diagonalScale, mul_pow] using
                mul_le_mul_of_nonneg_right hsquare (sq_nonneg (credit index))
  have scaled_normSq_pos :
      0 < coordinateNormSq (diagonalScale scale credit) := by
    have : 0 < lower ^ 2 * coordinateNormSq credit :=
      mul_pos (sq_pos_of_pos lower_pos) credit_normSq_pos
    exact this.trans_le scaled_lower
  let denominator := Real.sqrt
    (coordinateNormSq (diagonalScale scale credit) * coordinateNormSq credit)
  have denominator_pos : 0 < denominator := by
    dsimp [denominator]
    exact Real.sqrt_pos.2 (mul_pos scaled_normSq_pos credit_normSq_pos)
  have squared := diagonalScale_kantorovich_squared scale credit
    lower_nonneg lower_le_upper scale_mem
  have product_nonneg :
      0 ≤ coordinateNormSq (diagonalScale scale credit) *
        coordinateNormSq credit := by positivity
  have sqrt_sq : denominator ^ 2 =
      coordinateNormSq (diagonalScale scale credit) * coordinateNormSq credit := by
    dsimp [denominator]
    exact Real.sq_sqrt product_nonneg
  have root_sq : Real.sqrt (lower * upper) ^ 2 = lower * upper := by
    exact Real.sq_sqrt (mul_nonneg lower_nonneg upper_nonneg)
  have numerator_bound :
      2 * Real.sqrt (lower * upper) * denominator ≤
        (lower + upper) *
          coordinateInner (diagonalScale scale credit) credit := by
    apply le_of_sq_le_sq
    · rw [mul_pow, mul_pow, root_sq, sqrt_sq]
      nlinarith [squared]
    · positivity
  rw [coordinateCosine]
  rw [div_le_div_iff₀ sum_pos denominator_pos]
  simpa [mul_assoc, mul_left_comm, mul_comm] using numerator_bound

/-! ## Tight endpoint witness -/

namespace TightWitness

def scale : Fin 2 → ℝ := ![1, 4]

def credit : Fin 2 → ℝ := ![2, 1]

theorem scale_mem (index : Fin 2) :
    (1 : ℝ) ≤ scale index ∧ scale index ≤ 4 := by
  fin_cases index <;> norm_num [scale]

theorem credit_normSq : coordinateNormSq credit = 5 := by
  norm_num [coordinateNormSq_apply, credit, Fin.sum_univ_two]

theorem scaled_normSq : coordinateNormSq (diagonalScale scale credit) = 20 := by
  norm_num [coordinateNormSq_apply, diagonalScale, scale, credit,
    Fin.sum_univ_two]

theorem mixed : coordinateInner (diagonalScale scale credit) credit = 8 := by
  norm_num [coordinateInner, diagonalScale, scale, credit, Fin.sum_univ_two]

/-- The two-coordinate endpoint spectrum attains the sharp factor `4/5`. -/
theorem coordinateCosine_eq_kantorovichFactor :
    coordinateCosine (diagonalScale scale credit) credit = 4 / 5 := by
  rw [coordinateCosine, credit_normSq, scaled_normSq, mixed]
  have hsqrt : Real.sqrt (20 * 5) = 10 := by norm_num
  rw [hsqrt]
  norm_num

end TightWitness

namespace TwoEndpointTightFamily

/-- A two-endpoint scale spectrum parameterized by positive square roots. -/
def scale (lowerRoot upperRoot : ℝ) : Fin 2 → ℝ :=
  ![lowerRoot ^ 2, upperRoot ^ 2]

/-- Endpoint weights that attain the Kantorovich factor. -/
def credit (lowerRoot upperRoot : ℝ) : Fin 2 → ℝ :=
  ![upperRoot, lowerRoot]

/-- Every positive two-endpoint spectrum has a credit vector attaining the
sharp Kantorovich cosine factor. -/
theorem coordinateCosine_eq_kantorovichFactor
    (lowerRoot upperRoot : ℝ)
    (lowerRoot_pos : 0 < lowerRoot)
    (lowerRoot_le_upperRoot : lowerRoot ≤ upperRoot) :
    coordinateCosine
        (diagonalScale (scale lowerRoot upperRoot)
          (credit lowerRoot upperRoot))
        (credit lowerRoot upperRoot) =
      2 * Real.sqrt (lowerRoot ^ 2 * upperRoot ^ 2) /
        (lowerRoot ^ 2 + upperRoot ^ 2) := by
  have upperRoot_pos := lowerRoot_pos.trans_le lowerRoot_le_upperRoot
  have norm_credit :
      coordinateNormSq (credit lowerRoot upperRoot) =
        lowerRoot ^ 2 + upperRoot ^ 2 := by
    simp [coordinateNormSq_apply, credit, Fin.sum_univ_two]
    ring
  have norm_scaled :
      coordinateNormSq
          (diagonalScale (scale lowerRoot upperRoot)
            (credit lowerRoot upperRoot)) =
        (lowerRoot * upperRoot) ^ 2 *
          (lowerRoot ^ 2 + upperRoot ^ 2) := by
    simp [coordinateNormSq_apply, diagonalScale, scale, credit,
      Fin.sum_univ_two]
    ring
  have inner_scaled :
      coordinateInner
          (diagonalScale (scale lowerRoot upperRoot)
            (credit lowerRoot upperRoot))
          (credit lowerRoot upperRoot) =
        2 * (lowerRoot * upperRoot) ^ 2 := by
    simp [coordinateInner, diagonalScale, scale, credit, Fin.sum_univ_two]
    ring
  have product_eq :
      coordinateNormSq
            (diagonalScale (scale lowerRoot upperRoot)
              (credit lowerRoot upperRoot)) *
          coordinateNormSq (credit lowerRoot upperRoot) =
        (lowerRoot * upperRoot *
          (lowerRoot ^ 2 + upperRoot ^ 2)) ^ 2 := by
    rw [norm_scaled, norm_credit]
    ring
  have product_factor_pos :
      0 < lowerRoot * upperRoot *
        (lowerRoot ^ 2 + upperRoot ^ 2) := by positivity
  have root_product :
      Real.sqrt
          (coordinateNormSq
              (diagonalScale (scale lowerRoot upperRoot)
                (credit lowerRoot upperRoot)) *
            coordinateNormSq (credit lowerRoot upperRoot)) =
        lowerRoot * upperRoot *
          (lowerRoot ^ 2 + upperRoot ^ 2) := by
    rw [product_eq, Real.sqrt_sq_eq_abs, abs_of_pos product_factor_pos]
  have root_scale :
      Real.sqrt (lowerRoot ^ 2 * upperRoot ^ 2) =
        lowerRoot * upperRoot := by
    have square_eq :
        lowerRoot ^ 2 * upperRoot ^ 2 =
          (lowerRoot * upperRoot) ^ 2 := by ring
    rw [square_eq, Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos lowerRoot_pos upperRoot_pos)]
  rw [coordinateCosine, inner_scaled, root_product, root_scale]
  field_simp

end TwoEndpointTightFamily

/-! ## Schedule coefficients as spectral scales -/

/-- Settled-credit scale associated with one curvature eigenvalue. -/
def scheduledScale (readPrecision : ℝ) (schedule : List (ℝ × ℝ))
    (curvature : ℝ) : ℝ :=
  readPrecision * scheduleCoefficient curvature schedule 0

/-- Closed-form settled credit of a diagonal affine field. -/
def scheduledDiagonalCredit
    (readPrecision : ℝ) (schedule : List (ℝ × ℝ))
    (curvature bpCredit : ι → ℝ) : ι → ℝ :=
  diagonalScale (fun index =>
    scheduledScale readPrecision schedule (curvature index)) bpCredit

/-- A diagonal curvature spectrum and the spread of its schedule coefficients
give the sharp settled-credit cosine bound. -/
theorem kantorovichFactor_le_scheduledDiagonalCredit_cosine
    (readPrecision : ℝ) (schedule : List (ℝ × ℝ))
    (curvature bpCredit : ι → ℝ)
    {curvatureLower curvatureUpper scaleLower scaleUpper : ℝ}
    (curvature_mem : ∀ index,
      curvatureLower ≤ curvature index ∧ curvature index ≤ curvatureUpper)
    (scaleLower_pos : 0 < scaleLower)
    (scaleLower_le_scaleUpper : scaleLower ≤ scaleUpper)
    (schedule_scale_mem : ∀ value,
      curvatureLower ≤ value → value ≤ curvatureUpper →
      scaleLower ≤ scheduledScale readPrecision schedule value ∧
        scheduledScale readPrecision schedule value ≤ scaleUpper)
    (bp_normSq_pos : 0 < coordinateNormSq bpCredit) :
    2 * Real.sqrt (scaleLower * scaleUpper) /
        (scaleLower + scaleUpper) ≤
      coordinateCosine
        (scheduledDiagonalCredit readPrecision schedule curvature bpCredit)
        bpCredit := by
  apply kantorovichFactor_le_coordinateCosine_diagonalScale
    (fun index => scheduledScale readPrecision schedule (curvature index))
    bpCredit scaleLower_pos scaleLower_le_scaleUpper
  · intro index
    exact schedule_scale_mem (curvature index)
      (curvature_mem index).1 (curvature_mem index).2
  · exact bp_normSq_pos

/-! ## Nonlinear remainder -/

variable {Credit : Type*}
  [NormedAddCommGroup Credit] [InnerProductSpace ℝ Credit]

/-- Real cosine on a nonzero pair.  The hypotheses of the bound theorems keep
the denominator positive. -/
def realCosine (left right : Credit) : ℝ :=
  ⟪left, right⟫_ℝ / (‖left‖ * ‖right‖)

/-- A norm-bounded nonlinear remainder degrades a base cosine certificate by
the explicit factor `(kappa * ‖base‖ - rho) / (‖base‖ + rho)`. -/
theorem remainder_cosine_lower_bound
    (base actual bp : Credit) (kappa rho : ℝ)
    (bp_ne_zero : bp ≠ 0)
    (actual_ne_zero : actual ≠ 0)
    (base_norm_pos : 0 < ‖base‖)
    (rho_nonneg : 0 ≤ rho)
    (margin_nonneg : 0 ≤ kappa * ‖base‖ - rho)
    (base_alignment :
      kappa * ‖base‖ * ‖bp‖ ≤ ⟪base, bp⟫_ℝ)
    (remainder_bound : ‖actual - base‖ ≤ rho) :
    (kappa * ‖base‖ - rho) / (‖base‖ + rho) ≤
      realCosine actual bp := by
  have bp_norm_pos : 0 < ‖bp‖ := norm_pos_iff.mpr bp_ne_zero
  have actual_norm_upper : ‖actual‖ ≤ ‖base‖ + rho := by
    have triangle : ‖actual‖ ≤ ‖actual - base‖ + ‖base‖ := by
      calc
        ‖actual‖ = ‖(actual - base) + base‖ := by congr 1; abel
        _ ≤ ‖actual - base‖ + ‖base‖ := norm_add_le _ _
    linarith
  have actual_norm_pos : 0 < ‖actual‖ := norm_pos_iff.mpr actual_ne_zero
  have error_inner :
      -rho * ‖bp‖ ≤ ⟪actual - base, bp⟫_ℝ := by
    have cauchy := abs_real_inner_le_norm (actual - base) bp
    have lower := neg_le_of_abs_le cauchy
    nlinarith [mul_le_mul_of_nonneg_right remainder_bound (norm_nonneg bp)]
  have actual_alignment :
      (kappa * ‖base‖ - rho) * ‖bp‖ ≤ ⟪actual, bp⟫_ℝ := by
    rw [← sub_add_cancel actual base, inner_add_left]
    nlinarith
  have denominator_upper :
      ‖actual‖ * ‖bp‖ ≤ (‖base‖ + rho) * ‖bp‖ :=
    mul_le_mul_of_nonneg_right actual_norm_upper (norm_nonneg bp)
  have numerator_nonneg :
      0 ≤ (kappa * ‖base‖ - rho) * ‖bp‖ :=
    mul_nonneg margin_nonneg bp_norm_pos.le
  have lower_scaled :
      (kappa * ‖base‖ - rho) * (‖actual‖ * ‖bp‖) ≤
        (‖base‖ + rho) * ⟪actual, bp⟫_ℝ := by
    have left_le :
        (kappa * ‖base‖ - rho) * (‖actual‖ * ‖bp‖) ≤
          (kappa * ‖base‖ - rho) * ((‖base‖ + rho) * ‖bp‖) :=
      mul_le_mul_of_nonneg_left denominator_upper margin_nonneg
    have right_le :
        (kappa * ‖base‖ - rho) * ((‖base‖ + rho) * ‖bp‖) ≤
          (‖base‖ + rho) * ⟪actual, bp⟫_ℝ := by
      have factor_nonneg : 0 ≤ ‖base‖ + rho := by positivity
      nlinarith [mul_le_mul_of_nonneg_left actual_alignment factor_nonneg]
    exact left_le.trans right_le
  rw [realCosine]
  rw [div_le_div_iff₀ (by positivity : 0 < ‖base‖ + rho)
    (mul_pos actual_norm_pos bp_norm_pos)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using lower_scaled

/-! ## From field remainder to credit remainder along a certified path -/

/-- Membership in the closed settling ball centered at the feed-forward
prediction. -/
def InSettlingBall (prediction : Credit) (radius : ℝ) (state : Credit) : Prop :=
  ‖state - prediction‖ ≤ radius

/-- A nonlinear field differs from an affine reference field by at most
`rho` throughout a declared settling ball. -/
def FieldWithinOnBall
    (prediction : Credit) (radius rho : ℝ)
    (actualField affineField : Credit → Credit) : Prop :=
  ∀ state, InSettlingBall prediction radius state →
    ‖actualField state - affineField state‖ ≤ rho

/-- Settled state-space credit before applying a parameter pullback. -/
def stateSettledCredit
    (prediction settled : Credit) (readPrecision : ℝ) : Credit :=
  readPrecision • (prediction - settled)

/-- Propagate an initial state-error budget through a schedule.  Each step
multiplies the prior error by its affine-step Lipschitz factor and adds the
field-remainder charge `|rate| * rho`. -/
def scheduleErrorBound
    (stepFactor : ℝ × ℝ → ℝ) (rho : ℝ) :
    List (ℝ × ℝ) → ℝ → ℝ
  | [], initial => initial
  | entry :: rest, initial =>
      scheduleErrorBound stepFactor rho rest
        (stepFactor entry * initial + |entry.1| * rho)

/-- Pathwise certificate supplying exactly the premises needed to compare a
nonlinear settling trajectory with an affine reference trajectory.  The
states remain in the declared ball, and the affine step is Lipschitz between
the paired states at every scheduled entry. -/
inductive CertifiedSchedulePath
    (prediction : Credit) (radius : ℝ)
    (actualField affineField : Credit → Credit)
    (stepFactor : ℝ × ℝ → ℝ) :
    List (ℝ × ℝ) → Credit → Credit → Prop
  | nil (actualState affineState : Credit)
      (actual_mem : InSettlingBall prediction radius actualState)
      (affine_mem : InSettlingBall prediction radius affineState) :
      CertifiedSchedulePath prediction radius actualField affineField
        stepFactor [] actualState affineState
  | cons (entry : ℝ × ℝ) (rest : List (ℝ × ℝ))
      (actualState affineState : Credit)
      (actual_mem : InSettlingBall prediction radius actualState)
      (affine_mem : InSettlingBall prediction radius affineState)
      (factor_nonneg : 0 ≤ stepFactor entry)
      (affine_step_lipschitz :
        ‖prospectiveGradientStep prediction entry.2 entry.1 affineField
              actualState -
            prospectiveGradientStep prediction entry.2 entry.1 affineField
              affineState‖ ≤
          stepFactor entry * ‖actualState - affineState‖)
      (tail : CertifiedSchedulePath prediction radius actualField affineField
        stepFactor rest
          (prospectiveGradientStep prediction entry.2 entry.1 actualField
            actualState)
          (prospectiveGradientStep prediction entry.2 entry.1 affineField
            affineState)) :
      CertifiedSchedulePath prediction radius actualField affineField
        stepFactor (entry :: rest) actualState affineState

theorem scheduleErrorBound_mono
    (stepFactor : ℝ × ℝ → ℝ) (rho : ℝ)
    (schedule : List (ℝ × ℝ))
    (factor_nonneg : ∀ entry ∈ schedule, 0 ≤ stepFactor entry)
    {first second : ℝ} (first_le_second : first ≤ second) :
    scheduleErrorBound stepFactor rho schedule first ≤
      scheduleErrorBound stepFactor rho schedule second := by
  induction schedule generalizing first second with
  | nil => simpa [scheduleErrorBound]
  | cons entry rest ih =>
      simp only [scheduleErrorBound]
      apply ih (fun candidate candidate_mem =>
        factor_nonneg candidate (List.mem_cons_of_mem entry candidate_mem))
      have scaled := mul_le_mul_of_nonneg_left first_le_second
        (factor_nonneg entry (List.mem_cons_self ..))
      linarith

theorem scheduleErrorBound_nonneg
    (stepFactor : ℝ × ℝ → ℝ) (rho : ℝ)
    (schedule : List (ℝ × ℝ))
    (rho_nonneg : 0 ≤ rho)
    (factor_nonneg : ∀ entry ∈ schedule, 0 ≤ stepFactor entry)
    {initial : ℝ} (initial_nonneg : 0 ≤ initial) :
    0 ≤ scheduleErrorBound stepFactor rho schedule initial := by
  induction schedule generalizing initial with
  | nil => simpa [scheduleErrorBound]
  | cons entry rest ih =>
      simp only [scheduleErrorBound]
      apply ih (fun candidate candidate_mem =>
        factor_nonneg candidate (List.mem_cons_of_mem entry candidate_mem))
      exact add_nonneg
        (mul_nonneg (factor_nonneg entry (List.mem_cons_self ..)) initial_nonneg)
        (mul_nonneg (abs_nonneg entry.1) rho_nonneg)

theorem CertifiedSchedulePath.factor_nonneg
    {prediction : Credit} {radius : ℝ}
    {actualField affineField : Credit → Credit}
    {stepFactor : ℝ × ℝ → ℝ}
    {schedule : List (ℝ × ℝ)} {actualState affineState : Credit}
    (path : CertifiedSchedulePath prediction radius actualField affineField
      stepFactor schedule actualState affineState) :
    ∀ entry ∈ schedule, 0 ≤ stepFactor entry := by
  induction path with
  | nil => simp
  | cons current rest actual affine actual_mem affine_mem current_nonneg
      affine_lipschitz tail ih =>
      intro entry entry_mem
      rcases List.mem_cons.mp entry_mem with rfl | in_rest
      · exact current_nonneg
      · exact ih entry in_rest

/-- One nonlinear step differs from its affine reference by the affine
transport of the current state error plus the local field-remainder charge. -/
theorem prospectiveGradientStep_field_remainder_bound
    (prediction actualState affineState : Credit)
    (actualField affineField : Credit → Credit)
    (rate precision factor rho : ℝ)
    (field_remainder :
      ‖actualField actualState - affineField actualState‖ ≤ rho)
    (affine_step_lipschitz :
      ‖prospectiveGradientStep prediction precision rate affineField
            actualState -
          prospectiveGradientStep prediction precision rate affineField
            affineState‖ ≤
        factor * ‖actualState - affineState‖) :
    ‖prospectiveGradientStep prediction precision rate actualField actualState -
        prospectiveGradientStep prediction precision rate affineField
          affineState‖ ≤
      factor * ‖actualState - affineState‖ + |rate| * rho := by
  let actualStep := prospectiveGradientStep prediction precision rate actualField
  let affineStep := prospectiveGradientStep prediction precision rate affineField
  have same_state_difference :
      actualStep actualState - affineStep actualState =
        (-rate) • (actualField actualState - affineField actualState) := by
    dsimp [actualStep, affineStep]
    rw [prospectiveGradientStep, prospectiveGradientStep,
      prospectiveEnergyGradient, prospectiveEnergyGradient]
    module
  have triangle :
      ‖actualStep actualState - affineStep affineState‖ ≤
        ‖actualStep actualState - affineStep actualState‖ +
          ‖affineStep actualState - affineStep affineState‖ := by
    calc
      _ = ‖(actualStep actualState - affineStep actualState) +
            (affineStep actualState - affineStep affineState)‖ := by
              congr 1
              abel
      _ ≤ _ := norm_add_le _ _
  have same_state_bound :
      ‖actualStep actualState - affineStep actualState‖ ≤ |rate| * rho := by
    rw [same_state_difference, norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_left field_remainder (abs_nonneg rate)
  dsimp [actualStep, affineStep] at triangle affine_step_lipschitz ⊢
  linarith

/-- A certified path turns a field-remainder bound on the settling ball into
an explicit final-state error bound. -/
theorem scheduledIterate_field_remainder_bound
    (prediction : Credit) (radius rho : ℝ)
    (actualField affineField : Credit → Credit)
    (stepFactor : ℝ × ℝ → ℝ)
    (schedule : List (ℝ × ℝ))
    (actualStart affineStart : Credit)
    (field_within :
      FieldWithinOnBall prediction radius rho actualField affineField)
    (path : CertifiedSchedulePath prediction radius actualField affineField
      stepFactor schedule actualStart affineStart) :
    ‖scheduledIterate prediction actualField schedule actualStart -
        scheduledIterate prediction affineField schedule affineStart‖ ≤
      scheduleErrorBound stepFactor rho schedule
        ‖actualStart - affineStart‖ := by
  induction path with
  | nil actual affine actual_mem affine_mem =>
      simp [scheduledIterate, scheduleErrorBound]
  | cons entry rest actual affine actual_mem affine_mem factor_nonneg
      affine_lipschitz tail ih =>
      simp only [scheduledIterate, scheduleErrorBound]
      have one_step := prospectiveGradientStep_field_remainder_bound
        prediction actual affine actualField affineField entry.1 entry.2
        (stepFactor entry) rho (field_within actual actual_mem)
        affine_lipschitz
      exact ih.trans (scheduleErrorBound_mono stepFactor rho rest
        tail.factor_nonneg one_step)

/-- The state-space settled-credit error is the final-state error multiplied
by the absolute read precision. -/
theorem stateSettledCredit_field_remainder_bound
    (prediction : Credit) (radius rho readPrecision : ℝ)
    (actualField affineField : Credit → Credit)
    (stepFactor : ℝ × ℝ → ℝ)
    (schedule : List (ℝ × ℝ))
    (field_within :
      FieldWithinOnBall prediction radius rho actualField affineField)
    (path : CertifiedSchedulePath prediction radius actualField affineField
      stepFactor schedule prediction prediction) :
    ‖stateSettledCredit prediction
          (scheduledIterate prediction actualField schedule prediction)
          readPrecision -
        stateSettledCredit prediction
          (scheduledIterate prediction affineField schedule prediction)
          readPrecision‖ ≤
      |readPrecision| * scheduleErrorBound stepFactor rho schedule 0 := by
  have state_error := scheduledIterate_field_remainder_bound prediction radius
    rho actualField affineField stepFactor schedule prediction prediction
    field_within path
  simp only [sub_self, norm_zero] at state_error
  have credit_difference :
      stateSettledCredit prediction
            (scheduledIterate prediction actualField schedule prediction)
            readPrecision -
          stateSettledCredit prediction
            (scheduledIterate prediction affineField schedule prediction)
            readPrecision =
        readPrecision •
          (scheduledIterate prediction affineField schedule prediction -
            scheduledIterate prediction actualField schedule prediction) := by
    simp only [stateSettledCredit]
    module
  rw [credit_difference, norm_smul, Real.norm_eq_abs]
  have reversed_error :
      ‖scheduledIterate prediction affineField schedule prediction -
          scheduledIterate prediction actualField schedule prediction‖ ≤
        scheduleErrorBound stepFactor rho schedule 0 := by
    rw [norm_sub_rev]
    exact state_error
  exact mul_le_mul_of_nonneg_left reversed_error (abs_nonneg readPrecision)

/-- Nonlinear scheduled near-collapse.  A field remainder on a certified
settling ball incurs the explicit additional cosine charge obtained by
propagating `rho` through the scheduled affine Lipschitz factors. -/
theorem nonlinearScheduledCredit_cosine_lower_bound
    (prediction bp : Credit) (radius rho readPrecision kappa : ℝ)
    (actualField affineField : Credit → Credit)
    (stepFactor : ℝ × ℝ → ℝ)
    (schedule : List (ℝ × ℝ))
    (rho_nonneg : 0 ≤ rho)
    (field_within :
      FieldWithinOnBall prediction radius rho actualField affineField)
    (path : CertifiedSchedulePath prediction radius actualField affineField
      stepFactor schedule prediction prediction)
    (bp_ne_zero : bp ≠ 0)
    (actual_credit_ne_zero :
      stateSettledCredit prediction
        (scheduledIterate prediction actualField schedule prediction)
        readPrecision ≠ 0)
    (base_norm_pos :
      0 < ‖stateSettledCredit prediction
        (scheduledIterate prediction affineField schedule prediction)
        readPrecision‖)
    (margin_nonneg :
      0 ≤ kappa *
          ‖stateSettledCredit prediction
            (scheduledIterate prediction affineField schedule prediction)
            readPrecision‖ -
        |readPrecision| * scheduleErrorBound stepFactor rho schedule 0)
    (base_alignment :
      kappa *
          ‖stateSettledCredit prediction
            (scheduledIterate prediction affineField schedule prediction)
            readPrecision‖ * ‖bp‖ ≤
        ⟪stateSettledCredit prediction
            (scheduledIterate prediction affineField schedule prediction)
            readPrecision, bp⟫_ℝ) :
    let errorBudget :=
      |readPrecision| * scheduleErrorBound stepFactor rho schedule 0
    let actualCredit := stateSettledCredit prediction
      (scheduledIterate prediction actualField schedule prediction)
      readPrecision
    let baseCredit := stateSettledCredit prediction
      (scheduledIterate prediction affineField schedule prediction)
      readPrecision
    (kappa * ‖baseCredit‖ - errorBudget) /
        (‖baseCredit‖ + errorBudget) ≤ realCosine actualCredit bp := by
  dsimp only
  apply remainder_cosine_lower_bound _ _ _ kappa
    (|readPrecision| * scheduleErrorBound stepFactor rho schedule 0)
    bp_ne_zero actual_credit_ne_zero base_norm_pos
  · exact mul_nonneg (abs_nonneg readPrecision)
      (scheduleErrorBound_nonneg stepFactor rho schedule rho_nonneg
        path.factor_nonneg (by positivity))
  · exact margin_nonneg
  · exact base_alignment
  · exact stateSettledCredit_field_remainder_bound prediction radius rho
      readPrecision actualField affineField stepFactor schedule field_within path

/-! ## Schedule--geometry interaction -/

namespace ScheduleInteraction

def curvature : Fin 2 → ℝ := ![0, 2]

def bpCredit : Fin 2 → ℝ := ![1, 1]

def firstSchedule : List (ℝ × ℝ) := [(1 / 4, 2)]

def secondSchedule : List (ℝ × ℝ) := [(1 / 4, 2), (1 / 4, 2)]

theorem firstCredit :
    scheduledDiagonalCredit 2 firstSchedule curvature bpCredit = ![1 / 2, 1 / 2] := by
  funext index
  fin_cases index <;>
    norm_num [scheduledDiagonalCredit, scheduledScale, scheduleCoefficient,
      diagonalScale, firstSchedule, curvature, bpCredit]

theorem secondCredit :
    scheduledDiagonalCredit 2 secondSchedule curvature bpCredit = ![3 / 4, 1 / 2] := by
  funext index
  fin_cases index <;>
    norm_num [scheduledDiagonalCredit, scheduledScale, scheduleCoefficient,
      diagonalScale, secondSchedule, curvature, bpCredit]

/-- Outside scalar curvature, changing the schedule changes the settled
direction; the scalar-curvature hypothesis is therefore load-bearing. -/
theorem schedules_produce_nonproportional_directions :
    ¬ ∃ factor : ℝ,
      scheduledDiagonalCredit 2 secondSchedule curvature bpCredit =
        factor • scheduledDiagonalCredit 2 firstSchedule curvature bpCredit := by
  rintro ⟨factor, hfactor⟩
  rw [firstCredit, secondCredit] at hfactor
  have h0 := congrFun hfactor 0
  have h1 := congrFun hfactor 1
  norm_num at h0 h1
  nlinarith

end ScheduleInteraction

#print axioms diagonalScale_kantorovich_squared
#print axioms coordinateCosine_pos_smul_self
#print axioms kantorovichFactor_le_coordinateCosine_diagonalScale
#print axioms TightWitness.coordinateCosine_eq_kantorovichFactor
#print axioms TwoEndpointTightFamily.coordinateCosine_eq_kantorovichFactor
#print axioms kantorovichFactor_le_scheduledDiagonalCredit_cosine
#print axioms remainder_cosine_lower_bound
#print axioms scheduledIterate_field_remainder_bound
#print axioms nonlinearScheduledCredit_cosine_lower_bound
#print axioms ScheduleInteraction.schedules_produce_nonproportional_directions

end

end SettledCreditSpectralGeometry

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
