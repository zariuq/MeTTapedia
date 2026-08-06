import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CarrierCutHybridDescent

/-!
# Closed-form settled credit for affine task-gradient fields

For an affine task-gradient field with scalar curvature `a` about the
prediction point, `T` prospective settling steps from the prediction admit an
exact closed form: the iterate is `p - (r * Σ_{k<T} c^k) • δ` with contraction
factor `c = 1 - r * (π + a)` and `δ` the backpropagated credit at the
prediction.  Three consequences:

* **Depth-uniform collapse.**  The settled local credit is a *positive scalar
  multiple* of the backpropagated credit at *every* settling depth whenever
  the contraction factor is nonnegative.  Deeper settling changes the scale,
  never the direction.  Directional departure therefore cannot be produced by
  the settling depth, the rate, or the precision alone.
* **Curvature spread is the departure mechanism.**  With two distinct
  curvature eigenvalues the per-coordinate scales differ and the settled
  credit is provably not a scalar multiple of the backpropagated credit,
  while still having strictly positive inner product with it: the
  departs-but-descends band is inhabited.
* **A persistent anchor biases credit by an explicit, rate-independent
  direction.**  Adding an anchor term `μ • (s - m)` to the field is exactly a
  curvature shift plus a bias: the settled credit becomes a positive multiple
  of `δ + μ • (p - m)`.  The departure direction is toward the anchor, its
  relative magnitude is `μ * ‖p - m‖ / ‖δ‖`, and it does not vanish as the
  rate or depth vary.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SettledCreditClosedForm

open scoped InnerProductSpace
open CarrierOutputPC
open ProspectiveResidualSemantics

noncomputable section

variable {State Parameter : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- Affine task-gradient field with scalar curvature about the prediction:
`g s = a • (s - p) + δ`, so `δ` is the backpropagated credit at `p`. -/
def scalarCurvatureField (prediction : State) (curvature : ℝ)
    (bpCredit : State) : State → State :=
  fun state => curvature • (state - prediction) + bpCredit

@[simp] theorem scalarCurvatureField_apply_self
    (prediction : State) (curvature : ℝ) (bpCredit : State) :
    scalarCurvatureField prediction curvature bpCredit prediction = bpCredit := by
  simp [scalarCurvatureField]

/-- `T` accepted prospective settling steps started at the prediction. -/
def settleIterate (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (depth : ℕ) : State :=
  (prospectiveGradientStep prediction precision rate taskGradient)^[depth]
    prediction

/-- The per-step contraction factor of the affine settling recursion. -/
def contractionFactor (precision rate curvature : ℝ) : ℝ :=
  1 - rate * (precision + curvature)

/-- Partial geometric sum of the contraction factor. -/
def settleSum (precision rate curvature : ℝ) (depth : ℕ) : ℝ :=
  ∑ k ∈ Finset.range depth, contractionFactor precision rate curvature ^ k

@[simp] theorem settleSum_zero (precision rate curvature : ℝ) :
    settleSum precision rate curvature 0 = 0 := by
  simp [settleSum]

@[simp] theorem settleSum_one (precision rate curvature : ℝ) :
    settleSum precision rate curvature 1 = 1 := by
  simp [settleSum]

theorem settleSum_succ (precision rate curvature : ℝ) (depth : ℕ) :
    settleSum precision rate curvature (depth + 1) =
      1 + contractionFactor precision rate curvature *
        settleSum precision rate curvature depth := by
  rw [settleSum, settleSum, geom_sum_succ]
  ring

/-- With a nonnegative contraction factor the settle sum is at least one for
every positive depth. -/
theorem one_le_settleSum
    {precision rate curvature : ℝ}
    (factor_nonneg : 0 ≤ contractionFactor precision rate curvature)
    {depth : ℕ} (depth_pos : 1 ≤ depth) :
    1 ≤ settleSum precision rate curvature depth := by
  induction depth with
  | zero => omega
  | succ prior ih =>
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero prior)) with h | h
    · cases prior with
      | zero => simp
      | succ p => omega
    · cases prior with
      | zero => simp
      | succ p =>
        have prior_ge : 1 ≤ settleSum precision rate curvature (p + 1) :=
          ih (Nat.succ_le_succ (Nat.zero_le p))
        have sum_nonneg :
            0 ≤ contractionFactor precision rate curvature *
              settleSum precision rate curvature (p + 1) :=
          mul_nonneg factor_nonneg (le_trans zero_le_one prior_ge)
        calc 1 ≤ 1 + contractionFactor precision rate curvature *
                settleSum precision rate curvature (p + 1) := by linarith
        _ = settleSum precision rate curvature (p + 1 + 1) :=
            (settleSum_succ precision rate curvature (p + 1)).symm

theorem settleSum_pos
    {precision rate curvature : ℝ}
    (factor_nonneg : 0 ≤ contractionFactor precision rate curvature)
    {depth : ℕ} (depth_pos : 1 ≤ depth) :
    0 < settleSum precision rate curvature depth :=
  lt_of_lt_of_le one_pos (one_le_settleSum factor_nonneg depth_pos)

/-! ## The closed form -/

/-- Exact closed form for the settle iterate of a scalar-curvature affine
field: `T` steps from the prediction land at
`p - (rate * settleSum T) • δ`. -/
theorem settleIterate_scalarCurvatureField
    (prediction : State) (precision rate curvature : ℝ) (bpCredit : State) :
    ∀ depth : ℕ,
      settleIterate prediction precision rate
          (scalarCurvatureField prediction curvature bpCredit) depth =
        prediction -
          (rate * settleSum precision rate curvature depth) • bpCredit := by
  intro depth
  induction depth with
  | zero => simp [settleIterate]
  | succ prior ih =>
    have step :
        settleIterate prediction precision rate
            (scalarCurvatureField prediction curvature bpCredit) (prior + 1) =
          prospectiveGradientStep prediction precision rate
            (scalarCurvatureField prediction curvature bpCredit)
            (settleIterate prediction precision rate
              (scalarCurvatureField prediction curvature bpCredit) prior) := by
      simp [settleIterate, Function.iterate_succ_apply']
    rw [step, ih, prospectiveGradientStep, prospectiveEnergyGradient,
      scalarCurvatureField, settleSum_succ, contractionFactor]
    have displacement :
        prediction - (rate * settleSum precision rate curvature prior) • bpCredit -
            prediction =
          -((rate * settleSum precision rate curvature prior) • bpCredit) := by
      abel
    rw [displacement]
    simp only [smul_neg, smul_smul]
    module

/-- **Depth-uniform collapse.**  For every settling depth, the settled local
credit of a scalar-curvature affine field is an explicit scalar multiple of
the backpropagated credit. -/
theorem settledCredit_eq_smul_carrierBPCredit
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction : State) (precision rate curvature : ℝ) (bpCredit : State)
    (depth : ℕ) :
    carrierLocalCredit pullback prediction
        (settleIterate prediction precision rate
          (scalarCurvatureField prediction curvature bpCredit) depth)
        precision =
      (precision * (rate * settleSum precision rate curvature depth)) •
        carrierBPCredit pullback
          (scalarCurvatureField prediction curvature bpCredit) prediction := by
  rw [settleIterate_scalarCurvatureField, carrierLocalCredit, carrierBPCredit,
    pulledCredit, pulledCredit, scalarCurvatureField_apply_self]
  have residual :
      prediction -
          (prediction -
            (rate * settleSum precision rate curvature depth) • bpCredit) =
        (rate * settleSum precision rate curvature depth) • bpCredit := by
    abel
  rw [residual, smul_smul, map_smul]

/-- The collapse is positive: under a nonnegative contraction factor and
positive precision and rate, the settled credit is a *positive* multiple of
the backpropagated credit at every positive depth.  Depth, rate, and
precision can therefore never produce directional departure for
scalar-curvature fields. -/
theorem exists_pos_smul_settledCredit
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction : State) {precision rate curvature : ℝ} (bpCredit : State)
    (precision_pos : 0 < precision) (rate_pos : 0 < rate)
    (factor_nonneg : 0 ≤ contractionFactor precision rate curvature)
    {depth : ℕ} (depth_pos : 1 ≤ depth) :
    ∃ scale : ℝ, 0 < scale ∧
      carrierLocalCredit pullback prediction
          (settleIterate prediction precision rate
            (scalarCurvatureField prediction curvature bpCredit) depth)
          precision =
        scale • carrierBPCredit pullback
          (scalarCurvatureField prediction curvature bpCredit) prediction := by
  refine ⟨precision * (rate * settleSum precision rate curvature depth),
    ?_, settledCredit_eq_smul_carrierBPCredit pullback prediction precision
      rate curvature bpCredit depth⟩
  have sum_pos := settleSum_pos factor_nonneg depth_pos
  positivity

/-- Depth one recovers the sealed first-step scale `precision * rate`. -/
theorem settledCredit_depth_one_scale
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction : State) (precision rate curvature : ℝ) (bpCredit : State) :
    carrierLocalCredit pullback prediction
        (settleIterate prediction precision rate
          (scalarCurvatureField prediction curvature bpCredit) 1)
        precision =
      (precision * rate) • carrierBPCredit pullback
        (scalarCurvatureField prediction curvature bpCredit) prediction := by
  simpa using settledCredit_eq_smul_carrierBPCredit pullback prediction
    precision rate curvature bpCredit 1

/-! ## A persistent anchor is a curvature shift plus a credit bias -/

/-- Task-gradient field with an additional persistent anchor pull of weight
`anchorWeight` toward the anchor `m`. -/
def anchoredField (prediction : State) (curvature : ℝ) (bpCredit : State)
    (anchorWeight : ℝ) (anchor : State) : State → State :=
  fun state =>
    scalarCurvatureField prediction curvature bpCredit state +
      anchorWeight • (state - anchor)

/-- The anchored field *is* a scalar-curvature field: curvature shifts by the
anchor weight and the backpropagated credit gains the bias
`anchorWeight • (p - m)`. -/
theorem anchoredField_eq_scalarCurvatureField
    (prediction : State) (curvature : ℝ) (bpCredit : State)
    (anchorWeight : ℝ) (anchor : State) :
    anchoredField prediction curvature bpCredit anchorWeight anchor =
      scalarCurvatureField prediction (curvature + anchorWeight)
        (bpCredit + anchorWeight • (prediction - anchor)) := by
  funext state
  simp only [anchoredField, scalarCurvatureField]
  module

/-- **Persistent-anchor bias.**  Settled credit under an anchored field is an
explicit scalar multiple of `δ + anchorWeight • (p - m)`: the departure
direction is toward the anchor, with relative magnitude
`anchorWeight * ‖p - m‖` against `‖δ‖`, at every depth. -/
theorem anchored_settledCredit_eq_smul_biased
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction : State) (precision rate curvature : ℝ) (bpCredit : State)
    (anchorWeight : ℝ) (anchor : State) (depth : ℕ) :
    carrierLocalCredit pullback prediction
        (settleIterate prediction precision rate
          (anchoredField prediction curvature bpCredit anchorWeight anchor)
          depth)
        precision =
      (precision *
        (rate * settleSum precision rate (curvature + anchorWeight) depth)) •
        pulledCredit pullback
          (bpCredit + anchorWeight • (prediction - anchor)) := by
  rw [anchoredField_eq_scalarCurvatureField]
  simpa [carrierBPCredit] using
    settledCredit_eq_smul_carrierBPCredit pullback prediction precision rate
      (curvature + anchorWeight)
      (bpCredit + anchorWeight • (prediction - anchor)) depth

/-! ## Schedule-uniform collapse

A staged settling schedule assigns each step its own rate and precision.  On a
scalar-curvature field the iterate never leaves the line through the
prediction in the direction of the backpropagated credit, so the settled
credit remains a nonnegative multiple of BP for *every* schedule: staging can
change the scale, never the direction.  Directional departure therefore
cannot be attributed to a settling schedule either. -/

/-- Run one prospective step per schedule entry `(rate, precision)`. -/
def scheduledIterate (prediction : State) (taskGradient : State → State) :
    List (ℝ × ℝ) → State → State
  | [], state => state
  | (rate, precision) :: rest, state =>
      scheduledIterate prediction taskGradient rest
        (prospectiveGradientStep prediction precision rate taskGradient state)

/-- Displacement coefficient accumulated by a schedule along the credit
line, starting from coefficient `t`. -/
def scheduleCoefficient (curvature : ℝ) : List (ℝ × ℝ) → ℝ → ℝ
  | [], t => t
  | (rate, precision) :: rest, t =>
      scheduleCoefficient curvature rest
        (t * (1 - rate * (precision + curvature)) + rate)

/-- The scheduled iterate of a scalar-curvature field stays on the credit
line, with displacement given by the schedule coefficient. -/
theorem scheduledIterate_scalarCurvatureField
    (prediction : State) (curvature : ℝ) (bpCredit : State) :
    ∀ (schedule : List (ℝ × ℝ)) (t : ℝ),
      scheduledIterate prediction
          (scalarCurvatureField prediction curvature bpCredit) schedule
          (prediction - t • bpCredit) =
        prediction - scheduleCoefficient curvature schedule t • bpCredit := by
  intro schedule
  induction schedule with
  | nil => intro t; rfl
  | cons entry rest ih =>
    intro t
    obtain ⟨rate, precision⟩ := entry
    have step :
        prospectiveGradientStep prediction precision rate
            (scalarCurvatureField prediction curvature bpCredit)
            (prediction - t • bpCredit) =
          prediction -
            (t * (1 - rate * (precision + curvature)) + rate) • bpCredit := by
      rw [prospectiveGradientStep, prospectiveEnergyGradient,
        scalarCurvatureField]
      have displacement :
          prediction - t • bpCredit - prediction = -(t • bpCredit) := by abel
      rw [displacement]
      simp only [smul_neg, smul_smul]
      module
    rw [scheduledIterate, step, ih, scheduleCoefficient]

/-- Nonnegative factors and rates keep the schedule coefficient nonnegative. -/
theorem scheduleCoefficient_nonneg (curvature : ℝ) :
    ∀ (schedule : List (ℝ × ℝ)) (t : ℝ), 0 ≤ t →
      (∀ entry ∈ schedule,
        0 ≤ entry.1 ∧ 0 ≤ 1 - entry.1 * (entry.2 + curvature)) →
      0 ≤ scheduleCoefficient curvature schedule t := by
  intro schedule
  induction schedule with
  | nil => intro t ht _; exact ht
  | cons entry rest ih =>
    intro t ht hall
    obtain ⟨hrate, hfactor⟩ := hall entry (List.mem_cons_self ..)
    refine ih _ ?_ fun e he => hall e (List.mem_cons_of_mem _ he)
    have : 0 ≤ t * (1 - entry.1 * (entry.2 + curvature)) :=
      mul_nonneg ht hfactor
    obtain ⟨rate, precision⟩ := entry
    dsimp at *
    linarith

/-- A schedule whose final rate is positive produces a strictly positive
coefficient. -/
theorem scheduleCoefficient_pos (curvature : ℝ)
    (schedule : List (ℝ × ℝ)) (final : ℝ × ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hall : ∀ entry ∈ schedule ++ [final],
      0 ≤ entry.1 ∧ 0 ≤ 1 - entry.1 * (entry.2 + curvature))
    (hfinal : 0 < final.1) :
    0 < scheduleCoefficient curvature (schedule ++ [final]) t := by
  induction schedule generalizing t with
  | nil =>
    obtain ⟨rate, precision⟩ := final
    have hfactor := (hall (rate, precision) (by simp)).2
    have : 0 ≤ t * (1 - rate * (precision + curvature)) :=
      mul_nonneg ht hfactor
    simp only [List.nil_append, scheduleCoefficient]
    dsimp at hfinal ⊢
    linarith
  | cons entry rest ih =>
    obtain ⟨hrate, hfactor⟩ := hall entry (List.mem_cons_self ..)
    have hnext : 0 ≤ t * (1 - entry.1 * (entry.2 + curvature)) + entry.1 := by
      have := mul_nonneg ht hfactor
      linarith
    simpa [scheduleCoefficient] using
      ih _ hnext fun e he => hall e (List.mem_cons_of_mem _ he)

/-- **Schedule-uniform collapse.**  For any staged schedule of prospective
steps on a scalar-curvature field, the settled local credit read at any
positive precision is a nonnegative multiple of the backpropagated credit —
strictly positive when the final scheduled rate is positive.  A settling
schedule alone can never produce directional departure. -/
theorem scheduled_settledCredit_pos_smul
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction : State) (curvature : ℝ) (bpCredit : State)
    (readPrecision : ℝ) (readPrecision_pos : 0 < readPrecision)
    (schedule : List (ℝ × ℝ)) (final : ℝ × ℝ)
    (hall : ∀ entry ∈ schedule ++ [final],
      0 ≤ entry.1 ∧ 0 ≤ 1 - entry.1 * (entry.2 + curvature))
    (hfinal : 0 < final.1) :
    ∃ scale : ℝ, 0 < scale ∧
      carrierLocalCredit pullback prediction
          (scheduledIterate prediction
            (scalarCurvatureField prediction curvature bpCredit)
            (schedule ++ [final]) prediction)
          readPrecision =
        scale • carrierBPCredit pullback
          (scalarCurvatureField prediction curvature bpCredit) prediction := by
  have iterate_eq :
      scheduledIterate prediction
          (scalarCurvatureField prediction curvature bpCredit)
          (schedule ++ [final]) prediction =
        prediction -
          scheduleCoefficient curvature (schedule ++ [final]) 0 • bpCredit := by
    have closed := scheduledIterate_scalarCurvatureField prediction curvature
      bpCredit (schedule ++ [final]) 0
    simpa using closed
  refine ⟨readPrecision *
    scheduleCoefficient curvature (schedule ++ [final]) 0, ?_, ?_⟩
  · have := scheduleCoefficient_pos curvature schedule final 0 le_rfl hall hfinal
    positivity
  · rw [iterate_eq, carrierLocalCredit,
      carrierBPCredit, pulledCredit, pulledCredit,
      scalarCurvatureField_apply_self]
    have residual :
        prediction -
            (prediction -
              scheduleCoefficient curvature (schedule ++ [final]) 0 • bpCredit) =
          scheduleCoefficient curvature (schedule ++ [final]) 0 • bpCredit := by
      abel
    rw [residual, smul_smul, map_smul]

end

/-! ## Curvature spread: the two-eigenvalue departure witness

With two distinct curvature eigenvalues the per-coordinate settle scales
differ, so the settled credit is not any scalar multiple of the
backpropagated credit — yet its inner product with the backpropagated credit
remains strictly positive.  Numbers: precision `20`, rate `1/40`
(`rate * precision = 1/2`), depth `2`, curvatures `0` and `20`, credit
`(1, 1)`.  The coordinate scales are `π r S = 3/4` and `1/2`. -/

namespace SpreadWitness

open ProspectiveResidualSemantics

/-- Diagonal affine field on the Euclidean plane with per-coordinate
curvatures `0` and `20` about the origin and backpropagated credit `(1, 1)`. -/
noncomputable def diagonalField
    (state : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    ![0 * state 0 + 1, 20 * state 1 + 1]

/-- Two settling steps of the diagonal field from the origin, computed
explicitly: the two coordinates settle at different scales. -/
noncomputable def settledState : EuclideanSpace ℝ (Fin 2) :=
  (prospectiveGradientStep (0 : EuclideanSpace ℝ (Fin 2)) 20 (1 / 40)
      diagonalField)^[2] 0

/-- The settled local credit `precision • (prediction - settled)` in the
plane. -/
noncomputable def settledCredit : EuclideanSpace ℝ (Fin 2) :=
  (20 : ℝ) • ((0 : EuclideanSpace ℝ (Fin 2)) - settledState)

/-- Backpropagated credit at the prediction. -/
noncomputable def bpCredit : EuclideanSpace ℝ (Fin 2) := diagonalField 0

theorem settledState_eval :
    settledState =
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-(3 / 80), -(1 / 40)] := by
  have step :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        prospectiveGradientStep (0 : EuclideanSpace ℝ (Fin 2)) 20 (1 / 40)
            diagonalField x =
          x - (1 / 40 : ℝ) • (diagonalField x + (20 : ℝ) • x) := by
    intro x
    simp [prospectiveGradientStep, prospectiveEnergyGradient]
  rw [settledState]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, step]
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  funext i
  fin_cases i <;>
    simp [diagonalField, WithLp.equiv, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> norm_num

theorem bpCredit_eval :
    bpCredit = (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![1, 1] := by
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  funext i
  fin_cases i <;> simp [bpCredit, diagonalField]

theorem settledCredit_eval :
    settledCredit = (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3 / 4, 1 / 2] := by
  rw [settledCredit, settledState_eval]
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  funext i
  fin_cases i <;> simp [WithLp.equiv] <;> norm_num

/-- **Departure.**  With curvature spread the settled credit is not any
scalar multiple of the backpropagated credit: depth, rate, and precision
preserved direction in the scalar-curvature case, so spread is the mechanism
that breaks it. -/
theorem settledCredit_not_smul_bpCredit :
    ¬ ∃ scale : ℝ, settledCredit = scale • bpCredit := by
  rintro ⟨scale, h⟩
  rw [settledCredit_eval, bpCredit_eval] at h
  have h' := congrArg (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)) h
  rw [map_smul] at h'
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  simp [WithLp.linearEquiv, WithLp.equiv] at h0 h1
  norm_num [← h0] at h1

/-- **Descent.**  The same settled credit still has strictly positive inner
product with the backpropagated credit: the departure band is inhabited. -/
theorem settledCredit_inner_bpCredit_pos :
    0 < ⟪settledCredit, bpCredit⟫_ℝ := by
  rw [settledCredit_eval, bpCredit_eval, PiLp.inner_apply]
  simp [RCLike.inner_apply, WithLp.equiv, Fin.sum_univ_two]
  norm_num

end SpreadWitness

#print axioms SettledCreditClosedForm.settleIterate_scalarCurvatureField
#print axioms SettledCreditClosedForm.settledCredit_eq_smul_carrierBPCredit
#print axioms SettledCreditClosedForm.exists_pos_smul_settledCredit
#print axioms SettledCreditClosedForm.anchored_settledCredit_eq_smul_biased
#print axioms SettledCreditClosedForm.SpreadWitness.settledCredit_not_smul_bpCredit
#print axioms SettledCreditClosedForm.SpreadWitness.settledCredit_inner_bpCredit_pos
#print axioms SettledCreditClosedForm.scheduledIterate_scalarCurvatureField
#print axioms SettledCreditClosedForm.scheduleCoefficient_pos
#print axioms SettledCreditClosedForm.scheduled_settledCredit_pos_smul

end SettledCreditClosedForm

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
