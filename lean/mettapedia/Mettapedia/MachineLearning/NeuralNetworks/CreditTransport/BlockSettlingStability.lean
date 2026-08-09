/-
# Stability of block-diagonal settling under global, blockwise, and damped steps

Local model: a block-diagonal quadratic energy with per-block curvature
`curvature i > 0` and linear target `target i`.  The settle field on block `i`
is the affine residual `curvature i * state i - target i`.  This is the exact
local model of multi-site settling near an equilibrium; the nonconvex basin
question for the full nonlinear energy is *not* addressed here and remains
open.

Results:

* All three iterations — one global rate, per-block rates, and
  Levenberg-style damping — have exactly the same stationary set.  Solver
  substitution cannot move an equilibrium.
* Exact per-block error recursions and iterate closed forms.
* The global-rate dilemma: any global rate either destabilizes the stiffest
  block or retains, after `T` steps, at least `1 - T * (2 * tame / stiff)` of
  a tame block's error.  As curvature spread grows, a stable global rate
  starves every tame block.
* Per-block rates `c / curvature i` contract every block by the same factor
  `1 - c`, independent of spread; `c = 1` settles in one step.
* Damping is unconditionally stable: for every `damping ≥ 0` the per-block
  factor lies in `[0, 1)`.
* A fixed residual tolerance bounds no credit error uniformly across models:
  the credit weight can amplify an arbitrarily small residual arbitrarily.
* A departure witness with curvature ratio two: settled credit has positive
  inner product with the instantaneous credit, is not a scalar multiple of
  it, and has squared cosine strictly below one — while every block is
  strictly contracting under the global rate.  Directional departure needs
  curvature spread, not degenerate conditioning.
-/

import Mathlib.Tactic

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.BlockSettlingStability

variable {n : ℕ}

/-! ## The three iterations and their common stationary set -/

/-- One settle step with a single global rate. -/
def globalStep (curvature target : Fin n → ℝ) (rate : ℝ)
    (state : Fin n → ℝ) : Fin n → ℝ :=
  fun i => state i - rate * (curvature i * state i - target i)

/-- One settle step with an individual rate on every block. -/
def blockStep (curvature target : Fin n → ℝ) (rates : Fin n → ℝ)
    (state : Fin n → ℝ) : Fin n → ℝ :=
  fun i => state i - rates i * (curvature i * state i - target i)

/-- One Levenberg-style damped step: the residual is divided by the damped
curvature instead of being scaled by an explicit rate. -/
noncomputable def dampedStep (curvature target : Fin n → ℝ) (damping : ℝ)
    (state : Fin n → ℝ) : Fin n → ℝ :=
  fun i => state i - (curvature i * state i - target i) / (curvature i + damping)

/-- Stationarity of the block-diagonal settle field. -/
def IsStationary (curvature target : Fin n → ℝ) (state : Fin n → ℝ) : Prop :=
  ∀ i, curvature i * state i - target i = 0

theorem globalStep_fixed_iff (curvature target : Fin n → ℝ) {rate : ℝ}
    (hrate : rate ≠ 0) (state : Fin n → ℝ) :
    globalStep curvature target rate state = state ↔
      IsStationary curvature target state := by
  constructor
  · intro hfix i
    have h := congrFun hfix i
    simp only [globalStep] at h
    have hzero : rate * (curvature i * state i - target i) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hbad | hgood
    · exact absurd hbad hrate
    · exact hgood
  · intro hstat
    funext i
    simp [globalStep, hstat i]

theorem blockStep_fixed_iff (curvature target : Fin n → ℝ) {rates : Fin n → ℝ}
    (hrates : ∀ i, rates i ≠ 0) (state : Fin n → ℝ) :
    blockStep curvature target rates state = state ↔
      IsStationary curvature target state := by
  constructor
  · intro hfix i
    have h := congrFun hfix i
    simp only [blockStep] at h
    have hzero : rates i * (curvature i * state i - target i) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hbad | hgood
    · exact absurd hbad (hrates i)
    · exact hgood
  · intro hstat
    funext i
    simp [blockStep, hstat i]

theorem dampedStep_fixed_iff (curvature target : Fin n → ℝ) {damping : ℝ}
    (hpos : ∀ i, 0 < curvature i + damping) (state : Fin n → ℝ) :
    dampedStep curvature target damping state = state ↔
      IsStationary curvature target state := by
  constructor
  · intro hfix i
    have h := congrFun hfix i
    simp only [dampedStep] at h
    have hzero : (curvature i * state i - target i) / (curvature i + damping) = 0 := by
      linarith
    exact (div_eq_zero_iff.mp hzero).resolve_right (ne_of_gt (hpos i))
  · intro hstat
    funext i
    simp [dampedStep, hstat i]

/-- **Solver substitution cannot move an equilibrium.**  The global,
blockwise, and damped iterations have identical stationary sets. -/
theorem stationary_set_shared (curvature target : Fin n → ℝ)
    {rate : ℝ} (hrate : rate ≠ 0) {rates : Fin n → ℝ}
    (hrates : ∀ i, rates i ≠ 0) {damping : ℝ}
    (hpos : ∀ i, 0 < curvature i + damping) (state : Fin n → ℝ) :
    (globalStep curvature target rate state = state ↔
      blockStep curvature target rates state = state) ∧
    (globalStep curvature target rate state = state ↔
      dampedStep curvature target damping state = state) := by
  constructor
  · rw [globalStep_fixed_iff curvature target hrate,
      blockStep_fixed_iff curvature target hrates]
  · rw [globalStep_fixed_iff curvature target hrate,
      dampedStep_fixed_iff curvature target hpos]

/-! ## Exact error recursions -/

/-- The unique per-block equilibrium of a positive-curvature block. -/
noncomputable def equilibrium (curvature target : Fin n → ℝ) : Fin n → ℝ :=
  fun i => target i / curvature i

theorem globalStep_error (curvature target : Fin n → ℝ) (rate : ℝ)
    (state : Fin n → ℝ) {i : Fin n} (hcurv : curvature i ≠ 0) :
    globalStep curvature target rate state i - equilibrium curvature target i =
      (1 - rate * curvature i) *
        (state i - equilibrium curvature target i) := by
  simp only [globalStep, equilibrium]
  field_simp
  ring

theorem blockStep_error (curvature target : Fin n → ℝ) (rates : Fin n → ℝ)
    (state : Fin n → ℝ) {i : Fin n} (hcurv : curvature i ≠ 0) :
    blockStep curvature target rates state i - equilibrium curvature target i =
      (1 - rates i * curvature i) *
        (state i - equilibrium curvature target i) := by
  simp only [blockStep, equilibrium]
  field_simp
  ring

theorem dampedStep_error (curvature target : Fin n → ℝ) (damping : ℝ)
    (state : Fin n → ℝ) {i : Fin n} (hcurv : curvature i ≠ 0)
    (hdenom : curvature i + damping ≠ 0) :
    dampedStep curvature target damping state i - equilibrium curvature target i =
      (damping / (curvature i + damping)) *
        (state i - equilibrium curvature target i) := by
  simp only [dampedStep, equilibrium]
  field_simp
  ring

/-- Iterate closed form for the global rate. -/
theorem globalStep_iterate_error (curvature target : Fin n → ℝ) (rate : ℝ)
    (state : Fin n → ℝ) {i : Fin n} (hcurv : curvature i ≠ 0) (T : ℕ) :
    (globalStep curvature target rate)^[T] state i -
        equilibrium curvature target i =
      (1 - rate * curvature i) ^ T *
        (state i - equilibrium curvature target i) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Function.iterate_succ_apply',
        globalStep_error curvature target rate _ hcurv, ih, pow_succ]
      ring

/-! ## The global-rate dilemma -/

/-- A global rate beyond the stiff stability edge amplifies the stiff block's
error at every step. -/
theorem stiff_block_unstable {stiff rate : ℝ} (hstiff : 0 < stiff)
    (hrate : 2 / stiff < rate) : 1 < |1 - rate * stiff| := by
  have hgrow : 2 < rate * stiff := by
    calc 2 = 2 / stiff * stiff := by field_simp
    _ < rate * stiff := by
        exact mul_lt_mul_of_pos_right hrate hstiff
  rw [abs_of_neg (by linarith)]
  linarith

/-- A stiff-stable global rate retains, after `T` steps, at least
`1 - T * (2 * tame / stiff)` of a tame block's error fraction.  As the spread
`stiff / tame` grows with `T` fixed, the retained fraction approaches one:
the tame block is starved. -/
theorem tame_block_starved {tame stiff rate : ℝ} (htame : 0 < tame)
    (hspread : 2 * tame ≤ stiff) (_hrate_nonneg : 0 ≤ rate)
    (hrate : rate ≤ 2 / stiff) (T : ℕ) :
    1 - (T : ℝ) * (2 * tame / stiff) ≤ (1 - rate * tame) ^ T := by
  have hstiff : 0 < stiff := lt_of_lt_of_le (by linarith) hspread
  have hfrac_le_one : 2 * tame / stiff ≤ 1 := by
    rw [div_le_one hstiff]
    linarith
  have hfrac_nonneg : 0 ≤ 2 * tame / stiff := by positivity
  have hstep : rate * tame ≤ 2 * tame / stiff := by
    calc rate * tame ≤ 2 / stiff * tame := by
          exact mul_le_mul_of_nonneg_right hrate (le_of_lt htame)
    _ = 2 * tame / stiff := by ring
  have hbase_nonneg : 0 ≤ 1 - 2 * tame / stiff := by linarith
  have hbase_le : 1 - 2 * tame / stiff ≤ 1 - rate * tame := by linarith
  have hpow : (1 - 2 * tame / stiff) ^ T ≤ (1 - rate * tame) ^ T := by
    gcongr
  have hbernoulli :
      1 + (T : ℝ) * -(2 * tame / stiff) ≤ (1 + -(2 * tame / stiff)) ^ T := by
    exact one_add_mul_le_pow (by linarith) T
  have hrewrite : (1 + -(2 * tame / stiff)) ^ T = (1 - 2 * tame / stiff) ^ T := by
    ring_nf
  rw [hrewrite] at hbernoulli
  calc 1 - (T : ℝ) * (2 * tame / stiff) =
        1 + (T : ℝ) * -(2 * tame / stiff) := by ring
  _ ≤ (1 - 2 * tame / stiff) ^ T := hbernoulli
  _ ≤ (1 - rate * tame) ^ T := hpow

/-- Concrete starvation instance: curvatures `1` and `10^6`, the largest
stiff-stable-scale rate `10^-6`, eight settle steps — the tame block retains
at least `99%` of its error. -/
theorem starvation_instance :
    (99 / 100 : ℝ) ≤ (1 - (1 / 1000000 : ℝ) * 1) ^ 8 := by
  have h := tame_block_starved (tame := 1) (stiff := 1000000)
    (rate := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 8
  push_cast at h
  have hlow : (99 / 100 : ℝ) ≤ 1 - 8 * (2 * 1 / 1000000) := by norm_num
  linarith

/-! ## Spread-invariant alternatives -/

/-- Per-block rates `c / curvature i` contract every block by the same
factor `1 - c`, independent of curvature spread. -/
theorem blockStep_spread_invariant (curvature target : Fin n → ℝ) (c : ℝ)
    (state : Fin n → ℝ) {i : Fin n} (hcurv : curvature i ≠ 0) :
    blockStep curvature target (fun j => c / curvature j) state i -
        equilibrium curvature target i =
      (1 - c) * (state i - equilibrium curvature target i) := by
  rw [blockStep_error curvature target _ _ hcurv]
  congr 1
  field_simp

/-- `c = 1` settles every block exactly in one step. -/
theorem blockStep_newton_exact (curvature target : Fin n → ℝ)
    (state : Fin n → ℝ) {i : Fin n} (hcurv : curvature i ≠ 0) :
    blockStep curvature target (fun j => 1 / curvature j) state i =
      equilibrium curvature target i := by
  have h := blockStep_spread_invariant curvature target 1 state hcurv
  rw [show (1 : ℝ) - 1 = 0 by norm_num, zero_mul, sub_eq_zero] at h
  exact h

/-- Damping is unconditionally stable: for positive curvature and any
nonnegative damping, the per-block factor lies in `[0, 1)`. -/
theorem dampedStep_factor_stable {curvature damping : ℝ}
    (hcurv : 0 < curvature) (hdamp : 0 ≤ damping) :
    0 ≤ damping / (curvature + damping) ∧
      damping / (curvature + damping) < 1 := by
  have hdenom : 0 < curvature + damping := by linarith
  constructor
  · positivity
  · rw [div_lt_one hdenom]
    linarith

/-! ## A residual tolerance bounds no credit error uniformly -/

/-- Componentwise credit error is bounded by the residual once the credit
weights are bounded: the per-model constant is the weight bound. -/
theorem credit_error_le_weight_bound (weight residual : ℝ) {bound : ℝ}
    (hweight : |weight| ≤ bound) :
    |weight * residual| ≤ bound * |residual| := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right hweight (abs_nonneg residual)

/-- **No uniform constant exists.**  For every residual tolerance and every
demanded credit-error bound there is a model whose credit weight amplifies a
tolerance-satisfying residual beyond the bound.  A registered settling
tolerance must therefore be stated in credit units, or carry a per-model
weight bound. -/
theorem residual_tolerance_insufficient_for_credit (tolerance bound : ℝ)
    (htol : 0 < tolerance) :
    ∃ weight residual : ℝ,
      |residual| ≤ tolerance ∧ bound < |weight * residual| := by
  refine ⟨2 * (|bound| + 1) / tolerance, tolerance / 2, ?_, ?_⟩
  · rw [abs_of_pos (by positivity)]
    linarith
  · have hvalue : 2 * (|bound| + 1) / tolerance * (tolerance / 2) =
        |bound| + 1 := by
      field_simp
    rw [hvalue, abs_of_pos (by positivity)]
    have := abs_nonneg bound
    have := le_abs_self bound
    linarith

/-! ## Departure with bounded curvature spread

Settled credit after `T` global-rate steps from the zero state scales the
instantaneous credit `delta i` by the per-block factor
`rate * ∑_{k<T} (1 - rate * curvature i)^k`.  With curvatures `2` and `4`
(ratio two), rate `1/8`, and two steps, the scales are `7/32` and `6/32`:
distinct, both positive, both blocks strictly contracting.  The settled
credit therefore departs directionally from the instantaneous credit at
bounded conditioning. -/

/-- Per-block settled-credit scale after `T` steps at a global rate. -/
noncomputable def settleScale (rate curvature : ℝ) (T : ℕ) : ℝ :=
  rate * ∑ k ∈ Finset.range T, (1 - rate * curvature) ^ k

theorem settleScale_tame : settleScale (1 / 8) 2 2 = 7 / 32 := by
  simp [settleScale, Finset.sum_range_succ]
  norm_num

theorem settleScale_stiff : settleScale (1 / 8) 4 2 = 6 / 32 := by
  simp [settleScale, Finset.sum_range_succ]
  norm_num

/-- Both blocks of the witness are strictly contracting under the global
rate: the departure regime here is not the unstable regime. -/
theorem departure_witness_contracting :
    |1 - (1 / 8 : ℝ) * 2| < 1 ∧ |1 - (1 / 8 : ℝ) * 4| < 1 := by
  constructor <;> · rw [abs_of_pos (by norm_num)]; norm_num

/-- The settled credit is not a scalar multiple of the instantaneous credit:
per-block scales differ. -/
theorem departure_witness_not_parallel :
    ¬ ∃ c : ℝ,
      settleScale (1 / 8) 2 2 * 1 = c * 1 ∧
        settleScale (1 / 8) 4 2 * 1 = c * 1 := by
  rintro ⟨c, hfirst, hsecond⟩
  rw [settleScale_tame] at hfirst
  rw [settleScale_stiff] at hsecond
  norm_num at hfirst hsecond
  linarith

/-- Positive inner product: settled credit still descends along the
instantaneous credit. -/
theorem departure_witness_descent :
    0 < settleScale (1 / 8) 2 2 * 1 * 1 + settleScale (1 / 8) 4 2 * 1 * 1 := by
  rw [settleScale_tame, settleScale_stiff]
  norm_num

/-- Squared-cosine strictly below one, in exact rational arithmetic
(`169 < 170`): genuine directional departure at curvature ratio two. -/
theorem departure_witness_cosine_lt_one :
    (settleScale (1 / 8) 2 2 * 1 * 1 + settleScale (1 / 8) 4 2 * 1 * 1) ^ 2 <
      ((settleScale (1 / 8) 2 2 * 1) ^ 2 + (settleScale (1 / 8) 4 2 * 1) ^ 2) *
        ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) := by
  rw [settleScale_tame, settleScale_stiff]
  norm_num

/-- **Departure needs spread, not degeneracy.**  At curvature ratio two, with
every block strictly contracting, the settled credit has positive inner
product with the instantaneous credit, is not parallel to it, and has squared
cosine strictly below one. -/
theorem bounded_spread_departure :
    (|1 - (1 / 8 : ℝ) * 2| < 1 ∧ |1 - (1 / 8 : ℝ) * 4| < 1) ∧
      (0 < settleScale (1 / 8) 2 2 * 1 * 1 +
        settleScale (1 / 8) 4 2 * 1 * 1) ∧
      (¬ ∃ c : ℝ,
        settleScale (1 / 8) 2 2 * 1 = c * 1 ∧
          settleScale (1 / 8) 4 2 * 1 = c * 1) ∧
      ((settleScale (1 / 8) 2 2 * 1 * 1 +
          settleScale (1 / 8) 4 2 * 1 * 1) ^ 2 <
        ((settleScale (1 / 8) 2 2 * 1) ^ 2 +
            (settleScale (1 / 8) 4 2 * 1) ^ 2) *
          ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2)) :=
  ⟨departure_witness_contracting, departure_witness_descent,
    departure_witness_not_parallel, departure_witness_cosine_lt_one⟩

#print axioms stationary_set_shared
#print axioms globalStep_iterate_error
#print axioms stiff_block_unstable
#print axioms tame_block_starved
#print axioms starvation_instance
#print axioms blockStep_spread_invariant
#print axioms blockStep_newton_exact
#print axioms dampedStep_factor_stable
#print axioms credit_error_le_weight_bound
#print axioms residual_tolerance_insufficient_for_credit
#print axioms bounded_spread_departure

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.BlockSettlingStability
