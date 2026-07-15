import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PreconditionedLearning
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Coupled settling and weight dynamics

This file gives an exact discrete two-timescale model for a scalar linear
predictive-coding mode.  Each outer step first contracts the inference error
by a precision-controlled settling multiplier.  The weight step then uses the
new inference error together with the precision-weighted parameter error.

The resulting two-state transition is lower triangular.  Its fast multiplier
is `1 - precision`; its learning multiplier is
`1 - learningRate * precision`.  Thus the exact open stability region is
`0 < precision < 2` and `0 < learningRate * precision < 2`.  Below the
threshold every state converges when the two multipliers are distinct; above
the learning threshold a concrete invariant mode diverges in norm.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-- Fast inference error and slow weight error for one linear mode. -/
abbrev CoupledTwoTimescaleState := ℝ × ℝ

/-- Fast settling multiplier produced by a precision-scaled relaxation step. -/
noncomputable def coupledSettlingMultiplier (precision : ℝ) : ℝ :=
  1 - precision

/-- Slow learning multiplier after a precision-scaled weight update. -/
noncomputable def coupledLearningMultiplier
    (precision learningRate : ℝ) : ℝ :=
  1 - learningRate * precision

/-- One coupled outer step.  The first coordinate settles first; the second
coordinate then performs the weight update using that new inference error. -/
noncomputable def coupledTwoTimescaleUpdate
    (precision learningRate : ℝ) :
    CoupledTwoTimescaleState →ₗ[ℝ] CoupledTwoTimescaleState where
  toFun state :=
    let settledError := coupledSettlingMultiplier precision * state.1
    (settledError,
      learningRate * settledError +
        coupledLearningMultiplier precision learningRate * state.2)
  map_add' := by
    intro x y
    ext <;>
      simp [coupledSettlingMultiplier, coupledLearningMultiplier] <;>
      ring
  map_smul' := by
    intro c x
    ext <;>
      simp [coupledSettlingMultiplier, coupledLearningMultiplier] <;>
      ring

@[simp] theorem coupledTwoTimescaleUpdate_fst
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState) :
    (coupledTwoTimescaleUpdate precision learningRate state).1 =
      coupledSettlingMultiplier precision * state.1 := rfl

@[simp] theorem coupledTwoTimescaleUpdate_snd
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState) :
    (coupledTwoTimescaleUpdate precision learningRate state).2 =
      learningRate * coupledSettlingMultiplier precision * state.1 +
        coupledLearningMultiplier precision learningRate * state.2 := by
  simp [coupledTwoTimescaleUpdate]
  ring

/-- The pure weight-error mode is invariant under the coupled transition. -/
noncomputable def coupledLearningEigenmode : CoupledTwoTimescaleState := (0, 1)

theorem coupledLearningEigenmode_eigen
    (precision learningRate : ℝ) :
    coupledTwoTimescaleUpdate precision learningRate coupledLearningEigenmode =
      coupledLearningMultiplier precision learningRate •
        coupledLearningEigenmode := by
  ext <;>
    simp [coupledLearningEigenmode, coupledTwoTimescaleUpdate]

/-- Weight coordinate of the fast eigenmode when the two multipliers differ. -/
noncomputable def coupledSettlingModeWeightCoordinate
    (precision learningRate : ℝ) : ℝ :=
  learningRate * coupledSettlingMultiplier precision /
    (coupledSettlingMultiplier precision -
      coupledLearningMultiplier precision learningRate)

/-- Fast eigenmode, expressed in physical inference/weight coordinates. -/
noncomputable def coupledSettlingEigenmode
    (precision learningRate : ℝ) : CoupledTwoTimescaleState :=
  (1, coupledSettlingModeWeightCoordinate precision learningRate)

theorem coupledSettlingEigenmode_eigen
    (precision learningRate : ℝ)
    (hdistinct : coupledSettlingMultiplier precision ≠
      coupledLearningMultiplier precision learningRate) :
    coupledTwoTimescaleUpdate precision learningRate
        (coupledSettlingEigenmode precision learningRate) =
      coupledSettlingMultiplier precision •
        coupledSettlingEigenmode precision learningRate := by
  ext
  · simp [coupledSettlingEigenmode, coupledTwoTimescaleUpdate]
  · simp only [coupledTwoTimescaleUpdate_snd, coupledSettlingEigenmode,
      Prod.smul_snd, smul_eq_mul, mul_one]
    unfold coupledSettlingModeWeightCoordinate
    field_simp [sub_ne_zero.mpr hdistinct]
    ring

theorem linearMap_iterate_add {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (A : V →ₗ[ℝ] V) (steps : ℕ) (x y : V) :
    Nat.iterate A steps (x + y) =
      Nat.iterate A steps x + Nat.iterate A steps y := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

theorem linearMap_iterate_smul_eigen {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (A : V →ₗ[ℝ] V) (v : V) (eigenvalue coefficient : ℝ)
    (heigen : A v = eigenvalue • v) (steps : ℕ) :
    Nat.iterate A steps (coefficient • v) =
      (coefficient * eigenvalue ^ steps) • v := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, heigen, smul_smul]
      congr 1
      ring

/-- Every physical state decomposes into the fast and slow eigenmodes when
their multipliers are distinct. -/
theorem coupledTwoTimescaleState_decomposition
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState) :
    state =
      state.1 • coupledSettlingEigenmode precision learningRate +
        (state.2 - state.1 *
          coupledSettlingModeWeightCoordinate precision learningRate) •
            coupledLearningEigenmode := by
  ext <;>
    simp [coupledSettlingEigenmode, coupledLearningEigenmode]

/-- Exact iterate formula obtained by diagonalizing the coupled transition. -/
theorem coupledTwoTimescale_iterate_exact
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState)
    (steps : ℕ)
    (hdistinct : coupledSettlingMultiplier precision ≠
      coupledLearningMultiplier precision learningRate) :
    Nat.iterate (coupledTwoTimescaleUpdate precision learningRate) steps state =
      (state.1 * coupledSettlingMultiplier precision ^ steps) •
          coupledSettlingEigenmode precision learningRate +
        ((state.2 - state.1 *
            coupledSettlingModeWeightCoordinate precision learningRate) *
          coupledLearningMultiplier precision learningRate ^ steps) •
            coupledLearningEigenmode := by
  conv_lhs =>
    rw [coupledTwoTimescaleState_decomposition precision learningRate state]
  rw [linearMap_iterate_add,
    linearMap_iterate_smul_eigen
      (coupledTwoTimescaleUpdate precision learningRate)
      (coupledSettlingEigenmode precision learningRate)
      (coupledSettlingMultiplier precision) state.1
      (coupledSettlingEigenmode_eigen precision learningRate hdistinct),
    linearMap_iterate_smul_eigen
      (coupledTwoTimescaleUpdate precision learningRate)
      coupledLearningEigenmode
      (coupledLearningMultiplier precision learningRate)
      (state.2 - state.1 *
        coupledSettlingModeWeightCoordinate precision learningRate)
      (coupledLearningEigenmode_eigen precision learningRate)]

/-- Exact Jordan-form iterate when the fast and slow multipliers coincide. -/
theorem coupledTwoTimescale_iterate_repeated_exact
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState)
    (steps : ℕ)
    (hequal : coupledSettlingMultiplier precision =
      coupledLearningMultiplier precision learningRate) :
    Nat.iterate (coupledTwoTimescaleUpdate precision learningRate) steps state =
      (coupledSettlingMultiplier precision ^ steps * state.1,
        coupledSettlingMultiplier precision ^ steps * state.2 +
          (steps : ℝ) * learningRate *
            coupledSettlingMultiplier precision ^ steps * state.1) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih]
      ext
      · simp only [coupledTwoTimescaleUpdate_fst, pow_succ]
        ring
      · simp only [coupledTwoTimescaleUpdate_snd,
          hequal, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

theorem abs_one_sub_lt_one_iff (x : ℝ) :
    |1 - x| < 1 ↔ 0 < x ∧ x < 2 := by
  rw [abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Exact spectral stability region in precision/learning-rate coordinates. -/
theorem coupledTwoTimescale_multipliers_stable_iff
    (precision learningRate : ℝ) :
    |coupledSettlingMultiplier precision| < 1 ∧
        |coupledLearningMultiplier precision learningRate| < 1 ↔
      (0 < precision ∧ precision < 2) ∧
        (0 < learningRate * precision ∧ learningRate * precision < 2) := by
  simp only [coupledSettlingMultiplier, coupledLearningMultiplier,
    abs_one_sub_lt_one_iff]

/-- Below both spectral thresholds, every coupled state converges to zero.
The distinct-multiplier hypothesis excludes only the repeated-root coordinate
formula used here. -/
theorem coupledTwoTimescale_converges_below_threshold_of_distinct
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState)
    (hsettling : |coupledSettlingMultiplier precision| < 1)
    (hlearning : |coupledLearningMultiplier precision learningRate| < 1)
    (hdistinct : coupledSettlingMultiplier precision ≠
      coupledLearningMultiplier precision learningRate) :
    Filter.Tendsto
      (fun steps => Nat.iterate
        (coupledTwoTimescaleUpdate precision learningRate) steps state)
      Filter.atTop (nhds (0 : CoupledTwoTimescaleState)) := by
  have hsettlingPow :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hsettling
  have hlearningPow :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hlearning
  have hfastCoefficient : Filter.Tendsto
      (fun steps => state.1 * coupledSettlingMultiplier precision ^ steps)
      Filter.atTop (nhds 0) := by
    simpa using hsettlingPow.const_mul state.1
  have hslowCoefficient : Filter.Tendsto
      (fun steps =>
        (state.2 - state.1 *
          coupledSettlingModeWeightCoordinate precision learningRate) *
            coupledLearningMultiplier precision learningRate ^ steps)
      Filter.atTop (nhds 0) := by
    simpa using hlearningPow.const_mul
      (state.2 - state.1 *
        coupledSettlingModeWeightCoordinate precision learningRate)
  have hfast := hfastCoefficient.smul_const
    (coupledSettlingEigenmode precision learningRate)
  have hslow := hslowCoefficient.smul_const coupledLearningEigenmode
  have hsum := hfast.add hslow
  simpa only [zero_smul, zero_add] using hsum.congr' (Filter.Eventually.of_forall
    fun steps => (coupledTwoTimescale_iterate_exact
      precision learningRate state steps hdistinct).symm)

/-- On the repeated-root locus, the Jordan term is `steps * multiplier^steps`
and still vanishes throughout the open stability region. -/
theorem coupledTwoTimescale_converges_below_threshold_of_equal
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState)
    (hsettling : |coupledSettlingMultiplier precision| < 1)
    (hequal : coupledSettlingMultiplier precision =
      coupledLearningMultiplier precision learningRate) :
    Filter.Tendsto
      (fun steps => Nat.iterate
        (coupledTwoTimescaleUpdate precision learningRate) steps state)
      Filter.atTop (nhds (0 : CoupledTwoTimescaleState)) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hsettling
  have hfirst : Filter.Tendsto
      (fun steps => coupledSettlingMultiplier precision ^ steps * state.1)
      Filter.atTop (nhds 0) := by
    simpa using hpow.mul_const state.1
  have hweight : Filter.Tendsto
      (fun steps => coupledSettlingMultiplier precision ^ steps * state.2)
      Filter.atTop (nhds 0) := by
    simpa using hpow.mul_const state.2
  have hjordanBase :=
    tendsto_self_mul_const_pow_of_abs_lt_one hsettling
  have hjordan : Filter.Tendsto
      (fun steps : ℕ => (steps : ℝ) * learningRate *
        coupledSettlingMultiplier precision ^ steps * state.1)
      Filter.atTop (nhds 0) := by
    have h := (hjordanBase.const_mul learningRate).mul_const state.1
    simpa only [mul_zero, zero_mul] using h.congr' (Filter.Eventually.of_forall
      fun steps : ℕ => by ring)
  have hpair : Filter.Tendsto
      (fun steps : ℕ =>
        (coupledSettlingMultiplier precision ^ steps * state.1,
          coupledSettlingMultiplier precision ^ steps * state.2 +
            (steps : ℝ) * learningRate *
              coupledSettlingMultiplier precision ^ steps * state.1))
      Filter.atTop (nhds (0 : CoupledTwoTimescaleState)) :=
    (Prod.tendsto_iff _ _).2 ⟨hfirst, by simpa using hweight.add hjordan⟩
  exact hpair.congr' (Filter.Eventually.of_forall fun steps =>
    (coupledTwoTimescale_iterate_repeated_exact
      precision learningRate state steps hequal).symm)

/-- Full below-threshold stability theorem, including both distinct and
repeated spectral multipliers. -/
theorem coupledTwoTimescale_converges_below_threshold
    (precision learningRate : ℝ) (state : CoupledTwoTimescaleState)
    (hsettling : |coupledSettlingMultiplier precision| < 1)
    (hlearning : |coupledLearningMultiplier precision learningRate| < 1) :
    Filter.Tendsto
      (fun steps => Nat.iterate
        (coupledTwoTimescaleUpdate precision learningRate) steps state)
      Filter.atTop (nhds (0 : CoupledTwoTimescaleState)) := by
  by_cases hdistinct : coupledSettlingMultiplier precision ≠
      coupledLearningMultiplier precision learningRate
  · exact coupledTwoTimescale_converges_below_threshold_of_distinct
      precision learningRate state hsettling hlearning hdistinct
  · exact coupledTwoTimescale_converges_below_threshold_of_equal
      precision learningRate state hsettling (not_ne_iff.mp hdistinct)

/-- Exact trajectory of the invariant slow learning mode. -/
theorem coupledLearningEigenmode_iterate
    (precision learningRate : ℝ) (steps : ℕ) :
    Nat.iterate (coupledTwoTimescaleUpdate precision learningRate) steps
        coupledLearningEigenmode =
      coupledLearningMultiplier precision learningRate ^ steps •
        coupledLearningEigenmode := by
  simpa using linearMap_iterate_smul_eigen
    (coupledTwoTimescaleUpdate precision learningRate)
    coupledLearningEigenmode
    (coupledLearningMultiplier precision learningRate) 1
    (coupledLearningEigenmode_eigen precision learningRate) steps

theorem coupledLearningEigenmode_iterate_norm
    (precision learningRate : ℝ) (steps : ℕ) :
    ‖Nat.iterate (coupledTwoTimescaleUpdate precision learningRate) steps
        coupledLearningEigenmode‖ =
      |coupledLearningMultiplier precision learningRate| ^ steps := by
  rw [coupledLearningEigenmode_iterate]
  simp [coupledLearningEigenmode, Real.norm_eq_abs]

/-- Above the learning threshold, the invariant slow mode diverges in norm. -/
theorem coupledTwoTimescale_diverges_above_learning_threshold
    (precision learningRate : ℝ)
    (habove : 2 < learningRate * precision) :
    Filter.Tendsto
      (fun steps =>
        ‖Nat.iterate (coupledTwoTimescaleUpdate precision learningRate) steps
          coupledLearningEigenmode‖)
      Filter.atTop Filter.atTop := by
  have hmultiplier : 1 <
      |coupledLearningMultiplier precision learningRate| := by
    rw [coupledLearningMultiplier, abs_of_neg (by linarith)]
    linarith
  simpa only [coupledLearningEigenmode_iterate_norm] using
    tendsto_pow_atTop_atTop_of_one_lt hmultiplier

/-! ## Positive and negative witnesses -/

/-- With precision `1/2` and learning rate `2`, every initial coupled state
converges: the fast multiplier is `1/2` and the slow multiplier is zero. -/
theorem coupledTwoTimescale_stable_witness (state : CoupledTwoTimescaleState) :
    Filter.Tendsto
      (fun steps => Nat.iterate
        (coupledTwoTimescaleUpdate (1 / 2) 2) steps state)
      Filter.atTop (nhds (0 : CoupledTwoTimescaleState)) := by
  apply coupledTwoTimescale_converges_below_threshold
  · norm_num [coupledSettlingMultiplier]
  · norm_num [coupledLearningMultiplier]

/-- At the same precision but learning rate `8`, the slow mode has multiplier
`-3`, so its norm diverges to infinity. -/
theorem coupledTwoTimescale_divergent_witness :
    Filter.Tendsto
      (fun steps =>
        ‖Nat.iterate (coupledTwoTimescaleUpdate (1 / 2) 8) steps
          coupledLearningEigenmode‖)
      Filter.atTop Filter.atTop := by
  exact coupledTwoTimescale_diverges_above_learning_threshold
    (1 / 2) 8 (by norm_num)

/-- Crown: a single settling precision admits a convergent learning rate below
the exact threshold and a divergent learning rate above it. -/
theorem coupledTwoTimescale_threshold_witnessed :
    (∀ state : CoupledTwoTimescaleState,
      Filter.Tendsto
        (fun steps => Nat.iterate
          (coupledTwoTimescaleUpdate (1 / 2) 2) steps state)
        Filter.atTop (nhds (0 : CoupledTwoTimescaleState))) ∧
      Filter.Tendsto
        (fun steps =>
          ‖Nat.iterate (coupledTwoTimescaleUpdate (1 / 2) 8) steps
            coupledLearningEigenmode‖)
        Filter.atTop Filter.atTop :=
  ⟨coupledTwoTimescale_stable_witness,
    coupledTwoTimescale_divergent_witness⟩

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
