import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PreconditionedLearning
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Full-spectrum stability of predictive-coding residual operators

The stability criterion here applies to arbitrary elements of a complex
Banach algebra.  It therefore includes nonnormal finite matrices and block
continuous-linear operators; diagonalization or a modal basis is not assumed.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Filter Topology
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- Full-spectrum power stability in a complex Banach algebra.  The forward
direction is the nonnormal stability theorem: spectral radius below one forces
the complete operator powers, not merely selected eigenmodes, to vanish. -/
theorem spectralRadius_lt_one_iff_pow_tendsto_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [NormOneClass A] [Nontrivial A] (a : A) :
    spectralRadius ℂ a < 1 ↔
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  constructor
  · intro hradius
    obtain ⟨q, hradius_q, hq_one⟩ := exists_between hradius
    have hroot : ∀ᶠ n : ℕ in atTop,
        (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / (n : ℝ)) < q :=
      (spectrum.gelfand_formula a).eventually_lt tendsto_const_nhds hradius_q
    have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
    have hnorm_bound : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ q.toReal ^ n := by
      filter_upwards [hroot, hpositive] with n hnroot hnpositive
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpositive
      have hENN : (‖a ^ n‖₊ : ℝ≥0∞) < q ^ n := by
        rw [one_div] at hnroot
        have h := (ENNReal.rpow_inv_lt_iff hnreal).mp hnroot
        simpa using h
      have hleft_ne : (‖a ^ n‖₊ : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
      have hq_ne : q ≠ ∞ := ne_of_lt (hq_one.trans_le le_top)
      have hright_ne : q ^ n ≠ ∞ := ENNReal.pow_ne_top hq_ne
      have htoReal :=
        (ENNReal.toReal_le_toReal hleft_ne hright_ne).mpr (le_of_lt hENN)
      simpa [ENNReal.toReal_pow] using htoReal
    have hq_nonneg : 0 ≤ q.toReal := ENNReal.toReal_nonneg
    have hq_real_lt_one : q.toReal < 1 := by
      have hq_ne : q ≠ ∞ := ne_of_lt (hq_one.trans_le le_top)
      exact (ENNReal.toReal_lt_toReal hq_ne ENNReal.one_ne_top).mpr hq_one
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      hnorm_bound
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_real_lt_one)
  · intro hpowers
    have hnorm : Tendsto (fun n : ℕ => ‖a ^ n‖) atTop (𝓝 0) := by
      simpa using hpowers.norm
    have heventually_small : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ < 1 :=
      hnorm.eventually_lt tendsto_const_nhds zero_lt_one
    obtain ⟨n, hnpositive, hnpower⟩ : ∃ n : ℕ, 0 < n ∧ ‖a ^ n‖ < 1 := by
      obtain ⟨n, hn, hpos⟩ :=
        (heventually_small.and (eventually_gt_atTop 0)).exists
      exact ⟨n, hpos, hn⟩
    have hradius_power :
        (spectralRadius ℂ a) ^ n ≤ (‖a ^ n‖₊ : ℝ≥0∞) :=
      (spectrum.spectralRadius_pow_le' a n).trans
        (spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) (a ^ n))
    have hnorm_ennreal : (‖a ^ n‖₊ : ℝ≥0∞) < 1 := by
      exact_mod_cast hnpower
    by_contra hnot
    have hone_le : (1 : ℝ≥0∞) ≤ spectralRadius ℂ a := le_of_not_gt hnot
    have hone_power : (1 : ℝ≥0∞) ≤ (spectralRadius ℂ a) ^ n := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ≥0∞) ≤ 1) hone_le n
    exact (not_lt_of_ge (hone_power.trans hradius_power)) hnorm_ennreal

/-- Every rate strictly above the spectral radius gives a global geometric
envelope.  The constant absorbs the finite nonnormal transient before the
asymptotic rate takes over. -/
theorem operatorPowNorm_geometricEnvelope
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [NormOneClass A] [Nontrivial A] (a : A) (q : ℝ≥0∞)
    (hradius_q : spectralRadius ℂ a < q) (hq_one : q < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * q.toReal ^ n := by
  have hroot : ∀ᶠ n : ℕ in atTop,
      (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / (n : ℝ)) < q :=
    (spectrum.gelfand_formula a).eventually_lt tendsto_const_nhds hradius_q
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hq_ne_top : q ≠ ∞ := ne_of_lt (hq_one.trans_le le_top)
  have hq_pos : (0 : ℝ≥0∞) < q := lt_of_le_of_lt bot_le hradius_q
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
  have hq_real_pos : 0 < q.toReal := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hnorm_eventually : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ q.toReal ^ n := by
    filter_upwards [hroot, hpositive] with n hnroot hnpositive
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpositive
    have hENN : (‖a ^ n‖₊ : ℝ≥0∞) < q ^ n := by
      rw [one_div] at hnroot
      have h := (ENNReal.rpow_inv_lt_iff hnreal).mp hnroot
      simpa using h
    have hleft_ne : (‖a ^ n‖₊ : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    have hright_ne : q ^ n ≠ ∞ := ENNReal.pow_ne_top hq_ne_top
    have htoReal :=
      (ENNReal.toReal_le_toReal hleft_ne hright_ne).mpr (le_of_lt hENN)
    simpa [ENNReal.toReal_pow] using htoReal
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hnorm_eventually
  let B : ℝ := max 1 (‖a‖ / q.toReal)
  let C : ℝ := B ^ N
  have hB_one : 1 ≤ B := le_max_left _ _
  have hC_one : 1 ≤ C := one_le_pow₀ hB_one
  refine ⟨C, hC_one, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (by
      nlinarith [pow_nonneg (le_of_lt hq_real_pos) n])
  · have hnN : n ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hnorm_le : ‖a‖ ≤ B * q.toReal := by
      calc
        ‖a‖ = (‖a‖ / q.toReal) * q.toReal := by field_simp
        _ ≤ B * q.toReal := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (le_of_lt hq_real_pos)
    calc
      ‖a ^ n‖ ≤ ‖a‖ ^ n := norm_pow_le a n
      _ ≤ (B * q.toReal) ^ n :=
        pow_le_pow_left₀ (norm_nonneg a) hnorm_le n
      _ = B ^ n * q.toReal ^ n := mul_pow B q.toReal n
      _ ≤ B ^ N * q.toReal ^ n := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hB_one hnN)
          (pow_nonneg (le_of_lt hq_real_pos) n)
      _ = C * q.toReal ^ n := rfl

/-- A residual after `n` applications of an arbitrary continuous block
operator. -/
noncomputable def operatorResidualIterate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (departure : E →L[ℂ] E) (residual : E) (n : ℕ) : E :=
  (departure ^ n) residual

/-- The operator envelope controls every residual trajectory, with the same
transient constant and an additional factor for the initial residual norm. -/
theorem operatorResidualIterate_norm_geometricEnvelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (departure : E →L[ℂ] E) (residual : E) (q : ℝ≥0∞)
    (hradius_q : spectralRadius ℂ departure < q) (hq_one : q < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ,
      ‖operatorResidualIterate departure residual n‖ ≤
        C * q.toReal ^ n * ‖residual‖ := by
  obtain ⟨C, hC, hpower⟩ :=
    operatorPowNorm_geometricEnvelope departure q hradius_q hq_one
  refine ⟨C, hC, fun n => ?_⟩
  calc
    ‖operatorResidualIterate departure residual n‖ ≤
        ‖departure ^ n‖ * ‖residual‖ :=
      (departure ^ n).le_opNorm residual
    _ ≤ (C * q.toReal ^ n) * ‖residual‖ :=
      mul_le_mul_of_nonneg_right (hpower n) (norm_nonneg residual)
    _ = C * q.toReal ^ n * ‖residual‖ := rfl

/-- The full-spectrum theorem acts on every residual of an arbitrary block
operator, including generalized eigendirections of nonnormal operators. -/
theorem operatorResidualIterate_tendsto_zero_of_spectralRadius_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (departure : E →L[ℂ] E) (residual : E)
    (hradius : spectralRadius ℂ departure < 1) :
    Tendsto (operatorResidualIterate departure residual) atTop (𝓝 0) := by
  have hpowers :=
    (spectralRadius_lt_one_iff_pow_tendsto_zero departure).mp hradius
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · exact Eventually.of_forall fun n => (departure ^ n).le_opNorm residual
  · simpa using hpowers.norm.mul_const ‖residual‖

/-- The familiar modal power law is a corollary inside the operator theory,
not a separate stability criterion. -/
theorem operatorResidualIterate_eigenmode_exact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (departure : E →L[ℂ] E) (residual : E) (eigenvalue : ℂ)
    (heigen : departure residual = eigenvalue • residual) (n : ℕ) :
    operatorResidualIterate departure residual n =
      eigenvalue ^ n • residual := by
  induction n with
  | zero => simp [operatorResidualIterate]
  | succ n ih =>
      rw [operatorResidualIterate, pow_succ', mul_apply_eq_comp,
        show (departure ^ n) residual = operatorResidualIterate departure residual n by rfl,
        ih, map_smul, heigen, pow_succ', mul_smul]
      rw [smul_smul, smul_smul, mul_comm]

/-- Full-spectrum stability subsumes modal convergence whenever an eigenmode
is present. -/
theorem operatorEigenmode_tendsto_zero_of_spectralRadius_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (departure : E →L[ℂ] E) (residual : E) (eigenvalue : ℂ)
    (heigen : departure residual = eigenvalue • residual)
    (hradius : spectralRadius ℂ departure < 1) :
    Tendsto (fun n : ℕ => eigenvalue ^ n • residual) atTop (𝓝 0) := by
  exact (operatorResidualIterate_tendsto_zero_of_spectralRadius_lt_one
    departure residual hradius).congr'
      (Eventually.of_forall fun n =>
        operatorResidualIterate_eigenmode_exact
          departure residual eigenvalue heigen n)

/-! ## Matrix-preconditioner specialization -/

/-- Complexified multiweight residual space used for full-spectrum matrix
preconditioner analysis. -/
abbrev ComplexMultiweightResidualSpace (width : ℕ) :=
  EuclideanSpace ℂ (Fin width)

/-- Departure operator `I - P` of a matrix preconditioner. -/
noncomputable def complexMatrixPreconditionerDeparture {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℂ) :
    ComplexMultiweightResidualSpace width →L[ℂ]
      ComplexMultiweightResidualSpace width :=
  1 - (Matrix.toEuclideanCLM (n := Fin width) (𝕜 := ℂ)) preconditioner

/-- The matrix-preconditioned one-step residual is the same departure
operator used by the general stability theorem. -/
theorem complexMatrixPreconditionerDeparture_apply {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℂ)
    (residual : ComplexMultiweightResidualSpace width) :
    complexMatrixPreconditionerDeparture preconditioner residual =
      residual -
        (Matrix.toEuclideanCLM (n := Fin width) (𝕜 := ℂ)) preconditioner residual := by
  simp [complexMatrixPreconditionerDeparture]

/-- Full-spectrum matrix-preconditioner convergence.  Unlike the one-step
operator-norm bound, this theorem permits transient amplification and
nonnormal preconditioners. -/
theorem complexMatrixPreconditioner_fullSpectrum_convergence {width : ℕ}
    [NeZero width]
    (preconditioner : Matrix (Fin width) (Fin width) ℂ)
    (residual : ComplexMultiweightResidualSpace width)
    (hradius : spectralRadius ℂ
      (complexMatrixPreconditionerDeparture preconditioner) < 1) :
    Tendsto
      (operatorResidualIterate
        (complexMatrixPreconditionerDeparture preconditioner) residual)
      atTop (𝓝 0) :=
  operatorResidualIterate_tendsto_zero_of_spectralRadius_lt_one
    (complexMatrixPreconditionerDeparture preconditioner) residual hradius

/-! ## Parametrized nonnormal Jordan transients -/

/-- A two-mode Jordan residual operator.  Its eigenvalue controls asymptotic
stability, while `coupling` controls the finite nonnormal transient. -/
noncomputable def jordanTransientMatrix (eigenvalue coupling : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![eigenvalue, coupling; 0, eigenvalue]

/-- Exact powers of the complete two-parameter Jordan family. -/
theorem jordanTransientMatrix_pow_exact
    (eigenvalue coupling : ℂ) (n : ℕ) :
    jordanTransientMatrix eigenvalue coupling ^ n =
      !![eigenvalue ^ n,
        (n : ℂ) * coupling * eigenvalue ^ (n - 1);
        0, eigenvalue ^ n] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [jordanTransientMatrix]
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [jordanTransientMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
      · cases n with
        | zero =>
            simp [jordanTransientMatrix, Matrix.mul_apply, Fin.sum_univ_two]
        | succ n =>
            simp [jordanTransientMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
            ring
      · simp [jordanTransientMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [jordanTransientMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- The coupling changes the transient but not the spectrum. -/
theorem jordanTransientMatrix_spectrum (eigenvalue coupling : ℂ) :
    spectrum ℂ (jordanTransientMatrix eigenvalue coupling) = {eigenvalue} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  simp [Matrix.charpoly_fin_two, jordanTransientMatrix, Matrix.trace,
    Matrix.det_fin_two, Polynomial.IsRoot]
  constructor
  · intro h
    by_contra hne
    have hsquare : (z - eigenvalue) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hne)
    apply hsquare
    linear_combination h
  · rintro rfl
    ring

/-- Exact spectral radius of the Jordan family. -/
theorem jordanTransientMatrix_spectralRadius (eigenvalue coupling : ℂ) :
    spectralRadius ℂ (jordanTransientMatrix eigenvalue coupling) =
      ‖eigenvalue‖₊ := by
  rw [spectralRadius, jordanTransientMatrix_spectrum]
  simp

/-- Every nonzero coupling makes the Jordan family genuinely nonnormal. -/
theorem jordanTransientMatrix_not_normal
    (eigenvalue coupling : ℂ) (hcoupling : coupling ≠ 0) :
    jordanTransientMatrix eigenvalue coupling *
        (jordanTransientMatrix eigenvalue coupling).conjTranspose ≠
      (jordanTransientMatrix eigenvalue coupling).conjTranspose *
        jordanTransientMatrix eigenvalue coupling := by
  intro hnormal
  have h00 := congrFun (congrFun hnormal (0 : Fin 2)) (0 : Fin 2)
  simp [jordanTransientMatrix, Matrix.mul_apply, Matrix.conjTranspose,
    Fin.sum_univ_two] at h00
  have hzero : coupling * (starRingEnd ℂ) coupling = 0 := by
    calc
      coupling * (starRingEnd ℂ) coupling =
          (eigenvalue * (starRingEnd ℂ) eigenvalue +
            coupling * (starRingEnd ℂ) coupling) -
              (starRingEnd ℂ) eigenvalue * eigenvalue := by ring
      _ = 0 := sub_eq_zero.mpr h00
  have hstar : (starRingEnd ℂ) coupling ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hcoupling
  exact (mul_ne_zero hcoupling hstar) hzero

/-- The zero-eigenvalue subfamily is nilpotent in two steps for every
coupling magnitude. -/
theorem jordanTransientMatrix_zero_sq (coupling : ℂ) :
    jordanTransientMatrix 0 coupling ^ 2 = 0 := by
  rw [jordanTransientMatrix_pow_exact]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Unit residual aimed along the generalized eigendirection. -/
noncomputable def jordanTransientInput : Fin 2 → ℂ := ![0, 1]

theorem jordanTransientMatrix_mulVec_input (coupling : ℂ) :
    (jordanTransientMatrix 0 coupling).mulVec jordanTransientInput =
      ![coupling, 0] := by
  funext i
  fin_cases i <;>
    simp [jordanTransientMatrix, jordanTransientInput, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

theorem jordanTransientInput_norm : ‖jordanTransientInput‖ = 1 := by
  simp [jordanTransientInput, Pi.norm_def, Finset.univ_fin2]

theorem jordanTransientOutput_norm (coupling : ℂ) :
    ‖(![coupling, 0] : Fin 2 → ℂ)‖ = ‖coupling‖ := by
  simp [Pi.norm_def, Finset.univ_fin2]

/-- A coupling of norm above one amplifies a unit residual on the first step,
despite the zero spectrum and exact two-step convergence. -/
theorem jordanTransientMatrix_zero_transientAmplification
    (coupling : ℂ) (hcoupling : 1 < ‖coupling‖) :
    ‖(jordanTransientMatrix 0 coupling).mulVec jordanTransientInput‖ >
      ‖jordanTransientInput‖ := by
  rw [jordanTransientMatrix_mulVec_input, jordanTransientInput_norm,
    jordanTransientOutput_norm]
  exact hcoupling

/-- Negative boundary: even spectral radius zero permits arbitrarily large
first-step amplification.  Hence no transient bound can depend on spectral
radius alone. -/
theorem spectralRadius_zero_allows_arbitrary_transientAmplification
    (bound : ℝ) (hbound : 0 ≤ bound) :
    ∃ (departure : Matrix (Fin 2) (Fin 2) ℂ) (residual : Fin 2 → ℂ),
      spectralRadius ℂ departure = 0 ∧
      ‖residual‖ = 1 ∧
      bound < ‖departure.mulVec residual‖ ∧
      departure ^ 2 = 0 ∧
      departure * departure.conjTranspose ≠
        departure.conjTranspose * departure := by
  let coupling : ℂ := Complex.ofReal (bound + 1)
  have hcoupling_norm : ‖coupling‖ = bound + 1 := by
    rw [show coupling = Complex.ofReal (bound + 1) by rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  have hcoupling_ne : coupling ≠ 0 := by
    rw [show coupling = Complex.ofReal (bound + 1) by rfl,
      Complex.ofReal_ne_zero]
    linarith
  refine ⟨jordanTransientMatrix 0 coupling, jordanTransientInput,
    ?_, jordanTransientInput_norm, ?_, jordanTransientMatrix_zero_sq coupling,
    jordanTransientMatrix_not_normal 0 coupling hcoupling_ne⟩
  · simp [jordanTransientMatrix_spectralRadius]
  · rw [jordanTransientMatrix_mulVec_input, jordanTransientOutput_norm,
      hcoupling_norm]
    linarith

/-! The original concrete witness is retained as a specialization of the
parametrized family, so downstream paper references remain stable. -/

noncomputable def nonnormalTransientMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  jordanTransientMatrix 0 2

theorem nonnormalTransientMatrix_sq : nonnormalTransientMatrix ^ 2 = 0 :=
  jordanTransientMatrix_zero_sq 2

theorem nonnormalTransientMatrix_ne_zero : nonnormalTransientMatrix ≠ 0 := by
  intro h
  have hij := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [nonnormalTransientMatrix, jordanTransientMatrix] at hij

theorem nonnormalTransientMatrix_not_normal :
    nonnormalTransientMatrix * nonnormalTransientMatrix.conjTranspose ≠
      nonnormalTransientMatrix.conjTranspose * nonnormalTransientMatrix := by
  exact jordanTransientMatrix_not_normal 0 2 (by norm_num)

theorem nonnormalTransientMatrix_spectralRadius_zero :
    spectralRadius ℂ nonnormalTransientMatrix = 0 := by
  simp [nonnormalTransientMatrix, jordanTransientMatrix_spectralRadius]

/-- Stable-spectrum, nonnormal positive fixture.  Its first step amplifies a
unit residual by two, yet the complete matrix power sequence converges to
zero. -/
theorem nonnormalTransientMatrix_fullSpectrum_stable :
    spectralRadius ℂ nonnormalTransientMatrix < 1 ∧
      Tendsto (fun n : ℕ => nonnormalTransientMatrix ^ n) atTop (𝓝 0) ∧
      nonnormalTransientMatrix ≠ 0 ∧
      nonnormalTransientMatrix * nonnormalTransientMatrix.conjTranspose ≠
        nonnormalTransientMatrix.conjTranspose * nonnormalTransientMatrix := by
  have hradius : spectralRadius ℂ nonnormalTransientMatrix < 1 := by
    rw [nonnormalTransientMatrix_spectralRadius_zero]
    norm_num
  exact ⟨hradius,
    (spectralRadius_lt_one_iff_pow_tendsto_zero nonnormalTransientMatrix).mp hradius,
    nonnormalTransientMatrix_ne_zero,
    nonnormalTransientMatrix_not_normal⟩

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
