import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Rate generators and their Markov semigroups (finite form)

A finite set `Cfg` of configurations carries a family of rate channels indexed by a finite type
`K`.  The number `rate k c c'` is the rate at which channel `k` moves configuration `c` to `c'`.
Summing over channels gives the weighted coalgebra `rateKernel rate c c'`.  Self-loops
(`c' = c`) are allowed.

* `generator γ` is the rate matrix `Q` of a weight kernel `γ`: an off-diagonal entry is the rate,
  a diagonal entry is minus the total rate of leaving.  It has nonnegative off-diagonal entries
  (`generator_offDiag_nonneg`) and zero row sums (`generator_row_sum`).
* `totalRate γ c` is the total propensity of `c`, self-loops included.  The diagonal of `Q`
  leaves the self-loop out (`generator_diag_eq`), so self-loop rates do not change `Q`
  (`generator_selfLoop_irrelevant`), and `Q c c = -totalRate γ c` holds exactly when there is no
  self-loop at `c` (`generator_diag_eq_neg_totalRate_iff`).
* `markov Q t = exp (t • Q)` is the Markov semigroup.  It satisfies `markov Q 0 = 1`, the
  semigroup law, zero-defect row sums for every `t`, and, for `t ≥ 0`, entrywise nonnegativity.
  Nonnegativity goes through uniformisation (`exp_eq_uniformised`): for `ν ≠ 0`,
  `exp (t • Q) = exp (-(ν t)) • exp ((ν t) • (1 + ν⁻¹ • Q))`, and for `ν` at least every exit rate
  the matrix `1 + ν⁻¹ • Q` is stochastic.
* `hasDerivAt_markov` and `hasDerivAt_markov'` are the forward and backward Kolmogorov equations;
  at `t = 0` the derivative is `Q` itself.

The semigroup statements are proved for every rate matrix (`IsRateMatrix`), not only for
generators of weight kernels; `generator_ofRateMatrix` shows that every rate matrix is the
generator of its own off-diagonal part, so nothing is lost.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting

open Matrix

/-! ### The matrix exponential: series and eigenvectors -/

section Exponential

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The exponential series of a square matrix sums, in the entrywise topology, to its
exponential. -/
theorem hasSum_matrix_exp (A : Matrix n n 𝕜) :
    HasSum (fun k : ℕ => ((k.factorial : 𝕜)⁻¹) • A ^ k) (NormedSpace.exp A) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) A

/-- An eigenvector of `A` with eigenvalue `μ` is an eigenvector of `exp A` with eigenvalue
`exp μ`. -/
theorem exp_mulVec_of_mulVec_eq_smul (A : Matrix n n 𝕜) {v : n → 𝕜} {μ : 𝕜}
    (h : A *ᵥ v = μ • v) : NormedSpace.exp A *ᵥ v = NormedSpace.exp μ • v := by
  have hpow : ∀ k : ℕ, A ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have h1 : HasSum (fun k : ℕ => (((k.factorial : 𝕜)⁻¹) • A ^ k) *ᵥ v)
      (NormedSpace.exp A *ᵥ v) :=
    (hasSum_matrix_exp A).map (Matrix.mulVec.addMonoidHomLeft v)
      (continuous_id.matrix_mulVec continuous_const)
  have h2 : HasSum (fun k : ℕ => (((k.factorial : 𝕜)⁻¹) • μ ^ k) • v)
      (NormedSpace.exp μ • v) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) μ).smul_const v
  refine h1.unique ?_
  convert h2 using 2 with k
  rw [Matrix.smul_mulVec, hpow, smul_smul, smul_eq_mul]

end Exponential

/-! ### Entrywise nonnegative matrices -/

section Nonneg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Powers of an entrywise nonnegative real matrix are entrywise nonnegative. -/
theorem pow_apply_nonneg {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    0 ≤ (A ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

/-- The exponential of an entrywise nonnegative real matrix is entrywise nonnegative. -/
theorem exp_apply_nonneg {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (i j : n) :
    0 ≤ NormedSpace.exp A i j := by
  have h := Pi.hasSum.mp (Pi.hasSum.mp (hasSum_matrix_exp A) i) j
  refine h.nonneg fun k => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (pow_apply_nonneg hA k i j)

end Nonneg

/-! ### Rate channels and the weighted coalgebra -/

section Rates

variable {K Cfg : Type*} [Fintype K]

/-- The weighted coalgebra of a family of rate channels: the total rate from `c` to `c'`,
summed over all channels. -/
def rateKernel (rate : K → Cfg → Cfg → ℝ) (c c' : Cfg) : ℝ :=
  ∑ k, rate k c c'

theorem rateKernel_nonneg {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (c c' : Cfg) : 0 ≤ rateKernel rate c c' :=
  Finset.sum_nonneg fun k _ => hrate k c c'

end Rates

/-! ### The generator of a weight kernel -/

section Generator

variable {Cfg : Type*} [Fintype Cfg]

/-- The total propensity of `c`: the sum of all rates out of `c`, self-loops included. -/
def totalRate (γ : Cfg → Cfg → ℝ) (c : Cfg) : ℝ :=
  ∑ c', γ c c'

variable [DecidableEq Cfg]

/-- The generator `Q` of a weight kernel `γ`: `Q c c' = γ c c'` off the diagonal and
`Q c c = -∑_{c' ≠ c} γ c c'`. -/
def generator (γ : Cfg → Cfg → ℝ) : Matrix Cfg Cfg ℝ :=
  Matrix.of fun c c' => if c = c' then -∑ c'' ∈ Finset.univ.erase c, γ c c'' else γ c c'

theorem generator_apply_of_ne (γ : Cfg → Cfg → ℝ) {c c' : Cfg} (h : c ≠ c') :
    generator γ c c' = γ c c' := by
  simp [generator, h]

theorem generator_apply_self (γ : Cfg → Cfg → ℝ) (c : Cfg) :
    generator γ c c = -∑ c'' ∈ Finset.univ.erase c, γ c c'' := by
  simp [generator]

/-- Off-diagonal entries of the generator are nonnegative when the off-diagonal rates are. -/
theorem generator_offDiag_nonneg {γ : Cfg → Cfg → ℝ} (hγ : ∀ c c', c ≠ c' → 0 ≤ γ c c')
    {c c' : Cfg} (h : c ≠ c') : 0 ≤ generator γ c c' := by
  rw [generator_apply_of_ne γ h]
  exact hγ c c' h

/-- Every row of the generator sums to zero. -/
theorem generator_row_sum (γ : Cfg → Cfg → ℝ) (c : Cfg) : ∑ c', generator γ c c' = 0 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), generator_apply_self,
    Finset.sum_congr rfl fun c' hc' => generator_apply_of_ne γ (Finset.ne_of_mem_erase hc').symm]
  ring

/-- The generator kills the constant vector: `Q 1 = 0`. -/
theorem generator_mulVec_one (γ : Cfg → Cfg → ℝ) : generator γ *ᵥ 1 = 0 := by
  funext c
  simp [Matrix.mulVec, dotProduct, generator_row_sum]

/-- Remark 13.6: the diagonal of the generator is minus the total propensity with the self-loop
removed. -/
theorem generator_diag_eq (γ : Cfg → Cfg → ℝ) (c : Cfg) :
    generator γ c c = -(totalRate γ c - γ c c) := by
  rw [generator_apply_self, totalRate, ← Finset.add_sum_erase _ _ (Finset.mem_univ c)]
  ring

/-- The generator only sees the off-diagonal part of the weight kernel. -/
theorem generator_congr_offDiag {γ₁ γ₂ : Cfg → Cfg → ℝ}
    (h : ∀ c c', c ≠ c' → γ₁ c c' = γ₂ c c') : generator γ₁ = generator γ₂ := by
  ext c c'
  by_cases hc : c = c'
  · subst hc
    rw [generator_apply_self, generator_apply_self,
      Finset.sum_congr rfl fun c'' hc'' => h c c'' (Finset.ne_of_mem_erase hc'').symm]
  · rw [generator_apply_of_ne _ hc, generator_apply_of_ne _ hc, h c c' hc]

/-- Remark 13.6: adding, removing or changing self-loop rates does not change the generator. -/
theorem generator_selfLoop_irrelevant (γ : Cfg → Cfg → ℝ) (d : Cfg → ℝ) :
    generator (fun c c' => if c = c' then d c else γ c c') = generator γ :=
  generator_congr_offDiag fun c c' h => by simp [h]

/-- The diagonal of the generator equals minus the total propensity exactly when there is no
self-loop. -/
theorem generator_diag_eq_neg_totalRate_iff (γ : Cfg → Cfg → ℝ) (c : Cfg) :
    generator γ c c = -totalRate γ c ↔ γ c c = 0 := by
  rw [generator_diag_eq]
  constructor <;> intro h <;> linarith

/-- With a self-loop at `c`, the diagonal entry of the generator is not minus the total
propensity. -/
theorem generator_diag_ne_neg_totalRate {γ : Cfg → Cfg → ℝ} {c : Cfg} (h : γ c c ≠ 0) :
    generator γ c c ≠ -totalRate γ c :=
  fun h' => h ((generator_diag_eq_neg_totalRate_iff γ c).mp h')

/-- A configuration with a single self-loop of rate one: the generator is zero although the total
propensity is one. -/
example : generator (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) () () = 0 ∧
    totalRate (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) () = 1 := by
  simp [generator, totalRate]

/-- Without the self-loop the two agree. -/
example : generator (fun (_ : Unit) (_ : Unit) => (0 : ℝ)) () () =
    -totalRate (fun (_ : Unit) (_ : Unit) => (0 : ℝ)) () :=
  (generator_diag_eq_neg_totalRate_iff _ _).mpr rfl

/-- The transpose action of the generator on a population vector, with coefficients pushed
through any ring map: inflow minus outflow. -/
theorem sum_mul_generator {R : Type*} [CommRing R] (f : ℝ →+* R) (γ : Cfg → Cfg → ℝ)
    (p : Cfg → R) (c : Cfg) :
    ∑ c', p c' * f (generator γ c' c) = ∑ c', p c' * f (γ c' c) - p c * f (totalRate γ c) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c),
    ← Finset.add_sum_erase _ (fun c' => p c' * f (γ c' c)) (Finset.mem_univ c),
    Finset.sum_congr rfl fun c' hc' => by
      rw [generator_apply_of_ne γ (Finset.ne_of_mem_erase hc')],
    generator_diag_eq, map_neg, map_sub]
  ring

end Generator

/-! ### Rate matrices -/

section RateMatrix

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- A rate matrix (a `Q`-matrix): nonnegative off-diagonal entries and zero row sums. -/
structure IsRateMatrix (Q : Matrix Cfg Cfg ℝ) : Prop where
  offDiag_nonneg : ∀ c c', c ≠ c' → 0 ≤ Q c c'
  mulVec_one : Q *ᵥ 1 = 0

/-- A stochastic matrix: nonnegative entries and rows summing to one. -/
structure IsStochastic (P : Matrix Cfg Cfg ℝ) : Prop where
  nonneg : ∀ c c', 0 ≤ P c c'
  mulVec_one : P *ᵥ 1 = 1

omit [DecidableEq Cfg] in
theorem mulVec_one_apply (A : Matrix Cfg Cfg ℝ) (c : Cfg) : (A *ᵥ 1) c = ∑ c', A c c' := by
  simp [Matrix.mulVec, dotProduct]

/-- Theorem 13.1, finite form: the generator of a weight kernel with nonnegative off-diagonal
rates is a rate matrix. -/
theorem generator_isRateMatrix {γ : Cfg → Cfg → ℝ} (hγ : ∀ c c', c ≠ c' → 0 ≤ γ c c') :
    IsRateMatrix (generator γ) :=
  ⟨fun _ _ h => generator_offDiag_nonneg hγ h, generator_mulVec_one γ⟩

/-- The generator of the weighted coalgebra of nonnegative rate channels is a rate matrix. -/
theorem rateKernel_generator_isRateMatrix {K : Type*} [Fintype K] {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') : IsRateMatrix (generator (rateKernel rate)) :=
  generator_isRateMatrix fun c c' _ => rateKernel_nonneg hrate c c'

/-- Every rate matrix is the generator of its own off-diagonal part. -/
theorem generator_ofRateMatrix {Q : Matrix Cfg Cfg ℝ} (hQ : Q *ᵥ 1 = 0) :
    generator (fun c c' => Q c c') = Q := by
  ext c c'
  by_cases hc : c = c'
  · subst hc
    have hrow := congrFun hQ c
    rw [mulVec_one_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ c)] at hrow
    rw [generator_apply_self]
    simp only [Pi.zero_apply] at hrow
    linarith
  · exact generator_apply_of_ne _ hc

end RateMatrix

/-! ### The Markov semigroup -/

section Markov

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- The Markov semigroup `P(t) = exp (t • Q)`. -/
noncomputable def markov (Q : Matrix Cfg Cfg ℝ) (t : ℝ) : Matrix Cfg Cfg ℝ :=
  NormedSpace.exp (t • Q)

theorem markov_zero (Q : Matrix Cfg Cfg ℝ) : markov Q 0 = 1 := by
  simp [markov, NormedSpace.exp_zero]

/-- The semigroup law, for all real times. -/
theorem markov_add (Q : Matrix Cfg Cfg ℝ) (s t : ℝ) :
    markov Q (s + t) = markov Q s * markov Q t := by
  unfold markov
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Q).smul_left s).smul_right t)

/-- If `Q` kills the constant vector, `P(t)` fixes it, for every real `t`. -/
theorem markov_mulVec_one {Q : Matrix Cfg Cfg ℝ} (hQ : Q *ᵥ 1 = 0) (t : ℝ) :
    markov Q t *ᵥ 1 = 1 := by
  have h : (t • Q) *ᵥ (1 : Cfg → ℝ) = (0 : ℝ) • (1 : Cfg → ℝ) := by
    rw [Matrix.smul_mulVec, hQ, smul_zero, zero_smul]
  rw [markov, exp_mulVec_of_mulVec_eq_smul _ h, NormedSpace.exp_zero, one_smul]

/-- Every row of `P(t)` sums to one, for every real `t`. -/
theorem markov_row_sum {Q : Matrix Cfg Cfg ℝ} (hQ : Q *ᵥ 1 = 0) (t : ℝ) (c : Cfg) :
    ∑ c', markov Q t c c' = 1 := by
  rw [← mulVec_one_apply, markov_mulVec_one hQ t, Pi.one_apply]

/-- `exp (r • 1) = exp r • 1`. -/
theorem exp_smul_one (r : ℝ) :
    NormedSpace.exp (r • (1 : Matrix Cfg Cfg ℝ)) = Real.exp r • (1 : Matrix Cfg Cfg ℝ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext c
  rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]

/-- The uniformised jump matrix `1 + ν⁻¹ • Q`. -/
noncomputable def uniformised (Q : Matrix Cfg Cfg ℝ) (ν : ℝ) : Matrix Cfg Cfg ℝ :=
  1 + ν⁻¹ • Q

/-- Uniformisation: `exp (t • Q) = exp (-(ν t)) • exp ((ν t) • (1 + ν⁻¹ • Q))` for every
`ν ≠ 0` and every real `t`. -/
theorem exp_eq_uniformised (Q : Matrix Cfg Cfg ℝ) {ν : ℝ} (hν : ν ≠ 0) (t : ℝ) :
    NormedSpace.exp (t • Q) =
      Real.exp (-(ν * t)) • NormedSpace.exp ((ν * t) • uniformised Q ν) := by
  have hsplit : t • Q = (ν * t) • uniformised Q ν + (-(ν * t)) • (1 : Matrix Cfg Cfg ℝ) := by
    rw [uniformised, smul_add, smul_smul, neg_smul, show ν * t * ν⁻¹ = t by field_simp]
    abel
  have hcomm : Commute ((ν * t) • uniformised Q ν) ((-(ν * t)) • (1 : Matrix Cfg Cfg ℝ)) :=
    (Commute.one_right _).smul_right _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one, mul_smul_comm, mul_one]

omit [Fintype Cfg] in
/-- For `ν > 0` at least every exit rate, the uniformised matrix is entrywise nonnegative. -/
theorem uniformised_nonneg {Q : Matrix Cfg Cfg ℝ} (hoff : ∀ c c', c ≠ c' → 0 ≤ Q c c')
    {ν : ℝ} (hν : 0 < ν) (hdiag : ∀ c, -Q c c ≤ ν) (c c' : Cfg) :
    0 ≤ uniformised Q ν c c' := by
  simp only [uniformised, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hc : c = c'
  · subst hc
    have h : 1 + ν⁻¹ * Q c c = ν⁻¹ * (ν + Q c c) := by field_simp
    rw [if_pos rfl, h]
    exact mul_nonneg (inv_nonneg.mpr hν.le) (by linarith [hdiag c])
  · rw [if_neg hc, zero_add]
    exact mul_nonneg (inv_nonneg.mpr hν.le) (hoff c c' hc)

/-- The uniformised matrix of a rate matrix has rows summing to one. -/
theorem uniformised_mulVec_one {Q : Matrix Cfg Cfg ℝ} (hQ : Q *ᵥ 1 = 0) (ν : ℝ) :
    uniformised Q ν *ᵥ 1 = 1 := by
  rw [uniformised, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hQ, smul_zero,
    add_zero]

/-- For a rate matrix and `ν > 0` at least every exit rate, the uniformised matrix is
stochastic. -/
theorem uniformised_isStochastic {Q : Matrix Cfg Cfg ℝ} (hQ : IsRateMatrix Q) {ν : ℝ}
    (hν : 0 < ν) (hdiag : ∀ c, -Q c c ≤ ν) : IsStochastic (uniformised Q ν) :=
  ⟨uniformised_nonneg hQ.offDiag_nonneg hν hdiag, uniformised_mulVec_one hQ.mulVec_one ν⟩

/-- Every entry of `P(t)` is nonnegative for `t ≥ 0`, as soon as the off-diagonal entries of `Q`
are nonnegative. -/
theorem markov_nonneg {Q : Matrix Cfg Cfg ℝ} (hoff : ∀ c c', c ≠ c' → 0 ≤ Q c c') {t : ℝ}
    (ht : 0 ≤ t) (c c' : Cfg) : 0 ≤ markov Q t c c' := by
  set ν : ℝ := 1 + ∑ c, |Q c c| with hνdef
  have hsum : 0 ≤ ∑ c, |Q c c| := Finset.sum_nonneg fun c _ => abs_nonneg (Q c c)
  have hν : 0 < ν := by linarith
  have hdiag : ∀ c, -Q c c ≤ ν := fun c => by
    have h1 : |Q c c| ≤ ∑ c, |Q c c| :=
      Finset.single_le_sum (f := fun c => |Q c c|) (fun c _ => abs_nonneg (Q c c))
        (Finset.mem_univ c)
    linarith [neg_abs_le (Q c c)]
  rw [markov, exp_eq_uniformised Q hν.ne' t, Matrix.smul_apply, smul_eq_mul]
  refine mul_nonneg (Real.exp_pos _).le (exp_apply_nonneg (fun i j => ?_) c c')
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (mul_nonneg hν.le ht) (uniformised_nonneg hoff hν hdiag i j)

/-- For a rate matrix, `P(t)` is a stochastic matrix for every `t ≥ 0`. -/
theorem markov_isStochastic {Q : Matrix Cfg Cfg ℝ} (hQ : IsRateMatrix Q) {t : ℝ} (ht : 0 ≤ t) :
    IsStochastic (markov Q t) :=
  ⟨markov_nonneg hQ.offDiag_nonneg ht, markov_mulVec_one hQ.mulVec_one t⟩

/-- The forward Kolmogorov equation: `P'(t) = P(t) Q`. -/
theorem hasDerivAt_markov (Q : Matrix Cfg Cfg ℝ) (t : ℝ) :
    HasDerivAt (markov Q) (markov Q t * Q) t := by
  open scoped Matrix.Norms.Operator in
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Q t

/-- The backward Kolmogorov equation: `P'(t) = Q P(t)`. -/
theorem hasDerivAt_markov' (Q : Matrix Cfg Cfg ℝ) (t : ℝ) :
    HasDerivAt (markov Q) (Q * markov Q t) t := by
  open scoped Matrix.Norms.Operator in
  exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) Q t

/-- The generator is the derivative of the semigroup at time zero. -/
theorem hasDerivAt_markov_zero (Q : Matrix Cfg Cfg ℝ) : HasDerivAt (markov Q) Q 0 := by
  simpa [markov_zero] using hasDerivAt_markov Q 0

end Markov

end Mettapedia.GSLT.Weighting
