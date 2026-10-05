import Mettapedia.GSLT.Weighting.RateGenerator

/-!
# Quantum jumps over rate channels (Section 13.6, corrected)

Configurations `Cfg` index the basis `|c⟩` of `ℂ^Cfg`.  Channel `k` has nonnegative classical
rates `rate k c c''` and a phase `θ k`.  Three families of jump operators are compared.

* `channelJump` (the book's Definition 13.11): one operator per channel,
  `L_k = e^{iθ_k} ∑_{c, c''} √(rate k c c'') |c''⟩⟨c|`.
* `sourceJump`: one operator per channel and source configuration,
  `L_{k,c} = e^{iθ_k} ∑_{c''} √(rate k c c'') |c''⟩⟨c|`.
* `transitionJump`: one operator per channel, source and target,
  `L_{k,c,c''} = e^{iθ_k} √(rate k c c'') |c''⟩⟨c|`.

The book claims that with the per-channel operators and `H = 0` the populations (the diagonal of
`ρ`) follow the classical generator whatever the off-diagonal entries of `ρ` are, and that the
quantum-jump unravelling reduces exactly to Gillespie sampling.  This fails as soon as two
different sources reach a common target inside one channel: then `L_k† L_k` is not diagonal.
`Counterexample` formalizes this with three configurations: two states with the same populations
whose populations evolve differently, a basis state that acquires coherences, and a no-jump
survival probability that tends to `1/2` instead of decaying like `e^{-t}`.

The corrected statements.
* For any family whose operators have at most one nonzero entry per row (`RowSingle`), `∑ L†L` is
  diagonal with entry the total exit rate (`jumpSum_eq_diagonal`), and at `H = 0` the populations
  of every matrix `ρ` evolve by the transpose of the classical generator
  (`lindbladian_zero_apply_self`).
* Per-source and per-transition operators always qualify; per-channel operators qualify under
  `RowInjective` (within a channel each target has at most one source).
* The no-jump evolution from `|c⟩` at `H = 0` stays proportional to `|c⟩` and its squared norm is
  `e^{-a₀(c) t}`, where `a₀(c)` is the total propensity including self-loops
  (`sqNorm_noJump_zero_ket`).  A jump through transition `(k, c, c'')` has probability
  `rate k c c'' / a₀(c)` and lands exactly on `|c''⟩` up to a phase
  (`jumpProbability_transitionJump_ket`, `transitionJump_mulVec_ket`).  A self-loop jump returns
  to `|c⟩`; the classical exit rate is `a₀(c)` minus the self-loop rate
  (`totalRate_eq_exitRate_add_selfLoop`).
* The phases `θ` never matter: each family's Lindbladian is independent of `θ` for every
  Hamiltonian (`lindbladian_channelJump_phase_indep` and its siblings).  With per-transition
  operators and `H = 0`, diagonal states stay diagonal (`lindbladian_transitionJump_diagonal`), so
  coherence can only come from `H`; per-source operators with branching sources do create
  coherences (`Branching`).

The condition `RowInjective` is sufficient, not necessary, for closed population dynamics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting

open Matrix

/-! ### Lindblad dynamics of a finite family of jump operators -/

section Lindblad

variable {n J : Type*} [Fintype n] [Fintype J]

/-- The Lindbladian `𝓛 ρ = -i [H, ρ] + ∑ⱼ (Lⱼ ρ Lⱼ† - ½ {Lⱼ† Lⱼ, ρ})`. -/
noncomputable def lindbladian (H : Matrix n n ℂ) (L : J → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  -Complex.I • (H * ρ - ρ * H) +
    ∑ j, (L j * ρ * (L j)ᴴ - (1 / 2 : ℂ) • ((L j)ᴴ * L j * ρ + ρ * ((L j)ᴴ * L j)))

/-- The operator `∑ⱼ Lⱼ† Lⱼ`. -/
noncomputable def jumpSum (L : J → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ j, (L j)ᴴ * L j

/-- The effective Hamiltonian `H - (i/2) ∑ⱼ Lⱼ† Lⱼ`. -/
noncomputable def effHamiltonian (H : Matrix n n ℂ) (L : J → Matrix n n ℂ) : Matrix n n ℂ :=
  H - (Complex.I / 2) • jumpSum L

/-- The squared norm `∑ᵢ |ψᵢ|²`. -/
noncomputable def sqNorm (ψ : n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (ψ i)

/-- The jump weight `‖Lⱼ ψ‖²`: the rate of jump `j` in state `ψ`. -/
noncomputable def jumpWeight (L : J → Matrix n n ℂ) (j : J) (ψ : n → ℂ) : ℝ :=
  sqNorm (L j *ᵥ ψ)

/-- The probability that the next jump from `ψ` goes through `j`. -/
noncomputable def jumpProbability (L : J → Matrix n n ℂ) (j : J) (ψ : n → ℂ) : ℝ :=
  jumpWeight L j ψ / ∑ j', jumpWeight L j' ψ

/-- The classical rate from `a` to `r` carried by a family: `∑ⱼ |⟨r|Lⱼ|a⟩|²`. -/
noncomputable def transferRate (L : J → Matrix n n ℂ) (a r : n) : ℝ :=
  ∑ j, Complex.normSq (L j r a)

/-- Every row has at most one nonzero entry: each target is reached from at most one source. -/
def RowSingle (A : Matrix n n ℂ) : Prop :=
  ∀ r a b, A r a ≠ 0 → A r b ≠ 0 → a = b

/-- Every column has at most one nonzero entry: each source reaches at most one target. -/
def ColSingle (A : Matrix n n ℂ) : Prop :=
  ∀ a r s, A r a ≠ 0 → A s a ≠ 0 → r = s

omit [Fintype J] in
theorem conjTranspose_mul_self_apply_self (A : Matrix n n ℂ) (a : n) :
    (Aᴴ * A) a a = ((∑ r, Complex.normSq (A r a) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]

omit [Fintype J] in
theorem conjTranspose_mul_self_apply_of_ne {A : Matrix n n ℂ} (hA : RowSingle A) {a b : n}
    (h : a ≠ b) : (Aᴴ * A) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases ha : A r a = 0
  · simp [ha]
  · have hb : A r b = 0 := by
      by_contra hb
      exact h (hA r a b ha hb)
    simp [hb]

omit [Fintype J] in
theorem mul_mul_conjTranspose_apply_self {A : Matrix n n ℂ} (hA : RowSingle A)
    (ρ : Matrix n n ℂ) (r : n) :
    (A * ρ * Aᴴ) r r = ∑ a, (Complex.normSq (A r a) : ℂ) * ρ a a := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  · intro b _ hba
    by_cases ha : A r a = 0
    · simp [ha]
    · have hb : A r b = 0 := by
        by_contra hb
        exact hba (hA r b a hb ha)
      simp [hb]
  · simp

omit [Fintype J] in
theorem mul_apply_self_of_offDiag {D : Matrix n n ℂ} (hD : ∀ a b, a ≠ b → D a b = 0)
    (ρ : Matrix n n ℂ) (c : n) : (D * ρ) c c = D c c * ρ c c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · intro b _ hb
    rw [hD c b (Ne.symm hb), zero_mul]
  · simp

omit [Fintype J] in
theorem mul_apply_self_of_offDiag' {D : Matrix n n ℂ} (hD : ∀ a b, a ≠ b → D a b = 0)
    (ρ : Matrix n n ℂ) (c : n) : (ρ * D) c c = ρ c c * D c c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · intro b _ hb
    rw [hD b c hb, mul_zero]
  · simp

/-- The total exit rate of a family is the sum of its transfer rates. -/
theorem totalRate_transferRate (L : J → Matrix n n ℂ) (a : n) :
    totalRate (transferRate L) a = ∑ j, ∑ r, Complex.normSq (L j r a) := by
  rw [totalRate]
  simp only [transferRate]
  exact Finset.sum_comm

/-- Multiplying every jump operator by a phase does not change the Lindbladian, whatever `H`. -/
theorem lindbladian_phase (H : Matrix n n ℂ) (L : J → Matrix n n ℂ) {φ : J → ℂ}
    (hφ : ∀ j, ‖φ j‖ = 1) : lindbladian H (fun j => φ j • L j) = lindbladian H L := by
  have h1 : ∀ j, φ j * star (φ j) = 1 := fun j => by
    rw [Complex.star_def, Complex.mul_conj', hφ j]
    norm_num
  have h2 : ∀ j, star (φ j) * φ j = 1 := fun j => by rw [mul_comm, h1 j]
  funext ρ
  simp only [lindbladian, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    h1, h2, one_smul]

variable [DecidableEq n]

/-- For a family of row-single operators, `∑ L†L` is diagonal, with the total exit rate (self-loops
included) on the diagonal. -/
theorem jumpSum_eq_diagonal {L : J → Matrix n n ℂ} (hL : ∀ j, RowSingle (L j)) :
    jumpSum L = diagonal fun a => (totalRate (transferRate L) a : ℂ) := by
  ext a b
  rw [jumpSum, Matrix.sum_apply]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, totalRate_transferRate, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => conjTranspose_mul_self_apply_self (L j) a
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact Finset.sum_eq_zero fun j _ => conjTranspose_mul_self_apply_of_ne (hL j) hab

/-- Corrected Proposition 13.3: for a family of row-single jump operators and `H = 0`, the
populations of every matrix `ρ` evolve by the transpose of the classical generator of the transfer
rates; the off-diagonal entries of `ρ` do not enter. -/
theorem lindbladian_zero_apply_self {L : J → Matrix n n ℂ} (hL : ∀ j, RowSingle (L j))
    (ρ : Matrix n n ℂ) (c : n) :
    lindbladian 0 L ρ c c = ∑ a, ρ a a * (generator (transferRate L) a c : ℂ) := by
  have hD : ∀ j a b, a ≠ b → ((L j)ᴴ * L j) a b = 0 :=
    fun j _ _ h => conjTranspose_mul_self_apply_of_ne (hL j) h
  have hsum := sum_mul_generator Complex.ofRealHom (transferRate L) (fun a => ρ a a) c
  simp only [Complex.ofRealHom_eq_coe] at hsum
  rw [hsum, totalRate_transferRate]
  have hterm : ∀ j, (L j * ρ * (L j)ᴴ -
      (1 / 2 : ℂ) • ((L j)ᴴ * L j * ρ + ρ * ((L j)ᴴ * L j))) c c =
      ∑ a, (Complex.normSq (L j c a) : ℂ) * ρ a a -
        ((∑ r, Complex.normSq (L j r c) : ℝ) : ℂ) * ρ c c := fun j => by
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      mul_mul_conjTranspose_apply_self (hL j), mul_apply_self_of_offDiag (hD j),
      mul_apply_self_of_offDiag' (hD j), conjTranspose_mul_self_apply_self, smul_eq_mul]
    ring
  rw [lindbladian, Matrix.add_apply, Matrix.sum_apply]
  simp only [hterm, zero_mul, mul_zero, sub_zero, smul_zero, Matrix.zero_apply, zero_add]
  rw [Finset.sum_sub_distrib]
  simp only [transferRate, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- With `H = 0` and operators having at most one nonzero entry in each row and each column,
diagonal states stay diagonal: no coherence is created. -/
theorem lindbladian_zero_diagonal_apply_of_ne {L : J → Matrix n n ℂ}
    (hrow : ∀ j, RowSingle (L j)) (hcol : ∀ j, ColSingle (L j)) (p : n → ℂ) {r s : n}
    (hrs : r ≠ s) : lindbladian 0 L (diagonal p) r s = 0 := by
  have hD : ∀ j, ((L j)ᴴ * L j) r s = 0 := fun j => conjTranspose_mul_self_apply_of_ne (hrow j) hrs
  have hLρL : ∀ j, (L j * diagonal p * (L j)ᴴ) r s = 0 := fun j => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    by_cases hr : L j r a = 0
    · simp [hr]
    · have hs : L j s a = 0 := by
        by_contra hs
        exact hrs (hcol j a r s hr hs)
      simp [hs]
  have hDρ : ∀ j, ((L j)ᴴ * L j * diagonal p) r s = 0 := fun j => by
    rw [Matrix.mul_diagonal, hD j, zero_mul]
  have hρD : ∀ j, (diagonal p * ((L j)ᴴ * L j)) r s = 0 := fun j => by
    rw [Matrix.diagonal_mul, hD j, mul_zero]
  rw [lindbladian, Matrix.add_apply, Matrix.sum_apply]
  simp [hLρL, hDρ, hρD]

/-- The no-jump evolution `ψ(t) = exp (-i t H_eff) ψ` (unnormalised). -/
noncomputable def noJump (H : Matrix n n ℂ) (L : J → Matrix n n ℂ) (t : ℝ) (ψ : n → ℂ) :
    n → ℂ :=
  NormedSpace.exp ((-(Complex.I * t)) • effHamiltonian H L) *ᵥ ψ

theorem sqNorm_smul_single (z : ℂ) (c : n) :
    sqNorm (z • Pi.single c (1 : ℂ)) = Complex.normSq z := by
  rw [sqNorm, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- When `∑ L†L` is diagonal with entries `a`, the no-jump evolution at `H = 0` keeps `|c⟩` on its
ray: `ψ(t) = e^{-a(c) t / 2} |c⟩`. -/
theorem noJump_zero_ket {L : J → Matrix n n ℂ} {a : n → ℝ}
    (hD : jumpSum L = diagonal fun x => (a x : ℂ)) (t : ℝ) (c : n) :
    noJump 0 L t (Pi.single c 1) = Complex.exp (((-(t * a c / 2) : ℝ)) : ℂ) • Pi.single c 1 := by
  have hev : ((-(Complex.I * t)) • effHamiltonian 0 L) *ᵥ Pi.single c (1 : ℂ) =
      (((-(t * a c / 2) : ℝ)) : ℂ) • Pi.single c 1 := by
    rw [effHamiltonian, hD]
    funext x
    by_cases hx : x = c
    · subst hx
      simp only [zero_sub, smul_neg, Matrix.smul_mulVec, Matrix.neg_mulVec, Matrix.mulVec_diagonal,
        Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      push_cast
      linear_combination (t * (a x : ℂ) / 2) * Complex.I_sq
    · simp [hx]
  rw [noJump, exp_mulVec_of_mulVec_eq_smul _ hev, ← Complex.exp_eq_exp_ℂ]

/-- The survival probability of the no-jump evolution from `|c⟩` is `e^{-a(c) t}`: an exponential
waiting time with parameter `a(c)`. -/
theorem sqNorm_noJump_zero_ket {L : J → Matrix n n ℂ} {a : n → ℝ}
    (hD : jumpSum L = diagonal fun x => (a x : ℂ)) (t : ℝ) (c : n) :
    sqNorm (noJump 0 L t (Pi.single c 1)) = Real.exp (-(a c * t)) := by
  rw [noJump_zero_ket hD, sqNorm_smul_single, ← Complex.ofReal_exp, Complex.normSq_ofReal,
    ← Real.exp_add]
  congr 1
  ring

omit [Fintype J] in
theorem jumpWeight_ket (L : J → Matrix n n ℂ) (j : J) (c : n) :
    jumpWeight L j (Pi.single c 1) = ∑ r, Complex.normSq (L j r c) := by
  simp [jumpWeight, sqNorm]

/-- The jump weights out of `|c⟩` add up to the total exit rate. -/
theorem sum_jumpWeight_ket (L : J → Matrix n n ℂ) (c : n) :
    ∑ j, jumpWeight L j (Pi.single c 1) = totalRate (transferRate L) c := by
  simp only [jumpWeight_ket, totalRate_transferRate]

omit [DecidableEq n] in
/-- Jump probabilities sum to one whenever some jump is possible. -/
theorem sum_jumpProbability (L : J → Matrix n n ℂ) (ψ : n → ℂ)
    (h : ∑ j, jumpWeight L j ψ ≠ 0) : ∑ j, jumpProbability L j ψ = 1 := by
  simp only [jumpProbability, ← Finset.sum_div]
  exact div_self h

end Lindblad

/-! ### A Hamiltonian from withheld equations -/

section Hamiltonian

variable {n E : Type*} [Fintype n] [DecidableEq n] [Fintype E]

/-- Book Definition 13.12: `H = ∑ₑ hₑ ∑_{c ≡ₑ c'} (|c'⟩⟨c| + |c⟩⟨c'|)` for real couplings `hₑ` of
the equations withheld from the quotient. -/
noncomputable def withheldHamiltonian (h : E → ℝ) (rel : E → n → n → Prop)
    [∀ e, DecidableRel (rel e)] : Matrix n n ℂ :=
  ∑ e, (h e : ℂ) • ∑ c, ∑ c', if rel e c c' then single c' c 1 + single c c' 1 else 0

theorem withheldHamiltonian_isHermitian (h : E → ℝ) (rel : E → n → n → Prop)
    [∀ e, DecidableRel (rel e)] : (withheldHamiltonian h rel).IsHermitian := by
  unfold Matrix.IsHermitian withheldHamiltonian
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  split_ifs
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single,
      star_one, add_comm]
  · exact Matrix.conjTranspose_zero

end Hamiltonian

/-! ### Jump operators built from rate channels -/

section Channels

variable {K Cfg : Type*} [Fintype K] [Fintype Cfg] [DecidableEq Cfg]

/-- Book Definition 13.11, the per-channel jump operator
`L_k = e^{iθ_k} ∑_{c, c''} √(rate k c c'') |c''⟩⟨c|`. -/
noncomputable def channelJump (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (k : K) :
    Matrix Cfg Cfg ℂ :=
  Matrix.of fun c'' c => Complex.exp (θ k * Complex.I) * (Real.sqrt (rate k c c'') : ℂ)

/-- The per-source jump operator `L_{k,c} = e^{iθ_k} ∑_{c''} √(rate k c c'') |c''⟩⟨c|`. -/
noncomputable def sourceJump (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (i : K × Cfg) :
    Matrix Cfg Cfg ℂ :=
  Matrix.of fun c'' c => if c = i.2 then channelJump rate θ i.1 c'' c else 0

/-- The per-transition jump operator `L_{k,c,c''} = e^{iθ_k} √(rate k c c'') |c''⟩⟨c|`. -/
noncomputable def transitionJump (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (i : K × Cfg × Cfg) :
    Matrix Cfg Cfg ℂ :=
  Matrix.of fun r c => if c = i.2.1 ∧ r = i.2.2 then channelJump rate θ i.1 r c else 0

/-- Within each channel, each target configuration is reached from at most one source. -/
def RowInjective (rate : K → Cfg → Cfg → ℝ) : Prop :=
  ∀ k c₁ c₂ c'', rate k c₁ c'' ≠ 0 → rate k c₂ c'' ≠ 0 → c₁ = c₂

omit [Fintype K] [Fintype Cfg] [DecidableEq Cfg] in
/-- `|⟨c''|L_k|c⟩|²` is exactly the classical rate. -/
theorem normSq_channelJump {rate : K → Cfg → Cfg → ℝ} (θ : K → ℝ) {k : K} {c c'' : Cfg}
    (h : 0 ≤ rate k c c'') : Complex.normSq (channelJump rate θ k c'' c) = rate k c c'' := by
  rw [channelJump, Matrix.of_apply, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt h, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow,
    one_mul]

omit [Fintype K] [Fintype Cfg] in
theorem normSq_sourceJump {rate : K → Cfg → Cfg → ℝ} (θ : K → ℝ) {k : K} {c' c c'' : Cfg}
    (h : 0 ≤ rate k c c'') :
    Complex.normSq (sourceJump rate θ (k, c') c'' c) = if c = c' then rate k c c'' else 0 := by
  simp only [sourceJump, Matrix.of_apply]
  split_ifs
  · exact normSq_channelJump θ h
  · exact map_zero _

omit [Fintype K] [Fintype Cfg] in
theorem normSq_transitionJump {rate : K → Cfg → Cfg → ℝ} (θ : K → ℝ) {k : K} {c' c''' c r : Cfg}
    (h : 0 ≤ rate k c r) :
    Complex.normSq (transitionJump rate θ (k, c', c''') r c) =
      if c = c' ∧ r = c''' then rate k c r else 0 := by
  simp only [transitionJump, Matrix.of_apply]
  split_ifs
  · exact normSq_channelJump θ h
  · exact map_zero _

omit [Fintype Cfg] [DecidableEq Cfg] in
theorem transferRate_channelJump {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (θ : K → ℝ) : transferRate (channelJump rate θ) = rateKernel rate := by
  funext a r
  exact Finset.sum_congr rfl fun k _ => normSq_channelJump θ (hrate k a r)

theorem transferRate_sourceJump {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (θ : K → ℝ) : transferRate (sourceJump rate θ) = rateKernel rate := by
  funext a r
  simp only [transferRate, Fintype.sum_prod_type, normSq_sourceJump θ (hrate _ a r),
    Finset.sum_ite_eq, Finset.mem_univ, if_true, rateKernel]

theorem transferRate_transitionJump {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) :
    transferRate (transitionJump rate θ) = rateKernel rate := by
  funext a r
  simp [transferRate, Fintype.sum_prod_type, normSq_transitionJump θ (hrate _ a r), ite_and,
    rateKernel]

omit [Fintype K] [Fintype Cfg] [DecidableEq Cfg] in
theorem rowSingle_channelJump {rate : K → Cfg → Cfg → ℝ} (hinj : RowInjective rate) (θ : K → ℝ)
    (k : K) : RowSingle (channelJump rate θ k) := by
  intro r a b ha hb
  refine hinj k a b r (fun h => ha ?_) (fun h => hb ?_) <;>
    simp [channelJump, h]

omit [Fintype K] [Fintype Cfg] in
theorem rowSingle_sourceJump (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (i : K × Cfg) :
    RowSingle (sourceJump rate θ i) := by
  intro r a b ha hb
  simp only [sourceJump, Matrix.of_apply, ne_eq, ite_eq_right_iff, not_forall] at ha hb
  exact ha.1.trans hb.1.symm

omit [Fintype K] [Fintype Cfg] in
theorem rowSingle_transitionJump (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (i : K × Cfg × Cfg) :
    RowSingle (transitionJump rate θ i) := by
  intro r a b ha hb
  simp only [transitionJump, Matrix.of_apply, ne_eq, ite_eq_right_iff, not_forall] at ha hb
  exact ha.1.1.trans hb.1.1.symm

omit [Fintype K] [Fintype Cfg] in
theorem colSingle_transitionJump (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (i : K × Cfg × Cfg) :
    ColSingle (transitionJump rate θ i) := by
  intro a r s hr hs
  simp only [transitionJump, Matrix.of_apply, ne_eq, ite_eq_right_iff, not_forall] at hr hs
  exact hr.1.2.trans hs.1.2.symm

/-! #### Populations and the no-jump evolution -/

/-- Corrected Proposition 13.3, per-channel form: under `RowInjective` and with `H = 0`, the
populations of every matrix `ρ` evolve by the transpose of the classical generator. -/
theorem channelJump_populations {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (hinj : RowInjective rate) (θ : K → ℝ) (ρ : Matrix Cfg Cfg ℂ) (c : Cfg) :
    lindbladian 0 (channelJump rate θ) ρ c c =
      ∑ c', ρ c' c' * (generator (rateKernel rate) c' c : ℂ) := by
  rw [lindbladian_zero_apply_self (rowSingle_channelJump hinj θ), transferRate_channelJump hrate]

/-- Corrected Proposition 13.3, per-source form: no hypothesis on the jump structure. -/
theorem sourceJump_populations {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (θ : K → ℝ) (ρ : Matrix Cfg Cfg ℂ) (c : Cfg) :
    lindbladian 0 (sourceJump rate θ) ρ c c =
      ∑ c', ρ c' c' * (generator (rateKernel rate) c' c : ℂ) := by
  rw [lindbladian_zero_apply_self (rowSingle_sourceJump rate θ), transferRate_sourceJump hrate]

/-- Corrected Proposition 13.3, per-transition form: no hypothesis on the jump structure. -/
theorem transitionJump_populations {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (ρ : Matrix Cfg Cfg ℂ) (c : Cfg) :
    lindbladian 0 (transitionJump rate θ) ρ c c =
      ∑ c', ρ c' c' * (generator (rateKernel rate) c' c : ℂ) := by
  rw [lindbladian_zero_apply_self (rowSingle_transitionJump rate θ),
    transferRate_transitionJump hrate]

theorem jumpSum_channelJump {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (hinj : RowInjective rate) (θ : K → ℝ) :
    jumpSum (channelJump rate θ) = diagonal fun c => (totalRate (rateKernel rate) c : ℂ) := by
  rw [jumpSum_eq_diagonal (rowSingle_channelJump hinj θ), transferRate_channelJump hrate]

theorem jumpSum_sourceJump {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (θ : K → ℝ) :
    jumpSum (sourceJump rate θ) = diagonal fun c => (totalRate (rateKernel rate) c : ℂ) := by
  rw [jumpSum_eq_diagonal (rowSingle_sourceJump rate θ), transferRate_sourceJump hrate]

theorem jumpSum_transitionJump {rate : K → Cfg → Cfg → ℝ} (hrate : ∀ k c c', 0 ≤ rate k c c')
    (θ : K → ℝ) :
    jumpSum (transitionJump rate θ) = diagonal fun c => (totalRate (rateKernel rate) c : ℂ) := by
  rw [jumpSum_eq_diagonal (rowSingle_transitionJump rate θ), transferRate_transitionJump hrate]

/-- Corrected Theorem 13.3, waiting time, per-channel form under `RowInjective`: the no-jump
survival probability from `|c⟩` is `e^{-a₀(c) t}`. -/
theorem sqNorm_noJump_channelJump {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (hinj : RowInjective rate) (θ : K → ℝ) (t : ℝ)
    (c : Cfg) :
    sqNorm (noJump 0 (channelJump rate θ) t (Pi.single c 1)) =
      Real.exp (-(totalRate (rateKernel rate) c * t)) :=
  sqNorm_noJump_zero_ket (jumpSum_channelJump hrate hinj θ) t c

/-- Corrected Theorem 13.3, waiting time, per-source form. -/
theorem sqNorm_noJump_sourceJump {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (t : ℝ) (c : Cfg) :
    sqNorm (noJump 0 (sourceJump rate θ) t (Pi.single c 1)) =
      Real.exp (-(totalRate (rateKernel rate) c * t)) :=
  sqNorm_noJump_zero_ket (jumpSum_sourceJump hrate θ) t c

/-- Corrected Theorem 13.3, waiting time, per-transition form. -/
theorem sqNorm_noJump_transitionJump {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (t : ℝ) (c : Cfg) :
    sqNorm (noJump 0 (transitionJump rate θ) t (Pi.single c 1)) =
      Real.exp (-(totalRate (rateKernel rate) c * t)) :=
  sqNorm_noJump_zero_ket (jumpSum_transitionJump hrate θ) t c

omit [Fintype K] in
/-- The waiting-time parameter `a₀(c)` of the jump picture is the classical exit rate `-Q c c`
plus the self-loop rate; a self-loop jump returns to the same configuration
(`transitionJump_selfLoop_ket`). -/
theorem totalRate_eq_exitRate_add_selfLoop (γ : Cfg → Cfg → ℝ) (c : Cfg) :
    totalRate γ c = -generator γ c c + γ c c := by
  rw [generator_diag_eq]
  ring

/-! #### Where a jump lands -/

omit [Fintype K] in
/-- The jump through transition `(k, c, c'')` sends `|c⟩` to a multiple of `|c''⟩`. -/
theorem transitionJump_mulVec_ket (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (k : K) (c c'' : Cfg) :
    transitionJump rate θ (k, c, c'') *ᵥ Pi.single c 1 =
      channelJump rate θ k c'' c • Pi.single c'' 1 := by
  funext r
  rw [Matrix.mulVec_single_one]
  by_cases hr : r = c''
  · subst hr
    simp [transitionJump]
  · simp [transitionJump, hr]

omit [Fintype K] in
/-- A self-loop jump returns to the configuration it left. -/
theorem transitionJump_selfLoop_ket (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (k : K) (c : Cfg) :
    transitionJump rate θ (k, c, c) *ᵥ Pi.single c 1 =
      channelJump rate θ k c c • Pi.single c 1 :=
  transitionJump_mulVec_ket rate θ k c c

omit [Fintype K] in
theorem jumpWeight_transitionJump_ket {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (k : K) (c' c'' c : Cfg) :
    jumpWeight (transitionJump rate θ) (k, c', c'') (Pi.single c 1) =
      if c = c' then rate k c c'' else 0 := by
  rw [jumpWeight_ket]
  simp only [normSq_transitionJump θ (hrate _ _ _)]
  by_cases hc : c = c'
  · simp [hc]
  · simp [hc]

/-- Corrected Theorem 13.3, jump statistics: from `|c⟩` the jump goes through `(k, c, c'')` with
probability `rate k c c'' / a₀(c)`, and it lands on `|c''⟩` (`transitionJump_mulVec_ket`). -/
theorem jumpProbability_transitionJump_ket {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (k : K) (c c'' : Cfg) :
    jumpProbability (transitionJump rate θ) (k, c, c'') (Pi.single c 1) =
      rate k c c'' / totalRate (rateKernel rate) c := by
  rw [jumpProbability, sum_jumpWeight_ket, transferRate_transitionJump hrate,
    jumpWeight_transitionJump_ket hrate, if_pos rfl]

/-- The jump probabilities out of `|c⟩` along transitions leaving `c` sum to one. -/
theorem sum_jumpProbability_transitionJump_ket {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (c : Cfg)
    (hc : totalRate (rateKernel rate) c ≠ 0) :
    ∑ i, jumpProbability (transitionJump rate θ) i (Pi.single c 1) = 1 := by
  refine sum_jumpProbability _ _ ?_
  rwa [sum_jumpWeight_ket, transferRate_transitionJump hrate]

omit [Fintype K] in
/-- The book's per-channel operator applied to `|c⟩` is the column of `c`; its `c''` component has
squared modulus `rate k c c''` (`normSq_channelJump`). -/
theorem channelJump_mulVec_ket (rate : K → Cfg → Cfg → ℝ) (θ : K → ℝ) (k : K) (c : Cfg) :
    channelJump rate θ k *ᵥ Pi.single c 1 = fun c'' => channelJump rate θ k c'' c := by
  rw [Matrix.mulVec_single_one]
  rfl

omit [Fintype K] in
theorem jumpWeight_channelJump_ket {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (k : K) (c : Cfg) :
    jumpWeight (channelJump rate θ) k (Pi.single c 1) = ∑ c'', rate k c c'' := by
  rw [jumpWeight_ket]
  exact Finset.sum_congr rfl fun c'' _ => normSq_channelJump θ (hrate k c c'')

/-! #### Phases, and coherence only from the Hamiltonian -/

omit [Fintype K] [Fintype Cfg] [DecidableEq Cfg] in
theorem channelJump_phase (rate : K → Cfg → Cfg → ℝ) (θ θ' : K → ℝ) (k : K) :
    channelJump rate θ' k =
      Complex.exp (((θ' k - θ k : ℝ) : ℂ) * Complex.I) • channelJump rate θ k := by
  ext c'' c
  simp only [channelJump, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

omit [Fintype K] [Fintype Cfg] in
theorem sourceJump_phase (rate : K → Cfg → Cfg → ℝ) (θ θ' : K → ℝ) (i : K × Cfg) :
    sourceJump rate θ' i =
      Complex.exp (((θ' i.1 - θ i.1 : ℝ) : ℂ) * Complex.I) • sourceJump rate θ i := by
  ext c'' c
  simp only [sourceJump, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [channelJump_phase rate θ θ', Matrix.smul_apply, smul_eq_mul]
  · rw [mul_zero]

omit [Fintype K] [Fintype Cfg] in
theorem transitionJump_phase (rate : K → Cfg → Cfg → ℝ) (θ θ' : K → ℝ) (i : K × Cfg × Cfg) :
    transitionJump rate θ' i =
      Complex.exp (((θ' i.1 - θ i.1 : ℝ) : ℂ) * Complex.I) • transitionJump rate θ i := by
  ext r c
  simp only [transitionJump, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [channelJump_phase rate θ θ', Matrix.smul_apply, smul_eq_mul]
  · rw [mul_zero]

omit [DecidableEq Cfg] in
/-- Principle 13.1: the phases of the channels never enter the dynamics, whatever the
Hamiltonian. -/
theorem lindbladian_channelJump_phase_indep (rate : K → Cfg → Cfg → ℝ) (H : Matrix Cfg Cfg ℂ)
    (θ θ' : K → ℝ) : lindbladian H (channelJump rate θ') = lindbladian H (channelJump rate θ) := by
  rw [show channelJump rate θ' = fun k =>
      Complex.exp (((θ' k - θ k : ℝ) : ℂ) * Complex.I) • channelJump rate θ k from
    funext (channelJump_phase rate θ θ')]
  exact lindbladian_phase H _ fun k => Complex.norm_exp_ofReal_mul_I _

theorem lindbladian_sourceJump_phase_indep (rate : K → Cfg → Cfg → ℝ) (H : Matrix Cfg Cfg ℂ)
    (θ θ' : K → ℝ) : lindbladian H (sourceJump rate θ') = lindbladian H (sourceJump rate θ) := by
  rw [show sourceJump rate θ' = fun i =>
      Complex.exp (((θ' i.1 - θ i.1 : ℝ) : ℂ) * Complex.I) • sourceJump rate θ i from
    funext (sourceJump_phase rate θ θ')]
  exact lindbladian_phase H _ fun i => Complex.norm_exp_ofReal_mul_I _

theorem lindbladian_transitionJump_phase_indep (rate : K → Cfg → Cfg → ℝ)
    (H : Matrix Cfg Cfg ℂ) (θ θ' : K → ℝ) :
    lindbladian H (transitionJump rate θ') = lindbladian H (transitionJump rate θ) := by
  rw [show transitionJump rate θ' = fun i =>
      Complex.exp (((θ' i.1 - θ i.1 : ℝ) : ℂ) * Complex.I) • transitionJump rate θ i from
    funext (transitionJump_phase rate θ θ')]
  exact lindbladian_phase H _ fun i => Complex.norm_exp_ofReal_mul_I _

/-- With per-transition operators and `H = 0`, a diagonal state is sent to a diagonal matrix, and
the diagonal follows the classical generator: the dissipative part never creates coherence. -/
theorem lindbladian_transitionJump_diagonal {rate : K → Cfg → Cfg → ℝ}
    (hrate : ∀ k c c', 0 ≤ rate k c c') (θ : K → ℝ) (p : Cfg → ℂ) :
    lindbladian 0 (transitionJump rate θ) (diagonal p) =
      diagonal fun c => ∑ c', p c' * (generator (rateKernel rate) c' c : ℂ) := by
  ext r s
  by_cases hrs : r = s
  · subst hrs
    rw [diagonal_apply_eq, transitionJump_populations hrate θ]
    simp only [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hrs]
    exact lindbladian_zero_diagonal_apply_of_ne (rowSingle_transitionJump rate θ)
      (colSingle_transitionJump rate θ) p hrs

end Channels

/-! ### The book's per-channel operators without `RowInjective` -/

namespace Counterexample

open Filter Topology

/-- One channel, three configurations, and the transitions `0 → 2` and `1 → 2` at rate one: two
different sources share a target inside one channel. -/
def rate : Unit → Fin 3 → Fin 3 → ℝ :=
  fun _ c c'' => if c ≠ 2 ∧ c'' = 2 then 1 else 0

/-- The zero phase. -/
def θ : Unit → ℝ :=
  fun _ => 0

/-- The book's per-channel jump operator `|2⟩⟨0| + |2⟩⟨1|` for these rates. -/
noncomputable def L : Unit → Matrix (Fin 3) (Fin 3) ℂ :=
  channelJump rate θ

theorem rate_nonneg (k : Unit) (c c'' : Fin 3) : 0 ≤ rate k c c'' := by
  unfold rate
  split_ifs <;> norm_num

theorem not_rowInjective : ¬ RowInjective rate := by
  intro h
  exact absurd (h () 0 1 2 (by simp [rate]) (by simp [rate])) (by decide)

theorem L_apply (j : Unit) : L j = !![0, 0, 0; 0, 0, 0; 1, 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [L, channelJump, rate, θ]

/-- `L† L = |v⟩⟨v|` with `v = |0⟩ + |1⟩`: not diagonal. -/
theorem jumpSum_eq : jumpSum L = !![1, 1, 0; 1, 1, 0; 0, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [jumpSum, L_apply, Matrix.mul_apply, Fin.sum_univ_three]

/-- The pure state `|ψ⟩⟨ψ|` with `ψ = (|0⟩ - |1⟩)/√2`. -/
noncomputable def ρDark : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / 2, -1 / 2, 0; -1 / 2, 1 / 2, 0; 0, 0, 0]

/-- The mixed state `(|0⟩⟨0| + |1⟩⟨1|)/2`. -/
noncomputable def ρMix : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal ![1 / 2, 1 / 2, 0]

theorem ρDark_eq :
    ρDark = (1 / 2 : ℂ) • vecMulVec (![1, -1, 0] : Fin 3 → ℂ) (star ![1, -1, 0]) := by
  ext a b
  rw [Matrix.smul_apply, vecMulVec_apply]
  fin_cases a <;> fin_cases b <;> simp [ρDark] <;> norm_num

theorem ρDark_mul_self : ρDark * ρDark = ρDark := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ρDark, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem trace_ρDark : ρDark.trace = 1 := by
  rw [Matrix.trace_fin_three]
  simp [ρDark]
  norm_num

/-- The two states have the same populations `(1/2, 1/2, 0)`. -/
theorem ρDark_diag_eq (c : Fin 3) : ρDark c c = ρMix c c := by
  fin_cases c <;> simp [ρDark, ρMix]

/-- In the dark state the target population does not grow. -/
theorem lindbladian_ρDark : lindbladian 0 L ρDark 2 2 = 0 := by
  simp [lindbladian, L_apply, ρDark, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three]
  norm_num

/-- In the mixed state it grows at rate one. -/
theorem lindbladian_ρMix : lindbladian 0 L ρMix 2 2 = 1 := by
  simp [lindbladian, L_apply, ρMix, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three]
  norm_num

/-- The classical generator predicts growth rate one for every state with populations
`(1/2, 1/2, 0)`. -/
theorem classical_prediction (ρ : Matrix (Fin 3) (Fin 3) ℂ) (h0 : ρ 0 0 = 1 / 2)
    (h1 : ρ 1 1 = 1 / 2) (h2 : ρ 2 2 = 0) :
    ∑ c', ρ c' c' * (generator (rateKernel rate) c' 2 : ℂ) = 1 := by
  rw [Fin.sum_univ_three, h0, h1, h2,
    generator_apply_of_ne _ (by decide : (0 : Fin 3) ≠ 2),
    generator_apply_of_ne _ (by decide : (1 : Fin 3) ≠ 2)]
  simp [rateKernel, rate]
  norm_num

/-- Book Proposition 13.3 fails for the per-channel operators: populations do not follow the
classical generator. -/
theorem populations_not_closed :
    ¬ ∀ (ρ : Matrix (Fin 3) (Fin 3) ℂ) (c : Fin 3),
      lindbladian 0 L ρ c c = ∑ c', ρ c' c' * (generator (rateKernel rate) c' c : ℂ) := by
  intro h
  have h' := h ρDark 2
  rw [lindbladian_ρDark, classical_prediction ρDark (by simp [ρDark]) (by simp [ρDark])
    (by simp [ρDark])] at h'
  exact zero_ne_one h'

/-- Starting from the basis state `|0⟩⟨0|`, the per-channel Lindbladian creates a coherence
between `0` and `1`. -/
theorem lindbladian_basis_offDiag :
    lindbladian 0 L (diagonal (Pi.single 0 1)) 0 1 = -1 / 2 := by
  simp [lindbladian, L_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  norm_num

/-- The no-jump evolution from `|0⟩`:
`ψ(t) = ½ (|0⟩ - |1⟩) + ½ e^{-t} (|0⟩ + |1⟩)`. -/
theorem noJump_ket_zero (t : ℝ) :
    noJump 0 L t (Pi.single 0 1) =
      fun i => ((![(1 + Real.exp (-t)) / 2, (Real.exp (-t) - 1) / 2, 0] i : ℝ) : ℂ) := by
  have hM : (-(Complex.I * t)) • effHamiltonian 0 L =
      (-(t : ℂ) / 2) • !![(1 : ℂ), 1, 0; 1, 1, 0; 0, 0, 0] := by
    rw [effHamiltonian, jumpSum_eq, zero_sub, smul_neg, smul_smul, ← neg_smul]
    congr 1
    linear_combination ((t : ℂ) / 2) * Complex.I_sq
  have hw : ((-(t : ℂ) / 2) • !![(1 : ℂ), 1, 0; 1, 1, 0; 0, 0, 0]) *ᵥ (![1, -1, 0] : Fin 3 → ℂ) =
      (0 : ℂ) • (![1, -1, 0] : Fin 3 → ℂ) := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hv : ((-(t : ℂ) / 2) • !![(1 : ℂ), 1, 0; 1, 1, 0; 0, 0, 0]) *ᵥ (![1, 1, 0] : Fin 3 → ℂ) =
      ((-t : ℝ) : ℂ) • (![1, 1, 0] : Fin 3 → ℂ) := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have he : Pi.single (0 : Fin 3) (1 : ℂ) =
      (1 / 2 : ℂ) • (![1, -1, 0] : Fin 3 → ℂ) + (1 / 2 : ℂ) • (![1, 1, 0] : Fin 3 → ℂ) := by
    ext i
    fin_cases i <;> norm_num [Pi.single_apply]
  rw [noJump, hM, he, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    exp_mulVec_of_mulVec_eq_smul _ hw, exp_mulVec_of_mulVec_eq_smul _ hv, NormedSpace.exp_zero,
    one_smul, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]
  ext i
  fin_cases i <;> simp <;> ring

/-- The no-jump survival probability from `|0⟩` is `(1 + e^{-2t}) / 2`. -/
theorem survival_eq (t : ℝ) :
    sqNorm (noJump 0 L t (Pi.single 0 1)) = (1 + Real.exp (-(2 * t))) / 2 := by
  have h2 : Real.exp (-(2 * t)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [noJump_ket_zero, sqNorm, Fin.sum_univ_three, h2]
  simp only [Complex.normSq_ofReal]
  simp
  ring

/-- The survival probability tends to `1/2`: half of the time no jump ever happens. -/
theorem survival_tendsto :
    Tendsto (fun t => sqNorm (noJump 0 L t (Pi.single 0 1))) atTop (𝓝 (1 / 2)) := by
  simp only [survival_eq]
  have h : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop two_pos tendsto_id)
  simpa using (h.const_add 1).div_const 2

/-- The classical exit rate from `0` is one, so the classical survival probability is `e^{-t}`. -/
theorem classical_exitRate : generator (rateKernel rate) 0 0 = -1 := by
  rw [generator_diag_eq]
  simp [totalRate, rateKernel, rate]

/-- For every `t > 0` the quantum no-jump survival probability strictly exceeds the classical
one. -/
theorem classical_survival_lt {t : ℝ} (ht : 0 < t) :
    Real.exp (generator (rateKernel rate) 0 0 * t) < sqNorm (noJump 0 L t (Pi.single 0 1)) := by
  have hx : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h2 : Real.exp (-(2 * t)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [classical_exitRate, survival_eq, h2, neg_one_mul]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hx)]

/-- Per-source operators repair the example: the populations follow the classical generator. -/
theorem sourceJump_populations_fix (ρ : Matrix (Fin 3) (Fin 3) ℂ) (c : Fin 3) :
    lindbladian 0 (sourceJump rate θ) ρ c c =
      ∑ c', ρ c' c' * (generator (rateKernel rate) c' c : ℂ) :=
  sourceJump_populations rate_nonneg θ ρ c

/-- With per-source operators the survival probability from `|0⟩` is the classical `e^{-t}`. -/
theorem sourceJump_survival (t : ℝ) :
    sqNorm (noJump 0 (sourceJump rate θ) t (Pi.single 0 1)) = Real.exp (-t) := by
  rw [sqNorm_noJump_sourceJump rate_nonneg θ t 0]
  simp [totalRate, rateKernel, rate]

end Counterexample

/-! ### Per-source operators with a branching source create coherence -/

namespace Branching

/-- One channel, three configurations, and the transitions `0 → 1` and `0 → 2` at rate one. -/
def rate : Unit → Fin 3 → Fin 3 → ℝ :=
  fun _ c c'' => if c = 0 ∧ c'' ≠ 0 then 1 else 0

/-- The per-source operator of source `0` sends `|0⟩⟨0|` to a coherent superposition of `|1⟩` and
`|2⟩`. -/
theorem sourceJump_creates_coherence :
    lindbladian 0 (sourceJump rate fun _ => 0) (diagonal (Pi.single 0 1)) 1 2 = 1 := by
  simp [lindbladian, sourceJump, channelJump, rate, Matrix.mul_apply, Fin.sum_univ_three,
    Fintype.sum_prod_type]

/-- Per-transition operators do not. -/
theorem transitionJump_no_coherence :
    lindbladian 0 (transitionJump rate fun _ => 0) (diagonal (Pi.single 0 1)) 1 2 = 0 :=
  lindbladian_zero_diagonal_apply_of_ne (rowSingle_transitionJump _ _)
    (colSingle_transitionJump _ _) _ (by decide)

end Branching

end Mettapedia.GSLT.Weighting
