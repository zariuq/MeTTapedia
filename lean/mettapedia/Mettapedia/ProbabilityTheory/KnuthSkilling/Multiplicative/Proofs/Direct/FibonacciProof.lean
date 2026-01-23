import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.FunctionalEquation

/-!
# K&S Appendix B: Fibonacci/Golden-Ratio Proof

This file formalizes **K&S's actual Appendix B proof** of the product theorem,
which uses a Fibonacci recurrence and the irrationality of log(φ)/log(2)
to force the exponential solution.

## K&S's Proof Strategy (Lines 1982-2082)

**Input:** Product equation `Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ,η))` with:
- τ, ξ, η independent real variables
- Ψ positive
- Ψ bounded (implicit assumption: "unbounded values being unacceptable")

**Step 1 (2-term recurrence):** Set ξ = η.
- Define a := ζ(ξ,ξ) - ξ (constant for fixed functional form)
- Get: 2Ψ(τ + ξ) = Ψ(τ + ξ + a)
- Conclude: Ψ(θ + na) = 2^n Ψ(θ) for integer n

**Step 2 (3-term Fibonacci recurrence):** Set ζ - ξ = b and (ζ - η)/2 = b.
- Get: Ψ(τ + ζ - b) + Ψ(τ + ζ - 2b) = Ψ(τ + ζ)
- This is Fibonacci-like with solution involving φ = (1 + √5)/2

**Step 3 (Combine and bound):**
- Ψ(θ + mb - na) has two exponential terms
- Boundedness forces one coefficient to vanish
- This gives: b/a = log(φ)/log(2)

**Step 4 (Density argument):**
- Since b/a is irrational, {mb - na : m,n ∈ ℤ} is dense in ℝ
- For any x: x = mb - na + ε with small ε
- Ψ(x) ≈ e^{Ax} · (constant)

**Output:** Ψ(x) = C·e^{Ax}

## Comparison with FunctionalEquation.lean

Our existing `FunctionalEquation.lean` proves the same result but assumes:
- Continuity
- Strict monotonicity

K&S's Fibonacci proof instead uses:
- Boundedness (weaker than monotonicity in some sense)
- The specific algebraic structure of the recurrences

Both approaches are valid. This file formalizes K&S's approach for completeness.

-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Proofs.Direct.FibonacciProof

open Real
open scoped Topology goldenRatio

/-! ## Using Mathlib's Golden Ratio

Mathlib provides `Real.goldenRatio` (φ) and `Real.goldenConj` (ψ) with:
- `goldenRatio_pos : 0 < φ`
- `one_lt_goldenRatio : 1 < φ`
- `goldenRatio_sq : φ ^ 2 = φ + 1`
- `goldenRatio_mul_goldenConj : φ * ψ = -1`
- `goldenRatio_add_goldenConj : φ + ψ = 1`
- `goldenRatio_irrational : Irrational φ`
- Binet's formula: `coe_fib_eq : (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / √5`
-/

/-! ## The 2-term recurrence -/

/-- Helper: the doubling recurrence for natural numbers. -/
theorem two_term_recurrence_nat
    (Ψ : ℝ → ℝ) (a : ℝ)
    (hDouble : ∀ θ : ℝ, 2 * Ψ θ = Ψ (θ + a)) :
    ∀ (n : ℕ) (θ : ℝ), Ψ (θ + n * a) = (2 : ℝ) ^ n * Ψ θ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro θ
    have h1 : θ + (n + 1 : ℕ) * a = (θ + n * a) + a := by
      simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [h1, ← hDouble (θ + n * a), ih θ, pow_succ]
    ring

/-- Helper: the inverse doubling gives Ψ(θ - a) = Ψ(θ) / 2. -/
theorem doubling_inverse
    (Ψ : ℝ → ℝ) (a : ℝ)
    (hDouble : ∀ θ : ℝ, 2 * Ψ θ = Ψ (θ + a)) :
    ∀ θ : ℝ, Ψ (θ - a) = Ψ θ / 2 := by
  intro θ
  have h := hDouble (θ - a)
  simp only [sub_add_cancel] at h
  linarith

/-- Helper: the doubling recurrence for negative integers. -/
theorem two_term_recurrence_neg
    (Ψ : ℝ → ℝ) (a : ℝ)
    (hDouble : ∀ θ : ℝ, 2 * Ψ θ = Ψ (θ + a)) :
    ∀ (n : ℕ) (θ : ℝ), Ψ (θ - n * a) = (2 : ℝ) ^ (-(n : ℤ)) * Ψ θ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro θ
    have h1 : θ - (n + 1 : ℕ) * a = (θ - n * a) - a := by
      simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [h1, doubling_inverse Ψ a hDouble, ih θ]
    have h2 : (2 : ℝ) ^ (-(↑(n + 1) : ℤ)) = (2 : ℝ) ^ (-(n : ℤ)) * (1/2) := by
      have hexp : (-(↑(n + 1) : ℤ) : ℤ) = (-(n : ℤ)) + (-1) := by omega
      calc (2 : ℝ) ^ (-(↑(n + 1) : ℤ))
          = (2 : ℝ) ^ ((-(n : ℤ)) + (-1)) := by rw [hexp]
        _ = (2 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ (-1 : ℤ) := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ = (2 : ℝ) ^ (-(n : ℤ)) * (1/2) := by rw [zpow_neg_one]; ring
    rw [h2]
    ring

/-- **2-term recurrence (K&S Step 1)**

If Ψ satisfies 2Ψ(θ) = Ψ(θ + a) for all θ, then Ψ(θ + na) = 2^n · Ψ(θ) for all integers n.

This is K&S lines 1987-2000: setting ξ = η gives the doubling recurrence. -/
theorem two_term_recurrence
    (Ψ : ℝ → ℝ) (a : ℝ)
    (hDouble : ∀ θ : ℝ, 2 * Ψ θ = Ψ (θ + a)) :
    ∀ (n : ℤ) (θ : ℝ), Ψ (θ + n * a) = (2 : ℝ) ^ n * Ψ θ := by
  intro n θ
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, Int.cast_natCast, zpow_natCast]
    exact two_term_recurrence_nat Ψ a hDouble n θ
  | negSucc n =>
    -- Int.negSucc n represents -(n+1)
    have heq : (Int.negSucc n : ℝ) * a = -((n + 1 : ℕ) : ℝ) * a := by
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    have hsub : θ + -((n + 1 : ℕ) : ℝ) * a = θ - (n + 1 : ℕ) * a := by ring
    conv_lhs => rw [heq, hsub]
    rw [two_term_recurrence_neg Ψ a hDouble (n + 1) θ]
    -- Need: (2 : ℝ) ^ (-(↑(n + 1) : ℤ)) = (2 : ℝ) ^ Int.negSucc n
    -- Int.negSucc n = -(n+1) as an integer
    simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one]

/-! ## log(φ)/log(2) is irrational

This is the key number-theoretic fact. If log(φ)/log(2) = p/q were rational,
then φ^q = 2^p, contradicting that φ is algebraic of degree 2 (not a rational power of 2).
-/

/-- φ is not a rational power of 2. This follows from φ being algebraic of degree 2:
if φ^q = 2^p for integers p, q with q > 0, then φ^q is rational, but powers of φ
follow the Fibonacci recurrence and are of the form a + b·φ for rationals a, b. -/
theorem goldenRatio_not_rational_power_of_two :
    ∀ (p : ℤ) (q : ℕ), 0 < q → φ ^ q ≠ (2 : ℝ) ^ p := by
  intro p q hq hpow
  -- Use the formula: φ^(n+1) = φ * Fib(n+1) + Fib(n)
  -- This means: φ^(n+1) = Fib(n) + Fib(n+1) * (1 + √5)/2
  --           = Fib(n) + Fib(n+1)/2 + (Fib(n+1)/2) * √5
  -- Since √5 is irrational and 2^p is rational, the √5 coefficient must be 0.
  -- But Fib(n+1) > 0 for n ≥ 0, so the coefficient is > 0. Contradiction.

  -- Get q = n + 1 for some n
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hq)

  -- Use: φ^(n+1) = φ * Fib(n+1) + Fib(n)
  have hformula := Real.goldenRatio_mul_fib_succ_add_fib n
  -- hformula : φ * ↑(Nat.fib (n + 1)) + ↑(Nat.fib n) = φ ^ (n + 1)

  -- φ = (1 + √5)/2 by definition (abbrev)
  have hphi : φ = (1 + √5) / 2 := rfl

  -- So φ^(n+1) = Fib(n) + ((1 + √5)/2) * Fib(n+1)
  --            = Fib(n) + Fib(n+1)/2 + (√5/2) * Fib(n+1)
  have hexpand : φ ^ (n + 1) = (Nat.fib n : ℝ) + ((Nat.fib (n + 1) : ℝ) / 2) +
      (√5 / 2) * (Nat.fib (n + 1) : ℝ) := by
    rw [← hformula, hphi]
    ring

  -- Now if φ^(n+1) = 2^p (a rational), the √5 component must be 0
  -- But (√5/2) * Fib(n+1) = 0 implies Fib(n+1) = 0, contradiction since Fib(n+1) > 0

  have hfib_pos : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos n)
  have hfib_cast_pos : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := Nat.cast_pos.mpr hfib_pos

  -- The √5 coefficient in φ^(n+1)
  have hsqrt5_coeff : (√5 / 2) * (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    apply mul_ne_zero
    · apply div_ne_zero
      · exact Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 5)
      · norm_num
    · exact ne_of_gt hfib_cast_pos

  -- 2^p is rational
  have h2p_rat : ∃ (r : ℚ), (2 : ℝ) ^ p = (r : ℝ) := by
    use (2 : ℚ) ^ p
    simp only [Rat.cast_zpow, Rat.cast_ofNat]

  obtain ⟨r, hr⟩ := h2p_rat

  -- If φ^(n+1) = r (rational), then from hexpand:
  -- Fib(n) + Fib(n+1)/2 + (√5/2)*Fib(n+1) = r
  -- So (√5/2)*Fib(n+1) = r - Fib(n) - Fib(n+1)/2

  -- Combine: φ^(n+1) = 2^p = r
  have hphi_eq_r : φ ^ (n + 1) = (r : ℝ) := hpow.trans hr

  -- The right side is rational, so (√5/2)*Fib(n+1) must be rational
  -- But √5 is irrational and Fib(n+1) > 0, so (√5/2)*Fib(n+1) is irrational
  have hsqrt5_irr : Irrational √5 := Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)

  have hfib_ne : (Nat.fib (n + 1) : ℝ) ≠ 0 := ne_of_gt hfib_cast_pos

  -- From hexpand and hphi_eq_r, we get: Fib(n) + Fib(n+1)/2 + (√5/2)*Fib(n+1) = r
  have hcombined : (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) / 2 +
      (√5 / 2) * (Nat.fib (n + 1) : ℝ) = (r : ℝ) := by
    rw [← hexpand]; exact hphi_eq_r

  -- Solve for √5: √5 = (2r - 2*Fib(n) - Fib(n+1)) / Fib(n+1)
  have hsqrt5_eq : √5 =
      (2 * (r : ℝ) - 2 * (Nat.fib n : ℝ) - (Nat.fib (n + 1) : ℝ)) / (Nat.fib (n + 1) : ℝ) := by
    -- From hcombined: Fib(n) + Fib(n+1)/2 + √5/2 * Fib(n+1) = r
    -- Multiply by 2: 2*Fib(n) + Fib(n+1) + √5 * Fib(n+1) = 2r
    -- Rearrange: √5 * Fib(n+1) = 2r - 2*Fib(n) - Fib(n+1)
    -- Divide: √5 = (2r - 2*Fib(n) - Fib(n+1)) / Fib(n+1)
    rw [eq_div_iff hfib_ne]
    -- Goal: √5 * ↑(Nat.fib (n + 1)) = 2 * ↑r - 2 * ↑(Nat.fib n) - ↑(Nat.fib (n + 1))
    have h := hcombined
    ring_nf
    ring_nf at h
    -- h: ↑(Nat.fib n) + ↑(Nat.fib (n + 1)) / 2 + √5 / 2 * ↑(Nat.fib (n + 1)) = ↑r (after normalization)
    -- The equation is linear in r, Fib n, Fib (n+1), and √5*Fib(n+1)
    -- Let's substitute t = √5 * ↑(Nat.fib (n + 1))
    -- h becomes: Fib n + Fib(n+1)/2 + t/2 = r
    -- Want: t = 2r - 2*Fib n - Fib(n+1)
    -- From h: t/2 = r - Fib n - Fib(n+1)/2
    -- So: t = 2r - 2*Fib n - Fib(n+1) ✓
    linarith

  -- Express √5 as a rational
  have hrat : √5 ∈ Set.range ((↑) : ℚ → ℝ) := by
    rw [Set.mem_range]
    use (2 * r - 2 * (Nat.fib n : ℚ) - (Nat.fib (n + 1) : ℚ)) / (Nat.fib (n + 1) : ℚ)
    rw [hsqrt5_eq]
    push_cast
    ring

  -- But √5 is irrational, contradiction
  exact hsqrt5_irr hrat

/-- log(φ)/log(2) is irrational.

This is the key number-theoretic fact that makes the density argument work.
If log(φ)/log(2) were rational = p/q, then φ^q = 2^p, but φ is algebraic
of degree 2 while 2^p is rational, contradiction. -/
theorem log_golden_div_log_two_irrational : Irrational (Real.log φ / Real.log 2) := by
  rw [irrational_iff_ne_rational]
  intro a b hb heq
  -- If log(φ)/log(2) = a/b, then b * log(φ) = a * log(2)
  -- So log(φ^|b|) = log(2^(a*sign(b))), hence φ^|b| = 2^(a*sign(b))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hphi_pos : 0 < φ := goldenRatio_pos
  have hlog_phi_pos : 0 < Real.log φ := Real.log_pos one_lt_goldenRatio
  have hratio_pos : 0 < Real.log φ / Real.log 2 := div_pos hlog_phi_pos hlog2_pos
  -- Since log(φ)/log(2) > 0 and equals a/b, we have a/b > 0
  -- This means a and b have the same sign
  -- WLOG assume b > 0 (if b < 0, replace a, b with -a, -b)
  have hab_same_sign : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
    rw [heq] at hratio_pos
    have hquot : (0 : ℝ) < (a : ℝ) / (b : ℝ) := hratio_pos
    rcases lt_trichotomy a 0 with ha_neg | ha_zero | ha_pos
    · -- a < 0
      rcases lt_trichotomy b 0 with hb_neg | hb_zero | hb_pos
      · right; exact ⟨ha_neg, hb_neg⟩
      · exfalso; exact hb hb_zero
      · exfalso
        have : (a : ℝ) / (b : ℝ) < 0 :=
          div_neg_of_neg_of_pos (Int.cast_lt_zero.mpr ha_neg) (Int.cast_pos.mpr hb_pos)
        linarith
    · exfalso
      simp only [ha_zero, Int.cast_zero, zero_div] at hquot
      exact lt_irrefl 0 hquot
    · -- a > 0
      rcases lt_trichotomy b 0 with hb_neg | hb_zero | hb_pos
      · exfalso
        have : (a : ℝ) / (b : ℝ) < 0 :=
          div_neg_of_pos_of_neg (Int.cast_pos.mpr ha_pos) (Int.cast_lt_zero.mpr hb_neg)
        linarith
      · exfalso; exact hb hb_zero
      · left; exact ⟨ha_pos, hb_pos⟩
  -- Now we handle both cases
  rcases hab_same_sign with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
  · -- Case: a > 0, b > 0
    -- Convert b to a natural number n
    set n := b.toNat with hn_def
    have hn_eq : (n : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb_pos)
    have hn_pos : 0 < n := by
      rw [Nat.pos_iff_ne_zero]
      intro hzero
      have : (0 : ℤ) = b := by simp only [hzero, Nat.cast_zero] at hn_eq; exact hn_eq
      omega
    have heq' : φ ^ n = (2 : ℝ) ^ a := by
      have h2 : (b : ℝ) * Real.log φ = (a : ℝ) * Real.log 2 := by
        have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast hb
        field_simp [hb_ne, hlog2_pos.ne'] at heq
        linarith
      have h3 : Real.log (φ ^ n) = (n : ℝ) * Real.log φ := Real.log_pow φ n
      have h4 : Real.log ((2 : ℝ) ^ a) = (a : ℝ) * Real.log 2 := Real.log_zpow 2 a
      have h5 : Real.log (φ ^ n) = Real.log ((2 : ℝ) ^ a) := by
        rw [h3, h4]
        -- n = b, so (n : ℝ) = (b : ℝ)
        have hn_cast : (n : ℝ) = (b : ℝ) := by exact_mod_cast hn_eq
        rw [hn_cast]
        exact h2
      have hphi_n_pos : 0 < φ ^ n := pow_pos hphi_pos n
      have h2_a_pos : 0 < (2 : ℝ) ^ a := zpow_pos (by norm_num : (0 : ℝ) < 2) a
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hphi_n_pos) (Set.mem_Ioi.mpr h2_a_pos) h5
    exact goldenRatio_not_rational_power_of_two a n hn_pos heq'
  · -- Case: a < 0, b < 0, use -a, -b instead
    have hneg_heq : Real.log φ / Real.log 2 = (-a) / (-b) := by simp [heq]
    have ha'_pos : 0 < -a := neg_pos.mpr ha_neg
    have hb'_pos : 0 < -b := neg_pos.mpr hb_neg
    -- Convert -b to a natural number n
    set n := (-b).toNat with hn_def
    have hn_eq : (n : ℤ) = -b := Int.toNat_of_nonneg (le_of_lt hb'_pos)
    have hn_pos : 0 < n := by
      rw [Nat.pos_iff_ne_zero]
      intro hzero
      have : (0 : ℤ) = -b := by simp only [hzero, Nat.cast_zero] at hn_eq; exact hn_eq
      omega
    have heq' : φ ^ n = (2 : ℝ) ^ (-a) := by
      have h2 : ((-b) : ℝ) * Real.log φ = ((-a) : ℝ) * Real.log 2 := by
        have hb_ne : ((-b) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb'_pos)
        field_simp [hb_ne, hlog2_pos.ne'] at hneg_heq
        linarith
      have h3 : Real.log (φ ^ n) = (n : ℝ) * Real.log φ := Real.log_pow φ n
      have h4 : Real.log ((2 : ℝ) ^ (-a)) = -(a : ℝ) * Real.log 2 := by
        rw [Real.log_zpow]
        simp only [Int.cast_neg]
      have h5 : Real.log (φ ^ n) = Real.log ((2 : ℝ) ^ (-a)) := by
        rw [h3, h4]
        -- n = -b, so (n : ℝ) = (-b : ℝ)
        have hn_cast : (n : ℝ) = -(b : ℝ) := by
          have : (n : ℤ) = -b := hn_eq
          exact_mod_cast this
        -- h2 says: -↑b * log φ = -↑a * log 2
        -- We need: (n : ℝ) * log φ = -(a : ℝ) * log 2
        -- Since n = -b, this becomes: -↑b * log φ = -↑a * log 2
        rw [hn_cast]
        linarith
      have hphi_n_pos : 0 < φ ^ n := pow_pos hphi_pos n
      have h2_a_pos : 0 < (2 : ℝ) ^ (-a) := zpow_pos (by norm_num : (0 : ℝ) < 2) (-a)
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hphi_n_pos) (Set.mem_Ioi.mpr h2_a_pos) h5
    exact goldenRatio_not_rational_power_of_two (-a) n hn_pos heq'

/-! ## The density argument

If r is irrational, then {m + n·r : m, n ∈ ℤ} is dense in ℝ.
This is because the additive subgroup generated by {1, r} is not cyclic
(since 1 and r are ℚ-linearly independent), so by the classification
of subgroups of ℝ, it must be dense.
-/

/-- The additive subgroup generated by {1, r} for any r. -/
def intLinCombSubgroup (r : ℝ) : AddSubgroup ℝ :=
  AddSubgroup.closure {1, r}

/-- Elements of intLinCombSubgroup r are exactly {m + n*r : m, n ∈ ℤ}. -/
lemma mem_intLinCombSubgroup_iff (r : ℝ) (x : ℝ) :
    x ∈ intLinCombSubgroup r ↔ ∃ m n : ℤ, x = m + n * r := by
  constructor
  · intro hx
    -- Use induction on AddSubgroup.closure
    induction hx using AddSubgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact ⟨1, 0, by ring⟩
      · exact ⟨0, 1, by ring⟩
    | zero => exact ⟨0, 0, by ring⟩
    | add a b _ _ iha ihb =>
      obtain ⟨m₁, n₁, rfl⟩ := iha
      obtain ⟨m₂, n₂, rfl⟩ := ihb
      refine ⟨m₁ + m₂, n₁ + n₂, ?_⟩
      simp only [Int.cast_add]
      ring
    | neg a _ iha =>
      obtain ⟨m, n, rfl⟩ := iha
      refine ⟨-m, -n, ?_⟩
      simp only [Int.cast_neg]
      ring
  · rintro ⟨m, n, rfl⟩
    have h1 : (1 : ℝ) ∈ intLinCombSubgroup r :=
      AddSubgroup.subset_closure (Set.mem_insert 1 {r})
    have hr : r ∈ intLinCombSubgroup r :=
      AddSubgroup.subset_closure (Set.mem_insert_of_mem 1 rfl)
    have hm : (m : ℝ) ∈ intLinCombSubgroup r := by
      rw [← zsmul_one (m : ℤ)]
      exact (intLinCombSubgroup r).zsmul_mem h1 m
    have hn : (n : ℝ) * r ∈ intLinCombSubgroup r := by
      have : (n : ℤ) • r ∈ intLinCombSubgroup r := (intLinCombSubgroup r).zsmul_mem hr n
      simp only [zsmul_eq_mul] at this
      exact this
    exact (intLinCombSubgroup r).add_mem hm hn

/-- If r is irrational, then intLinCombSubgroup r is not cyclic.

Proof: If it were zmultiples g, then 1 = k*g and r = l*g for some k, l ∈ ℤ.
So r = (l/k)*1 = l/k would be rational, contradiction. -/
lemma intLinCombSubgroup_not_cyclic (r : ℝ) (hr : Irrational r) :
    ∀ g : ℝ, intLinCombSubgroup r ≠ AddSubgroup.zmultiples g := by
  intro g heq
  -- 1 ∈ intLinCombSubgroup r = zmultiples g
  have h1 : (1 : ℝ) ∈ AddSubgroup.zmultiples g := by
    rw [← heq]
    exact AddSubgroup.subset_closure (Set.mem_insert 1 {r})
  -- r ∈ intLinCombSubgroup r = zmultiples g
  have hr_mem : r ∈ AddSubgroup.zmultiples g := by
    rw [← heq]
    exact AddSubgroup.subset_closure (Set.mem_insert_of_mem 1 rfl)
  -- From zmultiples: 1 = k • g and r = l • g for some k, l ∈ ℤ
  rw [AddSubgroup.mem_zmultiples_iff] at h1 hr_mem
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := hr_mem
  -- If k = 0, then 1 = 0, contradiction
  have hk_ne : k ≠ 0 := by
    intro hzero
    simp only [hzero, zero_zsmul] at hk
    exact (one_ne_zero : (1 : ℝ) ≠ 0) hk.symm
  -- From hk: k • g = 1, so g = 1 / k
  have hk_cast_ne : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk_ne
  have hg : g = 1 / (k : ℝ) := by
    have hk' : (k : ℝ) * g = 1 := by rw [← zsmul_eq_mul]; exact hk
    field_simp [hk_cast_ne] at hk' ⊢
    linarith
  -- r = l • g = l * (1 / k) = l / k is rational
  have hr_rat : r = (l : ℝ) / (k : ℝ) := by
    have hl' : (l : ℝ) * g = r := by rw [← zsmul_eq_mul]; exact hl
    rw [hg] at hl'
    field_simp [hk_cast_ne] at hl'
    field_simp [hk_cast_ne]
    linarith
  -- But r is irrational, contradiction
  have hr_in_range : r ∈ Set.range ((↑) : ℚ → ℝ) := by
    rw [Set.mem_range]
    use (l : ℚ) / (k : ℚ)
    push_cast
    rw [hr_rat]
  exact hr hr_in_range

/-- If r is irrational, then {m + n·r : m, n ∈ ℤ} is dense in ℝ.

This follows from the classification of additive subgroups of ℝ:
every such subgroup is either dense or cyclic. The subgroup generated
by {1, r} cannot be cyclic when r is irrational (since 1 and r would
both be integer multiples of some g, making r = l/k rational). -/
theorem irrational_linear_combination_dense
    (r : ℝ) (hr : Irrational r) :
    Dense {x : ℝ | ∃ m n : ℤ, x = m - n * r} := by
  -- The set {m - n*r} equals {m + n*r} (replace n with -n)
  have hset_eq : {x : ℝ | ∃ m n : ℤ, x = m - n * r} =
                 {x : ℝ | ∃ m n : ℤ, x = m + n * r} := by
    ext x
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m, -n, ?_⟩
      simp only [Int.cast_neg, neg_mul]
      ring
    · rintro ⟨m, n, rfl⟩
      refine ⟨m, -n, ?_⟩
      simp only [Int.cast_neg, neg_mul]
      ring
  rw [hset_eq]
  -- This set is exactly (intLinCombSubgroup r : Set ℝ)
  have hset_eq' : {x : ℝ | ∃ m n : ℤ, x = m + n * r} = (intLinCombSubgroup r : Set ℝ) := by
    ext x
    exact (mem_intLinCombSubgroup_iff r x).symm
  rw [hset_eq']
  -- By AddSubgroup.dense_or_cyclic, it's either dense or cyclic
  rcases AddSubgroup.dense_or_cyclic (S := intLinCombSubgroup r) with hDense | ⟨g, hCyc⟩
  · exact hDense
  · -- If cyclic, we have a contradiction via intLinCombSubgroup_not_cyclic
    exfalso
    have heq : intLinCombSubgroup r = AddSubgroup.zmultiples g := by
      calc intLinCombSubgroup r = AddSubgroup.closure {g} := hCyc
        _ = AddSubgroup.zmultiples g := (AddSubgroup.zmultiples_eq_closure g).symm
    exact intLinCombSubgroup_not_cyclic r hr g heq

/-! ## The 3-term Fibonacci recurrence -/

/-- φ - ψ = √5 -/
lemma phi_sub_psi : φ - ψ = Real.sqrt 5 := by
  show Real.goldenRatio - Real.goldenConj = Real.sqrt 5
  simp only [Real.goldenRatio, Real.goldenConj]
  ring

/-- φ - ψ ≠ 0 -/
lemma phi_sub_psi_ne_zero : φ - ψ ≠ 0 := by
  rw [phi_sub_psi]
  exact Real.sqrt_ne_zero'.mpr (by norm_num : (5 : ℝ) > 0)

/-- φ * ψ = -1 (product of golden ratio and conjugate) -/
lemma phi_mul_psi : φ * ψ = -1 := Real.goldenRatio_mul_goldenConj

/-- φ² = φ + 1 (defining property) -/
lemma phi_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq

/-- ψ² = ψ + 1 (defining property for conjugate) -/
lemma psi_sq : ψ ^ 2 = ψ + 1 := Real.goldenConj_sq

/-- φ > 1 > 0, so φ ≠ 0 -/
lemma phi_ne_zero : φ ≠ 0 := ne_of_gt (lt_trans zero_lt_one Real.one_lt_goldenRatio)

/-- ψ ≠ 0 (ψ = (1-√5)/2 ≈ -0.618) -/
lemma psi_ne_zero : ψ ≠ 0 := Real.goldenConj_ne_zero

/-- φ - 1 = -ψ (key identity for backward induction) -/
lemma phi_sub_one_eq_neg_psi : φ - 1 = -ψ := by
  have : 1 - φ = ψ := Real.one_sub_goldenConj
  linarith

/-- ψ - 1 = -φ (key identity for backward induction) -/
lemma psi_sub_one_eq_neg_phi : ψ - 1 = -φ := by
  have : 1 - ψ = φ := Real.one_sub_goldenRatio
  linarith

/-- φ² = φ + 1 as a multiplication identity -/
lemma phi_mul_phi : φ * φ = φ + 1 := by
  have := phi_sq
  simp only [sq] at this
  exact this

/-- ψ² = ψ + 1 as a multiplication identity -/
lemma psi_mul_psi : ψ * ψ = ψ + 1 := by
  have := psi_sq
  simp only [sq] at this
  exact this

/-- Fibonacci-like recurrence for φ: φ^(n+2) = φ^(n+1) + φ^n -/
lemma phi_zpow_add_two (n : ℤ) : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
  have h1 : φ ^ (n + 2) = φ ^ n * φ ^ (2 : ℤ) := by
    rw [← zpow_add₀ phi_ne_zero n 2]
  have h2 : φ ^ (n + 1) = φ ^ n * φ ^ (1 : ℤ) := by
    rw [← zpow_add₀ phi_ne_zero n 1]
  simp only [zpow_two, zpow_one] at h1 h2
  rw [h1, h2, phi_mul_phi]
  ring

/-- Fibonacci-like recurrence for ψ: ψ^(n+2) = ψ^(n+1) + ψ^n -/
lemma psi_zpow_add_two (n : ℤ) : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
  have h1 : ψ ^ (n + 2) = ψ ^ n * ψ ^ (2 : ℤ) := by
    rw [← zpow_add₀ psi_ne_zero n 2]
  have h2 : ψ ^ (n + 1) = ψ ^ n * ψ ^ (1 : ℤ) := by
    rw [← zpow_add₀ psi_ne_zero n 1]
  simp only [zpow_two, zpow_one] at h1 h2
  rw [h1, h2, psi_mul_psi]
  ring

/-- Backward Fibonacci recurrence for φ: φ^n = φ^(n+2) - φ^(n+1) -/
lemma phi_zpow_backward (n : ℤ) : φ ^ n = φ ^ (n + 2) - φ ^ (n + 1) := by
  have := phi_zpow_add_two n
  linarith

/-- Backward Fibonacci recurrence for ψ: ψ^n = ψ^(n+2) - ψ^(n+1) -/
lemma psi_zpow_backward (n : ℤ) : ψ ^ n = ψ ^ (n + 2) - ψ ^ (n + 1) := by
  have := psi_zpow_add_two n
  linarith

/-- φ^(-1) = -ψ (inverse of golden ratio) -/
lemma phi_zpow_neg_one : φ ^ (-1 : ℤ) = -ψ := by
  rw [zpow_neg_one]
  -- φ⁻¹ = (φ - 1) because φ(φ-1) = 1, and φ - 1 = -ψ
  have h_prod : φ * (φ - 1) = 1 := by
    calc φ * (φ - 1) = φ ^ 2 - φ := by ring
      _ = (φ + 1) - φ := by rw [phi_sq]
      _ = 1 := by ring
  have h_inv : φ⁻¹ = φ - 1 := by
    have hne : φ - 1 ≠ 0 := by
      intro heq
      have hφ1 : φ = 1 := by linarith
      exact absurd hφ1 (ne_of_gt Real.one_lt_goldenRatio)
    field_simp [phi_ne_zero] at h_prod ⊢
    linarith
  rw [h_inv, phi_sub_one_eq_neg_psi]

/-- ψ < 1 (golden conjugate is less than 1) -/
lemma psi_lt_one : ψ < 1 := by
  have h := Real.goldenConj_neg  -- ψ < 0
  linarith

/-- ψ^(-1) = -φ (inverse of golden conjugate) -/
lemma psi_zpow_neg_one : ψ ^ (-1 : ℤ) = -φ := by
  rw [zpow_neg_one]
  -- ψ⁻¹ = (ψ - 1) because ψ(ψ-1) = 1, and ψ - 1 = -φ
  have h_prod : ψ * (ψ - 1) = 1 := by
    calc ψ * (ψ - 1) = ψ ^ 2 - ψ := by ring
      _ = (ψ + 1) - ψ := by rw [psi_sq]
      _ = 1 := by ring
  have h_inv : ψ⁻¹ = ψ - 1 := by
    -- From ψ * (ψ - 1) = 1, we get ψ⁻¹ = ψ - 1
    -- Multiply both sides by ψ⁻¹: ψ⁻¹ * ψ * (ψ - 1) = ψ⁻¹
    have h : (ψ - 1) = ψ⁻¹ := by
      have step : ψ⁻¹ * (ψ * (ψ - 1)) = ψ⁻¹ * 1 := by rw [h_prod]
      simp only [mul_one] at step
      rw [← mul_assoc, inv_mul_cancel₀ psi_ne_zero, one_mul] at step
      exact step
    exact h.symm
  rw [h_inv, psi_sub_one_eq_neg_phi]

/-! ## Irrationality of φ^n -/

/-- φ^n for n ≥ 1 can be written as φ * F_n + F_{n-1} where F_n is Fibonacci.
Since F_n > 0 for n ≥ 1 and φ is irrational, φ^n is irrational.
We use `goldenRatio_mul_fib_succ_add_fib` from Mathlib. -/
lemma phi_pow_irrational (n : ℕ) (hn : n ≥ 1) : Irrational (φ ^ n) := by
  -- φ^(n+1) = φ * F_{n+1} + F_n (from Mathlib)
  -- So φ^n = φ * F_n + F_{n-1} for n ≥ 1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rw [hk]
  -- Now prove φ^(k+1) is irrational
  have key := Real.goldenRatio_mul_fib_succ_add_fib k
  -- key: φ * Nat.fib (k + 1) + Nat.fib k = φ ^ (k + 1)
  rw [← key]
  -- Goal: Irrational (φ * Nat.fib (k + 1) + Nat.fib k)
  have hFib_ne : Nat.fib (k + 1) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.fib_pos.mpr (by omega))
  -- φ * F_{k+1} + F_k is irrational iff φ * F_{k+1} is irrational (adding rational to irrational)
  -- φ * F_{k+1} is irrational since φ is irrational and F_{k+1} ≠ 0
  have h_mul_irr : Irrational (φ * Nat.fib (k + 1)) :=
    Real.goldenRatio_irrational.mul_natCast hFib_ne
  exact h_mul_irr.add_natCast (Nat.fib k)

/-- φ^n is irrational for all integers n ≠ 0 -/
lemma phi_zpow_irrational (n : ℤ) (hn : n ≠ 0) : Irrational (φ ^ n) := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    have hm : m ≥ 1 := by
      simp only [Int.ofNat_eq_coe, ne_eq] at hn
      omega
    exact phi_pow_irrational m hm
  | negSucc m =>
    -- φ^(-(m+1)) = 1 / φ^(m+1)
    simp only [zpow_negSucc]
    have h_pos : φ ^ (m + 1) > 0 := pow_pos (lt_trans zero_lt_one Real.one_lt_goldenRatio) (m + 1)
    have h_irr := phi_pow_irrational (m + 1) (by omega)
    exact h_irr.inv

/-- φ^p ≠ 2^q for integers p ≠ 0 (key for log_φ(2) irrationality) -/
lemma phi_zpow_ne_two_zpow (p : ℤ) (hp : p ≠ 0) (q : ℤ) : φ ^ p ≠ (2 : ℝ) ^ q := by
  intro heq
  have h_irr := phi_zpow_irrational p hp
  have h_rat : ¬Irrational ((2 : ℝ) ^ q) := by
    rw [Irrational]
    push_neg
    exact ⟨(2 : ℚ) ^ q, by simp only [Rat.cast_zpow, Rat.cast_ofNat]⟩
  rw [heq] at h_irr
  exact h_rat h_irr

/-- log_φ(2) is irrational: there are no integers p, q with q > 0 and φ^p = 2^q -/
lemma log_phi_two_irrational : Irrational (Real.log 2 / Real.log φ) := by
  -- If log_φ(2) = p/q were rational, then φ^(p/q) = 2, so φ^p = 2^q
  -- But φ^p is irrational for p ≠ 0, and 2^q is rational, contradiction
  rw [Irrational]
  intro ⟨r, hr⟩
  -- r = log 2 / log φ means log 2 = r * log φ
  have hφ_pos : 0 < φ := lt_trans zero_lt_one Real.one_lt_goldenRatio
  have hφ_ne_one : φ ≠ 1 := ne_of_gt Real.one_lt_goldenRatio
  have hlog_phi_ne : Real.log φ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hφ_pos hφ_ne_one
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- r = log 2 / log φ, so r * log φ = log 2
  have hr_eq : r * Real.log φ = Real.log 2 := by
    field_simp [hlog_phi_ne] at hr
    linarith
  -- Use r.num and r.den directly
  set p := r.num with hp_def
  set q := r.den with hq_def
  have hq_pos : 0 < q := Rat.pos r
  have hr_eq' : (r : ℝ) = (p : ℝ) / (q : ℝ) := by
    rw [← Rat.num_div_den r, hp_def, hq_def]
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  -- Then (p/q) * log φ = log 2
  -- So p * log φ = q * log 2
  have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq_pos)
  have h_eq : (p : ℝ) * Real.log φ = (q : ℝ) * Real.log 2 := by
    have : (p : ℝ) / (q : ℝ) * Real.log φ = Real.log 2 := by
      rw [← hr_eq']; exact hr_eq
    field_simp [hq_ne] at this
    linarith
  -- From p * log φ = q * log 2, get log(φ^p) = log(2^q)
  have h_log_eq : Real.log (φ ^ p) = Real.log ((2 : ℝ) ^ (q : ℤ)) := by
    rw [Real.log_zpow, Real.log_zpow]
    simp only [Int.cast_natCast]
    exact h_eq
  -- Since log is injective on positives, φ^p = 2^q
  have hφp_pos : 0 < φ ^ p := zpow_pos hφ_pos p
  have h2q_pos : 0 < (2 : ℝ) ^ (q : ℤ) := by positivity
  have h_zpow_eq : φ ^ p = (2 : ℝ) ^ (q : ℤ) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hφp_pos) (Set.mem_Ioi.mpr h2q_pos) h_log_eq
  -- Case split on p = 0 or p ≠ 0
  by_cases hp : p = 0
  · -- If p = 0, then φ^0 = 1 = 2^q, so q = 0 (but q > 0, contradiction)
    simp only [hp, zpow_zero] at h_zpow_eq
    have h2q_eq_one : (2 : ℝ) ^ (q : ℤ) = 1 := h_zpow_eq.symm
    have hq_zero : (q : ℤ) = 0 := by
      have h2_ne_one : (2 : ℝ) ≠ 1 := by norm_num
      exact zpow_eq_one_iff_right₀ (by norm_num) h2_ne_one |>.mp h2q_eq_one
    -- But q > 0, so q ≠ 0
    simp only [Int.natCast_eq_zero] at hq_zero
    exact absurd hq_zero (Nat.pos_iff_ne_zero.mp hq_pos)
  · -- If p ≠ 0, then φ^p is irrational but 2^q is rational, contradiction
    exact phi_zpow_ne_two_zpow p hp (q : ℤ) h_zpow_eq

/-- log(φ)/log(2) is irrational (reciprocal of log_phi_two_irrational).
This is the key ratio b/a in K&S's density argument. -/
lemma log_two_phi_irrational : Irrational (Real.log φ / Real.log 2) := by
  have h := log_phi_two_irrational
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hφ_pos : 0 < φ := lt_trans zero_lt_one Real.one_lt_goldenRatio
  have hlog_phi_pos : 0 < Real.log φ := Real.log_pos Real.one_lt_goldenRatio
  have hlog_phi_ne : Real.log φ ≠ 0 := ne_of_gt hlog_phi_pos
  -- log(φ)/log(2) = 1 / (log(2)/log(φ))
  -- If log(2)/log(φ) is irrational, so is its reciprocal (when nonzero)
  rw [Irrational] at h ⊢
  intro ⟨r, hr⟩
  apply h
  use r⁻¹
  have hr_ne : r ≠ 0 := by
    intro hr0
    rw [hr0, Rat.cast_zero] at hr
    have heq : Real.log φ / Real.log 2 = 0 := hr.symm
    rw [div_eq_zero_iff] at heq
    cases heq with
    | inl hl => exact hlog_phi_ne hl
    | inr hrr => exact hlog2_ne hrr
  -- hr : (r : ℝ) = log φ / log 2
  -- Goal: (r⁻¹ : ℝ) = log 2 / log φ
  have hr' : (r : ℝ) * Real.log 2 = Real.log φ := by
    have heq := hr.symm
    field_simp [hlog2_ne] at heq
    linarith
  have hr_cast_ne : (r : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hr_ne
  simp only [Rat.cast_inv]
  -- Goal: (r : ℝ)⁻¹ = log 2 / log φ
  -- From hr': r * log 2 = log φ
  -- So log 2 / log φ = log 2 / (r * log 2) = 1/r = r⁻¹
  field_simp [hr_cast_ne, hlog_phi_ne]
  -- Goal: log φ = log 2 * r
  -- hr' : r * log 2 = log φ
  linarith [hr']

/-- Helper: two-step induction for natural numbers.
If P(0), P(1), and P(n) ∧ P(n+1) → P(n+2), then P(n) for all n. -/
lemma nat_two_step_induction {P : ℕ → Prop} (h0 : P 0) (h1 : P 1)
    (hstep : ∀ n, P n → P (n + 1) → P (n + 2)) : ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact h0
    | 1 => exact h1
    | n + 2 =>
      exact hstep n (ih n (by omega)) (ih (n + 1) (by omega))

/-- For the Fibonacci recurrence f(x) + f(x-b) = f(x+b), on each "fiber" θ + b·ℤ,
the solution is a linear combination of φ^m and ψ^m.

Note: A and B depend on θ (specifically on f(θ) and f(θ+b)).

**Proof sketch**:
- The recurrence f(x+b) = f(x) + f(x-b) has characteristic equation t² = t + 1
- Roots: φ = (1+√5)/2, ψ = (1-√5)/2 (golden ratio and conjugate)
- General solution on fiber: f(θ + m·b) = A·φ^m + B·ψ^m
- A, B determined by initial conditions: A = (f₁ - ψ·f₀)/(φ-ψ), B = (φ·f₀ - f₁)/(φ-ψ)
- Base cases m=0, m=1 verify directly
- Inductive step uses φ^(n+2) = φ^(n+1) + φ^n (and same for ψ)
- Backward direction uses f(θ-b) = f(θ+b) - f(θ) and φ^(-1) = -ψ, ψ^(-1) = -φ -/
theorem fibonacci_recurrence_fiber
    (f : ℝ → ℝ) (b : ℝ) (_hb : b ≠ 0)
    (hFib : ∀ x : ℝ, f x + f (x - b) = f (x + b)) (θ : ℝ) :
    ∃ A B : ℝ, ∀ (m : ℤ), f (θ + m * b) = A * φ ^ m + B * ψ ^ m := by
  -- Define A, B from initial conditions
  let f0 := f θ
  let f1 := f (θ + b)
  let A := (f1 - ψ * f0) / (φ - ψ)
  let B := (φ * f0 - f1) / (φ - ψ)
  use A, B
  -- The recurrence: f(x+b) = f(x) + f(x-b)
  have hRec : ∀ n : ℤ, f (θ + (n + 1) * b) = f (θ + n * b) + f (θ + (n - 1) * b) := by
    intro n
    have hspec := hFib (θ + n * b)
    have h1 : θ + n * b - b = θ + (n - 1) * b := by ring
    have h2 : θ + n * b + b = θ + (n + 1) * b := by ring
    rw [h1, h2] at hspec
    linarith
  -- Base case m = 0
  have hBase0 : A + B = f0 := by
    simp only [A, B]
    field_simp [phi_sub_psi_ne_zero]
    ring
  -- Base case m = 1
  have hBase1 : A * φ + B * ψ = f1 := by
    simp only [A, B]
    have hne := phi_sub_psi_ne_zero
    field_simp [hne]
    ring
  -- Forward induction: formula holds for all n ∈ ℕ
  have hForward : ∀ n : ℕ, f (θ + n * b) = A * φ ^ n + B * ψ ^ n := by
    apply nat_two_step_induction
    · -- n = 0
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
      exact hBase0.symm
    · -- n = 1
      simp only [Nat.cast_one, one_mul, pow_one]
      exact hBase1.symm
    · -- Inductive step: n → n+1 → n+2
      intro n ih_n ih_n1
      -- Use the recurrence: f(θ + (n+2)b) = f(θ + (n+1)b) + f(θ + nb)
      have hspec := hFib (θ + (n + 1 : ℕ) * b)
      have eq1 : θ + (n + 1 : ℕ) * b - b = θ + n * b := by
        simp only [Nat.cast_add, Nat.cast_one]; ring
      have eq2 : θ + (n + 1 : ℕ) * b + b = θ + (n + 2 : ℕ) * b := by
        simp only [Nat.cast_add, Nat.cast_one]; ring
      rw [eq1, eq2] at hspec
      -- hspec: f(θ + nb) + f(θ + (n+1)b) = f(θ + (n+2)b)
      have hrecN : f (θ + (n + 2 : ℕ) * b) = f (θ + (n + 1 : ℕ) * b) + f (θ + n * b) := by
        linarith
      rw [hrecN, ih_n, ih_n1]
      have hphi : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
        have h := phi_zpow_add_two n; simp only [zpow_natCast] at h; exact h
      have hpsi : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
        have h := psi_zpow_add_two n; simp only [zpow_natCast] at h; exact h
      rw [hphi, hpsi]; ring
  -- Backward direction uses: f(θ-b) = f(θ+b) - f(θ) and φ^(-1) = -ψ, ψ^(-1) = -φ
  -- Full proof requires careful two-step backward induction; we defer to future work.
  intro m
  cases m with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, Int.cast_natCast, zpow_natCast]
    exact hForward n
  | negSucc n =>
    -- Backward induction for negative integers
    -- Int.negSucc n represents -(n+1), so:
    -- n = 0: m = -1, n = 1: m = -2, etc.
    -- Use strong induction on n
    induction n using Nat.strong_induction_on with
    | _ n ih_neg =>
      -- The goal involves Int.negSucc n, let's convert to standard form
      -- Int.negSucc n = -(n + 1)
      have hgoal_lhs : θ + (Int.negSucc n : ℤ) * b = θ - (n + 1 : ℕ) * b := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [hgoal_lhs]
      -- Now prove f(θ - (n+1)b) = A * φ^(Int.negSucc n) + B * ψ^(Int.negSucc n)
      -- where Int.negSucc n = -(n+1)
      match n with
      | 0 =>
        -- m = -1: f(θ - b)
        simp only [zero_add, Nat.cast_one, one_mul]
        -- Use the recurrence: f(θ - b) = f(θ + b) - f(θ)
        have hRecAt : f θ + f (θ - b) = f (θ + b) := hFib θ
        have hfθ := hForward 0
        have hfθb := hForward 1
        simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one] at hfθ
        simp only [Nat.cast_one, one_mul, pow_one] at hfθb
        have hcompute : f (θ - b) = (A * φ + B * ψ) - (A + B) := by linarith
        rw [hcompute]
        have hphi_inv : φ ^ (Int.negSucc 0 : ℤ) = φ - 1 := by
          have : (Int.negSucc 0 : ℤ) = -1 := rfl
          rw [this, phi_zpow_neg_one, phi_sub_one_eq_neg_psi]
        have hpsi_inv : ψ ^ (Int.negSucc 0 : ℤ) = ψ - 1 := by
          have : (Int.negSucc 0 : ℤ) = -1 := rfl
          rw [this, psi_zpow_neg_one, psi_sub_one_eq_neg_phi]
        rw [hphi_inv, hpsi_inv]
        ring
      | n' + 1 =>
        -- m = -(n'+2): use backward recurrence
        simp only [Nat.cast_add, Nat.cast_one]
        -- Use the recurrence at x = θ - (n'+1)b
        have hRecAtM1 := hFib (θ - (n' + 1 : ℕ) * b)
        have heq_x_minus_b : θ - (n' + 1 : ℕ) * b - b = θ - (n' + 2 : ℕ) * b := by
          simp only [Nat.cast_add, Nat.cast_one]; ring
        have heq_x_plus_b : θ - (n' + 1 : ℕ) * b + b = θ - n' * b := by
          simp only [Nat.cast_add, Nat.cast_one]; ring
        rw [heq_x_minus_b, heq_x_plus_b] at hRecAtM1
        have hBackward : f (θ - (n' + 2 : ℕ) * b) = f (θ - n' * b) - f (θ - (n' + 1 : ℕ) * b) := by
          linarith
        have heq_cast : θ - (↑n' + 1 + 1) * b = θ - (n' + 2 : ℕ) * b := by
          simp only [Nat.cast_add]; ring
        rw [heq_cast, hBackward]
        -- Get IH values
        have ih_n'_plus_1 : f (θ - (n' + 1 : ℕ) * b) =
            A * φ ^ (Int.negSucc n' : ℤ) + B * ψ ^ (Int.negSucc n' : ℤ) := by
          have key := ih_neg n' (Nat.lt_succ_self n')
          have heq_lhs : θ + (Int.negSucc n' : ℤ) * b = θ - (n' + 1 : ℕ) * b := by
            simp only [Int.negSucc_eq]
            push_cast
            ring
          rw [heq_lhs] at key
          exact key
        have ih_n' : f (θ - n' * b) = A * φ ^ (-(n' : ℤ)) + B * ψ ^ (-(n' : ℤ)) := by
          cases n' with
          | zero =>
            simp only [Nat.cast_zero, neg_zero, zpow_zero, mul_one, zero_mul, sub_zero]
            have h0 := hForward 0
            simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one] at h0
            exact h0
          | succ k =>
            have key := ih_neg k (by omega : k < k + 1 + 1)
            have heq_lhs : θ + (Int.negSucc k : ℤ) * b = θ - (k + 1 : ℕ) * b := by
              simp only [Int.negSucc_eq]
              push_cast
              ring
            rw [heq_lhs] at key
            -- key has ↑(k + 1), goal has (↑k + 1). These are equal by push_cast.
            have h_negSucc_eq : (Int.negSucc k : ℤ) = -(↑k + 1 : ℤ) := Int.negSucc_eq k
            simp only [h_negSucc_eq] at key
            -- Now normalize ↑(k+1) to (↑k + 1) in key
            push_cast at key ⊢
            exact key
        rw [ih_n', ih_n'_plus_1]
        -- Use backward Fibonacci
        have hphi_back : φ ^ (Int.negSucc (n' + 1) : ℤ) =
            φ ^ (-(n' : ℤ)) - φ ^ (Int.negSucc n' : ℤ) := by
          have := phi_zpow_backward (Int.negSucc (n' + 1) : ℤ)
          -- phi_zpow_backward: φ^n = φ^(n+2) - φ^(n+1)
          -- So: φ^(Int.negSucc (n'+1)) = φ^(Int.negSucc (n'+1) + 2) - φ^(Int.negSucc (n'+1) + 1)
          -- = φ^(-(n'+2) + 2) - φ^(-(n'+2) + 1) = φ^(-n') - φ^(-(n'+1))
          have h1 : (Int.negSucc (n' + 1) : ℤ) + 2 = -(n' : ℤ) := by
            simp only [Int.negSucc_eq]; push_cast; ring
          have h2 : (Int.negSucc (n' + 1) : ℤ) + 1 = Int.negSucc n' := by
            simp only [Int.negSucc_eq]; push_cast; ring
          rw [h1, h2] at this
          exact this
        have hpsi_back : ψ ^ (Int.negSucc (n' + 1) : ℤ) =
            ψ ^ (-(n' : ℤ)) - ψ ^ (Int.negSucc n' : ℤ) := by
          have := psi_zpow_backward (Int.negSucc (n' + 1) : ℤ)
          have h1 : (Int.negSucc (n' + 1) : ℤ) + 2 = -(n' : ℤ) := by
            simp only [Int.negSucc_eq]; push_cast; ring
          have h2 : (Int.negSucc (n' + 1) : ℤ) + 1 = Int.negSucc n' := by
            simp only [Int.negSucc_eq]; push_cast; ring
          rw [h1, h2] at this
          exact this
        rw [hphi_back, hpsi_back]
        ring

/-- The set {m*b - n*a} for integers m,n is dense when b/a is irrational. -/
lemma scaled_linear_combo_dense (a b : ℝ) (ha : a ≠ 0) (hba : Irrational (b / a)) :
    Dense {x : ℝ | ∃ m n : ℤ, x = m * b - n * a} := by
  -- {m*b - n*a} = a * {m*(b/a) - n} = a * {m*(b/a) + (-n)}
  -- Since b/a is irrational, {m*(b/a) - n} is dense by irrational_linear_combination_dense
  have hDense : Dense {y : ℝ | ∃ p q : ℤ, y = p - q * (b / a)} :=
    irrational_linear_combination_dense (b / a) hba
  -- Dense means closure equals univ
  rw [dense_iff_closure_eq]
  -- Show closure is univ by showing every point is in closure
  ext x
  simp only [Set.mem_univ, iff_true, mem_closure_iff_nhds]
  intro U hU
  -- U is in nhds x, so there's an ε > 0 with ball(x, ε) ⊆ U
  rw [Metric.mem_nhds_iff] at hU
  obtain ⟨ε, hε, hball⟩ := hU
  -- Find y in the dense set close to x/a
  have habs_a_pos : 0 < |a| := abs_pos.mpr ha
  obtain ⟨y, hy_mem, hy_dist⟩ := hDense.exists_dist_lt (x / a) (div_pos hε habs_a_pos)
  obtain ⟨p, q, hpq⟩ := hy_mem
  -- The element p*a - q*b = a*(p - q*(b/a)) is close to x
  use a * (↑p - ↑q * (b / a))
  constructor
  · -- Show membership in U
    apply hball
    rw [Metric.mem_ball]
    rw [hpq] at hy_dist
    -- dist y (x/a) < ε/|a| means |y - x/a| < ε/|a|
    rw [Real.dist_eq] at hy_dist ⊢
    calc |a * (↑p - ↑q * (b / a)) - x|
        = |a * ((↑p - ↑q * (b / a)) - x / a)| := by field_simp [ha]
      _ = |a| * |↑p - ↑q * (b / a) - x / a| := abs_mul a _
      _ = |a| * |x / a - (↑p - ↑q * (b / a))| := by rw [abs_sub_comm]
      _ < |a| * (ε / |a|) := by
          apply mul_lt_mul_of_pos_left hy_dist habs_a_pos
      _ = ε := by field_simp [ne_of_gt habs_a_pos]
  · -- Show it's in the set
    -- We have a * (↑p - ↑q * (b / a)) = ↑p * a - ↑q * b
    -- The target set is {m * b - n * a}, so m = -q, n = -p
    refine ⟨-q, -p, ?_⟩
    simp only [Int.cast_neg]
    field_simp [ha]
    ring

/-- The density argument: if Ψ(θ + mb - na) = C·e^{A(mb-na)}·Ψ(θ) for all m,n
and b/a is irrational, then Ψ(x) = C'·e^{Ax} for all x. -/
theorem density_forces_exponential
    (Ψ : ℝ → ℝ) (A : ℝ) (a b : ℝ)
    (ha : a ≠ 0) (hba : Irrational (b / a))
    (hPos : ∀ x, 0 < Ψ x)
    (hCont : Continuous Ψ)  -- K&S uses this implicitly via "to arbitrarily high precision"
    (hExp : ∀ (m n : ℤ) (θ : ℝ), Ψ (θ + m * b - n * a) = Real.exp (A * (m * b - n * a)) * Ψ θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  -- Step 1: Show Ψ(x) = Ψ(0) * exp(A*x) for all x
  use Ψ 0, hPos 0
  intro x
  -- Step 2: By density, x is approximated by {m*b - n*a}
  have hDense := scaled_linear_combo_dense a b ha hba
  -- Step 3: Use continuity to extend from dense set to all of ℝ
  -- The key is that Ψ(y) = Ψ(0) * exp(A*y) holds for y in the dense set,
  -- and by continuity it extends to all x.

  -- First show: for y = m*b - n*a, we have Ψ(y) = Ψ(0) * exp(A*y)
  have hOnDense : ∀ m n : ℤ, Ψ (m * b - n * a) = Ψ 0 * Real.exp (A * (m * b - n * a)) := by
    intro m n
    have := hExp m n 0
    simp only [zero_add] at this
    linarith

  -- Define f(x) = Ψ(x) - Ψ(0) * exp(A*x)
  -- f is continuous and vanishes on the dense set, so f = 0 everywhere
  have hf_cont : Continuous (fun x => Ψ x - Ψ 0 * Real.exp (A * x)) :=
    hCont.sub (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id')))

  have hf_zero_dense : ∀ y ∈ {x : ℝ | ∃ m n : ℤ, x = m * b - n * a},
      Ψ y - Ψ 0 * Real.exp (A * y) = 0 := by
    intro y hy
    obtain ⟨m, n, rfl⟩ := hy
    rw [hOnDense m n]
    ring

  -- A continuous function that vanishes on a dense set vanishes everywhere
  have hf_zero : ∀ x, Ψ x - Ψ 0 * Real.exp (A * x) = 0 := by
    intro x
    have : IsClosed {x : ℝ | Ψ x - Ψ 0 * Real.exp (A * x) = 0} := by
      exact isClosed_eq hf_cont continuous_const
    have hsubset : {x : ℝ | ∃ m n : ℤ, x = m * b - n * a} ⊆
                   {x : ℝ | Ψ x - Ψ 0 * Real.exp (A * x) = 0} := by
      intro y hy
      exact hf_zero_dense y hy
    have hclosure : closure {x : ℝ | ∃ m n : ℤ, x = m * b - n * a} ⊆
                    {x : ℝ | Ψ x - Ψ 0 * Real.exp (A * x) = 0} := by
      exact this.closure_subset_iff.mpr hsubset
    have huniv : closure {x : ℝ | ∃ m n : ℤ, x = m * b - n * a} = Set.univ :=
      hDense.closure_eq
    rw [huniv] at hclosure
    exact hclosure (Set.mem_univ x)

  linarith [hf_zero x]

/-! ## Monotonicity-based continuity derivation

K&S's proof says "to arbitrarily high precision (ε → 0)" which implicitly assumes continuity.
This is unsatisfying for foundations - we want to DERIVE continuity, not assume it.

**Key insight**: The representation Θ : Scale → ℝ is an order isomorphism, hence monotone.
Monotone functions that agree with continuous functions on dense sets are themselves continuous.

This section develops the machinery to derive continuity from:
1. Positivity (Ψ > 0)
2. Monotonicity on the dense lattice (from the recurrence structure)
3. Agreement with exponential on the dense lattice

This is strictly weaker than assuming continuity à la Cox!
-/

/-- A function is monotone increasing on a set. -/
def MonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → f x ≤ f y

/-- A function is strictly monotone increasing on a set. -/
def StrictMonoOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x < y → f x < f y

/-- Key lemma: On the dense lattice, Ψ is strictly monotone.

From Ψ(θ + na) = 2^n · Ψ(θ), we see Ψ doubles with each step of size a.
Combined with positivity, this gives strict monotonicity along the lattice. -/
lemma exponential_on_lattice_strictMono
    (Ψ : ℝ → ℝ) (A a : ℝ) (_ha : a ≠ 0) (_hA : A ≠ 0)
    (hPos : ∀ x, 0 < Ψ x)
    (hLattice : ∀ m n : ℤ, ∀ θ : ℝ, Ψ (θ + m * a - n * a) = Real.exp (A * (m * a - n * a)) * Ψ θ) :
    (0 < A → StrictMonoOn Ψ {x : ℝ | ∃ m n : ℤ, x = m * a - n * a}) ∧
    (A < 0 → StrictMonoOn (fun x => -Ψ x) {x : ℝ | ∃ m n : ℤ, x = m * a - n * a}) := by
  constructor
  · intro hApos x hx y hy hxy
    obtain ⟨m₁, n₁, rfl⟩ := hx
    obtain ⟨m₂, n₂, rfl⟩ := hy
    -- x = m₁*a - n₁*a < y = m₂*a - n₂*a
    -- Ψ(x) = exp(A*x) * Ψ(0) and Ψ(y) = exp(A*y) * Ψ(0)
    -- Since A > 0 and x < y, we have exp(A*x) < exp(A*y)
    have h0 := hLattice m₁ n₁ 0
    have h1 := hLattice m₂ n₂ 0
    simp only [zero_add] at h0 h1
    rw [h0, h1]
    apply mul_lt_mul_of_pos_right
    · exact Real.exp_strictMono (mul_lt_mul_of_pos_left hxy hApos)
    · exact hPos 0
  · intro hAneg x hx y hy hxy
    obtain ⟨m₁, n₁, rfl⟩ := hx
    obtain ⟨m₂, n₂, rfl⟩ := hy
    have h0 := hLattice m₁ n₁ 0
    have h1 := hLattice m₂ n₂ 0
    simp only [zero_add] at h0 h1
    -- Goal: -Ψ(x) < -Ψ(y), i.e., Ψ(y) < Ψ(x)
    simp only [h0, h1, neg_lt_neg_iff]
    apply mul_lt_mul_of_pos_right
    · -- exp(A*y) < exp(A*x) because A < 0 and x < y
      apply Real.exp_strictMono
      exact mul_lt_mul_of_neg_left hxy hAneg
    · exact hPos 0

/-- **Key theorem**: Monotone + agrees with continuous on dense → continuous.

This is the crucial step that lets us DERIVE continuity rather than assume it.
A monotone function on ℝ has at most countably many discontinuities.
If it agrees with a continuous function on a dense set, there can be no discontinuities.

**Proof sketch**:
1. First prove f = g everywhere using squeeze argument
2. For any x:
   - Left limit L = sSup {f(y) : y < x} exists by `Monotone.tendsto_nhdsLT`
   - For y ∈ D with y < x: f(y) = g(y), and D ∩ Iio x is dense below x
   - By continuity of g and density, L = g(x)
   - Similarly right limit R = g(x)
   - By monotonicity: L ≤ f(x) ≤ R, so f(x) = g(x)
3. Therefore f = g, and f inherits continuity from g -/
theorem monotone_dense_continuous
    (f g : ℝ → ℝ) (D : Set ℝ)
    (hDense : Dense D)
    (hMono : Monotone f)
    (hgCont : Continuous g)
    (hAgree : ∀ x ∈ D, f x = g x) :
    Continuous f := by
  -- Step 1: Prove f = g everywhere
  suffices hEq : f = g by rw [hEq]; exact hgCont
  ext x
  -- Step 2: Show f(x) = g(x) by squeezing between left and right limits
  -- The left limit sSup (f '' Iio x) = g(x) because:
  -- - For y ∈ D ∩ Iio x, f(y) = g(y)
  -- - D ∩ Iio x is dense in Iio x (since D is dense)
  -- - g is continuous, so g(y) → g(x) as y → x⁻
  -- - Therefore sSup (f '' (D ∩ Iio x)) = sSup (g '' (D ∩ Iio x)) = g(x)

  -- Key lemma: For monotone f, f is squeezed between its limits at any point
  -- If both limits equal g(x), then f(x) = g(x)

  -- Use antisymmetry: prove g(x) ≤ f(x) and f(x) ≤ g(x)
  apply le_antisymm
  · -- f(x) ≤ g(x): For any ε > 0, find y ∈ D with x < y < x + δ and f(y) = g(y) ≤ g(x) + ε
    -- Then f(x) ≤ f(y) = g(y) ≤ g(x) + ε
    by_contra h
    push_neg at h
    -- h: g(x) < f(x)
    -- By continuity of g, ∃ δ > 0 such that |y - x| < δ → |g(y) - g(x)| < (f(x) - g(x))/2
    -- By density, ∃ y ∈ D with x < y < x + δ
    -- Then f(x) ≤ f(y) = g(y) < g(x) + (f(x) - g(x))/2 < f(x)
    -- Contradiction
    have hε : 0 < f x - g x := sub_pos.mpr h
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hgCont.continuousAt) _ (half_pos hε)
    obtain ⟨y, hy_mem, hy_dist⟩ := hDense.exists_dist_lt x hδ_pos
    -- We need y > x for the monotonicity argument
    -- Use density more carefully: get y ∈ D with x < y
    have hDense_right : ∀ a b : ℝ, a < b → ∃ y ∈ D, y ∈ Set.Ioo a b := by
      intro a b hab
      have : Set.Ioo a b ∈ 𝓝 ((a + b) / 2) := by
        apply Ioo_mem_nhds <;> linarith
      exact hDense.exists_mem_open isOpen_Ioo ⟨(a + b) / 2, by constructor <;> linarith⟩
    obtain ⟨y, hy_D, hy_x, hy_delta⟩ := hDense_right x (x + δ) (by linarith)
    have hfy_eq : f y = g y := hAgree y hy_D
    have hfx_le : f x ≤ f y := hMono (le_of_lt hy_x)
    have hgy_close : |g y - g x| < (f x - g x) / 2 := by
      apply hδ
      rw [Real.dist_eq]
      calc |y - x| = y - x := abs_of_pos (sub_pos.mpr hy_x)
        _ < x + δ - x := sub_lt_sub_right hy_delta x
        _ = δ := by ring
    have hgy_bound : g y < g x + (f x - g x) / 2 := by
      have := abs_sub_lt_iff.mp hgy_close
      linarith
    have hContra : f x < g x + (f x - g x) / 2 := calc
      f x ≤ f y := hfx_le
      _ = g y := hfy_eq
      _ < g x + (f x - g x) / 2 := hgy_bound
    linarith
  · -- g(x) ≤ f(x): Similar argument with y < x
    by_contra h
    push_neg at h
    -- h: f(x) < g(x)
    have hε : 0 < g x - f x := sub_pos.mpr h
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hgCont.continuousAt) _ (half_pos hε)
    have hDense_left : ∀ a b : ℝ, a < b → ∃ y ∈ D, y ∈ Set.Ioo a b := by
      intro a b hab
      have : Set.Ioo a b ∈ 𝓝 ((a + b) / 2) := by
        apply Ioo_mem_nhds <;> linarith
      exact hDense.exists_mem_open isOpen_Ioo ⟨(a + b) / 2, by constructor <;> linarith⟩
    obtain ⟨y, hy_D, hy_delta, hy_x⟩ := hDense_left (x - δ) x (by linarith)
    have hfy_eq : f y = g y := hAgree y hy_D
    have hfy_le : f y ≤ f x := hMono (le_of_lt hy_x)
    have hgy_close : |g y - g x| < (g x - f x) / 2 := by
      apply hδ
      rw [Real.dist_eq]
      calc |y - x| = x - y := abs_sub_comm y x ▸ abs_of_pos (sub_pos.mpr hy_x)
        _ < x - (x - δ) := sub_lt_sub_left hy_delta x
        _ = δ := by ring
    have hgy_bound : g x - (g x - f x) / 2 < g y := by
      have := abs_sub_lt_iff.mp hgy_close
      linarith
    have : g x - (g x - f x) / 2 < f x := calc
      g x - (g x - f x) / 2 < g y := hgy_bound
      _ = f y := hfy_eq.symm
      _ ≤ f x := hfy_le
    linarith

/-- Corollary: positive monotone function agreeing with exponential on dense set
equals that exponential everywhere. -/
theorem positive_monotone_exponential_unique
    (f : ℝ → ℝ) (C A : ℝ) (D : Set ℝ)
    (hDense : Dense D)
    (_hPos : ∀ x, 0 < f x)
    (_hC : 0 < C)
    (hMono : Monotone f ∨ Antitone f)  -- Either increasing or decreasing
    (hAgree : ∀ x ∈ D, f x = C * Real.exp (A * x)) :
    ∀ x, f x = C * Real.exp (A * x) := by
  -- The exponential function C * exp(A * x) is continuous
  have hExpCont : Continuous (fun x => C * Real.exp (A * x)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id'))
  -- f agrees with this continuous function on D
  -- By monotone_dense_continuous, f is continuous
  -- Two continuous functions that agree on a dense set are equal (Hausdorff, via Continuous.ext_on)
  intro x
  cases hMono with
  | inl hMono =>
    have hfCont : Continuous f := monotone_dense_continuous f (fun x => C * Real.exp (A * x)) D
      hDense hMono hExpCont hAgree
    -- Continuous functions agreeing on dense set are equal (ℝ is T2)
    have hEqOn : Set.EqOn f (fun x => C * Real.exp (A * x)) D := hAgree
    have := Continuous.ext_on hDense hfCont hExpCont hEqOn
    exact congrFun this x
  | inr hAnti =>
    -- Antitone case: -f is monotone, same argument
    have hfCont : Continuous f := by
      have hNegMono : Monotone (fun x => -f x) := fun _ _ h => neg_le_neg (hAnti h)
      have hNegCont := monotone_dense_continuous (fun x => -f x)
        (fun x => -(C * Real.exp (A * x))) D hDense hNegMono
        (continuous_neg.comp hExpCont) (fun x hx => by simp [hAgree x hx])
      -- hNegCont : Continuous (fun x => -f x)
      -- We need: Continuous f
      -- Since -(- f x) = f x, we have Continuous f
      have : (fun x => - -f x) = f := by ext x; ring
      rw [← this]
      exact Continuous.neg hNegCont
    have hEqOn : Set.EqOn f (fun x => C * Real.exp (A * x)) D := hAgree
    have := Continuous.ext_on hDense hfCont hExpCont hEqOn
    exact congrFun this x

/-! ## Deriving monotonicity from the recurrence structure -/

/-- From the 2-term recurrence Ψ(θ + na) = 2^n Ψ(θ), monotonicity follows. -/
lemma two_term_recurrence_monotone
    (Ψ : ℝ → ℝ) (a : ℝ) (_ha : 0 < a)
    (hPos : ∀ x, 0 < Ψ x)
    (hRec : ∀ θ : ℝ, ∀ n : ℤ, Ψ (θ + n * a) = (2 : ℝ) ^ n * Ψ θ) :
    ∀ θ : ℝ, ∀ m n : ℤ, m < n → Ψ (θ + m * a) < Ψ (θ + n * a) := by
  intro θ m n hmn
  rw [hRec θ m, hRec θ n]
  apply mul_lt_mul_of_pos_right
  · exact zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) hmn
  · exact hPos θ

/-! ## Deriving continuity from ProductEquation + StrictMono + Positivity

The key insight (GPT-5.2 Pro): We can derive continuity INDEPENDENTLY of knowing Ψ is exponential.

**Argument**:
1. From doubling: range Ψ ⊇ {C · 2^n : n ∈ ℤ}
2. {C · 2^n : n ∈ ℤ} is dense in (0, ∞)
3. A strictly monotone function with dense range in (0, ∞) has no jump discontinuities
4. Hence Ψ is continuous

**Why this works**: If Ψ had a jump discontinuity at x₀, the left and right limits would
differ, creating a "gap" (L, R) in the range. But the dense subset {C · 2^n} would
intersect this gap, contradiction.
-/

/-- **Continuity from ProductEquation + StrictMono + Positivity**

A strictly monotone positive function satisfying the ProductEquation is continuous.

**Key insight**: The ProductEquation forces range(Ψ) to be closed under addition!
From τ = 0: Ψ(ξ) + Ψ(η) = Ψ(ζ(ξ, η)), so for any u, v ∈ range(Ψ), u + v ∈ range(Ψ).

**Why this implies dense range**:
- Let C := Ψ(0) > 0. Then C ∈ range(Ψ).
- From doubling: C/2 = Ψ(-a), C/4 = Ψ(-2a), ... so C/2^k ∈ range(Ψ) for all k ∈ ℕ.
- From additive closure: C + C = 2C ∈ range(Ψ), and inductively mC ∈ range(Ψ).
- Combining: {m · C / 2^k : m ∈ ℕ, k ∈ ℕ} ⊆ range(Ψ).
- This is the set of positive dyadic rationals times C, which is DENSE in (0, ∞)!

**Why dense range implies continuity**:
- For strictly monotone Ψ, at any point x₀, left/right limits exist.
- If leftLim < rightLim, the gap (leftLim, rightLim) is NOT in range(Ψ) (except Ψ(x₀)).
- But range(Ψ) is dense in (0, ∞), so (leftLim, rightLim) ∩ range(Ψ) is dense in the gap.
- Contradiction! So leftLim = rightLim = Ψ(x₀), hence Ψ is continuous.
-/
theorem productEquation_strictMono_pos_continuous
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hStrictMono : StrictMono Ψ) :
    Continuous Ψ := by
  -- Step 1: Extract doubling parameter and constants
  let a : ℝ := ζ 0 0
  have hShift : ∀ τ : ℝ, Ψ (τ + a) = 2 * Ψ τ := fun τ => by
    simpa using ProductEquation.shift_two_mul hProd τ
  have ha_ne : a ≠ 0 := by
    intro ha0; have h := hShift 0; simp only [ha0, add_zero] at h; linarith [hPos 0]
  have ha_pos : 0 < a := by
    by_contra h; push_neg at h
    rcases h.lt_or_eq with ha_neg | ha_zero
    · have h1 : Ψ a < Ψ 0 := hStrictMono ha_neg
      have h2 : Ψ a = 2 * Ψ 0 := by simpa using hShift 0
      linarith [hPos 0]
    · exact ha_ne ha_zero

  let C := Ψ 0
  have hC_pos : 0 < C := hPos 0

  -- Step 2: Range is closed under addition (from ProductEquation at τ = 0)
  have hRangeAdd : ∀ u v : ℝ, u ∈ Set.range Ψ → v ∈ Set.range Ψ → (u + v) ∈ Set.range Ψ := by
    intro u v ⟨x, hx⟩ ⟨y, hy⟩
    use ζ x y
    have := hProd 0 x y
    simp only [zero_add] at this
    rw [hx, hy] at this
    exact this.symm

  -- Step 3: Doubling gives C/2^k in range for all k ∈ ℕ
  -- First prove the value equality, then get range membership
  have hHalving_eq : ∀ k : ℕ, Ψ (-(k : ℤ) * a) = C / 2 ^ k := by
    intro k
    induction k with
    | zero => simp [C]
    | succ n ih =>
      have h1 : (-(↑(n + 1) : ℤ) : ℝ) * a = -(n : ℤ) * a - a := by push_cast; ring
      rw [h1]
      have h2 : Ψ (-(n : ℤ) * a - a + a) = 2 * Ψ (-(n : ℤ) * a - a) := hShift _
      simp only [sub_add_cancel] at h2
      have h3 : Ψ (-(n : ℤ) * a - a) = Ψ (-(n : ℤ) * a) / 2 := by linarith
      rw [h3, ih]
      have hne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hne]
      ring
  have hHalving : ∀ k : ℕ, C / (2 : ℝ) ^ k ∈ Set.range Ψ := by
    intro k
    exact ⟨-(k : ℤ) * a, hHalving_eq k⟩

  -- Step 4: Additive closure gives mC/2^k in range for all m ≥ 1, k ∈ ℕ
  have hDyadicInRange : ∀ m k : ℕ, 1 ≤ m → (m : ℝ) * C / (2 : ℝ) ^ k ∈ Set.range Ψ := by
    intro m k hm
    induction m with
    | zero => omega
    | succ n ih =>
      -- (n+1) * C / 2^k = n * C / 2^k + C / 2^k
      have heq : ((n + 1 : ℕ) : ℝ) * C / (2 : ℝ) ^ k = (n : ℝ) * C / (2 : ℝ) ^ k + C / (2 : ℝ) ^ k := by
        have hne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
        field_simp [hne]
        push_cast
        ring
      rw [heq]
      cases n with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, zero_div, zero_add]
        exact hHalving k
      | succ n' =>
        apply hRangeAdd
        · exact ih (by omega)
        · exact hHalving k

  -- Step 5: The set {m * C / 2^k : m ≥ 1, k ∈ ℕ} is dense in (0, ∞)
  -- For any y > 0 and ε > 0, find m, k such that |m * C / 2^k - y| < ε
  have hDensityInPos : ∀ y : ℝ, 0 < y → ∀ ε > 0, ∃ v ∈ Set.range Ψ, |v - y| < ε := by
    intro y hy ε hε
    -- Strategy: choose k large enough that C/2^k < min(ε, y), then m ≈ y * 2^k / C
    -- Use Archimedean property: since 2^n → ∞, there exists k with 2^k > C / min(ε, y)
    have hmin_pos : 0 < min ε y := lt_min hε hy
    have h2_gt_1 : (1 : ℝ) < 2 := by norm_num
    have hquot_pos : 0 < C / min ε y := div_pos hC_pos hmin_pos
    -- From Archimedean property applied to logs:
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos h2_gt_1
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (C / min ε y) / Real.log 2)
    let k := n
    have hk_large' : (2 : ℝ) ^ k > C / min ε y := by
      have hlog_k : Real.log (C / min ε y) / Real.log 2 < k := hn
      have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
      rw [gt_iff_lt, ← Real.log_lt_log_iff hquot_pos h2k_pos]
      calc Real.log (C / min ε y)
          = Real.log (C / min ε y) / Real.log 2 * Real.log 2 := by field_simp
        _ < k * Real.log 2 := by apply mul_lt_mul_of_pos_right hlog_k hlog2_pos
        _ = Real.log (2 ^ k) := by rw [Real.log_pow]
    have hk_large : C / (2 : ℝ) ^ k < min ε y := by
      have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
      have h2k : (2 : ℝ) ^ k > C / min ε y := hk_large'
      calc C / (2 : ℝ) ^ k < C / (C / min ε y) := by
             apply div_lt_div_of_pos_left hC_pos
             · exact div_pos hC_pos hmin_pos
             · exact h2k
        _ = min ε y := by field_simp
    -- Choose m = ⌈y * 2^k / C⌉
    let r := y * (2 : ℝ) ^ k / C
    have hr_pos : 0 < r := div_pos (mul_pos hy (pow_pos (by norm_num) k)) hC_pos
    let m := Nat.ceil r
    have hm_ge_1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hr_pos).ne'
    use (m : ℝ) * C / (2 : ℝ) ^ k
    constructor
    · exact hDyadicInRange m k hm_ge_1
    · -- Show |m * C / 2^k - y| < ε
      have hceil_bound : r ≤ m := Nat.le_ceil r
      have hceil_lower : (m : ℝ) - 1 < r := by
        -- From Nat.ceil_lt_add_one: (m : ℝ) < r + 1, hence (m : ℝ) - 1 < r
        have h := Nat.ceil_lt_add_one (le_of_lt hr_pos)
        linarith
      have hne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
      have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
      rw [abs_lt]
      constructor
      · -- m * C / 2^k - y > -ε
        have h1 : y ≤ (m : ℝ) * C / (2 : ℝ) ^ k := by
          calc y = r * C / (2 : ℝ) ^ k := by simp only [r]; field_simp
            _ ≤ (m : ℝ) * C / (2 : ℝ) ^ k := by
              apply div_le_div_of_nonneg_right _ (le_of_lt h2k_pos)
              apply mul_le_mul_of_nonneg_right hceil_bound
              exact le_of_lt hC_pos
        linarith
      · -- m * C / 2^k - y < ε
        have h2 : (m : ℝ) * C / (2 : ℝ) ^ k < y + C / (2 : ℝ) ^ k := by
          have h3 : (m : ℝ) < r + 1 := by linarith
          calc (m : ℝ) * C / (2 : ℝ) ^ k
              < (r + 1) * C / (2 : ℝ) ^ k := by
                apply div_lt_div_of_pos_right _ h2k_pos
                apply mul_lt_mul_of_pos_right h3 hC_pos
            _ = y + C / (2 : ℝ) ^ k := by simp only [r]; field_simp
        have hstep : C / (2 : ℝ) ^ k < ε := lt_of_lt_of_le hk_large (min_le_left _ _)
        linarith

  -- Step 6: Dense range in (0, ∞) + strict mono → continuous
  -- Constructive approach: use density to find bounds, then use strict mono for δ
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Let y₀ = Ψ(x₀). Find v₁, v₂ in range with y₀ - ε < v₁ < y₀ < v₂ < y₀ + ε
  let y₀ := Ψ x₀
  have hy₀_pos : 0 < y₀ := hPos x₀

  -- Find v₂ > y₀ in range, within ε of y₀
  obtain ⟨v₂, hv₂_range, hv₂_close⟩ := hDensityInPos (y₀ + ε / 2) (by linarith) (ε / 2) (by linarith)
  have hv₂_above : y₀ < v₂ := by
    have : |v₂ - (y₀ + ε / 2)| < ε / 2 := hv₂_close
    rw [abs_lt] at this
    linarith
  have hv₂_bound : v₂ < y₀ + ε := by
    have : |v₂ - (y₀ + ε / 2)| < ε / 2 := hv₂_close
    rw [abs_lt] at this
    linarith

  -- Find v₁ < y₀ in range (handling case y₀ - ε/2 ≤ 0)
  by_cases hcase : y₀ - ε / 2 > 0
  case pos =>
    obtain ⟨v₁, hv₁_range, hv₁_close⟩ := hDensityInPos (y₀ - ε / 2) hcase (ε / 2) (by linarith)
    have hv₁_below : v₁ < y₀ := by
      have : |v₁ - (y₀ - ε / 2)| < ε / 2 := hv₁_close
      rw [abs_lt] at this
      linarith
    have hv₁_bound : y₀ - ε < v₁ := by
      have : |v₁ - (y₀ - ε / 2)| < ε / 2 := hv₁_close
      rw [abs_lt] at this
      linarith

    -- Get preimages x₁, x₂ with Ψ(x₁) = v₁, Ψ(x₂) = v₂
    obtain ⟨x₁, hx₁⟩ := hv₁_range
    obtain ⟨x₂, hx₂⟩ := hv₂_range

    -- By strict monotonicity: x₁ < x₀ < x₂
    have hx₁_lt : x₁ < x₀ := by
      by_contra h; push_neg at h
      have : Ψ x₁ ≥ Ψ x₀ := by
        rcases h.lt_or_eq with hlt | heq
        · exact le_of_lt (hStrictMono hlt)
        · simp [heq]
      rw [hx₁] at this
      linarith
    have hx₂_gt : x₀ < x₂ := by
      by_contra h; push_neg at h
      have : Ψ x₂ ≤ Ψ x₀ := by
        rcases h.lt_or_eq with hlt | heq
        · exact le_of_lt (hStrictMono hlt)
        · simp [heq]
      rw [hx₂] at this
      linarith

    -- δ = min(x₀ - x₁, x₂ - x₀)
    use min (x₀ - x₁) (x₂ - x₀)
    constructor
    · exact lt_min (by linarith) (by linarith)
    · intro x hx
      rw [Real.dist_eq] at hx ⊢
      have hx_in : x₁ < x ∧ x < x₂ := by
        constructor
        · have : |x - x₀| < x₀ - x₁ := lt_of_lt_of_le hx (min_le_left _ _)
          rw [abs_lt] at this
          linarith
        · have : |x - x₀| < x₂ - x₀ := lt_of_lt_of_le hx (min_le_right _ _)
          rw [abs_lt] at this
          linarith
      -- By strict mono: v₁ < Ψ(x) < v₂, hence |Ψ(x) - y₀| < ε
      have hΨx_bounds : v₁ < Ψ x ∧ Ψ x < v₂ := by
        constructor
        · rw [← hx₁]; exact hStrictMono hx_in.1
        · rw [← hx₂]; exact hStrictMono hx_in.2
      rw [abs_lt]
      constructor <;> linarith

  case neg =>
    -- y₀ - ε/2 ≤ 0, so y₀ ≤ ε/2. Just use v₂ bound and positivity for lower bound.
    push_neg at hcase
    obtain ⟨x₂, hx₂⟩ := hv₂_range
    have hx₂_gt : x₀ < x₂ := by
      by_contra h; push_neg at h
      have : Ψ x₂ ≤ Ψ x₀ := by
        rcases h.lt_or_eq with hlt | heq
        · exact le_of_lt (hStrictMono hlt)
        · simp [heq]
      rw [hx₂] at this
      linarith

    -- Find some x₁ < x₀ (any will do for lower bound since Ψ > 0)
    use min 1 (x₂ - x₀)
    constructor
    · exact lt_min one_pos (by linarith)
    · intro x hx
      rw [Real.dist_eq] at hx ⊢
      have hx_upper : x < x₂ := by
        have : |x - x₀| < x₂ - x₀ := lt_of_lt_of_le hx (min_le_right _ _)
        rw [abs_lt] at this
        linarith
      have hΨx_upper : Ψ x < v₂ := by
        by_cases hcmp : x < x₂
        · rw [← hx₂]; exact hStrictMono hcmp
        · push_neg at hcmp
          exfalso; linarith
      -- Lower bound: Ψ(x) > 0 and y₀ ≤ ε/2 means Ψ(x) > y₀ - ε (since y₀ - ε < 0 ≤ Ψ(x))
      have hΨx_lower : Ψ x > y₀ - ε := by
        have hΨx_pos : 0 < Ψ x := hPos x
        have : y₀ - ε < 0 := by linarith
        linarith
      rw [abs_lt]
      constructor <;> linarith

/-- **K&S Appendix B - Clean Version with Strict Monotonicity Assumed**

This version assumes `StrictMono Ψ`, which is what K&S actually have from Appendix A
(the representation theorem gives an order isomorphism, hence strict monotonicity).

**GPT-5.2 Pro's Key Insight**: Once we derive continuity from ProductEquation + StrictMono +
Positivity, we can apply the existing `productEquation_solution_of_continuous_strictMono`
directly, bypassing the entire Fibonacci/dense-set construction.

**Proof strategy** (simplified):
1. Derive continuity: ProductEquation + StrictMono + Positivity → Continuous Ψ
   (The doubling forces range to contain {C·2^n}, dense in (0,∞), ruling out jumps)
2. Apply `productEquation_solution_of_continuous_strictMono` from FunctionalEquation.lean

This is much cleaner than the original Fibonacci approach and avoids the β-bridge argument.
-/
theorem ks_appendix_b_fibonacci_strictMono
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hStrictMono : StrictMono Ψ) :  -- From Appendix A order isomorphism!
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  -- GPT-5.2 Pro's insight: derive continuity and apply the existing theorem
  -- Step 1: Derive continuity from ProductEquation + StrictMono + Positivity
  have hCont : Continuous Ψ := productEquation_strictMono_pos_continuous Ψ ζ hProd hPos hStrictMono
  -- Step 2: Apply the existing theorem from FunctionalEquation.lean
  exact productEquation_solution_of_continuous_strictMono hProd hPos hCont hStrictMono

/-- Variant for StrictAnti case (via negation). -/
theorem ks_appendix_b_fibonacci_strictAnti
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hStrictAnti : StrictAnti Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  -- Transform via Ψ'(x) = Ψ(-x)
  let Ψ' : ℝ → ℝ := fun x => Ψ (-x)
  let ζ' : ℝ → ℝ → ℝ := fun ξ η => -ζ (-ξ) (-η)
  have hProd' : ProductEquation Ψ' ζ' := by
    intro τ ξ η
    simp only [Ψ', ζ']
    have := hProd (-τ) (-ξ) (-η)
    simp only [neg_add_rev] at this ⊢
    convert this using 2 <;> ring_nf
  have hPos' : ∀ x, 0 < Ψ' x := fun x => hPos (-x)
  have hStrictMono' : StrictMono Ψ' := hStrictAnti.comp (fun _ _ h => neg_lt_neg h)
  obtain ⟨C', A', hC'_pos, hΨ'_eq⟩ := ks_appendix_b_fibonacci_strictMono Ψ' ζ' hProd' hPos' hStrictMono'
  refine ⟨C', -A', hC'_pos, ?_⟩
  intro x
  have := hΨ'_eq (-x)
  simp only [Ψ', neg_neg] at this
  simp only [mul_neg, neg_mul] at this ⊢
  exact this

end Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Proofs.Direct.FibonacciProof
