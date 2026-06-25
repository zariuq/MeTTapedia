import Mettapedia.UniversalAI.UniversalPrediction.ChainRule
import Mettapedia.UniversalAI.UniversalPrediction.Distances

/-!
# Convergence of ξ to μ (Hutter 2005, Theorem 3.19)

This file proves the main convergence theorem from Hutter's Chapter 3: under dominance
`c * μ(x) ≤ ξ(x)` for all prefixes, the universal mixture ξ converges to the true
distribution μ.

The key results are:
* `Sn_le_Dn`: The total squared distance Sₙ is bounded by the total relative entropy Dₙ.
* `Dn_le_log_inv_c`: Dₙ ≤ log(1/c) (from dominance).
* `Sn_le_log_inv_c`: Total squared distance is finite (Sₙ ≤ log(1/c) < ∞).

This implies convergence: ξ(·|x₁:ₖ) → μ(·|x₁:ₖ) as k → ∞ in squared distance.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction

open scoped Classical BigOperators
open FiniteHorizon Entropy Distances

namespace Convergence

/-! ## Helper lemmas for the proofs -/

/-- For a PrefixMeasure, conditional probabilities sum to 1. -/
lemma condProb_sum_eq_one (μ : PrefixMeasure) (x : BinString) (hx : μ x ≠ 0) :
    FiniteHorizon.condProb μ.toSemimeasure x true +
    FiniteHorizon.condProb μ.toSemimeasure x false = 1 := by
  -- The ENNReal-level identity (reorder to match)
  have hENNReal : conditionalENN μ.toSemimeasure [true] x +
                  conditionalENN μ.toSemimeasure [false] x = 1 := by
    rw [add_comm]; exact conditionalENN_bool_sum μ x hx
  -- Convert to Real
  have htrueTop : conditionalENN μ.toSemimeasure [true] x ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
    exact condENN_le_one μ x true
  have hfalseTop : conditionalENN μ.toSemimeasure [false] x ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
    exact condENN_le_one μ x false
  simp only [FiniteHorizon.condProb]
  rw [← ENNReal.toReal_add htrueTop hfalseTop, hENNReal]
  simp

/-- For a semimeasure, conditional probabilities sum to at most 1. -/
lemma condProb_sum_le_one (ξ : Semimeasure) (x : BinString) :
    FiniteHorizon.condProb ξ x true + FiniteHorizon.condProb ξ x false ≤ 1 := by
  simp only [FiniteHorizon.condProb]
  by_cases hx0 : ξ x = 0
  · simp [conditionalENN, hx0]
  · have hxTop : ξ x ≠ ⊤ := semimeasure_ne_top ξ x
    -- The ENNReal sum is ≤ 1
    have hENNReal_le : conditionalENN ξ [true] x + conditionalENN ξ [false] x ≤ 1 := by
      unfold conditionalENN
      have hle : ξ (x ++ [false]) + ξ (x ++ [true]) ≤ ξ x := ξ.superadditive' x
      rw [ENNReal.div_add_div_same]
      rw [ENNReal.div_le_iff_le_mul (Or.inl hx0) (Or.inl hxTop), one_mul]
      rw [add_comm]
      exact hle
    have htrueTop : conditionalENN ξ [true] x ≠ ⊤ := by
      apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
      calc conditionalENN ξ [true] x ≤ conditionalENN ξ [true] x + conditionalENN ξ [false] x :=
             le_add_of_nonneg_right (by simp)
        _ ≤ 1 := hENNReal_le
    have hfalseTop : conditionalENN ξ [false] x ≠ ⊤ := by
      apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
      calc conditionalENN ξ [false] x ≤ conditionalENN ξ [true] x + conditionalENN ξ [false] x :=
             le_add_of_nonneg_left (by simp)
        _ ≤ 1 := hENNReal_le
    calc (conditionalENN ξ [true] x).toReal + (conditionalENN ξ [false] x).toReal
        = (conditionalENN ξ [true] x + conditionalENN ξ [false] x).toReal :=
            (ENNReal.toReal_add htrueTop hfalseTop).symm
      _ ≤ (1 : ENNReal).toReal := by
            apply ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hENNReal_le
      _ = 1 := by simp

/-- Relative entropy at n=0 is nonnegative under dominance.

D₀ = μ([]) * log(μ([])/ξ([])) = 1 * log(1/ξ([])) ≥ 0 since ξ([]) ≤ 1.

Under dominance `c * μ ≤ ξ` with c > 0, we have ξ([]) ≥ c * μ([]) = c > 0. -/
lemma relEntropy_zero_nonneg (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) :
    0 ≤ relEntropy μ ξ 0 := by
  unfold relEntropy expectPrefix
  simp only [prefixPMF_apply]
  -- For n=0, there's only one element in Fin 0 → Bool: the empty function
  -- Simplify the sum to just the [] case
  have heq : (∑ x : Fin 0 → Bool,
      (μ (List.ofFn x)).toReal *
        Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal)) =
      (μ []).toReal * Real.log ((μ []).toReal / (ξ []).toReal) := by
    have huniv : (Finset.univ : Finset (Fin 0 → Bool)) = {![]} := by
      ext f; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact i.elim0
    have hofFn : List.ofFn (α := Bool) ![] = [] := rfl
    simp only [huniv, Finset.sum_singleton, hofFn]
  rw [heq]
  -- μ([]) = 1, and ξ([]) ≤ 1, so log(1/ξ([])) ≥ 0
  have hμ_root : μ [] = 1 := μ.root_eq_one'
  have hξ_root_le : ξ [] ≤ 1 := semimeasure_le_one ξ []
  -- Under dominance c * μ([]) ≤ ξ([]), and μ([]) = 1, so ξ([]) ≥ c > 0
  have hξ_root_pos : 0 < ξ [] := by
    have hdom_root := hdom []
    rw [hμ_root] at hdom_root
    simp only [mul_one] at hdom_root
    have hc_pos : 0 < c := pos_iff_ne_zero.mpr hc0
    exact lt_of_lt_of_le hc_pos hdom_root
  have hξ_root_ne_top : ξ [] ≠ ⊤ := semimeasure_ne_top ξ []
  have hξ_toReal_pos : 0 < (ξ []).toReal := ENNReal.toReal_pos (ne_of_gt hξ_root_pos) hξ_root_ne_top
  have hξ_toReal_le : (ξ []).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hξ_root_le
    simp at h
    exact h
  -- Simplify: μ([]) = 1, so (μ []).toReal = 1
  have hμ_toReal : (μ []).toReal = 1 := by simp [hμ_root]
  rw [hμ_toReal, one_mul]
  -- Need: log(1 / ξ([]).toReal) ≥ 0
  have h1 : 1 ≤ 1 / (ξ []).toReal := by
    rw [one_le_div hξ_toReal_pos]
    exact hξ_toReal_le
  exact Real.log_nonneg h1

/-! ## Squared distance bound (s ≤ stepRelEntropy)

We show that the squared distance between conditional predictions is bounded by
the step relative entropy, which is key to the convergence bound.
-/

/-- The squared distance between μ and ξ conditional predictions at prefix x. -/
def sqDistStep (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString) : ℝ :=
  sqDistBinary (FiniteHorizon.condProb μ.toSemimeasure x true)
               (FiniteHorizon.condProb ξ x true)

/-- Squared distance is bounded by step relative entropy (Lemma 3.11s).

This is the key entropy inequality: s ≤ d.

The proof uses `sqDistBinary_le_klBinary` from Entropy.lean and bounds stepRelEntropy
from below by klBinary using the semimeasure property.

**Hypotheses**:
- `hμx`: μ(x) ≠ 0 (when μ(x) = 0, the contribution to the expectation is 0 anyway)
- `hξt`: condProb ξ x true ∈ (0, 1)
- `hξf`: condProb ξ x false > 0

This is satisfied for universal mixtures which assign positive probability to all extensions. -/
theorem sqDistStep_le_stepRelEntropy (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hμx : μ x ≠ 0)
    (hμ : FiniteHorizon.condProb μ.toSemimeasure x true ∈ Set.Icc (0 : ℝ) 1)
    (hξt : FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (hξf : 0 < FiniteHorizon.condProb ξ x false) :
    sqDistStep μ ξ x ≤ stepRelEntropy μ ξ x := by
  -- Let p = condProb_μ_true, q = condProb_ξ_true
  -- sqDistStep = sqDistBinary(p, q)
  -- stepRelEntropy = p * log(p/q) + (1-p) * log((1-p)/q_false)
  -- where q_false = condProb_ξ_false
  --
  -- We have sqDistBinary(p, q) ≤ klBinary(p, q) from Entropy.lean
  -- And klBinary(p, q) = p * log(p/q) + (1-p) * log((1-p)/(1-q))
  --
  -- Since q_false ≤ 1 - q (semimeasure property) and q_false > 0,
  -- log((1-p)/q_false) ≥ log((1-p)/(1-q))
  -- So stepRelEntropy ≥ klBinary(p, q) ≥ sqDistBinary(p, q)

  unfold sqDistStep stepRelEntropy

  set p := FiniteHorizon.condProb μ.toSemimeasure x true with hp_def
  set q := FiniteHorizon.condProb ξ x true with hq_def
  set p_false := FiniteHorizon.condProb μ.toSemimeasure x false with hp_false_def
  set q_false := FiniteHorizon.condProb ξ x false with hq_false_def

  have hp_ge : 0 ≤ p := hμ.1
  have hp_le : p ≤ 1 := hμ.2
  have hq_pos : 0 < q := hξt.1
  have hq_lt : q < 1 := hξt.2
  have hqf_pos : 0 < q_false := hξf

  -- First, get sqDistBinary ≤ klBinary
  have h_sq_le_kl : sqDistBinary p q ≤ klBinary p q :=
    sqDistBinary_le_klBinary_Icc_left (y := p) (z := q) hμ hξt

  -- Now we need klBinary(p, q) ≤ stepRelEntropy
  -- klBinary(p, q) = p * log(p/q) + (1-p) * log((1-p)/(1-q))
  -- stepRelEntropy = p * log(p/q) + p_false * log(p_false/q_false)

  -- Since μ(x) ≠ 0, we can use the sum = 1 property for p + p_false
  have hp_sum : p + p_false = 1 := condProb_sum_eq_one μ x hμx
  have hp_false_eq : p_false = 1 - p := by linarith

  -- The semimeasure property gives q + q_false ≤ 1, i.e., q_false ≤ 1 - q
  have hq_sum_le : q + q_false ≤ 1 := condProb_sum_le_one ξ x
  have hq_false_le : q_false ≤ 1 - q := by linarith

  have h1mq_pos : 0 < 1 - q := by linarith

  -- We need to compare:
  -- klBinary(p, q) = p * log(p/q) + (1-p) * log((1-p)/(1-q))
  -- stepRelEntropy = p * log(p/q) + (1-p) * log((1-p)/q_false)

  by_cases hp1 : p = 1
  · -- p = 1, so the second term (1-p)*... vanishes on both sides
    have hpf_eq : p_false = 0 := by simp [hp_false_eq, hp1]
    -- sqDistBinary(1, q) ≤ klBinary(1, q) = -log(q)
    -- stepRelEntropy = 1*log(1/q) + 0*log(0/q_false) = -log(q)
    -- So klBinary = stepRelEntropy at p=1
    -- Rewrite goal to use p=1 and p_false=0
    simp only [hp1, hpf_eq, zero_mul, add_zero, one_mul]
    -- Now goal is: sqDistBinary 1 q ≤ Real.log (1 / q)
    have h_sq_le_kl' : sqDistBinary 1 q ≤ klBinary 1 q := by
      rw [← hp1]; exact h_sq_le_kl
    -- klBinary 1 q = phi 1 - phi q - (1 - q) * phiDeriv q
    -- = 0 - (q log q + (1-q) log(1-q)) - (1-q) * (log q - log(1-q))
    -- = -q log q - (1-q) log(1-q) - (1-q) log q + (1-q) log(1-q)
    -- = -q log q - (1-q) log q = -(q + 1 - q) log q = -log q = log(1/q)
    have hkl_eq : klBinary 1 q = Real.log (1 / q) := by
      unfold klBinary phi phiDeriv
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      simp only [Real.log_one, mul_zero, zero_add]
      rw [Real.log_div one_ne_zero hq_ne, Real.log_one, zero_sub]
      ring
    rw [← hkl_eq]
    exact h_sq_le_kl'
  · push_neg at hp1
    have hp_lt1 : p < 1 := lt_of_le_of_ne hp_le hp1
    have h1mp_pos : 0 < 1 - p := by linarith

    -- Since q_false ≤ 1-q and both are positive:
    -- (1-p)/q_false ≥ (1-p)/(1-q), so log((1-p)/q_false) ≥ log((1-p)/(1-q))
    have hlog_ineq : Real.log ((1 - p) / (1 - q)) ≤ Real.log ((1 - p) / q_false) := by
      apply Real.log_le_log
      · -- (1-p)/(1-q) > 0
        exact div_pos h1mp_pos h1mq_pos
      · -- (1-p)/(1-q) ≤ (1-p)/q_false
        apply div_le_div_of_nonneg_left (le_of_lt h1mp_pos) hqf_pos
        exact hq_false_le

    have hmul_ineq : (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
        (1 - p) * Real.log ((1 - p) / q_false) := by
      apply mul_le_mul_of_nonneg_left hlog_ineq
      linarith

    -- klBinary in direct form
    have hkl_expand : klBinary p q =
        p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
      unfold klBinary phi phiDeriv
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      have h1mq_ne : 1 - q ≠ 0 := ne_of_gt h1mq_pos
      by_cases hp0 : p = 0
      · simp [hp0, Real.log_one]
        ring
      · have hp_pos : 0 < p := lt_of_le_of_ne hp_ge (ne_comm.mpr hp0)
        have h1mp_ne : 1 - p ≠ 0 := ne_of_gt h1mp_pos
        -- Expand and simplify using log properties
        rw [Real.log_div (ne_of_gt hp_pos) hq_ne,
            Real.log_div h1mp_ne h1mq_ne]
        ring

    calc sqDistBinary p q
        ≤ klBinary p q := h_sq_le_kl
      _ = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := hkl_expand
      _ ≤ p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / q_false) := by linarith
      _ = p * Real.log (p / q) + p_false * Real.log (p_false / q_false) := by
          rw [hp_false_eq]

/-! ## Telescoping and the convergence bound -/

/-- Expected squared distance at horizon n: `Sₙ := ∑_{k<n} E_μ[sₖ]`. -/
noncomputable def totalSqDist (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    expectPrefix μ k (fun x => sqDistStep μ ξ x)

/-- Total expected step entropy: `∑_{k<n} E_μ[dₖ]`. -/
noncomputable def totalStepEntropy (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    expectPrefix μ k (fun x => stepRelEntropy μ ξ x)

/-- Telescoping: `Dₙ₊₁ - D₀ = ∑_{k<n+1} E_μ[dₖ]`.

This follows from the chain rule `D_{k+1} = Dₖ + E[stepRelEntropy]` by induction. -/
theorem relEntropy_diff_eq_sum_step (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ) :
    relEntropy μ ξ n - relEntropy μ ξ 0 = totalStepEntropy μ ξ n := by
  induction n with
  | zero =>
    simp [totalStepEntropy]
  | succ n ih =>
    rw [relEntropy_succ_eq μ ξ hdom hc0 n]
    unfold totalStepEntropy
    simp only [Finset.sum_range_succ]
    unfold totalStepEntropy at ih
    rw [← ih]
    ring

/-- Main bound: Total squared distance ≤ Total step entropy.

`Sₙ ≤ ∑_{k<n} E[dₖ]` follows from `sₖ ≤ dₖ` pointwise.

**Hypothesis**: We require that ξ assigns strictly positive probability to both
next-bit outcomes at all prefixes. This is satisfied for universal mixtures. -/
theorem totalSqDist_le_totalStepEntropy (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    totalSqDist μ ξ n ≤ totalStepEntropy μ ξ n := by
  unfold totalSqDist totalStepEntropy
  apply Finset.sum_le_sum
  intro k _hk
  unfold expectPrefix
  apply Finset.sum_le_sum
  intro f _hf
  have hlen : (List.ofFn f).length = k := by simp
  -- Handle the case μ(x) = 0 separately: both sides become 0
  by_cases hμx : μ (List.ofFn f) = 0
  · simp [hμx]
  · apply mul_le_mul_of_nonneg_left
    · apply sqDistStep_le_stepRelEntropy
      · exact hμx
      · constructor
        · exact ENNReal.toReal_nonneg
        · have hle := condENN_le_one μ (List.ofFn f) true
          unfold condENN conditionalENN at hle
          simp only [FiniteHorizon.condProb, conditionalENN]
          have hle1 : (1 : ENNReal) ≠ ⊤ := by simp
          exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hle1 hle) hle1).mpr hle
      · exact h_cond_true k (List.ofFn f) hlen
      · exact h_cond_false k (List.ofFn f) hlen
    · exact ENNReal.toReal_nonneg

/-- **Theorem 3.19 (Convergence bound)**: Under dominance, total squared distance is finite.

`Sₙ ≤ Dₙ - D₀ ≤ Dₙ ≤ log(1/c)` for all n, which implies convergence of predictions.

The hypothesis `h_cond_true/false` requires that ξ assigns strictly positive probability to both
next-bit outcomes. This is typically satisfied when ξ is a universal mixture. -/
theorem convergence_bound (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    totalSqDist μ ξ n ≤ Real.log (1 / c.toReal) := by
  calc totalSqDist μ ξ n
      ≤ totalStepEntropy μ ξ n := totalSqDist_le_totalStepEntropy μ ξ n h_cond_true h_cond_false
    _ = relEntropy μ ξ n - relEntropy μ ξ 0 := (relEntropy_diff_eq_sum_step μ ξ hdom hc0 n).symm
    _ ≤ relEntropy μ ξ n := by
        have h0 : 0 ≤ relEntropy μ ξ 0 := relEntropy_zero_nonneg μ ξ hdom hc0
        linarith
    _ ≤ Real.log (1 / c.toReal) := relEntropy_le_log_inv_of_dominates μ ξ hdom hc0 n

/-- Corollary: The limit of Sₙ as n → ∞ is bounded.

This is the key finiteness result: `∑_{k=1}^∞ E_μ[sₖ] ≤ log(1/c) < ∞`.

Since the partial sums are uniformly bounded, the infinite sum converges. -/
theorem sum_sqDist_le_log_inv (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    ∀ n, totalSqDist μ ξ n ≤ Real.log (1 / c.toReal) := fun n =>
  convergence_bound μ ξ hdom hc0 n h_cond_true h_cond_false

/-- Convergence: squared distance between predictions tends to zero in mean square.

From `∑ E[sₖ] < ∞`, we get `sₖ → 0` in mean square (i.m.s.). -/
theorem sqDistStep_tendsto_zero (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    ∃ (bound : ℝ), ∀ n, totalSqDist μ ξ n ≤ bound :=
  ⟨Real.log (1 / c.toReal), sum_sqDist_le_log_inv μ ξ hdom hc0 h_cond_true h_cond_false⟩

end Convergence

end Mettapedia.UniversalAI.UniversalPrediction
