/-
# Counterexample to K&S "Discontinuous Re-grading" Claim

In Section 2 of "Foundations of Inference," Knuth & Skilling claim that continuity is
"merely a convenient convention" and suggest that a discontinuous "re-grading" map Θ
could preserve the sum rule. They give the example of a base-conversion map.

**This file proves their claim is false.**

The sum rule requires: v(A ∨ B) + v(A ∧ B) = v(A) + v(B)

For a re-grading Θ: ℝ → ℝ to preserve the sum rule with ordinary addition, we need:
  Θ(x + y) = Θ(x) + Θ(y)  (additivity)

Combined with order-preservation (to maintain monotonicity), we prove:

**Theorem:** If Θ: ℝ → ℝ is additive and monotone, then Θ(x) = Θ(1) * x.

Hence Θ is linear, therefore continuous. There is no discontinuous re-grading
that preserves both the sum rule and monotonicity.

The pathological additive functions (constructed via Hamel bases in `CauchyPathology.lean`)
are necessarily **non-monotonic** — they oscillate wildly and cannot preserve order.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples

/-! ## Additive functions over ℚ are linear -/

/-- An additive function satisfies f(0) = 0. -/
theorem additive_zero {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y) :
    f 0 = 0 := by
  have h := hadd 0 0
  simp at h
  linarith

/-- An additive function satisfies f(n * x) = n * f(x) for natural n. -/
theorem additive_nsmul {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y)
    (n : ℕ) (x : ℝ) : f (n * x) = n * f x := by
  induction n with
  | zero => simp [additive_zero hadd]
  | succ n ih =>
    have h1 : f ((n + 1 : ℕ) * x) = f (n * x + x) := by
      congr 1; push_cast; ring
    have h2 : ((n + 1 : ℕ) : ℝ) * f x = n * f x + f x := by push_cast; ring
    rw [h1, hadd, ih, h2]

/-- An additive function satisfies f(-x) = -f(x). -/
theorem additive_neg {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y) (x : ℝ) :
    f (-x) = -f x := by
  have h := hadd x (-x)
  simp [additive_zero hadd] at h
  linarith

/-- An additive function satisfies f(n * x) = n * f(x) for integer n. -/
theorem additive_zsmul {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y)
    (n : ℤ) (x : ℝ) : f (n * x) = n * f x := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact additive_nsmul hadd n x
  | negSucc n =>
    have key : f (-((n + 1 : ℕ) * x)) = -((n + 1 : ℕ) : ℝ) * f x := by
      rw [additive_neg hadd, additive_nsmul hadd]
      ring
    convert key using 1 <;> simp [Int.negSucc_eq]; ring_nf

/-- An additive function satisfies f(q * x) = q * f(x) for rational q. -/
theorem additive_qsmul {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y)
    (q : ℚ) (x : ℝ) : f (q * x) = q * f x := by
  have hden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hx : (q.den : ℝ) * (x / q.den) = x := mul_div_cancel₀ x hden
  have hfx : f (x / q.den) = f x / q.den := by
    have hmul : (q.den : ℝ) * f (x / q.den) = f x := by
      calc (q.den : ℝ) * f (x / q.den) = f (q.den * (x / q.den)) := (additive_nsmul hadd q.den _).symm
        _ = f x := by rw [hx]
    field_simp at hmul ⊢
    linarith
  have hq : (q : ℝ) = q.num / q.den := by simp [Rat.cast_def]
  calc f (q * x)
      = f (q.num * (x / q.den)) := by congr 1; rw [hq]; field_simp
      _ = q.num * f (x / q.den) := additive_zsmul hadd q.num _
      _ = q.num * (f x / q.den) := by rw [hfx]
      _ = q * f x := by rw [hq]; field_simp

/-! ## Monotone additive functions are linear -/

/-- **Key Theorem:** A monotone additive function ℝ → ℝ is linear.

This refutes K&S's claim that discontinuous re-grading is viable.
Any re-grading that preserves both:
1. The sum rule (additivity)
2. Monotonicity (order-preservation)

must be of the form Θ(x) = c * x for some constant c, hence continuous.
-/
theorem monotone_additive_is_linear {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmono : Monotone f) :
    ∀ x, f x = f 1 * x := by
  intro x
  -- We show f(x) = f(1) * x by squeezing between rationals
  -- For any ε > 0, find rationals q₁ < x < q₂ with q₂ - q₁ < ε
  -- Then f(q₁) ≤ f(x) ≤ f(q₂) and f(qᵢ) = qᵢ * f(1)
  -- Taking ε → 0, we get f(x) = f(1) * x

  -- We have f(q) = q * f(1) for all rationals
  have hfq : ∀ q : ℚ, f q = q * f 1 := by
    intro q
    calc f q = f (q * 1) := by ring_nf
      _ = q * f 1 := additive_qsmul hadd q 1

  by_cases hf1 : f 1 = 0
  · -- If f(1) = 0, then f(q) = 0 for all rationals, hence f = 0 by monotonicity
    have hfq_zero : ∀ q : ℚ, f q = 0 := by
      intro q
      simp [hfq, hf1]
    -- For any x, squeeze between rationals
    have hfx_nonneg : ∀ y : ℝ, 0 ≤ f y := by
      intro y
      obtain ⟨q, hq⟩ := exists_rat_lt y
      have hle : f q ≤ f y := hmono (le_of_lt hq)
      simp [hfq_zero] at hle
      exact hle
    have hfx_nonpos : ∀ y : ℝ, f y ≤ 0 := by
      intro y
      obtain ⟨q, hq⟩ := exists_rat_gt y
      have hle : f y ≤ f q := hmono (le_of_lt hq)
      simp [hfq_zero] at hle
      exact hle
    have hfx : f x = 0 := le_antisymm (hfx_nonpos x) (hfx_nonneg x)
    simp [hfx, hf1]
  · -- f(1) ≠ 0 case: use density of rationals and squeezing
    -- First, since f is monotone and f(0) = 0, we have f(1) ≥ 0
    have hf1_nonneg : 0 ≤ f 1 := by
      have h0 : f 0 = 0 := additive_zero hadd
      have h01 : f 0 ≤ f 1 := hmono (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    have hf1_pos : 0 < f 1 := lt_of_le_of_ne hf1_nonneg (Ne.symm hf1)
    -- f(1) > 0 case
    apply le_antisymm
    · -- f(x) ≤ f(1) * x
      by_contra h
      push_neg at h
      -- f(x) > f(1) * x, derive contradiction (h says f 1 * x < f x)
      set gap := (f x - f 1 * x) / f 1 with hgap_def
      have hgap_pos : 0 < gap := by
        rw [hgap_def]
        apply div_pos <;> linarith
      obtain ⟨q, hxq, hqbound⟩ := exists_rat_btwn (show x < x + gap by linarith)
      have hfq_lt : f 1 * q < f x := by
        have hq_bound : (q : ℝ) < x + gap := hqbound
        calc f 1 * q < f 1 * (x + gap) := by nlinarith
          _ = f 1 * x + f 1 * gap := by ring
          _ = f 1 * x + (f x - f 1 * x) := by simp [hgap_def, mul_div_cancel₀ _ (ne_of_gt hf1_pos)]
          _ = f x := by ring
      have hfq_ge : f x ≤ f q := hmono (le_of_lt hxq)
      rw [hfq] at hfq_ge
      have hcomm : (q : ℝ) * f 1 = f 1 * q := mul_comm _ _
      linarith
    · -- f(1) * x ≤ f(x)
      by_contra h
      push_neg at h
      -- f(1) * x > f(x), derive contradiction (h says f x < f 1 * x)
      set gap := (f 1 * x - f x) / f 1 with hgap_def
      have hgap_pos : 0 < gap := by
        rw [hgap_def]
        apply div_pos <;> linarith
      obtain ⟨q, hqbound, hqx⟩ := exists_rat_btwn (show x - gap < x by linarith)
      have hfq_gt : f x < f 1 * q := by
        have hq_bound : x - gap < (q : ℝ) := hqbound
        calc f x = f 1 * x - (f 1 * x - f x) := by ring
          _ = f 1 * x - f 1 * gap := by simp [hgap_def, mul_div_cancel₀ _ (ne_of_gt hf1_pos)]
          _ = f 1 * (x - gap) := by ring
          _ < f 1 * q := by nlinarith
      have hfq_le : f q ≤ f x := hmono (le_of_lt hqx)
      rw [hfq] at hfq_le
      have hcomm : (q : ℝ) * f 1 = f 1 * q := mul_comm _ _
      linarith

/-- Corollary: A monotone additive bijection ℝ → ℝ is a positive scalar multiple. -/
theorem monotone_additive_bijection_is_pos_linear {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmono : StrictMono f) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, f x = c * x := by
  use f 1
  constructor
  · -- f(1) > 0 because f is strictly increasing and f(0) = 0
    have h0 : f 0 = 0 := additive_zero hadd
    have h1 : f 0 < f 1 := hmono (by norm_num : (0 : ℝ) < 1)
    linarith
  · exact monotone_additive_is_linear hadd hmono.monotone

/-- **Main Result:** Any "re-grading" Θ that preserves both monotonicity and
    the sum rule must be continuous (in fact, linear).

    This directly contradicts K&S's claim that "there can be no requirement of
    continuity" for valuations satisfying the sum rule.
-/
theorem regrade_preserving_sum_rule_is_continuous {Θ : ℝ → ℝ}
    (hΘ_add : ∀ x y, Θ (x + y) = Θ x + Θ y)  -- preserves sum rule
    (hΘ_mono : Monotone Θ) :                   -- preserves order
    Continuous Θ := by
  -- Θ is linear, hence continuous
  have hlin := monotone_additive_is_linear hΘ_add hΘ_mono
  -- Θ(x) = Θ(1) * x is continuous
  have heq : Θ = fun x => Θ 1 * x := funext hlin
  rw [heq]
  exact continuous_const.mul continuous_id

end Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples
