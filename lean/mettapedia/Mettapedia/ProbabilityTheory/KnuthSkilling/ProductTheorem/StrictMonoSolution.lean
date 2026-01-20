import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.Archimedean
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.FunctionalEquation

/-!
# Appendix B: Solving the Product Equation from `StrictMono` (No Extra Topology Assumed)

This module packages the **Lean-friendly Appendix B route** for the functional equation

`Ψ(τ + ξ) + Ψ(τ + η) = Ψ(τ + ζ(ξ,η))`

under the hypotheses K&S actually have after Appendix A:

- positivity `∀ x, 0 < Ψ x`
- strict monotonicity `StrictMono Ψ`

The key step is:

`ProductEquation + StrictMono + Positivity ⟹ Continuous Ψ`

so we can apply the complete solver in
`Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.FunctionalEquation`.

This file exists so downstream modules can use the *actual proof* without importing the
unrelated “golden ratio / Diophantine approximation” machinery from the historical Appendix B
proof route.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem

open Classical
open Set

/-! ## Continuity from `ProductEquation` + `StrictMono` + Positivity -/

/-- **Continuity from ProductEquation + StrictMono + Positivity**.

A strictly monotone positive function satisfying the `ProductEquation` is continuous.

Proof idea:
- From the product equation (at `τ = 0`), `range Ψ` is closed under addition.
- From the “doubling” consequence, `range Ψ` contains all dyadic multiples of `Ψ 0`.
- Dyadics are dense in `(0,∞)`, so `range Ψ` is dense in `(0,∞)`.
- A strictly monotone function cannot have a jump discontinuity with dense range. -/
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
    intro ha0
    have h := hShift 0
    simp only [ha0, add_zero] at h
    linarith [hPos 0]
  have ha_pos : 0 < a := by
    by_contra h
    push_neg at h
    rcases h.lt_or_eq with ha_neg | ha_zero
    · have h1 : Ψ a < Ψ 0 := hStrictMono ha_neg
      have h2 : Ψ a = 2 * Ψ 0 := by
        simpa using hShift 0
      linarith [hPos 0]
    · exact ha_ne ha_zero

  let C := Ψ 0
  have hC_pos : 0 < C := hPos 0

  -- Step 2: Range is closed under addition (from ProductEquation at τ = 0)
  have hRangeAdd : ∀ u v : ℝ, u ∈ Set.range Ψ → v ∈ Set.range Ψ → (u + v) ∈ Set.range Ψ := by
    intro u v ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨ζ x y, ?_⟩
    have := hProd 0 x y
    simp only [zero_add] at this
    rw [hx, hy] at this
    exact this.symm

  -- Step 3: Doubling gives `C / 2^k` in range for all `k`.
  have hHalving_eq : ∀ k : ℕ, Ψ (-(k : ℤ) * a) = C / 2 ^ k := by
    intro k
    induction k with
    | zero =>
      simp [C]
    | succ n ih =>
      have h1 : (-(↑(n + 1) : ℤ) : ℝ) * a = -(n : ℤ) * a - a := by
        push_cast
        ring
      rw [h1]
      have h2 : Ψ (-(n : ℤ) * a - a + a) = 2 * Ψ (-(n : ℤ) * a - a) := hShift _
      simp only [sub_add_cancel] at h2
      have h3 : Ψ (-(n : ℤ) * a - a) = Ψ (-(n : ℤ) * a) / 2 := by
        linarith
      rw [h3, ih]
      have hne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hne]
      ring
  have hHalving : ∀ k : ℕ, C / (2 : ℝ) ^ k ∈ Set.range Ψ := by
    intro k
    exact ⟨-(k : ℤ) * a, hHalving_eq k⟩

  -- Step 4: Additive closure gives `mC/2^k` in range for all `m ≥ 1, k`.
  have hDyadicInRange : ∀ m k : ℕ, 1 ≤ m → (m : ℝ) * C / (2 : ℝ) ^ k ∈ Set.range Ψ := by
    intro m k hm
    induction m with
    | zero =>
      omega
    | succ n ih =>
      have heq :
          ((n + 1 : ℕ) : ℝ) * C / (2 : ℝ) ^ k =
            (n : ℝ) * C / (2 : ℝ) ^ k + C / (2 : ℝ) ^ k := by
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

  -- Step 5: Density in `(0,∞)`.
  have hDensityInPos : ∀ y : ℝ, 0 < y → ∀ ε > 0, ∃ v ∈ Set.range Ψ, |v - y| < ε := by
    intro y hy ε hε
    have hmin_pos : 0 < min ε y := lt_min hε hy
    have hquot_pos : 0 < C / min ε y := div_pos hC_pos hmin_pos
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (C / min ε y) / Real.log 2)
    let k := n
    have hk_large' : (2 : ℝ) ^ k > C / min ε y := by
      have hlog_k : Real.log (C / min ε y) / Real.log 2 < k := hn
      have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
      rw [gt_iff_lt, ← Real.log_lt_log_iff hquot_pos h2k_pos]
      calc
        Real.log (C / min ε y)
            = Real.log (C / min ε y) / Real.log 2 * Real.log 2 := by
                field_simp [ne_of_gt hlog2_pos]
        _ < k * Real.log 2 := by
              exact mul_lt_mul_of_pos_right hlog_k hlog2_pos
        _ = Real.log (2 ^ k) := by
              rw [Real.log_pow]
    have hk_large : C / (2 : ℝ) ^ k < min ε y := by
      have h2k : (2 : ℝ) ^ k > C / min ε y := hk_large'
      calc
        C / (2 : ℝ) ^ k < C / (C / min ε y) := by
              apply div_lt_div_of_pos_left hC_pos
              · exact div_pos hC_pos hmin_pos
              · exact h2k
        _ = min ε y := by
              field_simp [ne_of_gt hmin_pos]
    -- Choose m = ⌈y * 2^k / C⌉
    let r := y * (2 : ℝ) ^ k / C
    have hr_pos : 0 < r := div_pos (mul_pos hy (pow_pos (by norm_num) k)) hC_pos
    let m := Nat.ceil r
    have hm_ge_1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hr_pos).ne'
    refine ⟨(m : ℝ) * C / (2 : ℝ) ^ k, hDyadicInRange m k hm_ge_1, ?_⟩
    -- Show `|(mC/2^k) - y| < ε`.
    have hceil_bound : r ≤ m := Nat.le_ceil r
    have hne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    rw [abs_lt]
    constructor
    · have h1 : y ≤ (m : ℝ) * C / (2 : ℝ) ^ k := by
        calc
          y = r * C / (2 : ℝ) ^ k := by
                simp only [r]
                field_simp [ne_of_gt hC_pos, hne]
          _ ≤ (m : ℝ) * C / (2 : ℝ) ^ k := by
                apply div_le_div_of_nonneg_right _ (le_of_lt h2k_pos)
                apply mul_le_mul_of_nonneg_right hceil_bound
                exact le_of_lt hC_pos
      linarith
    · have h2 : (m : ℝ) * C / (2 : ℝ) ^ k < y + C / (2 : ℝ) ^ k := by
        have h3 : (m : ℝ) < r + 1 := by
          -- `Nat.ceil_lt_add_one` gives `m < r+1`.
          have h := Nat.ceil_lt_add_one (le_of_lt hr_pos)
          linarith
        calc
          (m : ℝ) * C / (2 : ℝ) ^ k
              < (r + 1) * C / (2 : ℝ) ^ k := by
                    apply div_lt_div_of_pos_right _ h2k_pos
                    apply mul_lt_mul_of_pos_right h3 hC_pos
          _ = y + C / (2 : ℝ) ^ k := by
                simp only [r]
                field_simp [ne_of_gt hC_pos, hne]
      have hstep : C / (2 : ℝ) ^ k < ε := lt_of_lt_of_le hk_large (min_le_left _ _)
      linarith

  -- Step 6: Dense range in `(0,∞)` + strict mono → continuous.
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let y₀ := Ψ x₀
  have hy₀_pos : 0 < y₀ := hPos x₀

  -- Find `v₂` in range with `y₀ < v₂ < y₀ + ε`.
  obtain ⟨v₂, hv₂_range, hv₂_close⟩ :=
    hDensityInPos (y₀ + ε / 2) (by linarith) (ε / 2) (by linarith)
  have hv₂_above : y₀ < v₂ := by
    have : |v₂ - (y₀ + ε / 2)| < ε / 2 := hv₂_close
    rw [abs_lt] at this
    linarith
  have hv₂_bound : v₂ < y₀ + ε := by
    have : |v₂ - (y₀ + ε / 2)| < ε / 2 := hv₂_close
    rw [abs_lt] at this
    linarith

  -- Find `v₁` below `y₀` when possible, otherwise use positivity.
  by_cases hcase : y₀ - ε / 2 > 0
  · obtain ⟨v₁, hv₁_range, hv₁_close⟩ :=
      hDensityInPos (y₀ - ε / 2) hcase (ε / 2) (by linarith)
    have hv₁_below : v₁ < y₀ := by
      have : |v₁ - (y₀ - ε / 2)| < ε / 2 := hv₁_close
      rw [abs_lt] at this
      linarith
    have hv₁_bound : y₀ - ε < v₁ := by
      have : |v₁ - (y₀ - ε / 2)| < ε / 2 := hv₁_close
      rw [abs_lt] at this
      linarith

    obtain ⟨x₁, hx₁⟩ := hv₁_range
    obtain ⟨x₂, hx₂⟩ := hv₂_range

    have hx₁_lt : x₁ < x₀ := by
      by_contra h
      push_neg at h
      have : Ψ x₁ ≥ Ψ x₀ := by
        rcases h.lt_or_eq with hlt | heq
        · exact le_of_lt (hStrictMono hlt)
        · simp [heq]
      rw [hx₁] at this
      linarith
    have hx₂_gt : x₀ < x₂ := by
      by_contra h
      push_neg at h
      have : Ψ x₂ ≤ Ψ x₀ := by
        rcases h.lt_or_eq with hlt | heq
        · exact le_of_lt (hStrictMono hlt)
        · simp [heq]
      rw [hx₂] at this
      linarith

    refine ⟨min (x₀ - x₁) (x₂ - x₀), lt_min (by linarith) (by linarith), ?_⟩
    intro x hx
    rw [Real.dist_eq] at hx ⊢
    have hx_in : x₁ < x ∧ x < x₂ := by
      constructor
      · have : |x - x₀| < x₀ - x₁ := lt_of_lt_of_le hx (min_le_left _ _)
        rw [abs_lt] at this
        linarith
      · have : |x - x₀| < x₂ - x₀ := lt_of_lt_of_le hx (min_le_right _ _)
        rw [abs_lt] at this
        linarith
    have hΨx_bounds : v₁ < Ψ x ∧ Ψ x < v₂ := by
      constructor
      · rw [← hx₁]
        exact hStrictMono hx_in.1
      · rw [← hx₂]
        exact hStrictMono hx_in.2
    rw [abs_lt]
    constructor <;> linarith
  · push_neg at hcase
    obtain ⟨x₂, hx₂⟩ := hv₂_range
    have hx₂_gt : x₀ < x₂ := by
      by_contra h
      push_neg at h
      have : Ψ x₂ ≤ Ψ x₀ := by
        rcases h.lt_or_eq with hlt | heq
        · exact le_of_lt (hStrictMono hlt)
        · simp [heq]
      rw [hx₂] at this
      linarith
    refine ⟨min 1 (x₂ - x₀), lt_min one_pos (by linarith), ?_⟩
    intro x hx
    rw [Real.dist_eq] at hx ⊢
    have hx_upper : x < x₂ := by
      have : |x - x₀| < x₂ - x₀ := lt_of_lt_of_le hx (min_le_right _ _)
      rw [abs_lt] at this
      linarith
    have hΨx_upper : Ψ x < v₂ := by
      -- `StrictMono` on ℝ gives the strict inequality for `x < x₂`.
      rw [← hx₂]
      exact hStrictMono hx_upper
    have hΨx_lower : Ψ x > y₀ - ε := by
      have hΨx_pos : 0 < Ψ x := hPos x
      have : y₀ - ε < 0 := by linarith
      linarith
    rw [abs_lt]
    constructor <;> linarith

/-! ## Exponentiality (Appendix B) -/

/-- Appendix B exponential solution under `StrictMono` + positivity, with continuity *derived*. -/
theorem productEquation_solution_of_strictMono
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hStrictMono : StrictMono Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  have hCont : Continuous Ψ :=
    productEquation_strictMono_pos_continuous Ψ ζ hProd hPos hStrictMono
  exact productEquation_solution_of_continuous_strictMono hProd hPos hCont hStrictMono

/-- Appendix B exponential solution under `StrictAnti` + positivity. -/
theorem productEquation_solution_of_strictAnti
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
  obtain ⟨C', A', hC'_pos, hΨ'_eq⟩ :=
    productEquation_solution_of_strictMono Ψ' ζ' hProd' hPos' hStrictMono'
  refine ⟨C', -A', hC'_pos, ?_⟩
  intro x
  have := hΨ'_eq (-x)
  simp only [Ψ', neg_neg] at this
  simp only [mul_neg, neg_mul] at this ⊢
  exact this

end Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem
