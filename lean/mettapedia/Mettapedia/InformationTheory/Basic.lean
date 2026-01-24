import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.VecNotation

/-!
# Information Theory: Basic Definitions

This file defines the core types and functions for information theory:
- `ProbVec n`: Finite probability vectors (distributions over `Fin n`)
- `shannonEntropy`: Shannon entropy H(p) = -Σ pᵢ log pᵢ

## Main Definitions

* `ProbVec n` - A probability distribution over n outcomes
* `shannonEntropy` - Shannon entropy of a finite distribution
* `uniformDist` - The uniform distribution over n outcomes

## References

* Shannon, C.E. "A Mathematical Theory of Communication" (1948)
* Faddeev, D.K. "On the concept of entropy of a finite probabilistic scheme" (1956)
-/

namespace Mettapedia.InformationTheory

open Finset Real

/-- A probability distribution on a finite type `α`: a function `α → ℝ` with non-negative values
summing to `1`. -/
abbrev Prob (α : Type*) [Fintype α] := ↥(stdSimplex ℝ α)

/-- A probability vector over `n` outcomes: a function `Fin n → ℝ` with
    non-negative values summing to 1.

    This is `↥(stdSimplex ℝ (Fin n))` - the subtype of the standard simplex. -/
abbrev ProbVec (n : ℕ) := Prob (Fin n)

namespace ProbVec

variable {n : ℕ}

/-- Each component is non-negative -/
theorem nonneg (p : ProbVec n) (i : Fin n) : 0 ≤ p.1 i := p.2.1 i

/-- Components sum to 1 -/
theorem sum_eq_one (p : ProbVec n) : ∑ i, p.1 i = 1 := p.2.2

/-- Each component is at most 1 -/
theorem le_one (p : ProbVec n) (i : Fin n) : p.1 i ≤ 1 := by
  have h := p.sum_eq_one
  calc p.1 i ≤ ∑ j, p.1 j := Finset.single_le_sum (fun j _ => p.nonneg j) (mem_univ i)
    _ = 1 := h

/-- A probability vector is in [0,1]^n -/
theorem mem_Icc (p : ProbVec n) (i : Fin n) : p.1 i ∈ Set.Icc 0 1 :=
  ⟨p.nonneg i, p.le_one i⟩

end ProbVec

/-! ## Shannon Entropy -/

/-- **Shannon entropy** of a finite probability distribution.

    H(p) = -Σᵢ pᵢ log pᵢ = Σᵢ negMulLog(pᵢ)

    Using mathlib's `negMulLog x = -x * log x` which handles the convention
    that 0 * log 0 = 0 (since negMulLog 0 = 0). -/
noncomputable def shannonEntropy {n : ℕ} (p : ProbVec n) : ℝ :=
  ∑ i : Fin n, negMulLog (p.1 i)

/-- Alternative form: H(p) = -Σᵢ pᵢ log pᵢ -/
theorem shannonEntropy_eq_neg_sum {n : ℕ} (p : ProbVec n) :
    shannonEntropy p = -∑ i : Fin n, p.1 i * log (p.1 i) := by
  simp only [shannonEntropy, negMulLog, neg_mul]
  rw [← Finset.sum_neg_distrib]

/-! ## Uniform Distribution -/

/-- The uniform distribution over n outcomes: each has probability 1/n -/
noncomputable def uniformDist (n : ℕ) (hn : 0 < n) : ProbVec n :=
  ⟨fun _ => 1 / n, by
    constructor
    · intro _; positivity
    · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      field_simp⟩

theorem uniformDist_apply (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (uniformDist n hn).1 i = 1 / n := rfl

/-! ## Binary Distribution -/

/-- Binary distribution (p, 1-p) for p ∈ [0,1] -/
noncomputable def binaryDist (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ProbVec 2 :=
  ⟨![p, 1 - p], by
    constructor
    · intro i
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      · exact hp0
      · linarith
    · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]⟩

/-- The fair coin: (1/2, 1/2) -/
noncomputable def binaryUniform : ProbVec 2 :=
  binaryDist (1/2) (by norm_num) (by norm_num)

theorem binaryUniform_apply_zero : binaryUniform.1 0 = 1/2 := by
  simp only [binaryUniform, binaryDist, Matrix.cons_val_zero]

theorem binaryUniform_apply_one : binaryUniform.1 1 = 1/2 := by
  simp only [binaryUniform, binaryDist, Matrix.cons_val_one]
  norm_num

/-! ## Point Mass Distribution -/

/-- Point mass at index i: probability 1 at i, 0 elsewhere -/
noncomputable def pointMass {n : ℕ} (i : Fin n) : ProbVec n :=
  ⟨fun j => if j = i then 1 else 0, by
    constructor
    · intro j; by_cases hj : j = i <;> simp [hj]
    · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]⟩

theorem pointMass_apply_eq {n : ℕ} (i : Fin n) : (pointMass i).1 i = 1 := by
  simp only [pointMass, ↓reduceIte]

theorem pointMass_apply_ne {n : ℕ} (i j : Fin n) (h : j ≠ i) : (pointMass i).1 j = 0 := by
  simp only [pointMass, h, ↓reduceIte]

/-! ## Permutation of Probability Vectors -/

/-- Permute a probability vector by a permutation of indices -/
noncomputable def permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbVec n) : ProbVec n :=
  ⟨fun i => p.1 (σ⁻¹ i), by
    constructor
    · intro i; exact p.nonneg (σ⁻¹ i)
    · calc ∑ i, p.1 (σ⁻¹ i) = ∑ i, p.1 i := Equiv.sum_comp σ⁻¹ (fun i => p.1 i)
        _ = 1 := p.sum_eq_one⟩

@[simp]
theorem permute_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbVec n) (i : Fin n) :
    (permute σ p).1 i = p.1 (σ⁻¹ i) := rfl

/-! ## Grouping Operations (for Faddeev axiom)

These will be defined more carefully when needed for the Faddeev axioms.
For now, we provide simplified versions. -/

/-- Binary distribution normalization: given (a, b) with a + b > 0,
    return (a/(a+b), b/(a+b)). -/
noncomputable def normalizeBinary (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) : ProbVec 2 :=
  ⟨![a / (a + b), b / (a + b)], by
    constructor
    · intro i
      fin_cases i
      · exact div_nonneg ha (le_of_lt hab)
      · exact div_nonneg hb (le_of_lt hab)
    · simp [Fin.sum_univ_two]
      have hs : a + b ≠ 0 := ne_of_gt hab
      field_simp⟩

/-- Group the first two probabilities of a distribution.

`(p₀, p₁, p₂, ..., pₙ₊₁) ↦ (p₀ + p₁, p₂, ..., pₙ₊₁)`.

This helper is convenient for both Faddeev-style recursivity and Shannon–Khinchin strong additivity.
-/
noncomputable def groupFirstTwo {n : ℕ} (p : ProbVec (n + 2))
    (_h : 0 < p.1 0 + p.1 1) : ProbVec (n + 1) :=
  ⟨fun i =>
      if h0 : i.1 = 0 then p.1 0 + p.1 1
      else p.1 ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩,
    by
      constructor
      · intro i
        by_cases h0 : i.1 = 0
        · simpa [h0] using add_nonneg (p.2.1 0) (p.2.1 1)
        ·
          simpa [h0] using
            (p.2.1
              ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩)
      ·
        -- Sum = (p₀ + p₁) + Σᵢ₌₂ pᵢ = Σᵢ pᵢ = 1.
        have hsum := p.2.2
        -- Rewrite the original sum as `p₀ + p₁ + rest`.
        -- `hsum : p.1 0 + (p.1 1 + ∑ i : Fin n, p.1 i.succ.succ) = 1`.
        -- (We use `Fin.sum_univ_succ` twice.)
        have hsum' :
            p.1 0 + (p.1 1 + ∑ i : Fin n, p.1 i.succ.succ) = 1 := by
          simpa [Fin.sum_univ_succ, add_assoc] using hsum
        -- Compute the grouped sum and identify it with the left side of `hsum'`.
        have hgrouped :
            (∑ i : Fin (n + 1),
                (if h0 : i.1 = 0 then p.1 0 + p.1 1
                 else p.1 ⟨i.1 + 1, by
                   exact Nat.succ_lt_succ i.isLt⟩))
              =
            p.1 0 + (p.1 1 + ∑ i : Fin n, p.1 i.succ.succ) := by
          classical
          -- Decompose the sum into the `0`-term and the rest.
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ x : Fin n,
                  p.1 ⟨x.1 + 2, by
                    -- `x.1 < n` implies `x.1 + 2 < n + 2`.
                    exact Nat.succ_lt_succ (Nat.succ_lt_succ x.isLt)⟩)
                =
              ∑ i : Fin n, p.1 i.succ.succ := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rfl
          -- The `0` term is `(p₀ + p₁)`, and the rest shifts indices by 2.
          simp [add_assoc, htail]
        -- Conclude by rewriting via `hgrouped`.
        calc
          (∑ i : Fin (n + 1),
              (if h0 : i.1 = 0 then p.1 0 + p.1 1
               else p.1 ⟨i.1 + 1, by
                 exact Nat.succ_lt_succ i.isLt⟩))
              = p.1 0 + (p.1 1 + ∑ i : Fin n, p.1 i.succ.succ) := hgrouped
          _ = 1 := hsum'⟩

/-! ## Ternary Distribution -/

/-- Ternary distribution (a, b, c) for a, b, c ≥ 0 with a + b + c = 1 -/
noncomputable def ternaryDist (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) : ProbVec 3 :=
  ⟨![a, b, c], by
    constructor
    · intro i
      fin_cases i <;> simp
      · exact ha
      · exact hb
      · exact hc
    · simp [Fin.sum_univ_three]
      exact hsum⟩

/-- Expand a distribution by appending a zero:
    (p₀, ..., pₙ₋₁) ↦ (p₀, ..., pₙ₋₁, 0)

    This is for Shannon-Khinchin expansibility axiom. -/
noncomputable def expandZero {n : ℕ} (p : ProbVec n) : ProbVec (n + 1) :=
  ⟨Fin.snoc p.1 0, by
    constructor
    · intro i
      simp only [Fin.snoc]
      split_ifs with h
      · exact p.nonneg ⟨i, h⟩
      · norm_num
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, add_zero]
      exact p.sum_eq_one⟩

end Mettapedia.InformationTheory
