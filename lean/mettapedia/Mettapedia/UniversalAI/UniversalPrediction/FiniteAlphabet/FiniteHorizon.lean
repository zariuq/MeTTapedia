import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Finite-horizon relative entropy (Finite Alphabet)

This file is the finite-alphabet analogue of `UniversalPrediction/FiniteHorizon.lean`.

We avoid full measure theory on `α^Nat` by using the induced finite-horizon `PMF (Fin n → α)`
coming from `PrefixMeasure.prefixPMF` and defining expectations/relative entropy as finite sums.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

namespace FiniteHorizon

variable {α : Type*} [Fintype α]

/-- Expectation of a real-valued function on length-`n` strings under a prefix measure `μ`. -/
noncomputable def expect (μ : PrefixMeasure α) (n : ℕ) (f : (Fin n → α) → Real) : Real :=
  ∑ x : Fin n → α, (prefixPMF μ n x).toReal * f x

/-- Expectation of a real-valued function of the *prefix list* `x : List α` of length `n`. -/
noncomputable def expectPrefix (μ : PrefixMeasure α) (n : ℕ) (f : Word α → Real) : Real :=
  ∑ x : Fin n → α, (prefixPMF μ n x).toReal * f (List.ofFn x)

theorem sum_toReal_eq_one {β : Type*} [Fintype β] (p : PMF β) :
    (∑ b : β, (p b).toReal) = 1 := by
  classical
  have hsum : (∑ b : β, p b) = 1 := by
    simpa [tsum_fintype] using (p.tsum_coe : (∑' b : β, p b) = 1)
  have htoReal :
      ENNReal.toReal (∑ b : β, p b) = ∑ b : β, (p b).toReal := by
    simpa using
      (ENNReal.toReal_sum (s := (Finset.univ : Finset β)) (f := fun b => p b) (by
        intro b hb
        simpa using p.apply_ne_top b))
  calc
    (∑ b : β, (p b).toReal) = ENNReal.toReal (∑ b : β, p b) := by
      simpa using htoReal.symm
    _ = ENNReal.toReal (1 : ENNReal) := by simp [hsum]
    _ = 1 := by simp

theorem sum_prefixPMF_toReal (μ : PrefixMeasure α) (n : ℕ) :
    (∑ x : Fin n → α, (prefixPMF μ n x).toReal) = 1 :=
  sum_toReal_eq_one (p := prefixPMF μ n)

/-- A semimeasure dominates a probability measure only with constant `c ≤ 1`. -/
theorem dominates_const_le_one {μ : PrefixMeasure α} {ξ : Semimeasure α} {c : ENNReal}
    (hdom : Dominates ξ μ c) : c ≤ 1 := by
  have hle : c ≤ ξ ([] : Word α) := by
    simpa [μ.root_eq_one', mul_one] using hdom ([] : Word α)
  exact hle.trans ((Semimeasure.le_one ξ) ([] : Word α))

/-- Pointwise log-likelihood ratio bound from dominance. -/
theorem log_ratio_le_log_inv_of_dominates (μ : PrefixMeasure α) (ξ : Semimeasure α) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (x : Word α) :
    Real.log ((μ x).toReal / (ξ x).toReal) ≤ Real.log (1 / c.toReal) := by
  have hc1 : c ≤ 1 := dominates_const_le_one (μ := μ) (ξ := ξ) hdom
  have hcTop : c ≠ (⊤ : ENNReal) := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hcTop
  have hcReal_le_one : c.toReal ≤ 1 := by
    have := ENNReal.toReal_mono (hb := ENNReal.one_ne_top) hc1
    simpa using this
  have hone_le : (1 : Real) ≤ 1 / c.toReal := by
    have := one_div_le_one_div_of_le hcpos hcReal_le_one
    simpa using this
  by_cases hμ0 : μ x = 0
  · have : (0 : Real) ≤ Real.log (1 / c.toReal) := Real.log_nonneg hone_le
    simpa [hμ0] using this
  · have hξ0 : ξ x ≠ 0 := by
      intro hξ0
      have : μ x = 0 := Dominates.eq_zero_of_eq_zero (h := hdom) hc0 x hξ0
      exact hμ0 this
    have hμTop : μ x ≠ (⊤ : ENNReal) := by
      have hle : μ.toSemimeasure x ≤ 1 := Semimeasure.le_one (μ := μ.toSemimeasure) x
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hξTop : ξ x ≠ (⊤ : ENNReal) := Semimeasure.ne_top ξ x
    have hμpos : 0 < (μ x).toReal := ENNReal.toReal_pos hμ0 hμTop
    have hξpos : 0 < (ξ x).toReal := ENNReal.toReal_pos hξ0 hξTop
    have hratio_pos : 0 < (μ x).toReal / (ξ x).toReal := div_pos hμpos hξpos
    have hdomReal : c.toReal * (μ x).toReal ≤ (ξ x).toReal := by
      have h := ENNReal.toReal_mono (hb := hξTop) (hdom x)
      simpa [ENNReal.toReal_mul, mul_assoc] using h
    have hμ_le : (μ x).toReal ≤ (1 / c.toReal) * (ξ x).toReal := by
      have hmul : (μ x).toReal * c.toReal ≤ (ξ x).toReal := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hdomReal
      have hdiv : (μ x).toReal ≤ (ξ x).toReal / c.toReal := (le_div_iff₀ hcpos).2 hmul
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hratio_le : (μ x).toReal / (ξ x).toReal ≤ 1 / c.toReal :=
      (div_le_iff₀ hξpos).2 hμ_le
    exact Real.log_le_log hratio_pos hratio_le

/-- Finite-horizon prefix relative entropy `D_n(μ || ξ)`. -/
noncomputable def relEntropy (μ : PrefixMeasure α) (ξ : Semimeasure α) (n : ℕ) : Real :=
  ∑ x : Fin n → α,
    (prefixPMF μ n x).toReal * Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal)

/-- Dominance implies the standard finite-horizon KL bound `D_n(μ||ξ) ≤ log(1/c)`. -/
theorem relEntropy_le_log_inv_of_dominates (μ : PrefixMeasure α) (ξ : Semimeasure α) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ) :
    relEntropy μ ξ n ≤ Real.log (1 / c.toReal) := by
  classical
  have hterm : ∀ x : Fin n → α,
      (prefixPMF μ n x).toReal * Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal)
        ≤ (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := by
    intro x
    have hlog :=
      log_ratio_le_log_inv_of_dominates (μ := μ) (ξ := ξ) (hdom := hdom) (hc0 := hc0)
        (x := List.ofFn x)
    have hw_nonneg : 0 ≤ (prefixPMF μ n x).toReal := ENNReal.toReal_nonneg
    exact mul_le_mul_of_nonneg_left hlog hw_nonneg
  have hsum :
      (∑ x : Fin n → α,
            (prefixPMF μ n x).toReal *
              Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal)) ≤
          ∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → α))) (fun x hx => hterm x))
  have hweights : (∑ x : Fin n → α, (prefixPMF μ n x).toReal) = 1 :=
    sum_prefixPMF_toReal (μ := μ) (n := n)
  calc
    relEntropy μ ξ n
        = ∑ x : Fin n → α,
            (prefixPMF μ n x).toReal *
              Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal) := by
              simp [relEntropy]
    _ ≤ ∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := hsum
    _ = Real.log (1 / c.toReal) := by
          -- Factor out the constant log term and use `∑ weights = 1`.
          have hconst :
              (∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal)) =
                (∑ x : Fin n → α, (prefixPMF μ n x).toReal) * Real.log (1 / c.toReal) := by
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Fin n → α)))
                (f := fun x : Fin n → α => (prefixPMF μ n x).toReal)
                (a := Real.log (1 / c.toReal))).symm
          calc
            (∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal))
                = (∑ x : Fin n → α, (prefixPMF μ n x).toReal) * Real.log (1 / c.toReal) := hconst
            _ = 1 * Real.log (1 / c.toReal) := by simp [hweights]
            _ = Real.log (1 / c.toReal) := by simp

/-- Best-expert style bound: if `ξ` dominates `η` with constant `c`, then `D_n(μ||ξ) ≤ D_n(μ||η) + log(1/c)`. -/
theorem relEntropy_le_add_log_inv_of_dominates_right (μ : PrefixMeasure α) (ξ : Semimeasure α)
    (η : PrefixMeasure α) {c : ENNReal} (hdom : Dominates ξ η c) (hc0 : c ≠ 0)
    (hη0 : ∀ x : Word α, η x ≠ 0) (n : ℕ) :
    relEntropy μ ξ n ≤ relEntropy μ η.toSemimeasure n + Real.log (1 / c.toReal) := by
  classical
  -- Termwise bound: `log(μ/ξ) ≤ log(μ/η) + log(1/c)`.
  have hterm : ∀ x : Fin n → α,
      (prefixPMF μ n x).toReal *
            Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal) ≤
          (prefixPMF μ n x).toReal *
              Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal) +
            (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := by
    intro x
    set s : Word α := List.ofFn x
    by_cases hμ0 : μ s = 0
    · have hpmf0 : prefixPMF μ n x = 0 := by
        simpa [prefixPMF, s, hμ0]
      simp [hpmf0]
    · have hμTop : μ s ≠ (⊤ : ENNReal) := by
        have hle : μ.toSemimeasure s ≤ 1 := Semimeasure.le_one (μ := μ.toSemimeasure) s
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
      have hμpos : 0 < (μ s).toReal := ENNReal.toReal_pos hμ0 hμTop
      have hηTop : η s ≠ (⊤ : ENNReal) := by
        have hle : η.toSemimeasure s ≤ 1 := Semimeasure.le_one (μ := η.toSemimeasure) s
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
      have hηpos : 0 < (η s).toReal := ENNReal.toReal_pos (hη0 s) hηTop
      have hc1 : c ≤ 1 := dominates_const_le_one (μ := η) (ξ := ξ) hdom
      have hcTop : c ≠ (⊤ : ENNReal) := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
      have hξ0 : ξ s ≠ 0 := by
        intro hξ0
        have : η s = 0 := Dominates.eq_zero_of_eq_zero (h := hdom) hc0 s hξ0
        exact (hη0 s) this
      have hξTop : ξ s ≠ (⊤ : ENNReal) := Semimeasure.ne_top ξ s
      have hξpos : 0 < (ξ s).toReal := ENNReal.toReal_pos hξ0 hξTop
      have hdecomp :
          Real.log ((μ s).toReal / (ξ s).toReal) =
            Real.log ((μ s).toReal / (η s).toReal) + Real.log ((η s).toReal / (ξ s).toReal) := by
        have hmul :
            (μ s).toReal / (ξ s).toReal =
              ((μ s).toReal / (η s).toReal) * ((η s).toReal / (ξ s).toReal) := by
          field_simp [ne_of_gt hηpos, ne_of_gt hξpos]
        have hpos1 : 0 < (μ s).toReal / (η s).toReal := div_pos hμpos hηpos
        have hpos2 : 0 < (η s).toReal / (ξ s).toReal := div_pos hηpos hξpos
        calc
          Real.log ((μ s).toReal / (ξ s).toReal)
              = Real.log (((μ s).toReal / (η s).toReal) * ((η s).toReal / (ξ s).toReal)) := by
                  simp [hmul]
          _ = Real.log ((μ s).toReal / (η s).toReal) + Real.log ((η s).toReal / (ξ s).toReal) := by
                  simpa using
                    (Real.log_mul (x := (μ s).toReal / (η s).toReal) (y := (η s).toReal / (ξ s).toReal)
                      (ne_of_gt hpos1) (ne_of_gt hpos2))
      have hlog_ηξ :
          Real.log ((η s).toReal / (ξ s).toReal) ≤ Real.log (1 / c.toReal) := by
        exact log_ratio_le_log_inv_of_dominates (μ := η) (ξ := ξ) (hdom := hdom) (hc0 := hc0)
          (x := s)
      have hlog :
          Real.log ((μ s).toReal / (ξ s).toReal) ≤
            Real.log ((μ s).toReal / (η s).toReal) + Real.log (1 / c.toReal) := by
        linarith [hdecomp, hlog_ηξ]
      have hw_nonneg : 0 ≤ (prefixPMF μ n x).toReal := ENNReal.toReal_nonneg
      calc
        (prefixPMF μ n x).toReal * Real.log ((μ s).toReal / (ξ s).toReal)
            ≤ (prefixPMF μ n x).toReal *
                  (Real.log ((μ s).toReal / (η s).toReal) + Real.log (1 / c.toReal)) := by
                exact mul_le_mul_of_nonneg_left hlog hw_nonneg
        _ =
            (prefixPMF μ n x).toReal * Real.log ((μ s).toReal / (η s).toReal) +
              (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := by
                ring
  have hsum :
      relEntropy μ ξ n ≤
          relEntropy μ η.toSemimeasure n + Real.log (1 / c.toReal) := by
    have hweights : (∑ x : Fin n → α, (prefixPMF μ n x).toReal) = 1 :=
      sum_prefixPMF_toReal (μ := μ) (n := n)
    -- Sum the termwise bounds.
    have hsum' :
        (∑ x : Fin n → α,
              (prefixPMF μ n x).toReal *
                Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal)) ≤
            ∑ x : Fin n → α,
              ((prefixPMF μ n x).toReal *
                    Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal) +
                (prefixPMF μ n x).toReal * Real.log (1 / c.toReal)) := by
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → α))) (fun x hx => hterm x))
    -- Split the RHS sum and use `∑ weights = 1` to collapse the constant term.
    have hsplit :
        (∑ x : Fin n → α,
              ((prefixPMF μ n x).toReal *
                    Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal) +
                (prefixPMF μ n x).toReal * Real.log (1 / c.toReal))) =
          (∑ x : Fin n → α,
                (prefixPMF μ n x).toReal *
                  Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal)) +
            (∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal)) := by
      -- `∑ (A x + B x) = ∑ A x + ∑ B x`.
      simp [Finset.sum_add_distrib]
    have hconst :
        (∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal)) = Real.log (1 / c.toReal) := by
      have hfactor :
          (∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal)) =
            (∑ x : Fin n → α, (prefixPMF μ n x).toReal) * Real.log (1 / c.toReal) := by
        simpa using
          (Finset.sum_mul (s := (Finset.univ : Finset (Fin n → α)))
            (f := fun x : Fin n → α => (prefixPMF μ n x).toReal)
            (a := Real.log (1 / c.toReal))).symm
      calc
        (∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal))
            = (∑ x : Fin n → α, (prefixPMF μ n x).toReal) * Real.log (1 / c.toReal) := hfactor
        _ = 1 * Real.log (1 / c.toReal) := by simp [hweights]
        _ = Real.log (1 / c.toReal) := by simp
    -- Now conclude.
    have hmain :
        relEntropy μ ξ n ≤
          (∑ x : Fin n → α,
                (prefixPMF μ n x).toReal *
                  Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal)) +
            Real.log (1 / c.toReal) := by
      -- Rewrite `relEntropy` and apply the bounds.
      have : relEntropy μ ξ n =
          ∑ x : Fin n → α,
            (prefixPMF μ n x).toReal * Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal) := by
        simp [relEntropy]
      -- Combine.
      calc
        relEntropy μ ξ n
            = ∑ x : Fin n → α,
                (prefixPMF μ n x).toReal *
                  Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal) := this
        _ ≤ ∑ x : Fin n → α,
              ((prefixPMF μ n x).toReal *
                    Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal) +
                (prefixPMF μ n x).toReal * Real.log (1 / c.toReal)) := hsum'
        _ = (∑ x : Fin n → α,
                (prefixPMF μ n x).toReal *
                  Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal)) +
              (∑ x : Fin n → α, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal)) := hsplit
        _ = (∑ x : Fin n → α,
                (prefixPMF μ n x).toReal *
                  Real.log ((μ (List.ofFn x)).toReal / (η (List.ofFn x)).toReal)) +
              Real.log (1 / c.toReal) := by
              rw [hconst]
    -- Finally rewrite the first sum as `relEntropy μ η.toSemimeasure n`.
    simpa [relEntropy, PrefixMeasure.toSemimeasure] using hmain
  exact hsum

end FiniteHorizon

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
