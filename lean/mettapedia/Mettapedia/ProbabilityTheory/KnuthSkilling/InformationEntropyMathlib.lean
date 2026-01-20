import Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Mathlib bridge: KL divergence (finite `Fin n`) ↔ measure-theoretic `InformationTheory.klDiv`

This file connects the project’s discrete `ProbDist` KL divergence (`klDivergenceTop` in
`InformationEntropy.lean`) with mathlib’s general measure-theoretic KL divergence
`InformationTheory.klDiv`.

For the **countable** (including `ℕ`) generalization, where divergence is defined via `tsum`,
see `Mettapedia/ProbabilityTheory/KnuthSkilling/DivergenceMathlib.lean`.

Key points:
- We build the measure associated to a `ProbDist` as a finite sum of weighted Dirac measures.
- We prove that absolute continuity is exactly the usual “Q is positive on support of P” condition.
- Under that condition, mathlib’s `klDiv` reduces to the same finite sum as our `klDivergence`.

We use the explicit measurable space `⊤` on `Fin n` to avoid any instance ambiguity.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy

open scoped BigOperators ENNReal

open Classical MeasureTheory Real

namespace ProbDist

variable {n : ℕ}

/-- Interpret a finite probability distribution as a measure on `Fin n` (with measurable space `⊤`). -/
noncomputable def toMeasureTop (P : ProbDist n) : @Measure (Fin n) ⊤ := by
  classical
  exact ∑ i : Fin n, (ENNReal.ofReal (P.p i)) • Measure.dirac i

@[simp]
theorem toMeasureTop_apply_singleton (P : ProbDist n) (i : Fin n) : P.toMeasureTop {i} = ENNReal.ofReal (P.p i) := by
  classical
  -- Only the `i` term contributes to the sum.
  simp [ProbDist.toMeasureTop]
  have hsingle :
      (∑ x : Fin n, ENNReal.ofReal (P.p x) * ({i} : Set (Fin n)).indicator 1 x) =
        ENNReal.ofReal (P.p i) * ({i} : Set (Fin n)).indicator 1 i := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro x hx hxi
      simp [Set.indicator, hxi]
    · intro hi
      simpa using (hi (Finset.mem_univ i))
  simpa using hsingle

@[simp]
theorem toMeasureTop_univ (P : ProbDist n) : P.toMeasureTop Set.univ = 1 := by
  classical
  -- Evaluate the measure of `univ` and use `P.sum_one`.
  have hsum : (∑ i : Fin n, ENNReal.ofReal (P.p i)) = ENNReal.ofReal (∑ i : Fin n, P.p i) := by
    -- `ENNReal.ofReal` commutes with finite sums of nonnegative reals.
    simpa using
      (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => P.p i) (by intro i _; exact P.nonneg i)).symm
  -- Now compute.
  simp [ProbDist.toMeasureTop, hsum, P.sum_one]

/-- The associated measure is a probability measure. -/
instance instIsProbabilityMeasure_toMeasureTop (P : ProbDist n) :
    MeasureTheory.IsProbabilityMeasure P.toMeasureTop := by
  classical
  refine ⟨by simp⟩

/-- The associated measure is finite. -/
instance instIsFiniteMeasure_toMeasureTop (P : ProbDist n) : IsFiniteMeasure P.toMeasureTop := by
  classical
  refine ⟨by simp⟩

/-- If `Q` is positive on the support of `P`, then `P.toMeasureTop ≪ Q.toMeasureTop`. -/
theorem toMeasureTop_absolutelyContinuous_of_support_pos (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) : P.toMeasureTop ≪ Q.toMeasureTop := by
  classical
  intro s hs0
  -- Reduce to checking singleton masses (on a finite space).
  have hsingle : ∀ i : Fin n, i ∈ s → P.toMeasureTop {i} = 0 := by
    intro i his
    -- From `Q s = 0`, we get `Q {i} = 0` by monotonicity.
    have hQi0 : Q.toMeasureTop {i} = 0 := by
      have hsubset : ({i} : Set (Fin n)) ⊆ s := by
        intro x hx
        have hx' : x = i := by simpa [Set.mem_singleton_iff] using hx
        simpa [hx'] using his
      have hle : Q.toMeasureTop {i} ≤ Q.toMeasureTop s := measure_mono hsubset
      have hle0 : Q.toMeasureTop {i} ≤ 0 := by simpa [hs0] using hle
      exact le_antisymm hle0 (zero_le _)
    -- Convert to `Q.p i = 0`, then `P.p i = 0`.
    have hQi_real : Q.p i = 0 := by
      have : ENNReal.ofReal (Q.p i) = 0 := by simpa [toMeasureTop_apply_singleton] using hQi0
      have hle0 : Q.p i ≤ 0 := by
        -- `ofReal r = 0` implies `r ≤ 0`.
        simpa using (ENNReal.ofReal_eq_zero.mp this)
      exact le_antisymm hle0 (Q.nonneg i)
    have hPi_real : P.p i = 0 := by
      by_contra hPi
      have hQi_pos : 0 < Q.p i := hQ_pos i hPi
      simp [hQi_real] at hQi_pos
    simp [toMeasureTop_apply_singleton, hPi_real]
  -- Since all singleton masses in `s` are 0, the whole set has mass 0.
  -- Use `sum_measure_singleton` after converting `s` to a finset.
  let sFin : Finset (Fin n) := s.toFinset
  have hsFin : (sFin : Set (Fin n)) = s := by
    ext i; simp [sFin]
  have : P.toMeasureTop (sFin : Set (Fin n)) = 0 := by
    -- `μ sFin = ∑ i∈sFin μ{i}`.
    have hsum_single : (∑ i ∈ sFin, P.toMeasureTop {i}) = P.toMeasureTop (sFin : Set (Fin n)) := by
      simpa using (sum_measure_singleton (μ := P.toMeasureTop) (s := sFin))
    -- All summands are 0.
    have hsum0 : (∑ i ∈ sFin, P.toMeasureTop {i}) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : i ∈ (sFin : Set (Fin n)) := by
        simpa using (Finset.mem_coe.mp hi)
      have : i ∈ s := by simpa [hsFin] using this
      exact hsingle i this
    -- Conclude.
    calc
      P.toMeasureTop (sFin : Set (Fin n)) = ∑ i ∈ sFin, P.toMeasureTop {i} := by
        simpa [hsum_single] using hsum_single.symm
      _ = 0 := hsum0
  simpa [hsFin] using this

/-- If the support-positivity condition fails, then `klDiv` is `∞` (no absolute continuity). -/
theorem klDiv_toMeasureTop_eq_top_of_support_violation (P Q : ProbDist n) (i : Fin n)
    (hPi : P.p i ≠ 0) (hQi : Q.p i = 0) :
    @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop = ⊤ := by
  classical
  -- Show `¬ P.toMeasureTop ≪ Q.toMeasureTop` via the singleton `{i}`.
  have hnot : ¬ P.toMeasureTop ≪ Q.toMeasureTop := by
    intro hAC
    have hQ0 : Q.toMeasureTop {i} = 0 := by simp [toMeasureTop_apply_singleton, hQi]
    have hP0 : P.toMeasureTop {i} = 0 := hAC hQ0
    -- But `P.p i ≠ 0` implies `P.toMeasureTop {i} ≠ 0`.
    have hPi_pos : 0 < P.p i := (P.nonneg i).lt_of_ne' hPi
    have hPi_ofReal_ne : ENNReal.ofReal (P.p i) ≠ 0 := (ENNReal.ofReal_ne_zero_iff).2 hPi_pos
    have : P.toMeasureTop {i} ≠ 0 := by simpa [toMeasureTop_apply_singleton] using hPi_ofReal_ne
    exact this hP0
  simpa using (InformationTheory.klDiv_of_not_ac (μ := P.toMeasureTop) (ν := Q.toMeasureTop) hnot)

/-- On `Fin n`, mathlib's `klDiv` agrees with our `klDivergenceTop` (support-positivity case). -/
theorem klDiv_toMeasureTop_eq_of_support_pos (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop =
      ENNReal.ofReal (klDivergence P Q hQ_pos) := by
  classical
  have hAC : P.toMeasureTop ≪ Q.toMeasureTop :=
    toMeasureTop_absolutelyContinuous_of_support_pos (P := P) (Q := Q) hQ_pos
  let dens : Fin n → ℝ≥0∞ := fun i => ENNReal.ofReal (P.p i) / ENNReal.ofReal (Q.p i)
  have hdens_meas : Measurable dens := by
    -- Domain measurable space is `⊤`, so measurability is trivial.
    simp [dens, Measurable]
  have h_withDensity : P.toMeasureTop = Q.toMeasureTop.withDensity dens := by
    -- Two measures on a countable type are equal if they agree on singletons.
    apply Measure.ext_of_singleton
    intro i
    by_cases hPi0 : P.p i = 0
    · -- Then both sides evaluate to 0 on `{i}`.
      simp [dens, hPi0, toMeasureTop_apply_singleton, withDensity_apply]
    · have hQi_pos : 0 < Q.p i := hQ_pos i hPi0
      have hQi_ne0 : ENNReal.ofReal (Q.p i) ≠ 0 := (ENNReal.ofReal_ne_zero_iff).2 hQi_pos
      have hQi_ne_top : ENNReal.ofReal (Q.p i) ≠ (⊤ : ℝ≥0∞) := by simp
      have hmuldiv :
          ENNReal.ofReal (Q.p i) * (ENNReal.ofReal (P.p i) / ENNReal.ofReal (Q.p i)) =
            ENNReal.ofReal (P.p i) := by
        simpa [dens] using
          (ENNReal.mul_div_cancel (a := ENNReal.ofReal (Q.p i)) (b := ENNReal.ofReal (P.p i)) hQi_ne0 hQi_ne_top)
      -- Compute both singleton masses using `lintegral_singleton`.
      simp [dens, toMeasureTop_apply_singleton, withDensity_apply, hmuldiv]
  have hrn :
      P.toMeasureTop.rnDeriv Q.toMeasureTop =ᵐ[Q.toMeasureTop] dens := by
    -- `rnDeriv` of `ν.withDensity dens` w.r.t. `ν` is `dens`.
    simpa [h_withDensity] using (Measure.rnDeriv_withDensity (ν := Q.toMeasureTop) hdens_meas)
  -- Start from mathlib's `klDiv = lintegral klFun(rnDeriv)` formula.
  have hklDiv :
      @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop =
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((P.toMeasureTop.rnDeriv Q.toMeasureTop x).toReal)) ∂Q.toMeasureTop := by
    simp [InformationTheory.klDiv_eq_lintegral_klFun, hAC]
  -- Replace `rnDeriv` by `dens` in the integral.
  have hcongr :
      (fun x : Fin n =>
        ENNReal.ofReal (InformationTheory.klFun ((P.toMeasureTop.rnDeriv Q.toMeasureTop x).toReal)))
        =ᵐ[Q.toMeasureTop]
      (fun x : Fin n => ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal))) := by
    filter_upwards [hrn] with x hx
    simp [hx]
  have hlin :
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((P.toMeasureTop.rnDeriv Q.toMeasureTop x).toReal)) ∂Q.toMeasureTop) =
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) ∂Q.toMeasureTop := by
    exact lintegral_congr_ae hcongr
  rw [hklDiv, hlin]
  -- Compute the lintegral as a finite sum.
  have hsum :
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) ∂Q.toMeasureTop) =
        ∑ i : Fin n, ENNReal.ofReal (InformationTheory.klFun ((dens i).toReal)) * Q.toMeasureTop {i} := by
    simpa using (MeasureTheory.lintegral_fintype (μ := Q.toMeasureTop)
      (f := fun i : Fin n => ENNReal.ofReal (InformationTheory.klFun ((dens i).toReal))))
  rw [hsum]
  -- Rewrite singleton masses and simplify `toReal` of the ENNReal ratio.
  have htoReal_dens :
      ∀ i : Fin n, (dens i).toReal = P.p i / Q.p i := by
    intro i
    have hPi : 0 ≤ P.p i := P.nonneg i
    have hQi : 0 ≤ Q.p i := Q.nonneg i
    simp [dens, ENNReal.toReal_div, ENNReal.toReal_ofReal hPi, ENNReal.toReal_ofReal hQi]
  -- Turn each ENNReal term into `ofReal (Q.p i * klFun (P.p i / Q.p i))`.
  have hterm :
      ∀ i : Fin n,
        ENNReal.ofReal (InformationTheory.klFun ((dens i).toReal)) * ENNReal.ofReal (Q.p i)
          = ENNReal.ofReal (Q.p i * InformationTheory.klFun (P.p i / Q.p i)) := by
    intro i
    have hkl_nonneg : 0 ≤ InformationTheory.klFun (P.p i / Q.p i) :=
      InformationTheory.klFun_nonneg (div_nonneg (P.nonneg i) (Q.nonneg i))
    -- `ofReal a * ofReal b = ofReal (a*b)` when `a ≥ 0`.
    simpa [htoReal_dens i, mul_comm, mul_left_comm, mul_assoc] using (ENNReal.ofReal_mul hkl_nonneg).symm
  -- Rewrite the sum using `hterm`.
  have hsum1 :
      (∑ i : Fin n, ENNReal.ofReal (InformationTheory.klFun ((dens i).toReal)) * Q.toMeasureTop {i}) =
        ∑ i : Fin n, ENNReal.ofReal (Q.p i * InformationTheory.klFun (P.p i / Q.p i)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [toMeasureTop_apply_singleton, hterm i]
  rw [hsum1]
  -- Combine the sum of `ofReal` terms into a single `ofReal` of the real sum.
  have hnonneg : ∀ i : Fin n, 0 ≤ Q.p i * InformationTheory.klFun (P.p i / Q.p i) := by
    intro i
    exact mul_nonneg (Q.nonneg i)
      (InformationTheory.klFun_nonneg (div_nonneg (P.nonneg i) (Q.nonneg i)))
  have hsum_ofReal :
      ENNReal.ofReal (∑ i : Fin n, Q.p i * InformationTheory.klFun (P.p i / Q.p i)) =
        ∑ i : Fin n, ENNReal.ofReal (Q.p i * InformationTheory.klFun (P.p i / Q.p i)) := by
    simpa using
      (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => Q.p i * InformationTheory.klFun (P.p i / Q.p i))
        (by intro i _; exact hnonneg i))
  rw [← hsum_ofReal]
  -- Finally show the real sum is exactly our `klDivergence`.
  have hsum_real :
      (∑ i : Fin n, Q.p i * InformationTheory.klFun (P.p i / Q.p i)) = klDivergence P Q hQ_pos := by
    -- Expand `klFun` and cancel the normalization terms.
    have hterm_real :
        ∀ i : Fin n,
          Q.p i * InformationTheory.klFun (P.p i / Q.p i) =
            P.p i * log (P.p i / Q.p i) + (Q.p i - P.p i) := by
      intro i
      by_cases hPi0 : P.p i = 0
      · simp [InformationTheory.klFun, hPi0]
      · have hQi_pos : 0 < Q.p i := hQ_pos i hPi0
        have hQi_ne : Q.p i ≠ 0 := ne_of_gt hQi_pos
        -- Use `Q * (P/Q) = P` when `Q ≠ 0`.
        have hmuldiv : Q.p i * (P.p i / Q.p i) = P.p i := by
          calc
            Q.p i * (P.p i / Q.p i) = (Q.p i * P.p i) / Q.p i := by
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            _ = P.p i := by
              simpa [mul_comm] using (mul_div_cancel_left₀ (P.p i) hQi_ne)
        -- Expand `klFun` and simplify using `hmuldiv`.
        unfold InformationTheory.klFun
        -- `Q * ((P/Q) * log(P/Q) + 1 - (P/Q)) = P*log(P/Q) + (Q - P)`
        calc
          Q.p i * ((P.p i / Q.p i) * log (P.p i / Q.p i) + 1 - (P.p i / Q.p i))
              = Q.p i * ((P.p i / Q.p i) * log (P.p i / Q.p i)) + Q.p i * (1 - (P.p i / Q.p i)) := by
                ring
          _ = (Q.p i * (P.p i / Q.p i)) * log (P.p i / Q.p i) + (Q.p i - Q.p i * (P.p i / Q.p i)) := by
                ring
          _ = P.p i * log (P.p i / Q.p i) + (Q.p i - P.p i) := by
                simp [hmuldiv]
    -- Sum and cancel `∑ (Q - P) = 0` using normalization.
    calc
      (∑ i : Fin n, Q.p i * InformationTheory.klFun (P.p i / Q.p i))
          = ∑ i : Fin n, (P.p i * log (P.p i / Q.p i) + (Q.p i - P.p i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [hterm_real i]
      _ = (∑ i : Fin n, P.p i * log (P.p i / Q.p i)) + ∑ i : Fin n, (Q.p i - P.p i) := by
              simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, P.p i * log (P.p i / Q.p i)) + ((∑ i : Fin n, Q.p i) - (∑ i : Fin n, P.p i)) := by
              simp [Finset.sum_sub_distrib]
      _ = ∑ i : Fin n, P.p i * log (P.p i / Q.p i) := by
              simp [P.sum_one, Q.sum_one]
      _ = klDivergence P Q hQ_pos := by rfl
  simp [hsum_real]

/-- `klDiv` agrees with `klDivergenceTop` on `Fin n`.

This is the main bridge theorem: our discrete extended KL divergence is exactly mathlib’s
measure-theoretic `InformationTheory.klDiv` on the associated Dirac-sum measures.
-/
theorem klDiv_toMeasureTop_eq_klDivergenceTop (P Q : ProbDist n) :
    @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop = klDivergenceTop P Q := by
  classical
  by_cases hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i
  · simpa [klDivergenceTop, dif_pos hQ_pos] using
      (klDiv_toMeasureTop_eq_of_support_pos (P := P) (Q := Q) hQ_pos)
  · -- no absolute continuity: both sides are `∞`.
    have hex : ∃ i : Fin n, P.p i ≠ 0 ∧ Q.p i = 0 := by
      -- Since `Q.p i ≥ 0`, `¬ 0 < Q.p i` is equivalent to `Q.p i = 0`.
      classical
      have : ∃ i : Fin n, P.p i ≠ 0 ∧ ¬ 0 < Q.p i := by
        simpa [not_forall] using hQ_pos
      rcases this with ⟨i, hPi, hQi⟩
      refine ⟨i, hPi, ?_⟩
      have hQi_le : Q.p i ≤ 0 := le_of_not_gt hQi
      exact le_antisymm hQi_le (Q.nonneg i)
    rcases hex with ⟨i, hPi, hQi0⟩
    have hleft : @InformationTheory.klDiv (Fin n) ⊤ P.toMeasureTop Q.toMeasureTop = ⊤ :=
      klDiv_toMeasureTop_eq_top_of_support_violation (P := P) (Q := Q) i hPi hQi0
    simp [klDivergenceTop, dif_neg hQ_pos, hleft]

end ProbDist

end Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy
