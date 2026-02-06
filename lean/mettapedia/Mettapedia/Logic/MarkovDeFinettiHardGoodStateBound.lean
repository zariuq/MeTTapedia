import Mettapedia.Logic.MarkovDeFinettiHardApprox
import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardExcursions
import Mettapedia.Logic.MarkovDeFinettiHardBEST

/-!
# Markov de Finetti (Hard Direction) — Good‑state bound (bridge)

This file resolves the import cycle between `HardApprox` and `ExcursionModel` by
importing both.  It proves the Diaconis–Freedman **good‑state bound**: on evidence
states with `M` returns to the start, the per‑state approximation error is `O(1/M)`.

The proof strategy:
1. Each trajectory in the fiber at horizon `N` decomposes into `≈ M` excursions.
2. The prefix coefficient `prefixCoeff` equals the *without‑replacement* probability
   of the first `m` excursions matching a given pattern.
3. `W(empiricalParam s)` equals the *with‑replacement* probability under the same
   excursion empirical distribution.
4. The difference is bounded by `4m²/R` via `abs_excursion_wor_wr_le_take`,
   where `R ≈ M` and `m` depends only on `(k, n)`.

## Lemmas moved here from `HardApprox`

- `good_state_bound`
- `abs_weightedDiffCore_le`
- `weightedDiffCore_tendsto_zero`
- `weightedDiff_tendsto_zero`
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHard

open MeasureTheory

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacement
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardBEST

variable {k : ℕ}

/-! ## Good‑state bound (Diaconis–Freedman core)

The core approximation lemma: for evidence states with many returns to start,
the empirical Markov predictor approximates the uniform‑fiber prefix coefficient
at rate `O(1 / M)`.

Definitions and helper lemmas (`prefixExcursionCount`, `excursionListOfTraj_length`,
etc.) are in `MarkovDeFinettiHardBEST`.
-/

/-- **Excursion WOR/WR correspondence** (the core Diaconis–Freedman lemma).

For `R > 4n²`, the difference between `W(empiricalParam s)` and `prefixCoeff`
is bounded by `4n²/R` via the excursion decomposition.

The proof requires:
- Fiber partition into excursion prefix fibers (disjoint covering)
- BEST theorem consequence: uniform Euler path sampling → uniform excursion ordering
- Product decomposition of `wordProbNN` through excursion frequencies

These show `prefixCoeff = ∑ WOR` and `W(empiricalParam) = ∑ WR` over the same
index set, reducing the bound to `abs_excursion_wor_wr_le_take`. -/
private lemma excursion_wor_wr_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hRlarge : 4 * n * n < returnsToStart (k := k) s) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * (n : ℝ) * (n : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  exact excursion_bound_from_decomposition hk n e hN s hs hRlarge

/-- The per‑state excursion bound: the difference between the empirical
evidence polynomial and the prefix coefficient is bounded by `4n²/R`,
where `R = returnsToStart s`.

For `R ≤ 4n²`: the bound ≥ 1, which dominates |diff| since both values ∈ [0,1].
For `R > 4n²`: uses the genuine excursion WOR/WR correspondence. -/
private lemma excursion_decomposition_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * (n : ℝ) * (n : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  by_cases hsmall : returnsToStart (k := k) s ≤ 4 * n * n
  · -- Trivial case: R ≤ 4n², so 4n²/R ≥ 1 ≥ |diff|.
    have hdiff := abs_diffTerm_le_one (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs
    have hRreal : (0 : ℝ) < (returnsToStart (k := k) s : ℝ) :=
      Nat.cast_pos.mpr hRpos
    have hbound : (1 : ℝ) ≤ (4 * (n : ℝ) * (n : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
      rw [le_div_iff₀ hRreal]
      simp only [one_mul]
      exact_mod_cast hsmall
    linarith
  · -- Real case: R > 4n², use the excursion WOR/WR correspondence.
    have hRlarge : 4 * n * n < returnsToStart (k := k) s := by omega
    exact excursion_wor_wr_bound (k := k) hk n e hN s hs hRlarge

/-- The per‑state excursion bound: the difference between the empirical
evidence polynomial and the prefix coefficient is bounded by `4n²/M`.

Proved from `excursion_decomposition_bound` (with `R = returnsToStart s`)
and the hypothesis `M ≤ R`. -/
private lemma perState_excursion_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (M : ℕ) (hM : 0 < M) (hMret : M ≤ returnsToStart (k := k) s) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * (n : ℝ) * (n : ℝ)) / (M : ℝ) := by
  have hRpos : 0 < returnsToStart (k := k) s := Nat.lt_of_lt_of_le hM hMret
  have hR := excursion_decomposition_bound (k := k) hk n e hN s hs hRpos
  have hnum : (0 : ℝ) ≤ 4 * (n : ℝ) * (n : ℝ) := by positivity
  calc |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal|
      ≤ (4 * (n : ℝ) * (n : ℝ)) / (returnsToStart (k := k) s : ℝ) := hR
    _ ≤ (4 * (n : ℝ) * (n : ℝ)) / (M : ℝ) := by
        apply div_le_div_of_nonneg_left hnum
        · exact Nat.cast_pos.mpr hM
        · exact Nat.cast_le.mpr hMret

theorem good_state_bound
    (hk : 0 < k)
    (n : ℕ) (e : MarkovState k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N)
        (s : MarkovState k),
          s ∈ stateFinset k N →
            ∀ (M : ℕ), 0 < M → M ≤ returnsToStart (k := k) s →
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                  - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ C / (M : ℝ) := by
  -- The constant C = 4 * n * n works universally.
  refine ⟨4 * (n : ℝ) * (n : ℝ), by positivity, ?_⟩
  intro N hN s hs M hM hMret
  exact perState_excursion_bound (k := k) hk n e hN s hs M hM hMret

lemma abs_weightedDiffCore_le
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (n : ℕ) (e : MarkovState k) (N : ℕ) (hN : Nat.succ n ≤ N)
    (M : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hgood :
      ∀ (s : MarkovState k),
        s ∈ stateFinset k N →
          M ≤ returnsToStart (k := k) s →
            |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ C / (M : ℝ)) :
    |weightedDiffCore hk μ n e N hN| ≤ C / (M : ℝ) + badMass (k := k) μ N M := by
  classical
  have hsum_abs :
      |∑ s ∈ stateFinset k N,
        ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal) *
          (wμ (k := k) μ N s).toReal| ≤
        ∑ s ∈ stateFinset k N,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
              - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal := by
    have h :=
      (Finset.abs_sum_le_sum_abs
        (s := stateFinset k N)
        (f := fun s =>
          ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal) *
            (wμ (k := k) μ N s).toReal))
    simpa using h
  have hterm_le :
      ∀ s ∈ stateFinset k N,
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal ≤
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal := by
    intro s hs
    by_cases hbad : returnsToStart (k := k) s < M
    · have hdiff :=
        abs_diffTerm_le_one (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs
      have hw : 0 ≤ (wμ (k := k) μ N s).toReal := by exact ENNReal.toReal_nonneg
      have hmul := mul_le_mul_of_nonneg_right hdiff hw
      simpa [hbad] using hmul
    · have hgood' : M ≤ returnsToStart (k := k) s := le_of_not_gt hbad
      have hdiff := hgood s hs hgood'
      have hw : 0 ≤ (wμ (k := k) μ N s).toReal := by exact ENNReal.toReal_nonneg
      have hmul := mul_le_mul_of_nonneg_right hdiff hw
      simpa [hbad] using hmul
  have hsum_bound :
      ∑ s ∈ stateFinset k N,
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal ≤
        ∑ s ∈ stateFinset k N,
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal := by
    exact Finset.sum_le_sum hterm_le
  have hsplit_le :
      ∑ s ∈ stateFinset k N,
        (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
          (wμ (k := k) μ N s).toReal ≤
        badMass (k := k) μ N M + (C / (M : ℝ)) *
          ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal := by
    -- First compare to a pointwise upper bound.
    have hsum_le :
        ∑ s ∈ stateFinset k N,
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal ≤
          ∑ s ∈ stateFinset k N,
            ((if returnsToStart (k := k) s < M then (wμ (k := k) μ N s).toReal else 0) +
              (C / (M : ℝ)) * (wμ (k := k) μ N s).toReal) := by
      refine Finset.sum_le_sum ?_
      intro s hs
      by_cases hbad : returnsToStart (k := k) s < M
      · have hw : 0 ≤ (wμ (k := k) μ N s).toReal := by exact ENNReal.toReal_nonneg
        have hcm : 0 ≤ C / (M : ℝ) := by
          exact div_nonneg hC (Nat.cast_nonneg M)
        -- after simplification, it suffices to show nonnegativity
        simp [hbad]
        exact mul_nonneg hcm hw
      · simp [hbad]
    -- Now compute the sum on the right.
    have hsum_eq :
        (∑ s ∈ stateFinset k N,
            ((if returnsToStart (k := k) s < M then (wμ (k := k) μ N s).toReal else 0) +
              (C / (M : ℝ)) * (wμ (k := k) μ N s).toReal)) =
          badMass (k := k) μ N M + (C / (M : ℝ)) *
            ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal := by
      simp [badMass, Finset.sum_add_distrib, Finset.mul_sum]
    exact hsum_le.trans (by simp [hsum_eq])
  have hsum_wμ : ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal = 1 :=
    sum_wμ_toReal_eq_one (k := k) (μ := μ) N
  calc
    |weightedDiffCore hk μ n e N hN|
        = |∑ s ∈ stateFinset k N,
              ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                - (prefixCoeff (k := k) (h := hN) e s).toReal) *
                (wμ (k := k) μ N s).toReal| := by
              simp [weightedDiffCore]
    _ ≤ ∑ s ∈ stateFinset k N,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
              - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal := hsum_abs
    _ ≤ ∑ s ∈ stateFinset k N,
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal := hsum_bound
    _ ≤ badMass (k := k) μ N M + (C / (M : ℝ)) *
          ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal := hsplit_le
    _ = badMass (k := k) μ N M + (C / (M : ℝ)) * 1 := by
          simp [hsum_wμ]
    _ = C / (M : ℝ) + badMass (k := k) μ N M := by
          ring_nf
    _ = C / (M : ℝ) + badMass (k := k) μ N M := rfl

/-! The core asymptotic statement for the weighted difference. -/
theorem weightedDiffCore_tendsto_zero
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure μ)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
  classical
  -- Extract the Diaconis–Freedman good‑state bound.
  obtain ⟨C, hC, hgood⟩ := good_state_bound (k := k) (hk := hk) (n := n) (e := e)
  -- Use the metric characterization of convergence.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- Choose M with C / M < ε/2.
  obtain ⟨M, hMpos, hMbound⟩ : ∃ M : ℕ, 0 < M ∧ C / (M : ℝ) < ε / 2 := by
    by_cases hC0 : C = 0
    · refine ⟨1, ?_⟩
      refine ⟨by decide, ?_⟩
      simp [hC0, hε2]
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
      have hden : 0 < (2 : ℝ) * C := by nlinarith
      have hεC : 0 < ε / ((2 : ℝ) * C) := by exact div_pos hε hden
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hεC
      refine ⟨m + 1, Nat.succ_pos _, ?_⟩
      have hm' : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < ε / ((2 : ℝ) * C) := by
        simpa using hm
      have hmul : C * ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) < C * (ε / ((2 : ℝ) * C)) := by
        exact mul_lt_mul_of_pos_left hm' hCpos
      have hleft : C / ((m + 1 : ℕ) : ℝ) = C * ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
        ring
      have hright : C * (ε / ((2 : ℝ) * C)) = ε / 2 := by
        have hCne : C ≠ 0 := ne_of_gt hCpos
        field_simp [hCne]
      simpa [hleft, hright] using hmul
  -- Bad mass goes to zero for this fixed `M`.
  have hbad := badMass_tendsto_zero (k := k) (μ := μ) (M := M) hrec
  rw [Metric.tendsto_atTop] at hbad
  obtain ⟨N0, hN0⟩ := hbad (ε / 2) hε2
  -- Combine the good/bad split for all N ≥ max N0 (n+1).
  refine ⟨max N0 (Nat.succ n), ?_⟩
  intro N hN
  have hN0' : N0 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hN1' : Nat.succ n ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  have hbadN := hN0 N hN0'
  -- rewrite weightedDiff to the core sum
  have hcore : weightedDiff (k := k) hk μ n e N =
      weightedDiffCore hk μ n e N hN1' := by
    simp [weightedDiff, hN1', weightedDiffCore]
  have hbound :=
    abs_weightedDiffCore_le (k := k) (hk := hk) (μ := μ) (n := n) (e := e)
      (N := N) (hN := hN1') (M := M) (C := C) hC
      (fun s hs hret => hgood (N := N) hN1' s hs M hMpos hret)
  -- conclude the ε‑bound
  have hbadN' : |badMass (k := k) μ N M - 0| < ε / 2 := by
    simpa [Real.dist_eq, sub_zero] using hbadN
  have hbadN'' : badMass (k := k) μ N M < ε / 2 := by
    have hnonneg := badMass_nonneg (k := k) (μ := μ) (N := N) (M := M)
    simpa [abs_of_nonneg hnonneg] using hbadN'
  have hfinal : |weightedDiff (k := k) hk μ n e N| < ε := by
    have hle : |weightedDiff (k := k) hk μ n e N|
        ≤ C / (M : ℝ) + badMass (k := k) μ N M := by
      simpa [hcore] using hbound
    have hsum : C / (M : ℝ) + badMass (k := k) μ N M < ε := by
      linarith [hMbound, hbadN'']
    exact lt_of_le_of_lt hle hsum
  simpa [Real.dist_eq, sub_zero] using hfinal

/-!
### Diaconis–Freedman approximation lemma (main remaining gap)

This is the only hard analytic lemma required for the Markov de Finetti
hard direction. Once proven, the rest of the pipeline (moment polytope,
compactness, finite‑intersection) closes automatically.
-/

theorem weightedDiff_tendsto_zero
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure μ)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
  exact weightedDiffCore_tendsto_zero (k := k) (hk := hk) (μ := μ) hμ hrec n e

end MarkovDeFinettiHard

end Mettapedia.Logic
