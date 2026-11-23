/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Bitwise

/-!
# Borel's normal number theorem

Almost every number in `(0, 1]` is normal in base 2: the proportion of ones among its first
`n` binary digits tends to `1/2` (Borel 1909). This follows Billingsley, *Probability and
Measure*, Section 1: the binary digits are independent fair coin flips under Lebesgue measure,
the weak law follows from Chebyshev's inequality, and the strong form from a fourth-moment
bound on the Rademacher sums and the Borel–Cantelli lemma.

## Main definitions

* `dyadicDigit n ω`: the `n`-th binary digit of `ω ∈ (0, 1]`, nonterminating expansion.
* `sumDigits n ω`: the number of ones among the first `n` digits.
* `IsNormal ω`: `sumDigits n ω / n → 1/2`; `normalNumbers` is the set of normal `ω ∈ (0, 1]`.

## Main results

* `weakLawOfLargeNumbers_binary`: the weak law for the digit sums.
* `borelNormalNumberTheorem`: the normal numbers in `(0, 1]` have Lebesgue measure `1`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Mettapedia.ProbabilityTheory.NormalNumbers

/-! ## The Unit Interval -/

/-- The half-open unit interval (0, 1]. This is the sample space Ω in Billingsley's setup. -/
def halfOpenUnit : Set ℝ := Set.Ioc 0 1

/-- The half-open unit interval is measurable (it's a Borel set). -/
theorem halfOpenUnit_measurableSet : MeasurableSet halfOpenUnit := measurableSet_Ioc

/-- Lebesgue measure of (0, 1] is 1. -/
theorem volume_halfOpenUnit : volume halfOpenUnit = 1 := by
  simp [halfOpenUnit, Real.volume_Ioc]

/-! ## Dyadic Expansions

Every ω ∈ (0, 1] has a unique nonterminating binary expansion
ω = Σₙ d_n(ω) / 2^n where d_n(ω) ∈ {0, 1}.

For definiteness, dyadic rationals k/2^n take their nonterminating expansion
(ending in all 1s rather than all 0s).
-/

/-- The nth binary digit of ω ∈ (0, 1]. This is the "nonterminating" expansion:
for dyadic rationals, we choose the expansion ending in 1s. -/
def dyadicDigit (n : ℕ) (ω : ℝ) : ℕ :=
  if n = 0 then 0  -- Index from 1 in Billingsley's notation
  else
    let scaled := ω * 2^n
    if scaled - ⌊scaled⌋ > 0 then
      (⌊scaled⌋ : ℤ).toNat % 2
    else  -- ω is a dyadic rational at this level, take nonterminating expansion
      ((⌊scaled⌋ : ℤ).toNat - 1) % 2

/-- The nth digit is 0 or 1. -/
theorem dyadicDigit_le_one (n : ℕ) (ω : ℝ) : dyadicDigit n ω ≤ 1 := by
  simp only [dyadicDigit]
  split_ifs with h1 h2
  · omega
  all_goals {
    have h : ∀ k : ℕ, k % 2 ≤ 1 := fun k => Nat.lt_succ_iff.mp (Nat.mod_lt k (by norm_num))
    exact h _
  }

/-- dyadicDigit takes values 0 or 1. -/
theorem dyadicDigit_values (n : ℕ) (ω : ℝ) : dyadicDigit n ω = 0 ∨ dyadicDigit n ω = 1 := by
  have h := dyadicDigit_le_one n ω
  omega

/-- The sum of the first n binary digits S_n(ω) = Σᵢ₌₁ⁿ d_i(ω). -/
def sumDigits (n : ℕ) (ω : ℝ) : ℕ := (Finset.range n).sum (fun i => dyadicDigit (i + 1) ω)

/-! ## Dyadic Intervals

The interval {ω : d_i(ω) = u_i for i = 1,...,n} is a dyadic interval of rank n.
Its length is 1/2^n.
-/

/-- A dyadic interval of rank n specified by a binary sequence. -/
def dyadicInterval (n : ℕ) (u : Fin n → Bool) : Set ℝ :=
  Set.Ioc
    ((Finset.univ.sum fun i => if u i then (2 : ℝ)^(-(i.val + 1 : ℤ)) else 0))
    ((Finset.univ.sum fun i => if u i then (2 : ℝ)^(-(i.val + 1 : ℤ)) else 0) + (2 : ℝ)^(-(n : ℤ)))

/-- Dyadic intervals are measurable. -/
theorem dyadicInterval_measurableSet (n : ℕ) (u : Fin n → Bool) :
    MeasurableSet (dyadicInterval n u) := measurableSet_Ioc

/-- The Lebesgue measure of a dyadic interval of rank n is 1/2^n.
This is equation (1.10) in Billingsley. -/
theorem volume_dyadicInterval (n : ℕ) (u : Fin n → Bool) :
    volume (dyadicInterval n u) = (1 : ℝ≥0∞) / (2 : ℝ≥0∞)^n := by
  simp only [dyadicInterval, Real.volume_Ioc]
  set a := (Finset.univ.sum fun i => if u i then (2 : ℝ)^(-(↑i.val + 1 : ℤ)) else 0)
  have h : a + (2 : ℝ)^(-(n : ℤ)) - a = (2 : ℝ)^(-(n : ℤ)) := by ring
  rw [h]
  simp only [zpow_neg, zpow_natCast]
  have hpos : (0 : ℝ) < (2 : ℝ)^n := by positivity
  rw [one_div, ENNReal.ofReal_inv_of_pos hpos]
  congr 1
  simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-! ## Digit-Level Sets

For proving integration results, we need to understand the structure of sets
where individual digits take specific values.
-/

/-- The set where the nth digit equals a given value b ∈ {0, 1}. -/
def digitSet (n : ℕ) (b : ℕ) : Set ℝ :=
  {ω ∈ halfOpenUnit | dyadicDigit n ω = b}

/-- The digit sets partition (0,1]. -/
theorem digitSet_union (n : ℕ) (_hn : n ≥ 1) :
    digitSet n 0 ∪ digitSet n 1 = halfOpenUnit := by
  ext ω
  simp only [digitSet, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1
  · intro hω
    have h := dyadicDigit_le_one n ω
    interval_cases dyadicDigit n ω
    · left; exact ⟨hω, rfl⟩
    · right; exact ⟨hω, rfl⟩

/-- The digit sets are disjoint. -/
theorem digitSet_disjoint (n : ℕ) : Disjoint (digitSet n 0) (digitSet n 1) := by
  rw [Set.disjoint_iff]
  intro ω ⟨h0, h1⟩
  simp only [digitSet, Set.mem_ofPred_eq] at h0 h1
  omega

/-- The digit sets are subsets of halfOpenUnit. -/
theorem digitSet_subset (n : ℕ) (b : ℕ) : digitSet n b ⊆ halfOpenUnit := by
  intro ω hω
  simp only [digitSet, Set.mem_ofPred_eq] at hω
  exact hω.1

/-- The preimage of {b} under dyadicDigit n intersected with halfOpenUnit is digitSet n b. -/
theorem dyadicDigit_preimage (n : ℕ) (b : ℕ) :
    (fun ω => dyadicDigit n ω) ⁻¹' {b} ∩ halfOpenUnit = digitSet n b := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, digitSet, Set.mem_ofPred_eq]
  constructor
  · intro ⟨hd, hu⟩; exact ⟨hu, hd⟩
  · intro ⟨hu, hd⟩; exact ⟨hd, hu⟩

/-- Helper: the digit-1 intervals for rank n.
These are the intervals ((2k+1)/2^n, (2k+2)/2^n] for k = 0, ..., 2^(n-1)-1. -/
def digitOneIntervals (n : ℕ) : Set ℝ :=
  ⋃ k : Fin (2^(n-1)), Set.Ioc ((2*k.val + 1 : ℝ) / 2^n) ((2*k.val + 2 : ℝ) / 2^n)

/-- Helper: the digit-0 intervals for rank n.
These are the intervals ((2k)/2^n, (2k+1)/2^n] for k = 0, ..., 2^(n-1)-1. -/
def digitZeroIntervals (n : ℕ) : Set ℝ :=
  ⋃ k : Fin (2^(n-1)), Set.Ioc ((2*k.val : ℝ) / 2^n) ((2*k.val + 1 : ℝ) / 2^n)

/-- The digit-1 intervals are measurable. -/
theorem digitOneIntervals_measurableSet (n : ℕ) : MeasurableSet (digitOneIntervals n) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioc)

/-- The digit-0 intervals are measurable. -/
theorem digitZeroIntervals_measurableSet (n : ℕ) : MeasurableSet (digitZeroIntervals n) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioc)

/-- The digit-1 intervals are contained in halfOpenUnit. -/
theorem digitOneIntervals_subset_halfOpenUnit (n : ℕ) (hn : n ≥ 1) :
    digitOneIntervals n ⊆ halfOpenUnit := by
  intro x hx
  simp only [digitOneIntervals, Set.mem_iUnion, Set.mem_Ioc, halfOpenUnit] at hx ⊢
  obtain ⟨k, hk1, hk2⟩ := hx
  constructor
  · -- x > 0
    have h1 : (2*(k.val : ℝ) + 1) / 2^n ≥ 1 / 2^n := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ k.val := by positivity
      linarith
    have h2 : (1 : ℝ) / 2^n > 0 := by positivity
    linarith
  · -- x ≤ 1
    have hk_bound : k.val < 2^(n-1) := k.isLt
    have hn1 : 2 * 2^(n-1) = 2^n := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
    have h1 : (2*k.val + 2 : ℕ) ≤ 2^n := by
      calc 2*k.val + 2
          ≤ 2*(2^(n-1) - 1) + 2 := by omega
        _ = 2*2^(n-1) - 2 + 2 := by
            have h2pow : 2^(n-1) ≥ 1 := Nat.one_le_pow _ _ (by omega)
            omega
        _ = 2*2^(n-1) := by omega
        _ = 2^n := hn1
    have h2 : (2*k.val + 2 : ℝ) / 2^n ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
      calc (2*k.val + 2 : ℝ)
          = ↑(2*k.val + 2 : ℕ) := by norm_cast
        _ ≤ ↑(2^n : ℕ) := by exact_mod_cast h1
        _ = 2^n := by norm_cast
    linarith

/-- The digit-0 intervals are contained in halfOpenUnit. -/
theorem digitZeroIntervals_subset_halfOpenUnit (n : ℕ) (hn : n ≥ 1) :
    digitZeroIntervals n ⊆ halfOpenUnit := by
  intro x hx
  simp only [digitZeroIntervals, Set.mem_iUnion, Set.mem_Ioc, halfOpenUnit] at hx ⊢
  obtain ⟨k, hk1, hk2⟩ := hx
  constructor
  · -- x > 0: Since x > 2k/2^n ≥ 0
    have h0 : (0 : ℝ) ≤ (2*(k.val : ℝ)) / 2^n := by positivity
    linarith
  · -- x ≤ 1
    have hk_bound : k.val < 2^(n-1) := k.isLt
    have hn1 : 2 * 2^(n-1) = 2^n := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
    have h1 : (2*k.val + 1 : ℕ) ≤ 2^n := by
      have hstep : 2*(2^(n-1) - 1) + 1 < 2*2^(n-1) := by omega
      calc 2*k.val + 1
          ≤ 2*(2^(n-1) - 1) + 1 := by omega
        _ ≤ 2*2^(n-1) := by omega
        _ = 2^n := hn1
    have h2 : (2*k.val + 1 : ℝ) / 2^n ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
      calc (2*k.val + 1 : ℝ)
          = ↑(2*k.val + 1 : ℕ) := by norm_cast
        _ ≤ ↑(2^n : ℕ) := by exact_mod_cast h1
        _ = 2^n := by norm_cast
    linarith

/-- Helper: (2k+1).toNat = 2k+1 for k : ℕ cast to ℤ. -/
lemma toNat_two_mul_add_one (k : ℕ) : (2 * (k : ℤ) + 1).toNat = 2 * k + 1 := by
  have h1 : 2 * (k : ℤ) + 1 = ↑(2 * k + 1) := by push_cast; ring
  rw [h1, Int.toNat_natCast]

/-- Helper: dyadicDigit equals 1 for ω in ((2k+1)/2^n, (2k+2)/2^n] when n ≥ 1.
    The proof involves careful floor function analysis with type coercions. -/
lemma dyadicDigit_eq_one_of_mem_interval (n : ℕ) (hn : n ≥ 1) (k : ℕ) (ω : ℝ)
    (hlo : (2*k + 1 : ℝ) / 2^n < ω) (hhi : ω ≤ (2*k + 2 : ℝ) / 2^n) :
    dyadicDigit n ω = 1 := by
  -- Key insight: ω * 2^n ∈ ((2k+1), (2k+2)]
  have h2n_pos : (0 : ℝ) < 2^n := by positivity
  -- Transform bounds to scaled form
  have hlo' : (2*k + 1 : ℝ) < ω * 2^n := by
    rw [div_lt_iff₀ h2n_pos] at hlo; linarith
  have hhi' : ω * 2^n ≤ (2*k + 2 : ℝ) := by
    rw [le_div_iff₀ h2n_pos] at hhi; linarith
  set scaled := ω * 2^n with hscaled_def
  -- Cast equalities
  have hcast1 : ((2*k + 1 : ℕ) : ℝ) = (2 : ℝ) * k + 1 := by push_cast; ring
  have hcast2 : ((2*k + 2 : ℕ) : ℝ) = (2 : ℝ) * k + 2 := by push_cast; ring
  have hcast1' : ((2*k + 1 : ℤ) : ℝ) = (2 : ℝ) * k + 1 := by push_cast; ring
  have hcast2' : ((2*k + 2 : ℤ) : ℝ) = (2 : ℝ) * k + 2 := by push_cast; ring
  -- Establish floor bounds
  have hfloor_lb : (2*k + 1 : ℤ) ≤ ⌊scaled⌋ := by
    rw [Int.le_floor, hcast1']
    exact le_of_lt hlo'
  have hfloor_ub : ⌊scaled⌋ ≤ (2*k + 2 : ℤ) := by
    have hlt : ⌊scaled⌋ < (2*k + 3 : ℤ) := by
      rw [Int.floor_lt]
      have hcast3' : ((2*k + 3 : ℤ) : ℝ) = (2 : ℝ) * k + 3 := by push_cast; ring
      rw [hcast3']
      linarith
    omega
  -- Now floor is either 2k+1 or 2k+2
  have hfloor_cases : ⌊scaled⌋ = (2*k + 1 : ℤ) ∨ ⌊scaled⌋ = (2*k + 2 : ℤ) := by omega
  -- n ≠ 0
  have hn_ne : n ≠ 0 := by omega
  -- Case split on whether scaled is an integer
  by_cases hint : scaled - ↑⌊scaled⌋ > 0
  · -- Non-integer case: floor = 2k+1
    have hfl : ⌊scaled⌋ = (2*k + 1 : ℤ) := by
      rcases hfloor_cases with h | h
      · exact h
      · -- If floor = 2k+2, then scaled = 2k+2 (integer), contradicts hint
        exfalso
        have hle : (↑⌊scaled⌋ : ℝ) ≤ scaled := Int.floor_le scaled
        rw [h, hcast2'] at hle
        have hscaled_eq : scaled = (2 : ℝ) * k + 2 := le_antisymm hhi' hle
        -- scaled - ⌊scaled⌋ = 0 since scaled = 2k+2 and ⌊scaled⌋ = 2k+2
        have hsub_eq : scaled - ↑⌊scaled⌋ = 0 := by
          rw [h, hcast2', hscaled_eq, sub_self]
        linarith
    -- Compute dyadicDigit
    simp only [dyadicDigit, hn_ne, ↓reduceIte]
    rw [hfl]
    have h_tonat : ((2*k + 1 : ℤ)).toNat = 2*k + 1 := by
      have hcoe : (2*k + 1 : ℤ) = ↑(2*k + 1 : ℕ) := by norm_cast
      rw [hcoe, Int.toNat_natCast]
    rw [h_tonat]
    -- Split on the inner if
    split_ifs with h_inner
    · -- h_inner : 0 < ω * 2^n - ↑(2*↑k + 1)
      omega
    · -- ¬ h_inner, but we proved scaled - ⌊scaled⌋ > 0, contradiction
      exfalso
      rw [hfl, hcast1'] at hint
      linarith
  · -- Integer case: scaled = 2k+2, use nonterminating expansion
    push Not at hint
    -- scaled = ⌊scaled⌋
    have hscaled_int : scaled = ↑⌊scaled⌋ := by
      have hle : ↑⌊scaled⌋ ≤ scaled := Int.floor_le scaled
      linarith
    -- So floor = 2k+2 (since 2k+1 < scaled)
    have hfl : ⌊scaled⌋ = (2*k + 2 : ℤ) := by
      rcases hfloor_cases with h | h
      · exfalso
        rw [h, hcast1'] at hscaled_int
        linarith
      · exact h
    -- Compute dyadicDigit
    simp only [dyadicDigit, hn_ne, ↓reduceIte]
    rw [hfl]
    have h_tonat : ((2*k + 2 : ℤ)).toNat = 2*k + 2 := by
      have hcoe : (2*k + 2 : ℤ) = ↑(2*k + 2 : ℕ) := by norm_cast
      rw [hcoe, Int.toNat_natCast]
    rw [h_tonat]
    -- Split on the inner if
    split_ifs with h_inner
    · -- h_inner : 0 < ω * 2^n - ↑(2*↑k + 2), but we proved scaled - ⌊scaled⌋ ≤ 0, contradiction
      exfalso
      rw [hfl, hcast2'] at hint
      linarith
    · -- ¬ h_inner, good path
      omega

/-- Helper: dyadicDigit equals 0 for ω in ((2k)/2^n, (2k+1)/2^n] when n ≥ 1.
    Similar structure to dyadicDigit_eq_one_of_mem_interval. -/
lemma dyadicDigit_eq_zero_of_mem_interval (n : ℕ) (hn : n ≥ 1) (k : ℕ) (ω : ℝ)
    (hlo : (2*k : ℝ) / 2^n < ω) (hhi : ω ≤ (2*k + 1 : ℝ) / 2^n) :
    dyadicDigit n ω = 0 := by
  -- Key insight: scaled = ω * 2^n ∈ (2k, 2k+1]
  have h2n_pos : (0 : ℝ) < 2^n := by positivity
  -- Transform bounds to scaled form
  have hlo' : (2*k : ℝ) < ω * 2^n := by
    rw [div_lt_iff₀ h2n_pos] at hlo; linarith
  have hhi' : ω * 2^n ≤ (2*k + 1 : ℝ) := by
    rw [le_div_iff₀ h2n_pos] at hhi; linarith
  set scaled := ω * 2^n with hscaled_def
  -- Cast equalities
  have hcast0 : ((2*k : ℕ) : ℝ) = (2 : ℝ) * k := by push_cast; ring
  have hcast1 : ((2*k + 1 : ℕ) : ℝ) = (2 : ℝ) * k + 1 := by push_cast; ring
  have hcast0' : ((2*k : ℤ) : ℝ) = (2 : ℝ) * k := by push_cast; ring
  have hcast1' : ((2*k + 1 : ℤ) : ℝ) = (2 : ℝ) * k + 1 := by push_cast; ring
  -- Establish floor bounds
  have hfloor_lb : (2*k : ℤ) ≤ ⌊scaled⌋ := by
    rw [Int.le_floor, hcast0']
    exact le_of_lt hlo'
  have hfloor_ub : ⌊scaled⌋ ≤ (2*k + 1 : ℤ) := by
    have hlt : ⌊scaled⌋ < (2*k + 2 : ℤ) := by
      rw [Int.floor_lt]
      have hcast2' : ((2*k + 2 : ℤ) : ℝ) = (2 : ℝ) * k + 2 := by push_cast; ring
      rw [hcast2']
      linarith
    omega
  -- Now floor is either 2k or 2k+1
  have hfloor_cases : ⌊scaled⌋ = (2*k : ℤ) ∨ ⌊scaled⌋ = (2*k + 1 : ℤ) := by omega
  -- n ≠ 0
  have hn_ne : n ≠ 0 := by omega
  -- Case split on whether scaled is an integer
  by_cases hint : scaled - ↑⌊scaled⌋ > 0
  · -- Non-integer case: floor = 2k
    have hfl : ⌊scaled⌋ = (2*k : ℤ) := by
      rcases hfloor_cases with h | h
      · exact h
      · -- If floor = 2k+1, then scaled = 2k+1 (integer), contradicts hint
        exfalso
        have hle : (↑⌊scaled⌋ : ℝ) ≤ scaled := Int.floor_le scaled
        rw [h, hcast1'] at hle
        have hscaled_eq : scaled = (2 : ℝ) * k + 1 := le_antisymm hhi' hle
        have hsub_eq : scaled - ↑⌊scaled⌋ = 0 := by
          rw [h, hcast1', hscaled_eq, sub_self]
        linarith
    -- Compute dyadicDigit
    simp only [dyadicDigit, hn_ne, ↓reduceIte]
    rw [hfl]
    have h_tonat : ((2*k : ℤ)).toNat = 2*k := by
      have hcoe : (2*k : ℤ) = ↑(2*k : ℕ) := by norm_cast
      rw [hcoe, Int.toNat_natCast]
    rw [h_tonat]
    -- Split on the inner if
    split_ifs with h_inner
    · -- h_inner : 0 < ω * 2^n - ↑(2*↑k)
      omega
    · -- ¬ h_inner, but we proved scaled - ⌊scaled⌋ > 0, contradiction
      exfalso
      rw [hfl, hcast0'] at hint
      linarith
  · -- Integer case: scaled = 2k+1, use nonterminating expansion
    push Not at hint
    -- scaled = ⌊scaled⌋
    have hscaled_int : scaled = ↑⌊scaled⌋ := by
      have hle : ↑⌊scaled⌋ ≤ scaled := Int.floor_le scaled
      linarith
    -- So floor = 2k+1 (since 2k < scaled)
    have hfl : ⌊scaled⌋ = (2*k + 1 : ℤ) := by
      rcases hfloor_cases with h | h
      · exfalso
        rw [h, hcast0'] at hscaled_int
        linarith
      · exact h
    -- Compute dyadicDigit
    simp only [dyadicDigit, hn_ne, ↓reduceIte]
    rw [hfl]
    have h_tonat : ((2*k + 1 : ℤ)).toNat = 2*k + 1 := by
      have hcoe : (2*k + 1 : ℤ) = ↑(2*k + 1 : ℕ) := by norm_cast
      rw [hcoe, Int.toNat_natCast]
    rw [h_tonat]
    -- Split on the inner if
    split_ifs with h_inner
    · -- h_inner : 0 < ω * 2^n - ↑(2*↑k + 1), but we proved scaled - ⌊scaled⌋ ≤ 0, contradiction
      exfalso
      rw [hfl, hcast1'] at hint
      linarith
    · -- ¬ h_inner, good path
      omega

/-- Key structural lemma: digitOneIntervals n = digitSet n 1 for n ≥ 1.
This establishes that the set where digit n equals 1 is exactly the union of
the "odd-indexed" dyadic intervals at level n. -/
theorem digitOneIntervals_eq_digitSet (n : ℕ) (hn : n ≥ 1) :
    digitOneIntervals n = digitSet n 1 := by
  ext ω
  simp only [digitOneIntervals, digitSet, Set.mem_iUnion, Set.mem_Ioc,
             Set.mem_ofPred_eq, halfOpenUnit]
  constructor
  · -- digitOneIntervals → digitSet
    intro ⟨k, hk1, hk2⟩
    constructor
    · exact digitOneIntervals_subset_halfOpenUnit n hn (Set.mem_iUnion.mpr ⟨k, Set.mem_Ioc.mpr ⟨hk1, hk2⟩⟩)
    · exact dyadicDigit_eq_one_of_mem_interval n hn k.val ω hk1 hk2
  · -- digitSet → digitOneIntervals
    intro ⟨⟨hω_pos, hω_le1⟩, hdigit⟩
    -- If dyadicDigit n ω = 1, then ω is in some ((2k+1)/2^n, (2k+2)/2^n]
    have h2n_pos : (0 : ℝ) < 2^n := by positivity
    set scaled := ω * 2^n with hscaled_def
    -- scaled ∈ (0, 2^n]
    have hscaled_pos : 0 < scaled := by positivity
    have hscaled_le : scaled ≤ 2^n := by
      rw [hscaled_def]; calc ω * 2^n ≤ 1 * 2^n := by nlinarith
        _ = 2^n := one_mul _
    -- n ≠ 0
    have hn_ne : n ≠ 0 := by omega
    have hfloor_nonneg : 0 ≤ ⌊scaled⌋ := Int.floor_nonneg.mpr (le_of_lt hscaled_pos)
    set floorNat := ⌊scaled⌋.toNat with hfloorNat_def
    have hfloorNat_eq : (floorNat : ℤ) = ⌊scaled⌋ := Int.toNat_of_nonneg hfloor_nonneg
    have hfloorNat_eq_real : (floorNat : ℝ) = (⌊scaled⌋ : ℝ) := by
      have h1 : (floorNat : ℤ) = ⌊scaled⌋ := hfloorNat_eq
      exact_mod_cast h1
    -- Case split on whether scaled is an integer
    by_cases hint : scaled - ↑⌊scaled⌋ > 0
    · -- Non-integer case: digit = ⌊scaled⌋.toNat % 2 = 1
      simp only [dyadicDigit, hn_ne, ↓reduceIte] at hdigit
      rw [if_pos hint] at hdigit
      -- ⌊scaled⌋.toNat % 2 = 1, so ⌊scaled⌋.toNat is odd
      have hodd : floorNat % 2 = 1 := hdigit
      -- ⌊scaled⌋ ≤ 2^n - 1 since scaled < ⌊scaled⌋ + 1 ≤ 2^n (because scaled ≤ 2^n and not integer at 2^n)
      have hfloor_lt : ⌊scaled⌋ < (2^n : ℤ) := by
        rw [Int.floor_lt]
        have h1 : scaled ≤ 2^n := hscaled_le
        have h2 : scaled ≠ 2^n := by
          intro heq
          have hfrac : scaled - ↑⌊scaled⌋ = 0 := by
            rw [heq]
            -- ⌊2^n⌋ = 2^n since 2^n is a natural number
            have h2n_nat : (2 : ℝ)^n = ↑(2^n : ℕ) := by norm_cast
            have hfl : ⌊(↑(2^n : ℕ) : ℝ)⌋ = ↑(2^n : ℕ) := Int.floor_natCast (2^n)
            rw [h2n_nat, hfl]
            simp only [Int.cast_natCast, sub_self]
          linarith
        -- Goal: scaled < (2^n : ℤ) cast to ℝ
        -- We have h1 : scaled ≤ 2^n and h2 : scaled ≠ 2^n
        have h2n_eq : (↑(2^n : ℕ) : ℝ) = (2 : ℝ)^n := by norm_cast
        have h2n_eq' : (↑(2^n : ℤ) : ℝ) = (2 : ℝ)^n := by norm_cast
        rw [h2n_eq']
        exact lt_of_le_of_ne h1 h2
      -- floorNat < 2^n
      have hfloorNat_lt : floorNat < 2^n := by
        have h1 : (floorNat : ℤ) < 2^n := by rw [hfloorNat_eq]; exact hfloor_lt
        exact_mod_cast h1
      -- floorNat is odd, so floorNat = 2k + 1
      have hexists_k : ∃ k : ℕ, floorNat = 2 * k + 1 := by
        use floorNat / 2
        have h1 : floorNat % 2 = 1 := hodd
        omega
      obtain ⟨k, hk_eq⟩ := hexists_k
      -- k < 2^(n-1)
      have hk_lt : k < 2^(n-1) := by
        have h1 : 2 * k + 1 < 2^n := by rw [← hk_eq]; exact hfloorNat_lt
        have h2 : 2 * 2^(n-1) = 2^n := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
        omega
      -- Provide k as witness
      use ⟨k, hk_lt⟩
      simp
      constructor
      · -- (2k+1)/2^n < ω
        rw [div_lt_iff₀ h2n_pos]
        -- Need: 2k+1 < scaled
        have hfloor_lt_scaled : (↑⌊scaled⌋ : ℝ) < scaled := by
          have hle : (↑⌊scaled⌋ : ℝ) ≤ scaled := Int.floor_le scaled
          linarith
        calc (2*k + 1 : ℝ)
            = ↑(2*k + 1 : ℕ) := by push_cast; ring
          _ = (floorNat : ℝ) := by rw [hk_eq]
          _ = (⌊scaled⌋ : ℝ) := hfloorNat_eq_real
          _ < scaled := hfloor_lt_scaled
      · -- ω ≤ (2k+2)/2^n
        rw [le_div_iff₀ h2n_pos]
        -- Need: ω * 2^n ≤ 2k+2
        have hscaled_lt_floor_succ : scaled < ↑⌊scaled⌋ + 1 := Int.lt_floor_add_one scaled
        have h_calc : scaled < (2*k + 2 : ℝ) := calc scaled
            < ↑⌊scaled⌋ + 1 := hscaled_lt_floor_succ
          _ = (floorNat : ℝ) + 1 := by rw [hfloorNat_eq_real]
          _ = (2*k + 1 : ℝ) + 1 := by rw [hk_eq]; norm_cast
          _ = (2*k + 2 : ℝ) := by ring
        linarith
    · -- Integer case: digit = (⌊scaled⌋.toNat - 1) % 2 = 1
      push Not at hint
      simp only [dyadicDigit, hn_ne, ↓reduceIte] at hdigit
      -- Since scaled - ⌊scaled⌋ ≤ 0 and ⌊scaled⌋ ≤ scaled, we have scaled = ⌊scaled⌋
      have hscaled_eq : scaled = ↑⌊scaled⌋ := by
        have hle : (↑⌊scaled⌋ : ℝ) ≤ scaled := Int.floor_le scaled
        linarith
      -- The condition in dyadicDigit is now ¬(scaled - ⌊scaled⌋ > 0), i.e., false
      have hcond_false : ¬(ω * 2^n - ↑⌊ω * 2^n⌋ > 0) := by
        rw [← hscaled_def]; push Not; exact hint
      rw [if_neg hcond_false] at hdigit
      -- (⌊scaled⌋.toNat - 1) % 2 = 1
      -- floorNat > 0 (since scaled > 0 and scaled is an integer)
      have hfloorNat_pos : floorNat > 0 := by
        -- Since scaled = ⌊scaled⌋ and scaled > 0, we have ⌊scaled⌋ > 0
        have h1 : (0 : ℝ) < ↑⌊scaled⌋ := by rw [← hscaled_eq]; exact hscaled_pos
        have h2 : (0 : ℤ) < ⌊scaled⌋ := by
          have hle : (0 : ℝ) = ((0 : ℤ) : ℝ) := by norm_cast
          rw [hle] at h1
          exact_mod_cast h1
        have h3 : 0 < (floorNat : ℤ) := by rw [hfloorNat_eq]; exact h2
        omega
      -- floorNat ≤ 2^n
      have hfloorNat_le : floorNat ≤ 2^n := by
        have h1 : (floorNat : ℝ) = scaled := by
          rw [hfloorNat_eq_real]; exact hscaled_eq.symm
        have h2 : (floorNat : ℝ) ≤ 2^n := by rw [h1]; exact hscaled_le
        exact_mod_cast h2
      -- (floorNat - 1) % 2 = 1, so floorNat - 1 is odd, so floorNat is even
      have heven : (floorNat - 1) % 2 = 1 := hdigit
      -- floorNat = 2k + 2 for some k
      have hexists_k : ∃ k : ℕ, floorNat = 2 * k + 2 := by
        use (floorNat - 1) / 2
        have h1 : (floorNat - 1) % 2 = 1 := heven
        omega
      obtain ⟨k, hk_eq⟩ := hexists_k
      -- k < 2^(n-1)
      have hk_lt : k < 2^(n-1) := by
        have h1 : 2 * k + 2 ≤ 2^n := by rw [← hk_eq]; exact hfloorNat_le
        have h2 : 2 * 2^(n-1) = 2^n := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
        omega
      -- Provide k as witness
      use ⟨k, hk_lt⟩
      simp
      constructor
      · -- (2k+1)/2^n < ω
        rw [div_lt_iff₀ h2n_pos]
        -- scaled = floorNat = 2k+2 > 2k+1
        calc (2*k + 1 : ℝ)
            < (2*k + 2 : ℝ) := by linarith
          _ = ↑(2*k + 2 : ℕ) := by push_cast; ring
          _ = (floorNat : ℝ) := by rw [hk_eq]
          _ = (⌊scaled⌋ : ℝ) := hfloorNat_eq_real
          _ = scaled := hscaled_eq.symm
      · -- ω ≤ (2k+2)/2^n
        rw [le_div_iff₀ h2n_pos]
        -- scaled = 2k+2, and scaled = ω * 2^n
        have hscaled_eq_floor : ω * 2^n = (floorNat : ℝ) := by
          rw [← hscaled_def, hscaled_eq, hfloorNat_eq_real]
        rw [hscaled_eq_floor, hk_eq]
        norm_cast

/-- digitZeroIntervals n = digitSet n 0 for n ≥ 1. -/
theorem digitZeroIntervals_eq_digitSet (n : ℕ) (hn : n ≥ 1) :
    digitZeroIntervals n = digitSet n 0 := by
  ext ω
  simp only [digitZeroIntervals, digitSet, Set.mem_iUnion, Set.mem_Ioc,
             Set.mem_ofPred_eq, halfOpenUnit]
  constructor
  · intro ⟨k, hk1, hk2⟩
    constructor
    · exact digitZeroIntervals_subset_halfOpenUnit n hn (Set.mem_iUnion.mpr ⟨k, Set.mem_Ioc.mpr ⟨hk1, hk2⟩⟩)
    · exact dyadicDigit_eq_zero_of_mem_interval n hn k.val ω hk1 hk2
  · -- digitSet → digitZeroIntervals
    intro ⟨⟨hω_pos, hω_le1⟩, hdigit⟩
    -- If dyadicDigit n ω = 0, then ω is in some ((2k)/2^n, (2k+1)/2^n]
    have h2n_pos : (0 : ℝ) < 2^n := by positivity
    set scaled := ω * 2^n with hscaled_def
    -- scaled ∈ (0, 2^n]
    have hscaled_pos : 0 < scaled := by positivity
    have hscaled_le : scaled ≤ 2^n := by
      rw [hscaled_def]; calc ω * 2^n ≤ 1 * 2^n := by nlinarith
        _ = 2^n := one_mul _
    -- n ≠ 0
    have hn_ne : n ≠ 0 := by omega
    have hfloor_nonneg : 0 ≤ ⌊scaled⌋ := Int.floor_nonneg.mpr (le_of_lt hscaled_pos)
    set floorNat := ⌊scaled⌋.toNat with hfloorNat_def
    have hfloorNat_eq : (floorNat : ℤ) = ⌊scaled⌋ := Int.toNat_of_nonneg hfloor_nonneg
    have hfloorNat_eq_real : (floorNat : ℝ) = (⌊scaled⌋ : ℝ) := by
      have h1 : (floorNat : ℤ) = ⌊scaled⌋ := hfloorNat_eq
      exact_mod_cast h1
    -- Case split on whether scaled is an integer
    by_cases hint : scaled - ↑⌊scaled⌋ > 0
    · -- Non-integer case: digit = ⌊scaled⌋.toNat % 2 = 0
      simp only [dyadicDigit, hn_ne, ↓reduceIte] at hdigit
      rw [if_pos hint] at hdigit
      -- ⌊scaled⌋.toNat % 2 = 0, so ⌊scaled⌋.toNat is even
      have heven : floorNat % 2 = 0 := hdigit
      -- ⌊scaled⌋ < 2^n since scaled ≤ 2^n and scaled is not an integer
      have hfloor_lt : ⌊scaled⌋ < (2^n : ℤ) := by
        rw [Int.floor_lt]
        have h1 : scaled ≤ 2^n := hscaled_le
        have h2 : scaled ≠ 2^n := by
          intro heq
          have hfrac : scaled - ↑⌊scaled⌋ = 0 := by
            rw [heq]
            have h2n_nat : (2 : ℝ)^n = ↑(2^n : ℕ) := by norm_cast
            have hfl : ⌊(↑(2^n : ℕ) : ℝ)⌋ = ↑(2^n : ℕ) := Int.floor_natCast (2^n)
            rw [h2n_nat, hfl]
            simp only [Int.cast_natCast, sub_self]
          linarith
        have h2n_eq' : (↑(2^n : ℤ) : ℝ) = (2 : ℝ)^n := by norm_cast
        rw [h2n_eq']
        exact lt_of_le_of_ne h1 h2
      -- floorNat < 2^n
      have hfloorNat_lt : floorNat < 2^n := by
        have h1 : (floorNat : ℤ) < 2^n := by rw [hfloorNat_eq]; exact hfloor_lt
        exact_mod_cast h1
      -- floorNat is even, so floorNat = 2k
      have hexists_k : ∃ k : ℕ, floorNat = 2 * k := by
        use floorNat / 2
        have h1 : floorNat % 2 = 0 := heven
        omega
      obtain ⟨k, hk_eq⟩ := hexists_k
      -- k < 2^(n-1)
      have hk_lt : k < 2^(n-1) := by
        have h1 : 2 * k < 2^n := by rw [← hk_eq]; exact hfloorNat_lt
        have h2 : 2 * 2^(n-1) = 2^n := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
        omega
      -- Provide k as witness
      use ⟨k, hk_lt⟩
      simp
      constructor
      · -- (2k)/2^n < ω
        rw [div_lt_iff₀ h2n_pos]
        -- Need: 2k < scaled
        have hfloor_lt_scaled : (↑⌊scaled⌋ : ℝ) < scaled := by
          have hle : (↑⌊scaled⌋ : ℝ) ≤ scaled := Int.floor_le scaled
          linarith
        calc (2*k : ℝ)
            = ↑(2*k : ℕ) := by push_cast; ring
          _ = (floorNat : ℝ) := by rw [hk_eq]
          _ = (⌊scaled⌋ : ℝ) := hfloorNat_eq_real
          _ < scaled := hfloor_lt_scaled
      · -- ω ≤ (2k+1)/2^n
        rw [le_div_iff₀ h2n_pos]
        -- Need: ω * 2^n ≤ 2k+1
        have hscaled_lt_floor_succ : scaled < ↑⌊scaled⌋ + 1 := Int.lt_floor_add_one scaled
        have h_calc : scaled < (2*k + 1 : ℝ) := calc scaled
            < ↑⌊scaled⌋ + 1 := hscaled_lt_floor_succ
          _ = (floorNat : ℝ) + 1 := by rw [hfloorNat_eq_real]
          _ = (2*k : ℝ) + 1 := by rw [hk_eq]; norm_cast
          _ = (2*k + 1 : ℝ) := by ring
        linarith
    · -- Integer case: digit = (⌊scaled⌋.toNat - 1) % 2 = 0
      push Not at hint
      simp only [dyadicDigit, hn_ne, ↓reduceIte] at hdigit
      -- Since scaled - ⌊scaled⌋ ≤ 0 and ⌊scaled⌋ ≤ scaled, we have scaled = ⌊scaled⌋
      have hscaled_eq : scaled = ↑⌊scaled⌋ := by
        have hle : (↑⌊scaled⌋ : ℝ) ≤ scaled := Int.floor_le scaled
        linarith
      -- The condition in dyadicDigit is now ¬(scaled - ⌊scaled⌋ > 0)
      have hcond_false : ¬(ω * 2^n - ↑⌊ω * 2^n⌋ > 0) := by
        rw [← hscaled_def]; push Not; exact hint
      rw [if_neg hcond_false] at hdigit
      -- (⌊scaled⌋.toNat - 1) % 2 = 0
      -- floorNat > 0 (since scaled > 0 and scaled is an integer)
      have hfloorNat_pos : floorNat > 0 := by
        have h1 : (0 : ℝ) < ↑⌊scaled⌋ := by rw [← hscaled_eq]; exact hscaled_pos
        have h2 : (0 : ℤ) < ⌊scaled⌋ := by
          have hle : (0 : ℝ) = ((0 : ℤ) : ℝ) := by norm_cast
          rw [hle] at h1
          exact_mod_cast h1
        have h3 : 0 < (floorNat : ℤ) := by rw [hfloorNat_eq]; exact h2
        omega
      -- floorNat ≤ 2^n
      have hfloorNat_le : floorNat ≤ 2^n := by
        have h1 : (floorNat : ℝ) = scaled := by
          rw [hfloorNat_eq_real]; exact hscaled_eq.symm
        have h2 : (floorNat : ℝ) ≤ 2^n := by rw [h1]; exact hscaled_le
        exact_mod_cast h2
      -- (floorNat - 1) % 2 = 0, so floorNat - 1 is even, so floorNat is odd
      have hodd : (floorNat - 1) % 2 = 0 := hdigit
      -- floorNat = 2k + 1 for some k
      have hexists_k : ∃ k : ℕ, floorNat = 2 * k + 1 := by
        use (floorNat - 1) / 2
        have h1 : (floorNat - 1) % 2 = 0 := hodd
        omega
      obtain ⟨k, hk_eq⟩ := hexists_k
      -- k < 2^(n-1)
      have hk_lt : k < 2^(n-1) := by
        have h1 : 2 * k + 1 ≤ 2^n := by rw [← hk_eq]; exact hfloorNat_le
        have h2 : 2 * 2^(n-1) = 2^n := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
        omega
      -- Provide k as witness
      use ⟨k, hk_lt⟩
      simp
      constructor
      · -- (2k)/2^n < ω
        rw [div_lt_iff₀ h2n_pos]
        -- scaled = floorNat = 2k+1 > 2k
        calc (2*k : ℝ)
            < (2*k + 1 : ℝ) := by linarith
          _ = ↑(2*k + 1 : ℕ) := by push_cast; ring
          _ = (floorNat : ℝ) := by rw [hk_eq]
          _ = (⌊scaled⌋ : ℝ) := hfloorNat_eq_real
          _ = scaled := hscaled_eq.symm
      · -- ω ≤ (2k+1)/2^n
        rw [le_div_iff₀ h2n_pos]
        -- scaled = 2k+1
        have hscaled_eq_floor : ω * 2^n = (floorNat : ℝ) := by
          rw [← hscaled_def, hscaled_eq, hfloorNat_eq_real]
        rw [hscaled_eq_floor, hk_eq]
        norm_cast

/-- The digit set is measurable.
For n ≥ 1, digitSet n b equals the corresponding digit intervals which are measurable.
For n = 0 or b ≥ 2, digitSet n b is either empty or halfOpenUnit. -/
theorem digitSet_measurableSet (n : ℕ) (b : ℕ) : MeasurableSet (digitSet n b) := by
  -- Handle b ≥ 2 first: digitSet is empty
  by_cases hb2 : b ≥ 2
  · have h : digitSet n b = ∅ := by
      ext x
      simp only [digitSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨_, hd⟩
      have hle := dyadicDigit_le_one n x
      omega
    rw [h]
    exact MeasurableSet.empty
  push Not at hb2
  -- Now b ∈ {0, 1}
  have hb01 : b = 0 ∨ b = 1 := by omega
  by_cases hn : n ≥ 1
  · -- n ≥ 1: use the interval characterization
    rcases hb01 with hb0 | hb1
    · -- b = 0
      rw [hb0, ← digitZeroIntervals_eq_digitSet n hn]
      exact digitZeroIntervals_measurableSet n
    · -- b = 1
      rw [hb1, ← digitOneIntervals_eq_digitSet n hn]
      exact digitOneIntervals_measurableSet n
  · -- n = 0: dyadicDigit 0 ω = 0 for all ω
    push Not at hn
    have hn0 : n = 0 := by omega
    rcases hb01 with hb0 | hb1
    · -- n = 0, b = 0: digitSet 0 0 = halfOpenUnit
      simp only [hn0, hb0, digitSet, dyadicDigit, ↓reduceIte]
      convert halfOpenUnit_measurableSet using 1
      ext x
      simp only [Set.mem_ofPred_eq, and_true]
    · -- n = 0, b = 1: digitSet 0 1 = ∅ (since digit is always 0)
      simp only [hn0, hb1, digitSet, dyadicDigit, ↓reduceIte]
      convert MeasurableSet.empty using 1
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _; omega

/-- The digit-1 intervals are pairwise disjoint. -/
theorem digitOneIntervals_pairwiseDisjoint (n : ℕ) :
    ∀ i j : Fin (2^(n-1)), i ≠ j →
      Disjoint (Set.Ioc ((2*i.val + 1 : ℝ) / 2^n) ((2*i.val + 2 : ℝ) / 2^n))
               (Set.Ioc ((2*j.val + 1 : ℝ) / 2^n) ((2*j.val + 2 : ℝ) / 2^n)) := by
  intro i j hij
  rw [Set.disjoint_iff]
  intro x ⟨hi, hj⟩
  simp only [Set.mem_Ioc] at hi hj
  have hpos : (0 : ℝ) < 2^n := by positivity
  -- The intervals don't overlap unless i = j
  by_cases h : i.val < j.val
  · -- i < j, so interval i is entirely to the left of interval j
    have hnat : 2*i.val + 2 ≤ 2*j.val + 1 := by omega
    have hbound : (2*i.val + 2 : ℝ) ≤ 2*j.val + 1 := by exact_mod_cast hnat
    have hdiv : (2*i.val + 2 : ℝ) / 2^n ≤ (2*j.val + 1 : ℝ) / 2^n :=
      div_le_div_of_nonneg_right hbound (le_of_lt hpos)
    linarith [hi.1, hi.2, hj.1, hj.2]
  · push Not at h
    have hne : j.val < i.val := Nat.lt_of_le_of_ne h (fun heq => hij (Fin.ext heq.symm))
    have hnat : 2*j.val + 2 ≤ 2*i.val + 1 := by omega
    have hbound : (2*j.val + 2 : ℝ) ≤ 2*i.val + 1 := by exact_mod_cast hnat
    have hdiv : (2*j.val + 2 : ℝ) / 2^n ≤ (2*i.val + 1 : ℝ) / 2^n :=
      div_le_div_of_nonneg_right hbound (le_of_lt hpos)
    linarith [hi.1, hi.2, hj.1, hj.2]

/-- The digit-0 intervals are pairwise disjoint. -/
theorem digitZeroIntervals_pairwiseDisjoint (n : ℕ) :
    ∀ i j : Fin (2^(n-1)), i ≠ j →
      Disjoint (Set.Ioc ((2*i.val : ℝ) / 2^n) ((2*i.val + 1 : ℝ) / 2^n))
               (Set.Ioc ((2*j.val : ℝ) / 2^n) ((2*j.val + 1 : ℝ) / 2^n)) := by
  intro i j hij
  rw [Set.disjoint_iff]
  intro x ⟨hi, hj⟩
  simp only [Set.mem_Ioc] at hi hj
  have hpos : (0 : ℝ) < 2^n := by positivity
  by_cases h : i.val < j.val
  · have hnat : 2*i.val + 1 ≤ 2*j.val := by omega
    have hbound : (2*i.val + 1 : ℝ) ≤ 2*j.val := by exact_mod_cast hnat
    have hdiv : (2*i.val + 1 : ℝ) / 2^n ≤ (2*j.val : ℝ) / 2^n :=
      div_le_div_of_nonneg_right hbound (le_of_lt hpos)
    linarith [hi.1, hi.2, hj.1, hj.2]
  · push Not at h
    have hne : j.val < i.val := Nat.lt_of_le_of_ne h (fun heq => hij (Fin.ext heq.symm))
    have hnat : 2*j.val + 1 ≤ 2*i.val := by omega
    have hbound : (2*j.val + 1 : ℝ) ≤ 2*i.val := by exact_mod_cast hnat
    have hdiv : (2*j.val + 1 : ℝ) / 2^n ≤ (2*i.val : ℝ) / 2^n :=
      div_le_div_of_nonneg_right hbound (le_of_lt hpos)
    linarith [hi.1, hi.2, hj.1, hj.2]

/-- Volume of the digit-1 intervals is 1/2. -/
theorem volume_digitOneIntervals (n : ℕ) (hn : n ≥ 1) :
    volume (digitOneIntervals n) = 1/2 := by
  simp only [digitOneIntervals]
  have hpw : ∀ i j : Fin (2^(n-1)), i ≠ j →
      Disjoint (Set.Ioc ((2*i.val + 1 : ℝ) / 2^n) ((2*i.val + 2 : ℝ) / 2^n))
               (Set.Ioc ((2*j.val + 1 : ℝ) / 2^n) ((2*j.val + 2 : ℝ) / 2^n)) :=
    digitOneIntervals_pairwiseDisjoint n
  rw [measure_iUnion hpw (fun _ => measurableSet_Ioc)]
  simp only [Real.volume_Ioc]
  have hcalc : ∀ k : Fin (2^(n-1)),
      (2*k.val + 2 : ℝ) / 2^n - (2*k.val + 1 : ℝ) / 2^n = 1 / 2^n := by
    intro k
    field_simp
    ring
  simp_rw [hcalc]
  simp_rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^n)]
  simp only [ENNReal.ofReal_one]
  simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simp only [nsmul_eq_mul, mul_one_div]
  -- Goal: ↑(2^(n-1)) / (2:ℝ≥0∞)^n = 1/2
  have h2ne : (2 : ℝ≥0∞)^(n-1) ≠ 0 := by simp
  have h2netop : (2 : ℝ≥0∞)^(n-1) ≠ ⊤ := by simp
  -- Use 1 * 2^(n-1) / (2 * 2^(n-1)) = 1 / 2
  conv_lhs =>
    rw [show (↑(2 ^ (n - 1) : ℕ) : ℝ≥0∞) = 1 * (2 : ℝ≥0∞)^(n-1) by
          simp only [one_mul]; norm_cast]
    rw [show (2 : ℝ≥0∞)^n = 2 * 2^(n-1) by
          conv_lhs => rw [← hn1]
          rw [pow_succ, mul_comm]]
  exact ENNReal.mul_div_mul_right 1 2 h2ne h2netop

/-- Volume of the digit-0 intervals is 1/2. -/
theorem volume_digitZeroIntervals (n : ℕ) (hn : n ≥ 1) :
    volume (digitZeroIntervals n) = 1/2 := by
  simp only [digitZeroIntervals]
  have hpw : ∀ i j : Fin (2^(n-1)), i ≠ j →
      Disjoint (Set.Ioc ((2*i.val : ℝ) / 2^n) ((2*i.val + 1 : ℝ) / 2^n))
               (Set.Ioc ((2*j.val : ℝ) / 2^n) ((2*j.val + 1 : ℝ) / 2^n)) :=
    digitZeroIntervals_pairwiseDisjoint n
  rw [measure_iUnion hpw (fun _ => measurableSet_Ioc)]
  simp only [Real.volume_Ioc]
  have hcalc : ∀ k : Fin (2^(n-1)),
      (2*k.val + 1 : ℝ) / 2^n - (2*k.val : ℝ) / 2^n = 1 / 2^n := by
    intro k
    field_simp
    ring
  simp_rw [hcalc]
  simp_rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^n)]
  simp only [ENNReal.ofReal_one]
  simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simp only [nsmul_eq_mul, mul_one_div]
  -- Goal: ↑(2^(n-1)) / (2:ℝ≥0∞)^n = 1/2
  have h2ne : (2 : ℝ≥0∞)^(n-1) ≠ 0 := by simp
  have h2netop : (2 : ℝ≥0∞)^(n-1) ≠ ⊤ := by simp
  -- Use 1 * 2^(n-1) / (2 * 2^(n-1)) = 1 / 2
  conv_lhs =>
    rw [show (↑(2 ^ (n - 1) : ℕ) : ℝ≥0∞) = 1 * (2 : ℝ≥0∞)^(n-1) by
          simp only [one_mul]; norm_cast]
    rw [show (2 : ℝ≥0∞)^n = 2 * 2^(n-1) by
          conv_lhs => rw [← hn1]
          rw [pow_succ, mul_comm]]
  exact ENNReal.mul_div_mul_right 1 2 h2ne h2netop

/-- Each digit set has measure 1/2.
This follows from the fact that the nth digit is 1 on exactly half of the unit interval. -/
theorem volume_digitSet_one (n : ℕ) (hn : n ≥ 1) :
    volume (digitSet n 1) = 1/2 := by
  -- Key insight: use bounds from both directions
  -- digitOneIntervals n ⊆ digitSet n 1, so volume(digitSet n 1) ≥ 1/2
  -- digitZeroIntervals n ⊆ digitSet n 0, so volume(digitSet n 0) ≥ 1/2
  -- But volume(digitSet n 0) + volume(digitSet n 1) = 1
  -- Therefore both must equal exactly 1/2

  -- Forward inclusions (from the proved direction of the eq theorems)
  have h_one_sub : digitOneIntervals n ⊆ digitSet n 1 := by
    intro ω hω
    rw [digitOneIntervals_eq_digitSet n hn] at hω
    exact hω
  have h_zero_sub : digitZeroIntervals n ⊆ digitSet n 0 := by
    intro ω hω
    rw [digitZeroIntervals_eq_digitSet n hn] at hω
    exact hω

  -- Volumes of interval sets
  have h_vol_one_int : volume (digitOneIntervals n) = 1/2 := volume_digitOneIntervals n hn
  have h_vol_zero_int : volume (digitZeroIntervals n) = 1/2 := volume_digitZeroIntervals n hn

  -- Lower bounds from inclusions
  have h_lb1 : volume (digitSet n 1) ≥ 1/2 := by
    calc volume (digitSet n 1) ≥ volume (digitOneIntervals n) := measure_mono h_one_sub
         _ = 1/2 := h_vol_one_int
  have h_lb0 : volume (digitSet n 0) ≥ 1/2 := by
    calc volume (digitSet n 0) ≥ volume (digitZeroIntervals n) := measure_mono h_zero_sub
         _ = 1/2 := h_vol_zero_int

  -- Partition property gives total = 1
  have h_union := digitSet_union n hn
  have h_disj := digitSet_disjoint n
  have h_meas1 := digitSet_measurableSet n 1
  have h_add : volume (digitSet n 0 ∪ digitSet n 1) = volume (digitSet n 0) + volume (digitSet n 1) :=
    measure_union h_disj h_meas1
  rw [h_union, volume_halfOpenUnit] at h_add

  -- Now we have: v0 + v1 = 1, v0 ≥ 1/2, v1 ≥ 1/2
  -- This forces v0 = v1 = 1/2
  have h_ub1 : volume (digitSet n 1) ≤ 1/2 := by
    have h : volume (digitSet n 0) + volume (digitSet n 1) = 1 := h_add.symm
    -- From v0 ≥ 1/2 and v0 + v1 = 1, we get v1 ≤ 1/2
    have hne0 : volume (digitSet n 0) ≠ ⊤ := by
      have hsub : digitSet n 0 ⊆ halfOpenUnit := digitSet_subset n 0
      have hle : volume (digitSet n 0) ≤ volume halfOpenUnit := measure_mono hsub
      rw [volume_halfOpenUnit] at hle
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    -- v1 = 1 - v0 ≤ 1 - 1/2 = 1/2
    have h_eq : volume (digitSet n 1) = 1 - volume (digitSet n 0) := by
      rw [← h, ENNReal.add_sub_cancel_left hne0]
    rw [h_eq]
    -- 1 - v0 ≤ 1/2 when v0 ≥ 1/2
    calc (1 : ℝ≥0∞) - volume (digitSet n 0)
        ≤ 1 - 1/2 := tsub_le_tsub_left h_lb0 1
      _ = 1/2 := by norm_num

  -- Conclude
  exact le_antisymm h_ub1 h_lb1

/-- Each digit set has measure 1/2. -/
theorem volume_digitSet_zero (n : ℕ) (hn : n ≥ 1) :
    volume (digitSet n 0) = 1/2 := by
  -- Derive from volume_digitSet_one using the partition property
  have h_union := digitSet_union n hn
  have h_disj := digitSet_disjoint n
  have h_vol : volume halfOpenUnit = 1 := volume_halfOpenUnit
  have h_meas1 := digitSet_measurableSet n 1
  have h_add : volume (digitSet n 0 ∪ digitSet n 1) = volume (digitSet n 0) + volume (digitSet n 1) :=
    measure_union h_disj h_meas1
  rw [h_union, h_vol] at h_add
  have h_one := volume_digitSet_one n hn
  -- h_add : 1 = volume (digitSet n 0) + volume (digitSet n 1)
  -- h_one : volume (digitSet n 1) = 1/2
  -- Goal: volume (digitSet n 0) = 1/2
  rw [h_one] at h_add
  -- h_add : 1 = volume (digitSet n 0) + 1/2
  have h_half_ne_top : (1/2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have : volume (digitSet n 0) + 1/2 = 1 := h_add.symm
  calc volume (digitSet n 0)
      = volume (digitSet n 0) + 1/2 - 1/2 := by rw [ENNReal.add_sub_cancel_right h_half_ne_top]
    _ = 1 - 1/2 := by rw [this]
    _ = 1/2 := by norm_num

/-! ## Probability Theory Interpretation

The probability P(A) for a finite union of disjoint intervals is defined as the
sum of their lengths. This is the restriction of Lebesgue measure.
-/

/-- Probability measure on (0,1] is Lebesgue measure restricted to this set.
Since volume(0,1] = 1, this is already a probability measure. -/
def probMeasureUnit : Measure ℝ := volume.restrict halfOpenUnit

/-- The probability measure is indeed a probability measure. -/
theorem probMeasureUnit_isProbabilityMeasure : IsProbabilityMeasure probMeasureUnit := by
  constructor
  simp only [probMeasureUnit, Measure.restrict_apply_univ, halfOpenUnit, Real.volume_Ioc]
  norm_num

/-! ## The Weak Law of Large Numbers

Theorem 1.1: For each ε > 0,
  lim_{n→∞} P{ω : |S_n(ω)/n - 1/2| ≥ ε} = 0

This is the weak law of large numbers for the binary digits.
-/

/-- The event that the empirical frequency deviates from 1/2 by at least ε. -/
def deviationEvent (n : ℕ) (ε : ℝ) : Set ℝ :=
  {ω ∈ halfOpenUnit | |((sumDigits n ω : ℝ) / n) - 1/2| ≥ ε}

/-- The level set of sumDigits on halfOpenUnit. -/
def sumDigitsLevelSet (n k : ℕ) : Set ℝ :=
  {ω ∈ halfOpenUnit | sumDigits n ω = k}

/-- sumDigitsLevelSet is contained in halfOpenUnit. -/
theorem sumDigitsLevelSet_subset (n k : ℕ) : sumDigitsLevelSet n k ⊆ halfOpenUnit := by
  intro ω hω
  exact hω.1

/-- sumDigits n ω ≤ n (each digit is 0 or 1). -/
theorem sumDigits_le (n : ℕ) (ω : ℝ) : sumDigits n ω ≤ n := by
  unfold sumDigits
  calc (Finset.range n).sum (fun i => dyadicDigit (i + 1) ω)
      ≤ (Finset.range n).sum (fun _ => 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact dyadicDigit_le_one (i + 1) ω
    _ = n := by simp [Finset.card_range]

/-- sumDigits is monotone in n: m ≤ n → sumDigits m ω ≤ sumDigits n ω -/
theorem sumDigits_mono {m n : ℕ} (hmn : m ≤ n) (ω : ℝ) : sumDigits m ω ≤ sumDigits n ω := by
  unfold sumDigits
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono hmn

/-- The difference sumDigits n ω - sumDigits m ω is at most n - m for m ≤ n. -/
theorem sumDigits_diff_le {m n : ℕ} (hmn : m ≤ n) (ω : ℝ) :
    sumDigits n ω - sumDigits m ω ≤ n - m := by
  -- sumDigits n ω = sumDigits m ω + Σ_{i=m}^{n-1} d_{i+1}(ω)
  -- Each digit is 0 or 1, so the sum of n - m digits is at most n - m
  unfold sumDigits
  rw [← Finset.sum_range_add_sum_Ico _ hmn]
  simp only [add_tsub_cancel_left]
  calc ((Finset.Ico m n).sum fun i => dyadicDigit (i + 1) ω)
      ≤ (Finset.Ico m n).sum (fun _ => 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact dyadicDigit_le_one (i + 1) ω
    _ = Finset.card (Finset.Ico m n) := by simp
    _ = n - m := Nat.card_Ico m n

/-- The level set for k > n is empty. -/
theorem sumDigitsLevelSet_empty_of_gt (n k : ℕ) (hk : k > n) :
    sumDigitsLevelSet n k = ∅ := by
  ext ω
  simp only [sumDigitsLevelSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  have := sumDigits_le n ω
  omega

/-- A digit configuration for n digits specifies which digits are 1.
    This is represented as a function from Fin n to Bool. -/
def digitConfiguration (n : ℕ) (config : Fin n → Bool) : Set ℝ :=
  ⋂ i : Fin n, digitSet (i.val + 1) (if config i then 1 else 0)

/-- Each digit configuration is measurable. -/
theorem digitConfiguration_measurableSet (n : ℕ) (config : Fin n → Bool) :
    MeasurableSet (digitConfiguration n config) := by
  unfold digitConfiguration
  apply MeasurableSet.iInter
  intro i
  exact digitSet_measurableSet (i.val + 1) (if config i then 1 else 0)

/-- Each digit configuration for n ≥ 1 is a subset of halfOpenUnit. -/
theorem digitConfiguration_subset (n : ℕ) (hn : n ≥ 1) (config : Fin n → Bool) :
    digitConfiguration n config ⊆ halfOpenUnit := by
  intro ω hω
  simp only [digitConfiguration, Set.mem_iInter] at hω
  have h := hω ⟨0, hn⟩
  exact digitSet_subset 1 (if config ⟨0, hn⟩ then 1 else 0) h

/-- The level set is measurable. This is the key measurability lemma.
    The level set {ω ∈ halfOpenUnit | sumDigits n ω = k} is a finite union of
    digit configurations, each of which is a finite intersection of measurable digit sets.
    - For k > n: the set is empty (sumDigits n ≤ n always)
    - For n = 0: the set is halfOpenUnit (if k = 0) or empty (if k > 0)
    - For n ≥ 1, k ≤ n: the set is ⋃ (configs with k ones) digitConfiguration
      This is a finite union of measurable sets, hence measurable. -/
theorem sumDigitsLevelSet_measurableSet (n k : ℕ) : MeasurableSet (sumDigitsLevelSet n k) := by
  by_cases hk : k > n
  · rw [sumDigitsLevelSet_empty_of_gt n k hk]
    exact MeasurableSet.empty
  · push Not at hk
    by_cases hn : n = 0
    · -- For n = 0, sumDigits 0 ω = 0 for all ω
      subst hn
      simp only [sumDigitsLevelSet, sumDigits, Finset.range_zero, Finset.sum_empty]
      by_cases hk' : k = 0
      · subst hk'
        convert halfOpenUnit_measurableSet using 1
        ext ω; simp only [Set.mem_ofPred_eq, and_true]
      · convert MeasurableSet.empty using 1
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _; omega
    · -- For n ≥ 1, k ≤ n: the level set is a finite union of digit configurations
      -- Each configuration specifies which k of the n digits are 1
      -- This is a finite union of finite intersections of measurable sets
      have h_eq : sumDigitsLevelSet n k =
          ⋃ config ∈ (Finset.univ : Finset (Fin n → Bool)).filter
              (fun c => (Finset.univ.filter (fun i : Fin n => c i)).card = k),
            digitConfiguration n config := by
        ext ω
        simp only [sumDigitsLevelSet, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_filter,
                   Finset.mem_univ, true_and]
        constructor
        · -- Forward: ω ∈ level set → ω matches some config with k ones
          intro ⟨hω, hsum⟩
          -- Define config from ω's actual digits
          use fun i => decide (dyadicDigit (i.val + 1) ω = 1)
          -- Show ω matches the config (ω ∈ digitConfiguration)
          refine ⟨?_, ?_⟩
          · -- Show config has exactly k ones
            -- We need: (Finset.univ.filter (fun i => decide (d_i = 1))).card = k
            -- First show this equals sumDigits n ω
            have h_sum_eq : sumDigits n ω =
                (Finset.univ.filter fun i : Fin n => decide (dyadicDigit (i.val + 1) ω = 1)).card := by
              unfold sumDigits
              -- sumDigits = Σ i ∈ range n, dyadicDigit (i+1) ω
              -- Each digit is 0 or 1, so this equals the count of 1s
              have h1 : ∀ i ∈ Finset.range n, dyadicDigit (i + 1) ω =
                  if dyadicDigit (i + 1) ω = 1 then 1 else 0 := by
                intro i _
                rcases dyadicDigit_values (i + 1) ω with h | h <;> simp [h]
              rw [Finset.sum_congr rfl h1, Finset.sum_boole]
              -- Now show the cardinalities are equal via bijection
              -- {i ∈ range n | d_{i+1} = 1}.card = {j : Fin n | d_{j+1} = 1}.card
              have h_card_eq : (Finset.filter (fun i => dyadicDigit (i + 1) ω = 1) (Finset.range n)).card =
                  (Finset.filter (fun j : Fin n => decide (dyadicDigit (j.val + 1) ω = 1)) Finset.univ).card := by
                refine Finset.card_bij' (fun i hi => ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩)
                    (fun j _ => j.val) ?_ ?_ ?_ ?_
                · intro i hi
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
                  exact (Finset.mem_filter.mp hi).2
                · intro j hj
                  simp only [Finset.mem_filter, Finset.mem_range, Fin.is_lt, true_and]
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hj
                  exact hj
                · intro i _; rfl
                · intro j _; simp only [Fin.eta]
              exact h_card_eq
            rw [← h_sum_eq, hsum]
          · -- Show ω matches the config (ω ∈ digitConfiguration)
            unfold digitConfiguration
            simp only [Set.mem_iInter, digitSet, Set.mem_ofPred_eq]
            intro i
            constructor
            · exact hω
            · -- dyadicDigit (i.val + 1) ω = if decide(...) then 1 else 0
              by_cases h : dyadicDigit (i.val + 1) ω = 1
              · simp [h]
              · rcases dyadicDigit_values (i.val + 1) ω with hv | hv
                · simp [hv]
                · exact absurd hv h
        · -- Backward: ω matches config with k ones → ω ∈ level set
          intro ⟨config, hcard, hmatch⟩
          constructor
          · -- ω ∈ halfOpenUnit: follows from digitConfiguration ⊆ halfOpenUnit
            have hn' : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
            exact digitConfiguration_subset n hn' config hmatch
          · -- sumDigits n ω = k
            unfold digitConfiguration at hmatch
            simp only [Set.mem_iInter, digitSet, Set.mem_ofPred_eq] at hmatch
            -- Relate sumDigits to the cardinality of the filter set
            -- sumDigits = Σ_i d_i = Σ_i (if config ⟨i, _⟩ then 1 else 0) = card {i | config ⟨i, _⟩}
            -- = card {j : Fin n | config j} = k
            have h_sum : sumDigits n ω = (Finset.univ.filter fun j : Fin n => config j).card := by
              unfold sumDigits
              -- Use Fin.sum_univ_eq_sum_range to switch between Fin n and range n
              rw [← Fin.sum_univ_eq_sum_range]
              -- Now sum over Fin n
              have h_eq : ∀ j : Fin n, dyadicDigit (j.val + 1) ω = if config j then 1 else 0 :=
                fun j => (hmatch j).2
              simp_rw [h_eq]
              rw [Finset.sum_boole, Nat.cast_id]
            rw [h_sum, hcard]
      rw [h_eq]
      apply MeasurableSet.biUnion
      · exact Finset.countable_toSet _
      · intro config _
        exact digitConfiguration_measurableSet n config

/-- The deviation event is measurable. -/
theorem deviationEvent_measurableSet (n : ℕ) (ε : ℝ) :
    MeasurableSet (deviationEvent n ε) := by
  unfold deviationEvent
  by_cases hn : n = 0
  · -- For n = 0, 0/0 = 0 in Lean, so |0/0 - 1/2| = |0 - 1/2| = 1/2
    subst hn
    simp only [Nat.cast_zero, sumDigits, Finset.range_zero, Finset.sum_empty]
    -- The goal is now MeasurableSet {ω ∈ halfOpenUnit | |0/0 - 1/2| ≥ ε}
    -- Since 0/0 = 0 in ℝ, |0/0 - 1/2| = |-1/2| = 1/2
    have h_abs : |(0 : ℝ) / 0 - 1/2| = 1/2 := by norm_num
    by_cases hε : (1 : ℝ) / 2 ≥ ε
    · -- The set is halfOpenUnit since 1/2 ≥ ε means the condition is always satisfied
      convert halfOpenUnit_measurableSet using 1
      ext ω
      simp only [Set.mem_ofPred_eq, h_abs]
      exact ⟨fun h => h.1, fun h => ⟨h, hε⟩⟩
    · -- The set is empty since 1/2 < ε means the condition is never satisfied
      push Not at hε
      convert MeasurableSet.empty using 1
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, h_abs, iff_false, not_and, ge_iff_le,
                 not_le]
      intro _
      exact hε
  · -- For n ≥ 1, the deviation event is a finite union of level sets
    have h_eq : {ω ∈ halfOpenUnit | |((sumDigits n ω : ℝ) / n) - 1/2| ≥ ε}
              = ⋃ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => |(k : ℝ) / n - 1/2| ≥ ε),
                  sumDigitsLevelSet n k := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range,
                 sumDigitsLevelSet]
      constructor
      · intro ⟨hω, hdev⟩
        use sumDigits n ω
        refine ⟨⟨?_, hdev⟩, hω, rfl⟩
        have h := sumDigits_le n ω
        omega
      · intro ⟨k, ⟨_, hdev⟩, hω, hsum⟩
        refine ⟨hω, ?_⟩
        rw [hsum]
        exact hdev
    rw [h_eq]
    apply MeasurableSet.biUnion
    · -- The index set is countable (it's a finite subset of ℕ)
      have : Set.Countable ((Finset.range (n + 1)).filter (fun k : ℕ => |(k : ℝ) / n - 1/2| ≥ ε) : Set ℕ) :=
        Finset.countable_toSet _
      exact this
    · intro k _
      exact sumDigitsLevelSet_measurableSet n k

-- `weakLawOfLargeNumbers_binary` (Theorem 1.1) is proven at the end of the file —
-- its full statement and proof require helper lemmas defined there.  Any early usage
-- can reference the final theorem directly.

/-! ## The Strong Law of Large Numbers / Borel's Normal Number Theorem

Theorem 1.2 (Borel's Normal Number Theorem):
Almost every ω ∈ (0,1] is a normal number, meaning
  lim_{n→∞} S_n(ω)/n = 1/2

This is a much stronger result than the weak law.
-/

/-- A real number ω is normal (in base 2) if the empirical digit frequency converges to 1/2. -/
def IsNormal (ω : ℝ) : Prop :=
  Filter.Tendsto (fun n => (sumDigits n ω : ℝ) / n) Filter.atTop (nhds (1/2 : ℝ))

/-- The set of normal numbers in (0,1]. -/
def normalNumbers : Set ℝ := {ω ∈ halfOpenUnit | IsNormal ω}

/-- Helper: the set {ω ∈ halfOpenUnit | |S_n/n - 1/2| < ε} is measurable.
    This is halfOpenUnit \ deviationEvent n ε. -/
theorem smallDeviationSet_measurableSet (n : ℕ) (ε : ℝ) :
    MeasurableSet {ω ∈ halfOpenUnit | |((sumDigits n ω : ℝ) / n) - 1/2| < ε} := by
  by_cases hε : ε ≤ 0
  · -- For ε ≤ 0, the set is empty since |·| ≥ 0
    convert MeasurableSet.empty using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    intro _
    exact le_trans hε (abs_nonneg _)
  · push Not at hε
    -- For ε > 0, {ω ∈ H | |·| < ε} = H \ {ω ∈ H | |·| ≥ ε} = H \ deviationEvent
    have h_eq : {ω ∈ halfOpenUnit | |((sumDigits n ω : ℝ) / n) - 1/2| < ε}
              = halfOpenUnit \ deviationEvent n ε := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, deviationEvent, not_and, not_le]
      constructor
      · intro ⟨hω, hlt⟩
        exact ⟨hω, fun _ => hlt⟩
      · intro ⟨hω, hcond⟩
        exact ⟨hω, hcond hω⟩
    rw [h_eq]
    exact MeasurableSet.diff halfOpenUnit_measurableSet (deviationEvent_measurableSet n ε)

/-- The set of normal numbers is measurable.
    This follows from the characterization of limits via ε-N conditions with rational ε. -/
theorem normalNumbers_measurableSet : MeasurableSet normalNumbers := by
  -- normalNumbers = {ω ∈ halfOpenUnit | IsNormal ω}
  -- IsNormal ω ↔ S_n/n → 1/2 ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |S_n/n - 1/2| < ε
  -- Using rational approximation: ↔ ∀ k ≥ 1, ∃ N, ∀ n ≥ N, |S_n/n - 1/2| < 1/k
  -- So: normalNumbers = halfOpenUnit ∩ ⋂_{k≥1} ⋃_N ⋂_{n≥N} {ω ∈ halfOpenUnit | |S_n/n - 1/2| < 1/k}
  unfold normalNumbers IsNormal
  -- Use the metric space characterization of tendsto
  have h_tendsto_char : ∀ ω, Filter.Tendsto (fun n => (sumDigits n ω : ℝ) / n) Filter.atTop (nhds (1/2))
      ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |((sumDigits n ω : ℝ) / n) - 1/2| < ε := by
    intro ω
    rw [Metric.tendsto_atTop]
    simp only [Real.dist_eq]
  -- Rewrite using the characterization with countable intersections/unions
  have h_eq : {ω ∈ halfOpenUnit | Filter.Tendsto (fun n => (sumDigits n ω : ℝ) / n)
                                    Filter.atTop (nhds (1/2))}
            = ⋂ k : ℕ+, ⋃ N : ℕ, ⋂ n : {m : ℕ // m ≥ N},
                {ω ∈ halfOpenUnit | |((sumDigits n.val ω : ℝ) / n.val) - 1/2| < 1/(k : ℕ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ⟨hω, htend⟩ k
      rw [h_tendsto_char] at htend
      have hk : (0 : ℝ) < 1 / k := by positivity
      obtain ⟨N, hN⟩ := htend (1/k) hk
      exact ⟨N, fun ⟨n, hn⟩ => ⟨hω, hN n hn⟩⟩
    · intro hcond
      constructor
      · -- Get membership from any condition (k=1, N=0)
        have h := hcond ⟨1, one_pos⟩
        obtain ⟨N, hN⟩ := h
        exact (hN ⟨N, le_refl N⟩).1
      · rw [h_tendsto_char]
        intro ε hε
        -- Find k such that 1/k < ε using Archimedean property
        have ⟨k, hk⟩ := exists_nat_gt (1/ε)
        have hk_pos : 0 < k := by
          by_contra h
          push Not at h
          interval_cases k
          · simp only [Nat.cast_zero, one_div] at hk
            have : 0 < ε⁻¹ := by positivity
            linarith
        have hk_bound : 1/(k : ℝ) < ε := by
          have hk_pos : (k : ℝ) > 0 := by positivity
          exact (one_div_lt hk_pos hε).mpr hk
        obtain ⟨N, hN⟩ := hcond ⟨k, hk_pos⟩
        exact ⟨N, fun n hn => lt_trans (hN ⟨n, hn⟩).2 hk_bound⟩
  rw [h_eq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro ⟨n, _⟩
  exact smallDeviationSet_measurableSet n (1/k)

-- `borelNormalNumberTheorem` (Theorem 1.2) is stated and proven at the end of the file —
-- it depends on `ae_convergence_along_sq` and `normalNumbers_eq_iInter`, which are in the
-- "Weak Law of Large Numbers - Complete Proof" section that comes later.

/-- The dyadicDigit function as a real-valued function is AEStronglyMeasurable on halfOpenUnit.
    This suffices for integration purposes since we integrate over halfOpenUnit.
    The function is constant (0 or 1) on each measurable digit set. -/
theorem dyadicDigit_aestronglyMeasurable_halfOpenUnit (n : ℕ) (_hn : n ≥ 1) :
    AEStronglyMeasurable (fun ω => (dyadicDigit n ω : ℝ)) (volume.restrict halfOpenUnit) := by
  -- dyadicDigit n ω = indicator(digitSet n 1)(fun _ => 1) on halfOpenUnit
  -- This is because dyadicDigit is 1 on digitSet n 1, and 0 on digitSet n 0
  have h_meas1 := digitSet_measurableSet n 1
  have h_ind : AEStronglyMeasurable (Set.indicator (digitSet n 1) (fun _ => (1 : ℝ)))
               (volume.restrict halfOpenUnit) := by
    exact (Measurable.indicator measurable_const h_meas1).aestronglyMeasurable
  -- Now show dyadicDigit equals this indicator a.e. on halfOpenUnit
  refine AEStronglyMeasurable.congr h_ind ?_
  filter_upwards [ae_restrict_mem halfOpenUnit_measurableSet] with ω hω
  simp only [Set.indicator]
  by_cases h1 : ω ∈ digitSet n 1
  · simp only [h1, ↓reduceIte]
    simp only [digitSet, Set.mem_ofPred_eq] at h1
    simp [h1.2]
  · simp only [h1, ↓reduceIte]
    -- In halfOpenUnit but not digitSet n 1 means in digitSet n 0
    have h0 : ω ∈ digitSet n 0 := by
      simp only [digitSet, Set.mem_ofPred_eq, halfOpenUnit, Set.mem_Ioc] at h1 ⊢
      push Not at h1
      simp only [halfOpenUnit, Set.mem_Ioc] at hω
      rcases dyadicDigit_values n ω with hv | hv
      · exact ⟨⟨hω.1, hω.2⟩, hv⟩
      · exfalso; exact h1 ⟨hω.1, hω.2⟩ hv
    simp only [digitSet, Set.mem_ofPred_eq] at h0
    simp [h0.2]

/-! ## Rademacher Functions

The Rademacher functions r_n(ω) = 2d_n(ω) - 1 take values ±1.
They are more convenient for analysis than the digits d_n.
-/

/-- The nth Rademacher function: r_n(ω) = 2d_n(ω) - 1. -/
def rademacher (n : ℕ) (ω : ℝ) : ℤ := 2 * (dyadicDigit n ω : ℤ) - 1

/-- Rademacher functions take values ±1. -/
theorem rademacher_values (n : ℕ) (ω : ℝ) : rademacher n ω = 1 ∨ rademacher n ω = -1 := by
  simp only [rademacher]
  have h := dyadicDigit_le_one n ω
  interval_cases dyadicDigit n ω <;> simp

/-- The Rademacher function as a real-valued function is AEStronglyMeasurable on halfOpenUnit.
    This suffices for integration purposes since we integrate over halfOpenUnit.
    The function is constant on each digit set, and these partition halfOpenUnit. -/
theorem rademacher_aestronglyMeasurable_halfOpenUnit (n : ℕ) (_hn : n ≥ 1) :
    AEStronglyMeasurable (fun ω => (rademacher n ω : ℝ)) (volume.restrict halfOpenUnit) := by
  -- The function takes only values ±1, and is constant on each measurable digit set
  -- rademacher = 1 on digitSet n 1, rademacher = -1 on digitSet n 0
  -- These two sets partition halfOpenUnit, so rademacher is piecewise constant
  have h_meas1 := digitSet_measurableSet n 1
  -- Use indicator function representation
  -- rademacher n ω = 2 * indicator (digitSet n 1) ω - 1 on halfOpenUnit
  have h_ind : AEStronglyMeasurable (Set.indicator (digitSet n 1) (fun _ => (1 : ℝ)))
               (volume.restrict halfOpenUnit) := by
    exact (Measurable.indicator measurable_const h_meas1).aestronglyMeasurable
  -- 2 * indicator - 1 is AEStronglyMeasurable
  have h_linear := h_ind.const_smul (2 : ℝ)
  have h_const : AEStronglyMeasurable (fun _ : ℝ => (1 : ℝ)) (volume.restrict halfOpenUnit) :=
    aestronglyMeasurable_const
  have h_final := h_linear.sub h_const
  -- Now show rademacher equals this a.e. on halfOpenUnit
  refine AEStronglyMeasurable.congr h_final ?_
  -- Use ae_restrict_mem: a.e. for volume.restrict halfOpenUnit, we have ω ∈ halfOpenUnit
  filter_upwards [ae_restrict_mem halfOpenUnit_measurableSet] with ω hω
  simp only [Set.indicator, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h1 : ω ∈ digitSet n 1
  · simp only [h1, ↓reduceIte]
    -- rademacher n ω = 1 when ω ∈ digitSet n 1
    simp only [digitSet, Set.mem_ofPred_eq] at h1
    simp only [rademacher, h1.2]; ring
  · simp only [h1, ↓reduceIte]
    -- In halfOpenUnit but not digitSet n 1 means in digitSet n 0
    have h0 : ω ∈ digitSet n 0 := by
      simp only [digitSet, Set.mem_ofPred_eq, halfOpenUnit, Set.mem_Ioc] at h1 ⊢
      push Not at h1
      simp only [halfOpenUnit, Set.mem_Ioc] at hω
      rcases dyadicDigit_values n ω with hv | hv
      · exact ⟨⟨hω.1, hω.2⟩, hv⟩
      · exfalso; exact h1 ⟨hω.1, hω.2⟩ hv
    -- rademacher n ω = -1 when ω ∈ digitSet n 0
    simp only [digitSet, Set.mem_ofPred_eq, halfOpenUnit, Set.mem_Ioc] at h0
    simp only [rademacher, h0.2]; norm_num

/-- The partial sum of Rademacher functions. -/
def rademacherSum (n : ℕ) (ω : ℝ) : ℤ := (Finset.range n).sum (fun i => rademacher (i + 1) ω)

/-- Relation between digit sum and Rademacher sum:
    S_n = (s_n + n)/2 where S_n = Σ d_i and s_n = Σ r_i. -/
theorem sumDigits_eq_rademacher (n : ℕ) (ω : ℝ) :
    2 * (sumDigits n ω : ℤ) = rademacherSum n ω + n := by
  simp only [sumDigits, rademacherSum, rademacher]
  -- Goal: 2 * Σᵢ (dyadicDigit (i+1) ω : ℤ) = Σᵢ (2 * dyadicDigit (i+1) ω - 1) + n
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range]
  rw [← Finset.mul_sum]
  push_cast
  ring

/-! ## Chebyshev's Inequality

Billingsley proves the weak law using Chebyshev's inequality applied to step functions.
-/

/-- Chebyshev's inequality for the probability measure on (0,1]:
    P{ω : |f(ω)| ≥ a} ≤ (1/a²) ∫ f(ω)² dω.
    Requires f² to be integrable on the unit interval. -/
theorem chebyshev_inequality_unit (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hf : Measurable f) (hf_int : IntegrableOn (fun ω => (f ω)^2) halfOpenUnit volume) :
    probMeasureUnit {ω | |f ω| ≥ a} ≤
      ENNReal.ofReal ((1 / a^2) * ∫ ω in halfOpenUnit, (f ω)^2 ∂volume) := by
  -- Strategy: {|f| ≥ a} = {f² ≥ a²}, apply Markov to f²
  -- Key observation: a ≤ |f ω| ↔ a² ≤ |f ω|² = (f ω)²
  have h_set_eq : {ω | |f ω| ≥ a} = {ω | a^2 ≤ (f ω)^2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ge_iff_le, ← sq_abs (f ω)]
    constructor
    · intro h
      exact sq_le_sq' (by linarith) h
    · intro h
      have hab : 0 ≤ |f ω| := abs_nonneg _
      nlinarith [sq_nonneg a, sq_nonneg (|f ω|)]
  rw [h_set_eq]
  -- Now apply Markov's inequality to f²
  have hf_sq_meas : Measurable (fun ω => (f ω)^2) := hf.pow_const 2
  have hf_sq_aemeas : AEMeasurable (fun ω => ENNReal.ofReal ((f ω)^2)) probMeasureUnit :=
    (hf_sq_meas.ennreal_ofReal).aemeasurable
  -- The set {a² ≤ f²} in ℝ form equals {ofReal a² ≤ ofReal (f²)} for nonneg f²
  have h_set_ennreal : probMeasureUnit {ω | a^2 ≤ (f ω)^2} =
      probMeasureUnit {ω | ENNReal.ofReal (a^2) ≤ ENNReal.ofReal ((f ω)^2)} := by
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)]
  rw [h_set_ennreal]
  -- From Markov: a² * P{a² ≤ f²} ≤ ∫⁻ f², so P{a² ≤ f²} ≤ (∫⁻ f²)/a²
  have ha_sq_pos : (0 : ℝ) < a^2 := sq_pos_of_pos ha
  have ha_sq_ne_zero : ENNReal.ofReal (a^2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr ha_sq_pos)
  have ha_sq_ne_top : ENNReal.ofReal (a^2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_div := meas_ge_le_lintegral_div hf_sq_aemeas ha_sq_ne_zero ha_sq_ne_top
  simp only [probMeasureUnit] at h_div ⊢
  -- f² is integrable and nonneg, so lintegral equals Bochner integral
  have hf_sq_nonneg : 0 ≤ᵐ[volume.restrict halfOpenUnit] (fun ω => (f ω)^2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  calc (volume.restrict halfOpenUnit) {ω | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal ((f ω) ^ 2)}
      ≤ (∫⁻ ω, ENNReal.ofReal ((f ω)^2) ∂(volume.restrict halfOpenUnit)) / ENNReal.ofReal (a^2) := h_div
    _ = ENNReal.ofReal (∫ ω in halfOpenUnit, (f ω)^2 ∂volume) / ENNReal.ofReal (a^2) := by
        congr 1
        rw [← ofReal_integral_eq_lintegral_ofReal hf_int hf_sq_nonneg]
    _ = ENNReal.ofReal ((1 / a^2) * ∫ ω in halfOpenUnit, (f ω)^2 ∂volume) := by
        rw [ENNReal.div_eq_inv_mul]
        have hinv : (ENNReal.ofReal (a^2))⁻¹ = ENNReal.ofReal (a^2)⁻¹ :=
          (ENNReal.ofReal_inv_of_pos ha_sq_pos).symm
        rw [hinv, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (a^2)⁻¹), one_div]

/-! ## Supporting Lemmas -/

/-- On the set where d_n = 1, the Rademacher function r_n = +1. -/
theorem rademacher_on_digitSet_one (n : ℕ) (ω : ℝ) (hω : ω ∈ digitSet n 1) :
    rademacher n ω = 1 := by
  simp only [digitSet, Set.mem_ofPred_eq] at hω
  simp only [rademacher, hω.2]
  norm_num

/-- On the set where d_n = 0, the Rademacher function r_n = -1. -/
theorem rademacher_on_digitSet_zero (n : ℕ) (ω : ℝ) (hω : ω ∈ digitSet n 0) :
    rademacher n ω = -1 := by
  simp only [digitSet, Set.mem_ofPred_eq] at hω
  simp only [rademacher, hω.2]
  norm_num

/-- Rademacher is integrable on digitSet n 1 (where it equals 1). -/
theorem rademacher_integrableOn_digitSet_one (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => (rademacher n ω : ℝ)) (digitSet n 1) volume := by
  have hfin : volume (digitSet n 1) ≠ ⊤ := by
    rw [volume_digitSet_one n hn]; norm_num
  have hmeas : MeasurableSet (digitSet n 1) := digitSet_measurableSet n 1
  -- On digitSet n 1, rademacher n = 1 (constant)
  have heq : Set.EqOn (fun ω => (rademacher n ω : ℝ)) (fun _ => (1 : ℝ)) (digitSet n 1) := by
    intro x hx
    simp [rademacher_on_digitSet_one n x hx]
  have hC : ‖(1 : ℝ)‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_const (hs := hfin) (hC := hC)).congr_fun heq.symm hmeas

/-- Rademacher is integrable on digitSet n 0 (where it equals -1). -/
theorem rademacher_integrableOn_digitSet_zero (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => (rademacher n ω : ℝ)) (digitSet n 0) volume := by
  have hfin : volume (digitSet n 0) ≠ ⊤ := by
    rw [volume_digitSet_zero n hn]; norm_num
  have hmeas : MeasurableSet (digitSet n 0) := digitSet_measurableSet n 0
  -- On digitSet n 0, rademacher n = -1 (constant)
  have heq : Set.EqOn (fun ω => (rademacher n ω : ℝ)) (fun _ => (-1 : ℝ)) (digitSet n 0) := by
    intro x hx
    simp [rademacher_on_digitSet_zero n x hx]
  have hC : ‖(-1 : ℝ)‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_const (hs := hfin) (hC := hC)).congr_fun heq.symm hmeas

/-- The dyadic digit function is measurable on all of ℝ.
    This follows from the fact that preimages of {0} and {1} are countable unions of
    half-open intervals, which are measurable.

    Note: This is a technical lemma used for `rademacher_measurable`. For integration
    on halfOpenUnit, the specialized lemmas `dyadicDigit_aestronglyMeasurable_halfOpenUnit`
    and `digitSet_measurableSet` are more directly applicable.

    The proof structure:
    - For n = 0: constant function (always 0), trivially measurable
    - For n ≥ 1: preimage of {k} is a countable union of Ioc intervals, plus Iic 0 for k=0 -/
theorem dyadicDigit_measurable (n : ℕ) : Measurable (fun ω : ℝ => dyadicDigit n ω) := by
  -- The proof is compositional: `dyadicDigit n` is built from `ω * 2^n`, `Int.floor`,
  -- `Int.fract`, and arithmetic on ℤ/ℕ.  Since ℕ carries the top σ-algebra, any function
  -- into ℕ post-composed with a measurable ℝ → ℤ is measurable via `measurable_from_top`.
  by_cases hn : n = 0
  · have hfun : (fun ω : ℝ => dyadicDigit n ω) = fun _ => 0 := by
      funext ω; simp [dyadicDigit, hn]
    rw [hfun]; exact measurable_const
  · have hscaled : Measurable (fun ω : ℝ => ω * (2 : ℝ)^n) :=
      measurable_id.mul_const _
    have hfloor : Measurable (fun ω : ℝ => (⌊ω * (2 : ℝ)^n⌋ : ℤ)) := hscaled.floor
    have hfract : Measurable (fun ω : ℝ => Int.fract (ω * (2 : ℝ)^n)) := hscaled.fract
    have hcond : MeasurableSet {ω : ℝ | 0 < Int.fract (ω * (2 : ℝ)^n)} :=
      measurableSet_lt measurable_const hfract
    have hbr1 : Measurable (fun ω : ℝ => ((⌊ω * (2 : ℝ)^n⌋ : ℤ).toNat % 2)) :=
      (measurable_from_top (α := ℤ) (β := ℕ) (f := fun k => k.toNat % 2)).comp hfloor
    have hbr2 : Measurable (fun ω : ℝ => (((⌊ω * (2 : ℝ)^n⌋ : ℤ).toNat - 1) % 2)) :=
      (measurable_from_top (α := ℤ) (β := ℕ) (f := fun k => (k.toNat - 1) % 2)).comp hfloor
    have hfun : (fun ω : ℝ => dyadicDigit n ω) =
        fun ω : ℝ => if 0 < Int.fract (ω * (2 : ℝ)^n)
          then (⌊ω * (2 : ℝ)^n⌋ : ℤ).toNat % 2
          else ((⌊ω * (2 : ℝ)^n⌋ : ℤ).toNat - 1) % 2 := by
      funext ω
      simp only [dyadicDigit, if_neg hn, Int.fract, gt_iff_lt]
      exact if_congr Iff.rfl rfl rfl
    rw [hfun]
    exact Measurable.ite hcond hbr1 hbr2

/-- The Rademacher function is measurable on all of ℝ. -/
theorem rademacher_measurable (n : ℕ) : Measurable (fun ω : ℝ => (rademacher n ω : ℝ)) := by
  -- `rademacher n ω = 2 * (dyadicDigit n ω : ℤ) - 1`, and the ℕ → ℝ stage is automatic
  -- since ℕ carries the top σ-algebra.
  have hfun : (fun ω : ℝ => (rademacher n ω : ℝ)) =
      (fun k : ℕ => ((2 * (k : ℤ) - 1 : ℤ) : ℝ)) ∘ (fun ω : ℝ => dyadicDigit n ω) := by
    funext ω; rfl
  rw [hfun]
  exact measurable_from_top.comp (dyadicDigit_measurable n)

/-- The Rademacher function is integrable on any finite measure set.
This follows from boundedness: |r_n(ω)| ≤ 1 for all ω.
Note: For digit sets where n ≥ 1, use the specialized lemmas above. -/
theorem rademacher_integrableOn (n : ℕ) (s : Set ℝ) (hs : volume s < ⊤) :
    IntegrableOn (fun ω => (rademacher n ω : ℝ)) s volume := by
  -- Use IntegrableOn.of_bound which takes AEStronglyMeasurable on the restricted measure
  -- Rademacher is bounded by 1 in norm
  have h_bdd : ∀ᵐ a ∂(volume.restrict s), ‖(rademacher n a : ℝ)‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    rcases rademacher_values n ω with h | h <;> simp [h]
  -- For measurability on the restricted measure - use that rademacher is globally measurable
  have h_meas : AEStronglyMeasurable (fun ω => (rademacher n ω : ℝ)) (volume.restrict s) :=
    (rademacher_measurable n).aestronglyMeasurable
  exact IntegrableOn.of_bound hs h_meas 1 h_bdd

/-- The expected value of a Rademacher function is 0. -/
theorem expected_rademacher (n : ℕ) (hn : n ≥ 1) :
    ∫ ω in halfOpenUnit, (rademacher n ω : ℝ) ∂volume = 0 := by
  -- Rewrite halfOpenUnit as disjoint union of digit sets
  rw [← digitSet_union n hn]
  have h_disj := digitSet_disjoint n
  have h_meas0 := digitSet_measurableSet n 0
  have h_meas1 := digitSet_measurableSet n 1
  -- Establish integrability on each set (using specialized lemmas for digit sets)
  have h_int0 := rademacher_integrableOn_digitSet_zero n hn
  have h_int1 := rademacher_integrableOn_digitSet_one n hn
  -- Split the integral
  rw [setIntegral_union h_disj h_meas1 h_int0 h_int1]
  -- On digitSet n 0: rademacher = -1; on digitSet n 1: rademacher = +1
  have h0 : ∫ ω in digitSet n 0, (rademacher n ω : ℝ) ∂volume =
            ∫ ω in digitSet n 0, (-1 : ℝ) ∂volume := by
    apply setIntegral_congr_ae h_meas0
    apply Filter.Eventually.of_forall
    intro x hx
    rw [rademacher_on_digitSet_zero n x hx]; simp
  have h1 : ∫ ω in digitSet n 1, (rademacher n ω : ℝ) ∂volume =
            ∫ ω in digitSet n 1, (1 : ℝ) ∂volume := by
    apply setIntegral_congr_ae h_meas1
    apply Filter.Eventually.of_forall
    intro x hx
    rw [rademacher_on_digitSet_one n x hx]; simp
  rw [h0, h1]
  -- Compute constant integrals
  rw [setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul]
  have hv0 : volume.real (digitSet n 0) = (1/2 : ℝ) := by
    simp only [Measure.real, volume_digitSet_zero n hn]; norm_num
  have hv1 : volume.real (digitSet n 1) = (1/2 : ℝ) := by
    simp only [Measure.real, volume_digitSet_one n hn]; norm_num
  rw [hv0, hv1]; ring

/-- Rademacher function squared equals 1. -/
theorem rademacher_sq_eq_one (n : ℕ) (ω : ℝ) : (rademacher n ω : ℝ)^2 = 1 := by
  rcases rademacher_values n ω with h | h <;> simp [h]

/-- The L² norm of a Rademacher function is 1 (since r_n² = 1). -/
theorem rademacher_sq_integral (n : ℕ) (_hn : n ≥ 1) :
    ∫ ω in halfOpenUnit, (rademacher n ω : ℝ)^2 ∂volume = 1 := by
  simp_rw [rademacher_sq_eq_one]
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  simp only [halfOpenUnit]
  rw [Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

/-- Rademacher function is integrable on halfOpenUnit (sorry-free version). -/
theorem rademacher_integrableOn_halfOpenUnit (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => (rademacher n ω : ℝ)) halfOpenUnit volume := by
  have hfin : volume halfOpenUnit < ⊤ := by rw [volume_halfOpenUnit]; norm_num
  have hmeas : AEStronglyMeasurable (fun ω => (rademacher n ω : ℝ)) (volume.restrict halfOpenUnit) :=
    rademacher_aestronglyMeasurable_halfOpenUnit n hn
  have hbdd : ∀ᵐ x ∂(volume.restrict halfOpenUnit), ‖(rademacher n x : ℝ)‖ ≤ 1 := by
    filter_upwards with ω; rcases rademacher_values n ω with h | h <;> simp [h]
  exact IntegrableOn.of_bound hfin hmeas 1 hbdd

/-- The Rademacher sum is integrable on halfOpenUnit (sorry-free version). -/
theorem rademacherSum_integrableOn_halfOpenUnit (n : ℕ) :
    IntegrableOn (fun ω => (rademacherSum n ω : ℝ)) halfOpenUnit volume := by
  simp only [rademacherSum, IntegrableOn]
  have hfin : volume halfOpenUnit < ⊤ := by rw [volume_halfOpenUnit]; norm_num
  have h : ∀ i ∈ Finset.range n, Integrable (fun ω => (rademacher (i + 1) ω : ℝ)) (volume.restrict halfOpenUnit) := by
    intro i _hi
    exact rademacher_integrableOn_halfOpenUnit (i + 1) (by omega)
  refine (integrable_finsetSum (Finset.range n) h).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp [Int.cast_sum]

/-- The Rademacher sum is integrable on any finite measure set. -/
theorem rademacherSum_integrableOn (n : ℕ) (s : Set ℝ) (hs : volume s < ⊤) :
    IntegrableOn (fun ω => (rademacherSum n ω : ℝ)) s volume := by
  simp only [rademacherSum, IntegrableOn]
  -- Use integrable_finset_sum with the restricted measure
  have h : ∀ i ∈ Finset.range n, Integrable (fun ω => (rademacher (i + 1) ω : ℝ)) (volume.restrict s) := by
    intro i _hi
    exact rademacher_integrableOn (i + 1) s hs
  refine (integrable_finsetSum (Finset.range n) h).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp [Int.cast_sum]

/-- Product of Rademacher functions is integrable on halfOpenUnit. -/
theorem rademacher_mul_integrableOn_halfOpenUnit (i j : ℕ) (hi : i ≥ 1) (hj : j ≥ 1) :
    IntegrableOn (fun ω => (rademacher i ω : ℝ) * (rademacher j ω : ℝ)) halfOpenUnit volume := by
  have hfin : volume halfOpenUnit < ⊤ := by rw [volume_halfOpenUnit]; norm_num
  have hmeas : AEStronglyMeasurable (fun ω => (rademacher i ω : ℝ) * (rademacher j ω : ℝ))
               (volume.restrict halfOpenUnit) := by
    apply AEStronglyMeasurable.mul
    · exact rademacher_aestronglyMeasurable_halfOpenUnit i hi
    · exact rademacher_aestronglyMeasurable_halfOpenUnit j hj
  have hbdd : ∀ᵐ x ∂(volume.restrict halfOpenUnit),
      ‖(rademacher i x : ℝ) * (rademacher j x : ℝ)‖ ≤ 1 := by
    filter_upwards with ω
    rcases rademacher_values i ω with hi' | hi' <;>
    rcases rademacher_values j ω with hj' | hj' <;> simp [hi', hj']
  exact IntegrableOn.of_bound hfin hmeas 1 hbdd

/-- Rademacher squared is integrable on halfOpenUnit. -/
theorem rademacher_sq_integrableOn_halfOpenUnit (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => (rademacher n ω : ℝ)^2) halfOpenUnit volume := by
  have hfin : volume halfOpenUnit < ⊤ := by rw [volume_halfOpenUnit]; norm_num
  have hmeas : AEStronglyMeasurable (fun ω => (rademacher n ω : ℝ)^2) (volume.restrict halfOpenUnit) := by
    have h := rademacher_aestronglyMeasurable_halfOpenUnit n hn
    have h2 := h.mul h
    convert h2 using 1
    ext ω; simp only [Pi.mul_apply, sq]
  have hbdd : ∀ᵐ x ∂(volume.restrict halfOpenUnit), ‖(rademacher n x : ℝ)^2‖ ≤ 1 := by
    filter_upwards with ω; rcases rademacher_values n ω with h | h <;> simp [h]
  exact IntegrableOn.of_bound hfin hmeas 1 hbdd

/-- Rademacher sum squared is integrable on halfOpenUnit. -/
theorem rademacherSum_sq_integrableOn_halfOpenUnit (n : ℕ) :
    IntegrableOn (fun ω => (rademacherSum n ω : ℝ)^2) halfOpenUnit volume := by
  have hfin : volume halfOpenUnit < ⊤ := by rw [volume_halfOpenUnit]; norm_num
  have hmeas : AEStronglyMeasurable (fun ω => (rademacherSum n ω : ℝ)^2) (volume.restrict halfOpenUnit) :=
    (rademacherSum_integrableOn_halfOpenUnit n).aestronglyMeasurable.pow 2
  have hbdd : ∀ᵐ x ∂(volume.restrict halfOpenUnit), ‖(rademacherSum n x : ℝ)^2‖ ≤ (n : ℝ)^2 := by
    filter_upwards with ω
    have h_bound : |(rademacherSum n ω : ℝ)| ≤ n := by
      simp only [rademacherSum]
      have h1 : (↑(∑ i ∈ Finset.range n, rademacher (i + 1) ω) : ℝ)
              = ∑ i ∈ Finset.range n, (↑(rademacher (i + 1) ω) : ℝ) := Int.cast_sum _ _
      rw [h1]
      calc |∑ i ∈ Finset.range n, (↑(rademacher (i + 1) ω) : ℝ)|
        ≤ ∑ i ∈ Finset.range n, |(↑(rademacher (i + 1) ω) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          rcases rademacher_values (i + 1) ω with h | h <;> simp [h, abs_of_pos, abs_of_neg]
      _ = n := by simp
    rw [norm_pow, Real.norm_eq_abs, sq_abs]
    have h_neg : -(n : ℝ) ≤ (rademacherSum n ω : ℝ) := by
      have := abs_nonneg (rademacherSum n ω : ℝ)
      linarith [neg_abs_le (rademacherSum n ω : ℝ)]
    have h_pos : (rademacherSum n ω : ℝ) ≤ n := le_of_abs_le h_bound
    exact sq_le_sq' h_neg h_pos
  refine IntegrableOn.of_bound hfin hmeas ((n : ℝ)^2) ?_
  convert hbdd using 0

/-- Rademacher sum times Rademacher is integrable on halfOpenUnit. -/
theorem rademacherSum_mul_rademacher_integrableOn_halfOpenUnit (n : ℕ) :
    IntegrableOn (fun ω => (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ)) halfOpenUnit volume := by
  have hfin : volume halfOpenUnit < ⊤ := by rw [volume_halfOpenUnit]; norm_num
  have hmeas : AEStronglyMeasurable (fun ω => (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ))
               (volume.restrict halfOpenUnit) := by
    apply AEStronglyMeasurable.mul
    · exact (rademacherSum_integrableOn_halfOpenUnit n).aestronglyMeasurable
    · exact rademacher_aestronglyMeasurable_halfOpenUnit (n + 1) (by omega)
  have hbdd : ∀ᵐ x ∂(volume.restrict halfOpenUnit),
      ‖(rademacherSum n x : ℝ) * (rademacher (n + 1) x : ℝ)‖ ≤ (n : ℝ) := by
    filter_upwards with ω
    have h_s : |(rademacherSum n ω : ℝ)| ≤ n := by
      simp only [rademacherSum]
      have h1 : (↑(∑ i ∈ Finset.range n, rademacher (i + 1) ω) : ℝ)
              = ∑ i ∈ Finset.range n, (↑(rademacher (i + 1) ω) : ℝ) := Int.cast_sum _ _
      rw [h1]
      calc |∑ i ∈ Finset.range n, (↑(rademacher (i + 1) ω) : ℝ)|
        ≤ ∑ i ∈ Finset.range n, |(↑(rademacher (i + 1) ω) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          rcases rademacher_values (i + 1) ω with h | h <;> simp [h, abs_of_pos, abs_of_neg]
      _ = n := by simp
    have h_r : |(rademacher (n + 1) ω : ℝ)| ≤ 1 := by
      rcases rademacher_values (n + 1) ω with h | h <;> simp [h, abs_of_pos, abs_of_neg]
    simp only [norm_mul, Real.norm_eq_abs]
    calc |(rademacherSum n ω : ℝ)| * |(rademacher (n + 1) ω : ℝ)| ≤ (n : ℝ) * 1 :=
          mul_le_mul h_s h_r (abs_nonneg _) (Nat.cast_nonneg _)
    _ = n := by ring
  refine IntegrableOn.of_bound hfin hmeas (n : ℝ) ?_
  convert hbdd using 0

/-- dyadicDigit is integrable on digitSet n 1 (where it equals 1). -/
theorem dyadicDigit_integrableOn_digitSet_one (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => (dyadicDigit n ω : ℝ)) (digitSet n 1) volume := by
  have hfin : volume (digitSet n 1) ≠ ⊤ := by
    rw [volume_digitSet_one n hn]; norm_num
  have hmeas : MeasurableSet (digitSet n 1) := digitSet_measurableSet n 1
  -- On digitSet n 1, dyadicDigit n = 1 (constant)
  have heq : Set.EqOn (fun ω => (dyadicDigit n ω : ℝ)) (fun _ => (1 : ℝ)) (digitSet n 1) := by
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]
  have hC : ‖(1 : ℝ)‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_const (hs := hfin) (hC := hC)).congr_fun heq.symm hmeas

/-- dyadicDigit is integrable on digitSet n 0 (where it equals 0). -/
theorem dyadicDigit_integrableOn_digitSet_zero (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => (dyadicDigit n ω : ℝ)) (digitSet n 0) volume := by
  have hfin : volume (digitSet n 0) ≠ ⊤ := by
    rw [volume_digitSet_zero n hn]; norm_num
  have hmeas : MeasurableSet (digitSet n 0) := digitSet_measurableSet n 0
  -- On digitSet n 0, dyadicDigit n = 0 (constant)
  have heq : Set.EqOn (fun ω => (dyadicDigit n ω : ℝ)) (fun _ => (0 : ℝ)) (digitSet n 0) := by
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]
  have hC : ‖(0 : ℝ)‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_const (hs := hfin) (hC := hC)).congr_fun heq.symm hmeas

/-- The dyadicDigit function is integrable on any finite measure set.
Note: For digit sets where n ≥ 1, use the specialized lemmas above. -/
theorem dyadicDigit_integrableOn (n : ℕ) (s : Set ℝ) (hs : volume s < ⊤) :
    IntegrableOn (fun ω => (dyadicDigit n ω : ℝ)) s volume := by
  -- Use IntegrableOn.of_bound which takes AEStronglyMeasurable on the restricted measure
  -- dyadicDigit is bounded by 1 in norm (it takes values 0 or 1)
  have h_bdd : ∀ᵐ a ∂(volume.restrict s), ‖(dyadicDigit n a : ℝ)‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    rcases dyadicDigit_values n ω with h | h <;> simp [h]
  -- Measurability follows from the global `dyadicDigit_measurable` lemma.
  have h_meas : AEStronglyMeasurable (fun ω => (dyadicDigit n ω : ℝ)) (volume.restrict s) :=
    (measurable_from_top.comp (dyadicDigit_measurable n)).aestronglyMeasurable
  exact IntegrableOn.of_bound hs h_meas 1 h_bdd

/-- The expected value of a single binary digit is 1/2. -/
theorem expected_dyadicDigit (n : ℕ) (hn : n ≥ 1) :
    ∫ ω in halfOpenUnit, (dyadicDigit n ω : ℝ) ∂volume = 1/2 := by
  -- Split halfOpenUnit into digit sets
  rw [← digitSet_union n hn]
  have h_disj := digitSet_disjoint n
  have h_meas0 := digitSet_measurableSet n 0
  have h_meas1 := digitSet_measurableSet n 1
  -- Integrability (using specialized lemmas)
  have h_int0 := dyadicDigit_integrableOn_digitSet_zero n hn
  have h_int1 := dyadicDigit_integrableOn_digitSet_one n hn
  -- Split the integral
  rw [setIntegral_union h_disj h_meas1 h_int0 h_int1]
  -- On digitSet n 0: dyadicDigit = 0; on digitSet n 1: dyadicDigit = 1
  have h0 : ∫ ω in digitSet n 0, (dyadicDigit n ω : ℝ) ∂volume =
            ∫ ω in digitSet n 0, (0 : ℝ) ∂volume := by
    apply setIntegral_congr_ae h_meas0
    apply Filter.Eventually.of_forall
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]
  have h1 : ∫ ω in digitSet n 1, (dyadicDigit n ω : ℝ) ∂volume =
            ∫ ω in digitSet n 1, (1 : ℝ) ∂volume := by
    apply setIntegral_congr_ae h_meas1
    apply Filter.Eventually.of_forall
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]
  rw [h0, h1]
  -- Compute constant integrals
  rw [setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one]
  have hv1 : volume.real (digitSet n 1) = (1/2 : ℝ) := by
    simp only [Measure.real, volume_digitSet_one n hn]; norm_num
  rw [hv1]

/-- The variance integrand is integrable on digitSet n 1 (where (1-1/2)² = 1/4). -/
theorem variance_integrand_integrableOn_digitSet_one (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => ((dyadicDigit n ω : ℝ) - 1/2)^2) (digitSet n 1) volume := by
  have hfin : volume (digitSet n 1) ≠ ⊤ := by
    rw [volume_digitSet_one n hn]; norm_num
  have hmeas : MeasurableSet (digitSet n 1) := digitSet_measurableSet n 1
  -- On digitSet n 1, (dyadicDigit n ω - 1/2)² = (1 - 1/2)² = 1/4 (constant)
  have heq : Set.EqOn (fun ω => ((dyadicDigit n ω : ℝ) - 1/2)^2) (fun _ => (1/4 : ℝ)) (digitSet n 1) := by
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]; ring
  have hC : ‖(1/4 : ℝ)‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_const (hs := hfin) (hC := hC)).congr_fun heq.symm hmeas

/-- The variance integrand is integrable on digitSet n 0 (where (0-1/2)² = 1/4). -/
theorem variance_integrand_integrableOn_digitSet_zero (n : ℕ) (hn : n ≥ 1) :
    IntegrableOn (fun ω => ((dyadicDigit n ω : ℝ) - 1/2)^2) (digitSet n 0) volume := by
  have hfin : volume (digitSet n 0) ≠ ⊤ := by
    rw [volume_digitSet_zero n hn]; norm_num
  have hmeas : MeasurableSet (digitSet n 0) := digitSet_measurableSet n 0
  -- On digitSet n 0, (dyadicDigit n ω - 1/2)² = (0 - 1/2)² = 1/4 (constant)
  have heq : Set.EqOn (fun ω => ((dyadicDigit n ω : ℝ) - 1/2)^2) (fun _ => (1/4 : ℝ)) (digitSet n 0) := by
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]; ring
  have hC : ‖(1/4 : ℝ)‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_const (hs := hfin) (hC := hC)).congr_fun heq.symm hmeas

/-- The centered digit squared equals 1/4 for any digit value.
    Since dyadicDigit ∈ {0,1}, we have (d - 1/2)² = 1/4 always. -/
theorem variance_integrand_eq_const (n : ℕ) (ω : ℝ) :
    ((dyadicDigit n ω : ℝ) - 1/2)^2 = 1/4 := by
  rcases dyadicDigit_values n ω with h | h <;> simp [h] <;> norm_num

/-- Helper: The centered digit squared function is integrable.
Note: For digit sets where n ≥ 1, use the specialized lemmas above. -/
theorem variance_integrand_integrableOn (n : ℕ) (s : Set ℝ) (hs : volume s < ⊤) :
    IntegrableOn (fun ω => ((dyadicDigit n ω : ℝ) - 1/2)^2) s volume := by
  -- The function equals constant 1/4 (since (0-1/2)² = (1-1/2)² = 1/4)
  have h_eq : (fun ω => ((dyadicDigit n ω : ℝ) - 1/2)^2) = fun _ => (1/4 : ℝ) := by
    ext ω; exact variance_integrand_eq_const n ω
  rw [h_eq]
  exact integrableOn_const (hs := hs.ne)

/-- The variance of a single binary digit is 1/4. -/
theorem variance_dyadicDigit (n : ℕ) (hn : n ≥ 1) :
    ∫ ω in halfOpenUnit, ((dyadicDigit n ω : ℝ) - 1/2)^2 ∂volume = 1/4 := by
  -- Split halfOpenUnit into digit sets
  rw [← digitSet_union n hn]
  have h_disj := digitSet_disjoint n
  have h_meas0 := digitSet_measurableSet n 0
  have h_meas1 := digitSet_measurableSet n 1
  -- Integrability (using specialized lemmas)
  have h_int0 := variance_integrand_integrableOn_digitSet_zero n hn
  have h_int1 := variance_integrand_integrableOn_digitSet_one n hn
  -- Split the integral
  rw [setIntegral_union h_disj h_meas1 h_int0 h_int1]
  -- On digitSet n 0: (0 - 1/2)² = 1/4; on digitSet n 1: (1 - 1/2)² = 1/4
  have h0 : ∫ ω in digitSet n 0, ((dyadicDigit n ω : ℝ) - 1/2)^2 ∂volume =
            ∫ ω in digitSet n 0, (1/4 : ℝ) ∂volume := by
    apply setIntegral_congr_ae h_meas0
    apply Filter.Eventually.of_forall
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]
    ring
  have h1 : ∫ ω in digitSet n 1, ((dyadicDigit n ω : ℝ) - 1/2)^2 ∂volume =
            ∫ ω in digitSet n 1, (1/4 : ℝ) ∂volume := by
    apply setIntegral_congr_ae h_meas1
    apply Filter.Eventually.of_forall
    intro x hx
    simp only [digitSet, Set.mem_ofPred_eq] at hx
    simp [hx.2]
    ring
  rw [h0, h1]
  -- Compute constant integrals
  rw [setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul]
  have hv0 : volume.real (digitSet n 0) = (1/2 : ℝ) := by
    simp only [Measure.real, volume_digitSet_zero n hn]; norm_num
  have hv1 : volume.real (digitSet n 1) = (1/2 : ℝ) := by
    simp only [Measure.real, volume_digitSet_one n hn]; norm_num
  rw [hv0, hv1]
  ring

/-- The intersection of digit sets is measurable. -/
theorem digitSet_inter_measurableSet (n m : ℕ) (b₁ b₂ : ℕ) :
    MeasurableSet (digitSet n b₁ ∩ digitSet m b₂) :=
  (digitSet_measurableSet n b₁).inter (digitSet_measurableSet m b₂)

/-- The four intersections partition halfOpenUnit for distinct n, m ≥ 1. -/
theorem digitSet_inter_partition (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    (digitSet n 0 ∩ digitSet m 0) ∪ (digitSet n 0 ∩ digitSet m 1) ∪
    (digitSet n 1 ∩ digitSet m 0) ∪ (digitSet n 1 ∩ digitSet m 1) = halfOpenUnit := by
  -- First, regroup the unions to combine terms with the same first factor
  have h1 : digitSet n 0 ∩ digitSet m 0 ∪ digitSet n 0 ∩ digitSet m 1 =
      digitSet n 0 ∩ (digitSet m 0 ∪ digitSet m 1) := (Set.inter_union_distrib_left _ _ _).symm
  have h2 : digitSet n 1 ∩ digitSet m 0 ∪ digitSet n 1 ∩ digitSet m 1 =
      digitSet n 1 ∩ (digitSet m 0 ∪ digitSet m 1) := (Set.inter_union_distrib_left _ _ _).symm
  -- Group the last two terms
  rw [Set.union_assoc, h2, h1]
  -- Now we have: (A ∩ X) ∪ (B ∩ X) where X = digitSet m 0 ∪ digitSet m 1
  rw [← Set.union_inter_distrib_right]
  -- Now: (A ∪ B) ∩ X
  rw [digitSet_union m hm, digitSet_union n hn, Set.inter_self]

/-- The four intersections are pairwise disjoint. -/
theorem digitSet_inter_pairwise_disjoint (n m : ℕ) (b₁ b₂ c₁ c₂ : ℕ)
    (_hb₁ : b₁ ≤ 1) (_hb₂ : b₂ ≤ 1) (_hc₁ : c₁ ≤ 1) (_hc₂ : c₂ ≤ 1)
    (hne : (b₁, b₂) ≠ (c₁, c₂)) :
    Disjoint (digitSet n b₁ ∩ digitSet m b₂) (digitSet n c₁ ∩ digitSet m c₂) := by
  rw [Set.disjoint_iff]
  intro ω ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  simp only [digitSet, Set.mem_ofPred_eq] at h1 h2 h3 h4
  have heq1 : b₁ = c₁ := by omega
  have heq2 : b₂ = c₂ := by omega
  exact hne (Prod.ext heq1 heq2)

/-- The four intersection sets partition digitSet m b₂. -/
theorem digitSet_inter_partition_m (n m : ℕ) (_hn : n ≥ 1) (_hm : m ≥ 1) (b₂ : ℕ) :
    (digitSet n 0 ∩ digitSet m b₂) ∪ (digitSet n 1 ∩ digitSet m b₂) = digitSet m b₂ := by
  ext ω
  simp only [Set.mem_union, Set.mem_inter_iff, digitSet, Set.mem_ofPred_eq]
  constructor
  · intro h
    rcases h with ⟨⟨hω, _⟩, ⟨_, hm_eq⟩⟩ | ⟨⟨hω, _⟩, ⟨_, hm_eq⟩⟩
    · exact ⟨hω, hm_eq⟩
    · exact ⟨hω, hm_eq⟩
  · intro ⟨hω, hm_eq⟩
    have h := dyadicDigit_values n ω
    rcases h with hn_eq | hn_eq
    · left; exact ⟨⟨hω, hn_eq⟩, ⟨hω, hm_eq⟩⟩
    · right; exact ⟨⟨hω, hn_eq⟩, ⟨hω, hm_eq⟩⟩

/-- The two halves of the partition are disjoint. -/
theorem digitSet_inter_disjoint_m (n m : ℕ) (b₂ : ℕ) :
    Disjoint (digitSet n 0 ∩ digitSet m b₂) (digitSet n 1 ∩ digitSet m b₂) := by
  rw [Set.disjoint_iff]
  intro ω ⟨⟨⟨_, h0⟩, _⟩, ⟨⟨_, h1⟩, _⟩⟩
  omega

/-! ### XOR Bijection Lemmas

For proving that d_n=0 and d_n=1 halves have equal measure within digitSet m b₂,
we use the XOR bijection k ↦ k ⊕ 2^(m-n) which preserves k%2 but toggles d_n.
-/

/-- XOR with 2^j preserves mod 2 when j ≥ 1. -/
theorem xor_pow_mod_two (k j : ℕ) (hj : j ≥ 1) : (k ^^^ 2^j) % 2 = k % 2 := by
  have h2j_even : 2^j % 2 = 0 := by
    have hj_pos : j ≠ 0 := by omega
    simp only [Nat.pow_mod, Nat.mod_self, zero_pow hj_pos, Nat.zero_mod]
  rw [Nat.xor_mod_two_eq]
  omega

/-- Bit j equals decide ((k / 2^j) % 2 = 1). -/
theorem testBit_eq_div_mod (k j : ℕ) : k.testBit j = decide ((k / 2^j) % 2 = 1) := by
  rw [show k.testBit j = (k / 2^j).testBit 0 by rw [Nat.testBit_div_two_pow]; simp]
  rw [Nat.testBit_zero]

/-- XOR with 2^j toggles bit j. -/
theorem xor_pow_testBit (k j : ℕ) : (k ^^^ 2^j).testBit j = !k.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  simp

/-- XOR with 2^j toggles (k / 2^j) % 2. -/
theorem xor_pow_toggles_div_mod (k j : ℕ) :
    (k ^^^ 2^j) / 2^j % 2 = 1 - k / 2^j % 2 := by
  have h1 := xor_pow_testBit k j
  rw [testBit_eq_div_mod, testBit_eq_div_mod] at h1
  have hmod_le : k / 2^j % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega : 2 > 0))
  have hmod_le' : (k ^^^ 2^j) / 2^j % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega : 2 > 0))
  interval_cases k / 2^j % 2 <;> interval_cases (k ^^^ 2^j) / 2^j % 2 <;> simp_all

/-- XOR keeps values in range: if k < 2^m and j < m, then k ^^^ 2^j < 2^m. -/
theorem xor_pow_lt (k j m : ℕ) (hk : k < 2^m) (hj : j < m) : k ^^^ 2^j < 2^m :=
  Nat.xor_lt_two_pow hk (Nat.pow_lt_pow_right (by omega) hj)

/-- The XOR bijection on interval indices with d_m = b₂.
For n < m, maps {k : k%2 = b₂, d_n(k) = 0} to {k : k%2 = b₂, d_n(k) = 1}. -/
theorem xor_bijection_card_eq (m n b₂ : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) (h : n < m) (_hb₂ : b₂ ≤ 1) :
    (Finset.filter (fun k => k % 2 = b₂ ∧ (k / 2^(m-n)) % 2 = 0) (Finset.range (2^m))).card =
    (Finset.filter (fun k => k % 2 = b₂ ∧ (k / 2^(m-n)) % 2 = 1) (Finset.range (2^m))).card := by
  -- The bijection k ↦ k ⊕ 2^(m-n) maps between these sets
  let j := m - n
  have hj : j ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt h)
  have hj_lt : j < m := Nat.sub_lt hm hn
  let S₀ := Finset.filter (fun k => k % 2 = b₂ ∧ (k / 2^j) % 2 = 0) (Finset.range (2^m))
  let S₁ := Finset.filter (fun k => k % 2 = b₂ ∧ (k / 2^j) % 2 = 1) (Finset.range (2^m))
  -- Define the bijection
  let f : ℕ → ℕ := fun k => k ^^^ 2^j
  -- f is an involution
  have hf_inv : ∀ k, f (f k) = k := fun k => Nat.xor_xor_cancel_right k (2^j)
  -- f preserves membership in range
  have hf_range : ∀ k, k < 2^m → f k < 2^m := fun k hk => xor_pow_lt k j m hk hj_lt
  -- f maps S₀ to S₁
  have hf_maps : ∀ k ∈ S₀, f k ∈ S₁ := by
    intro k hk
    simp only [S₀, S₁, Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hk_range, hk_mod, hk_div⟩ := hk
    refine ⟨hf_range k hk_range, (xor_pow_mod_two k j hj).trans hk_mod, ?_⟩
    rw [xor_pow_toggles_div_mod, hk_div]
  -- Similarly, f maps S₁ to S₀
  have hf_maps_back : ∀ k ∈ S₁, f k ∈ S₀ := by
    intro k hk
    simp only [S₀, S₁, Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hk_range, hk_mod, hk_div⟩ := hk
    refine ⟨hf_range k hk_range, (xor_pow_mod_two k j hj).trans hk_mod, ?_⟩
    rw [xor_pow_toggles_div_mod, hk_div]
  -- Since f is an involution mapping S₀ ↔ S₁, they have equal cardinality
  have hbij : S₀.card = S₁.card := by
    apply Finset.card_bij (fun k _ => f k) hf_maps
    · -- Injectivity
      intro a ha b hb hab
      have h1 := hf_inv a
      have h2 := hf_inv b
      rw [hab] at h1
      exact h1.symm.trans h2
    · -- Surjectivity
      intro b hb
      use f b, hf_maps_back b hb
      exact hf_inv b
  exact hbij

/-- Symmetric version of xor_bijection_card_eq for n > m.
Here we toggle d_n (bit 0) while preserving d_m (bit n-m). -/
theorem xor_bijection_card_eq' (n m b₂ : ℕ) (hn : n ≥ 1) (_hm : m ≥ 1) (h : m < n) (_hb₂ : b₂ ≤ 1) :
    (Finset.filter (fun k => (k / 2^(n-m)) % 2 = b₂ ∧ k % 2 = 0) (Finset.range (2^n))).card =
    (Finset.filter (fun k => (k / 2^(n-m)) % 2 = b₂ ∧ k % 2 = 1) (Finset.range (2^n))).card := by
  -- The bijection k ↦ k ⊕ 1 toggles bit 0 while preserving bit (n-m) ≥ 1
  let j := n - m
  have hj : j ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt h)
  let S₀ := Finset.filter (fun k => (k / 2^j) % 2 = b₂ ∧ k % 2 = 0) (Finset.range (2^n))
  let S₁ := Finset.filter (fun k => (k / 2^j) % 2 = b₂ ∧ k % 2 = 1) (Finset.range (2^n))
  let f : ℕ → ℕ := fun k => k ^^^ 1
  have hf_inv : ∀ k, f (f k) = k := fun k => Nat.xor_xor_cancel_right k 1
  have hf_range : ∀ k, k < 2^n → f k < 2^n := fun k hk => by
    simp only [f]
    have hn_ne : n ≠ 0 := by omega
    exact Nat.xor_lt_two_pow hk (Nat.one_lt_two_pow hn_ne)
  -- XOR with 1 preserves (k / 2^j) % 2 when j ≥ 1
  have hf_preserves_high : ∀ k, (f k / 2^j) % 2 = (k / 2^j) % 2 := by
    intro k
    simp only [f]
    -- XOR with 1 only affects bit 0, not bit j ≥ 1
    -- Use testBit: (k ^^^ 1).testBit j = k.testBit j for j ≥ 1
    have h1_testBit : (1 : ℕ).testBit j = false := by
      rw [Nat.testBit_eq_false_of_lt]
      exact Nat.one_lt_two_pow (by omega : j ≠ 0)
    have h1 : (k ^^^ 1).testBit j = k.testBit j := by
      rw [Nat.testBit_xor, h1_testBit, Bool.xor_false]
    -- Convert testBit equality to div/mod equality
    rw [testBit_eq_div_mod, testBit_eq_div_mod] at h1
    have hmod_cases1 : (k ^^^ 1) / 2^j % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))
    have hmod_cases2 : k / 2^j % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))
    interval_cases (k ^^^ 1) / 2^j % 2 <;> interval_cases k / 2^j % 2 <;> simp_all
  -- XOR with 1 toggles k % 2
  have hf_toggles : ∀ k, (f k) % 2 = 1 - k % 2 := by
    intro k
    simp only [f]
    rw [Nat.xor_mod_two_eq]
    have hmod_le : k % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt k (by omega))
    omega
  have hf_maps : ∀ k ∈ S₀, f k ∈ S₁ := by
    intro k hk
    simp only [S₀, S₁, Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hk_range, hk_high, hk_low⟩ := hk
    refine ⟨hf_range k hk_range, ?_, ?_⟩
    · rw [hf_preserves_high]; exact hk_high
    · rw [hf_toggles, hk_low]
  have hf_maps_back : ∀ k ∈ S₁, f k ∈ S₀ := by
    intro k hk
    simp only [S₀, S₁, Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hk_range, hk_high, hk_low⟩ := hk
    refine ⟨hf_range k hk_range, ?_, ?_⟩
    · rw [hf_preserves_high]; exact hk_high
    · rw [hf_toggles, hk_low]
  have hbij : S₀.card = S₁.card := by
    apply Finset.card_bij (fun k _ => f k) hf_maps
    · intro a ha b hb hab
      have h1 := hf_inv a; have h2 := hf_inv b
      rw [hab] at h1; exact h1.symm.trans h2
    · intro b hb
      use f b, hf_maps_back b hb
      exact hf_inv b
  exact hbij

/-- A rank-m interval: (k/2^m, (k+1)/2^m]. -/
def rankMInterval (m k : ℕ) : Set ℝ :=
  Set.Ioc ((k : ℝ) / 2^m) (((k : ℕ) + 1 : ℝ) / 2^m)

/-- Rank-m intervals are measurable. -/
theorem rankMInterval_measurableSet (m k : ℕ) : MeasurableSet (rankMInterval m k) :=
  measurableSet_Ioc

/-- Volume of a rank-m interval is 1/2^m. -/
theorem volume_rankMInterval (m k : ℕ) :
    volume (rankMInterval m k) = (1 : ℝ≥0∞) / 2^m := by
  simp only [rankMInterval, Real.volume_Ioc]
  have hcalc : ((k : ℕ) + 1 : ℝ) / 2^m - (k : ℝ) / 2^m = 1 / 2^m := by field_simp; ring
  rw [hcalc, ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^m)]
  simp only [ENNReal.ofReal_one]
  congr 1
  simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- Rank-m intervals are pairwise disjoint. -/
theorem rankMInterval_pairwiseDisjoint (m : ℕ) :
    ∀ i j : ℕ, i ≠ j → Disjoint (rankMInterval m i) (rankMInterval m j) := by
  intro i j hij
  rw [Set.disjoint_iff]
  intro x ⟨hi, hj⟩
  simp only [rankMInterval, Set.mem_Ioc] at hi hj
  have hpos : (0 : ℝ) < 2^m := by positivity
  by_cases h : i < j
  · have hnat : (i : ℕ) + 1 ≤ j := h
    have hbound : ((i : ℕ) + 1 : ℝ) / 2^m ≤ (j : ℝ) / 2^m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
      exact_mod_cast hnat
    linarith [hi.1, hi.2, hj.1, hj.2]
  · push Not at h
    have hne : j < i := Nat.lt_of_le_of_ne h (Ne.symm hij)
    have hnat : (j : ℕ) + 1 ≤ i := hne
    have hbound : ((j : ℕ) + 1 : ℝ) / 2^m ≤ (i : ℝ) / 2^m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
      exact_mod_cast hnat
    linarith [hi.1, hi.2, hj.1, hj.2]

/-- Rank-m intervals with k < 2^m are subsets of halfOpenUnit. -/
theorem rankMInterval_subset_halfOpenUnit (m k : ℕ) (hk : k < 2^m) :
    rankMInterval m k ⊆ halfOpenUnit := by
  intro ω hω
  simp only [rankMInterval, Set.mem_Ioc, halfOpenUnit] at hω ⊢
  have hpos : (0 : ℝ) < 2^m := by positivity
  constructor
  · -- ω > k/2^m ≥ 0
    have hge : (k : ℝ) / 2^m ≥ 0 := by positivity
    linarith [hω.1]
  · calc ω ≤ ((k : ℕ) + 1 : ℝ) / 2^m := hω.2
      _ ≤ (2^m : ℝ) / 2^m := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
          have h : (k : ℕ) + 1 ≤ 2^m := hk
          exact_mod_cast h
      _ = 1 := div_self (ne_of_gt hpos)

/-- The union of rank-m intervals over a Finset has measure = card * (1/2^m). -/
theorem volume_iUnion_rankMInterval (m : ℕ) (S : Finset ℕ) (_hS : ∀ k ∈ S, k < 2^m) :
    volume (⋃ k ∈ S, rankMInterval m k) = S.card * ((1 : ℝ≥0∞) / 2^m) := by
  have h_pw : (S : Set ℕ).PairwiseDisjoint (rankMInterval m) := by
    intro i hi j hj hij
    exact rankMInterval_pairwiseDisjoint m i j hij
  rw [measure_biUnion_finset h_pw (fun k _ => rankMInterval_measurableSet m k)]
  simp only [volume_rankMInterval]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]

/-- For ω in the interior of a rank-m interval with m ≥ 1, dyadicDigit m ω = k % 2.
This is for ω ∈ Ioo, excluding the right boundary. -/
theorem dyadicDigit_of_mem_rankMInterval_interior (m k : ℕ) (ω : ℝ) (hm : m ≥ 1)
    (hω : ω ∈ Set.Ioo ((k : ℝ) / 2^m) (((k : ℕ) + 1 : ℝ) / 2^m)) (_hk : k < 2^m) :
    dyadicDigit m ω = k % 2 := by
  simp only [Set.mem_Ioo] at hω
  have hpos : (0 : ℝ) < 2^m := by positivity
  have hm_pos : m ≠ 0 := by omega
  have h_floor : ⌊ω * 2^m⌋ = k := by
    rw [Int.floor_eq_iff]
    constructor
    · -- k ≤ ω * 2^m (strict: k < ω * 2^m)
      have h1 : (k : ℝ) / 2^m < ω := hω.1
      have hcalc : (k : ℝ) / 2^m * 2^m < ω * 2^m := by nlinarith
      have hk_eq : (k : ℝ) / 2^m * 2^m = k := by field_simp
      rw [hk_eq] at hcalc
      have hk_int : (k : ℤ) = (k : ℝ) := by simp
      linarith
    · -- ω * 2^m < k + 1
      have h2 : ω < ((k : ℕ) + 1 : ℝ) / 2^m := hω.2
      have hcalc : ω * 2^m < ((k : ℕ) + 1 : ℝ) / 2^m * 2^m := by nlinarith
      have hk1_eq : ((k : ℕ) + 1 : ℝ) / 2^m * 2^m = ((k : ℕ) + 1 : ℝ) := by field_simp
      rw [hk1_eq] at hcalc
      have hcast : ((k : ℕ) + 1 : ℝ) = ((k : ℤ) + 1 : ℝ) := by norm_cast
      rw [hcast] at hcalc
      linarith
  -- Since ω is in the open interval, ω * 2^m is strictly between k and k+1
  have h_frac_pos : ω * 2^m - ⌊ω * 2^m⌋ > 0 := by
    rw [h_floor]
    have h1 : (k : ℝ) / 2^m < ω := hω.1
    have hcalc : (k : ℝ) < ω * 2^m := by
      have h_eq : (k : ℝ) / 2^m * 2^m = k := by field_simp
      nlinarith
    simp only [Int.cast_natCast]
    linarith
  -- Now unfold dyadicDigit and simplify
  simp only [dyadicDigit, hm_pos, ↓reduceIte]
  rw [h_floor] at h_frac_pos
  simp only [Int.cast_natCast] at h_frac_pos
  -- The goal has ↑↑k (ℕ → ℤ → ℝ), normalize to ↑k (ℕ → ℝ)
  simp only [Int.cast_natCast, h_floor]
  simp only [if_pos h_frac_pos, Int.toNat_natCast]

/-- For ω in the interior of a rank-m interval with n < m, dyadicDigit n ω = (k / 2^(m-n)) % 2.
This extends the interior formula to the lower digit. -/
theorem dyadicDigit_lower_of_mem_rankMInterval_interior (n m k : ℕ) (ω : ℝ) (hn : n ≥ 1) (_hm : m ≥ 1) (hnm : n < m)
    (hω : ω ∈ Set.Ioo ((k : ℝ) / 2^m) (((k : ℕ) + 1 : ℝ) / 2^m)) (_hk : k < 2^m) :
    dyadicDigit n ω = (k / 2^(m-n)) % 2 := by
  simp only [Set.mem_Ioo] at hω
  have hpos_m : (0 : ℝ) < 2^m := by positivity
  have hpos_n : (0 : ℝ) < 2^n := by positivity
  have hn_pos : n ≠ 0 := by omega
  have hj_pos : m - n > 0 := Nat.sub_pos_of_lt hnm
  have hpos_j : (0 : ℝ) < 2^(m-n) := by positivity
  -- The key is that ω ∈ (k/2^m, (k+1)/2^m) implies ⌊ω * 2^n⌋ = k / 2^(m-n)
  -- ω * 2^n ∈ (k * 2^n / 2^m, (k+1) * 2^n / 2^m) = (k / 2^(m-n), (k+1) / 2^(m-n))
  have h_floor : ⌊ω * 2^n⌋ = k / 2^(m-n) := by
    rw [Int.floor_eq_iff]
    constructor
    · -- k / 2^(m-n) ≤ ω * 2^n
      have h1 : (k : ℝ) / 2^m < ω := hω.1
      have h_scale : (k : ℝ) / 2^m * 2^n = (k : ℝ) / 2^(m-n) := by
        have hpow : (2 : ℝ)^m = 2^n * 2^(m-n) := by
          rw [← pow_add]; congr 1; omega
        field_simp [ne_of_gt hpos_n, ne_of_gt hpos_j]
        rw [hpow]; ring
      have hcalc : (k : ℝ) / 2^(m-n) < ω * 2^n := by
        rw [← h_scale]; nlinarith
      have h_nat_le : (k / 2^(m-n) : ℕ) ≤ (k : ℝ) / 2^(m-n) := by
        have hdiv : (k / 2^(m-n) : ℕ) * 2^(m-n) ≤ k := Nat.div_mul_le_self k _
        calc ((k / 2^(m-n) : ℕ) : ℝ) = (k / 2^(m-n) : ℕ) * 2^(m-n) / 2^(m-n) := by
              field_simp
          _ ≤ (k : ℝ) / 2^(m-n) := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hpos_j)
              exact_mod_cast hdiv
      have h_le : ((k / 2^(m-n) : ℕ) : ℝ) < ω * 2^n := by
        calc ((k / 2^(m-n) : ℕ) : ℝ) ≤ (k : ℝ) / 2^(m-n) := h_nat_le
          _ < ω * 2^n := hcalc
      exact_mod_cast le_of_lt h_le
    · -- ω * 2^n < k / 2^(m-n) + 1
      have h2 : ω < ((k : ℕ) + 1 : ℝ) / 2^m := hω.2
      have h_scale : ((k : ℕ) + 1 : ℝ) / 2^m * 2^n = ((k : ℕ) + 1 : ℝ) / 2^(m-n) := by
        have hpow : (2 : ℝ)^m = 2^n * 2^(m-n) := by
          rw [← pow_add]; congr 1; omega
        calc ((k : ℕ) + 1 : ℝ) / 2^m * 2^n
            = ((k : ℕ) + 1 : ℝ) / (2^n * 2^(m-n)) * 2^n := by rw [hpow]
          _ = ((k : ℕ) + 1 : ℝ) * 2^n / (2^n * 2^(m-n)) := by ring
          _ = ((k : ℕ) + 1 : ℝ) / 2^(m-n) := by field_simp [ne_of_gt hpos_n]
      have hcalc : ω * 2^n < ((k : ℕ) + 1 : ℝ) / 2^(m-n) := by
        rw [← h_scale]; nlinarith
      -- Need: ω * 2^n < ↑(k / 2^(m-n)) + 1
      -- We have: ω * 2^n < (k+1) / 2^(m-n)
      -- Key: (k+1) / 2^(m-n) ≤ k / 2^(m-n) + 1
      have hdiv : ((k : ℕ) + 1 : ℝ) / 2^(m-n) ≤ (k / 2^(m-n) : ℕ) + 1 := by
        have hnat : (k + 1 : ℕ) ≤ (k / 2^(m-n) + 1) * 2^(m-n) := by
          have hdiv_ineq : k / 2^(m-n) * 2^(m-n) + 2^(m-n) = (k / 2^(m-n) + 1) * 2^(m-n) := by ring
          rw [← hdiv_ineq]
          have hrem : k % 2^(m-n) < 2^(m-n) := Nat.mod_lt k (Nat.two_pow_pos (m-n))
          have hdivmod : k = k / 2^(m-n) * 2^(m-n) + k % 2^(m-n) := by
            rw [mul_comm]; exact (Nat.div_add_mod k (2^(m-n))).symm
          omega
        calc ((k : ℕ) + 1 : ℝ) / 2^(m-n)
            ≤ ((k / 2^(m-n) + 1) * 2^(m-n) : ℕ) / 2^(m-n) := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hpos_j)
              exact_mod_cast hnat
          _ = ((k / 2^(m-n) + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_mul, mul_div_assoc]
              simp [ne_of_gt hpos_j]
          _ = (k / 2^(m-n) : ℕ) + 1 := by norm_cast
      calc ω * 2^n < ((k : ℕ) + 1 : ℝ) / 2^(m-n) := hcalc
        _ ≤ (k / 2^(m-n) : ℕ) + 1 := hdiv
        _ = (↑(k / 2^(m-n)) : ℤ) + 1 := by norm_cast
  -- Since ω is in the open interval, ω * 2^n is not an integer
  have h_frac_pos : ω * 2^n - ⌊ω * 2^n⌋ > 0 := by
    rw [h_floor]
    have h1 : (k : ℝ) / 2^m < ω := hω.1
    have h_scale : (k : ℝ) / 2^m * 2^n = (k : ℝ) / 2^(m-n) := by
      have hpow : (2 : ℝ)^m = 2^n * 2^(m-n) := by
        rw [← pow_add]; congr 1; omega
      field_simp [ne_of_gt hpos_n, ne_of_gt hpos_j]
      rw [hpow]; ring
    have hcalc : (k : ℝ) / 2^(m-n) < ω * 2^n := by
      rw [← h_scale]; nlinarith
    have h_nat_le : (k / 2^(m-n) : ℕ) ≤ (k : ℝ) / 2^(m-n) := by
      have hdiv : (k / 2^(m-n) : ℕ) * 2^(m-n) ≤ k := Nat.div_mul_le_self k _
      calc ((k / 2^(m-n) : ℕ) : ℝ) = (k / 2^(m-n) : ℕ) * 2^(m-n) / 2^(m-n) := by
            field_simp
        _ ≤ (k : ℝ) / 2^(m-n) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hpos_j)
            exact_mod_cast hdiv
    -- After rw [h_floor], goal is ω * 2^n - ↑↑(k / 2^(m-n)) > 0
    -- where ↑↑ is ℕ → ℤ → ℝ, which simplifies to ℕ → ℝ
    calc ω * 2^n - ↑↑(k / 2^(m-n))
        > (k : ℝ) / 2^(m-n) - ↑↑(k / 2^(m-n)) := by linarith
      _ = (k : ℝ) / 2^(m-n) - (k / 2^(m-n) : ℕ) := by norm_cast
      _ ≥ 0 := by linarith
  -- Now unfold dyadicDigit and simplify
  simp only [dyadicDigit, hn_pos, ↓reduceIte]
  rw [h_floor] at h_frac_pos
  norm_cast at h_frac_pos
  simp only [h_floor]
  norm_cast
  simp only [if_pos h_frac_pos, Int.toNat_natCast]

/-- The Finset of rank-m interval indices for digitSet n b₁ ∩ digitSet m b₂ when n < m. -/
def digitSetInterFinset (n m b₁ b₂ : ℕ) : Finset ℕ :=
  Finset.filter (fun k => k % 2 = b₂ ∧ (k / 2^(m-n)) % 2 = b₁) (Finset.range (2^m))

/-- Elements of digitSetInterFinset are in range. -/
theorem digitSetInterFinset_subset (n m b₁ b₂ : ℕ) : ∀ k ∈ digitSetInterFinset n m b₁ b₂, k < 2^m := by
  intro k hk
  simp only [digitSetInterFinset, Finset.mem_filter, Finset.mem_range] at hk
  exact hk.1

/-- The union of rank-m intervals for indices in digitSetInterFinset equals
digitSet n b₁ ∩ digitSet m b₂ up to measure zero (on the interior).

**Proof Strategy:**
For ω not on a rank-m boundary (ω * 2^m ∉ ℤ), we have:
1. ω lies in exactly one Ioo interval (k/2^m, (k+1)/2^m)
2. For such ω, dyadicDigit m ω = k % 2 and dyadicDigit n ω = (k / 2^(m-n)) % 2
3. Thus ω ∈ digitSet n b₁ ∩ digitSet m b₂ iff k ∈ digitSetInterFinset -/
theorem digitSetInter_interior_eq_iUnion (n m b₁ b₂ : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n < m)
    (_hb₁ : b₁ ≤ 1) (_hb₂ : b₂ ≤ 1) :
    ∀ ω, ω ∈ Set.Ioo (0 : ℝ) 1 →
      (∀ j : ℕ, j ≤ 2^m → ω * 2^m ≠ j) →  -- ω is not a rank-m boundary
      (ω ∈ digitSet n b₁ ∩ digitSet m b₂ ↔
       ω ∈ ⋃ k ∈ digitSetInterFinset n m b₁ b₂, Set.Ioo ((k : ℝ) / 2^m) (((k : ℕ) + 1 : ℝ) / 2^m)) := by
  intro ω hω_unit hω_not_boundary
  have hpos : (0 : ℝ) < 2^m := by positivity
  -- Find the unique interval containing ω
  have hk_exists : ∃ k : ℕ, k < 2^m ∧ ω ∈ Set.Ioo ((k : ℝ) / 2^m) (((k : ℕ) + 1 : ℝ) / 2^m) := by
    let k := (⌊ω * 2^m⌋).toNat
    have hω_pos : 0 < ω * 2^m := by nlinarith [hω_unit.1]
    have hω_lt : ω * 2^m < 2^m := by nlinarith [hω_unit.2]
    have hfloor_nn : 0 ≤ ⌊ω * 2^m⌋ := Int.floor_nonneg.mpr (le_of_lt hω_pos)
    have hfloor_lt : ⌊ω * 2^m⌋ < (2^m : ℤ) := by
      rw [Int.floor_lt]; exact_mod_cast hω_lt
    have hk_range : k < 2^m := by
      simp only [k]
      have h1 : (⌊ω * 2^m⌋.toNat : ℤ) < 2^m := by
        rw [Int.toNat_of_nonneg hfloor_nn]
        exact hfloor_lt
      exact_mod_cast h1
    use k, hk_range
    simp only [Set.mem_Ioo, k]
    constructor
    · -- ω > k / 2^m
      have hcast : ((⌊ω * 2^m⌋.toNat : ℕ) : ℝ) = (⌊ω * 2^m⌋ : ℤ) := by
        have h := Int.toNat_of_nonneg hfloor_nn
        exact_mod_cast h
      rw [hcast]
      have hfloor_le := Int.floor_le (ω * 2^m)
      -- Need strict inequality. Since ω is not a boundary, ω * 2^m ≠ floor
      have hstrict : (⌊ω * 2^m⌋ : ℝ) < ω * 2^m := by
        have hle := Int.floor_le (ω * 2^m)
        rcases hle.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          have : ω * 2^m = ⌊ω * 2^m⌋ := heq.symm
          have hnat : ⌊ω * 2^m⌋.toNat ≤ 2^m := by
            have h1 : (⌊ω * 2^m⌋.toNat : ℤ) < 2^m := by
              rw [Int.toNat_of_nonneg hfloor_nn]; exact hfloor_lt
            omega
          have heq' : ω * 2^m = (⌊ω * 2^m⌋.toNat : ℕ) := by
            have h := Int.toNat_of_nonneg hfloor_nn
            have h1 : ω * 2^m = (⌊ω * 2^m⌋ : ℝ) := heq.symm
            have h2 : (⌊ω * 2^m⌋ : ℝ) = (⌊ω * 2^m⌋.toNat : ℕ) := by
              have h3 : (⌊ω * 2^m⌋.toNat : ℤ) = ⌊ω * 2^m⌋ := h
              exact_mod_cast h3.symm
            rw [h2] at h1
            exact h1
          exact hω_not_boundary ⌊ω * 2^m⌋.toNat hnat heq'
      rw [div_lt_iff₀ hpos]
      exact hstrict
    · -- ω < (k + 1) / 2^m
      have hcast : ((⌊ω * 2^m⌋.toNat : ℕ) : ℝ) = (⌊ω * 2^m⌋ : ℤ) := by
        have h := Int.toNat_of_nonneg hfloor_nn
        exact_mod_cast h
      -- Goal: ω < (↑⌊ω * 2^m⌋.toNat + 1) / 2^m
      -- First simplify the numerator
      have h_num : (⌊ω * 2^m⌋.toNat : ℝ) + 1 = (⌊ω * 2^m⌋ : ℤ) + 1 := by
        have h := Int.toNat_of_nonneg hfloor_nn
        have h' : (⌊ω * 2^m⌋.toNat : ℝ) = (⌊ω * 2^m⌋ : ℤ) := by exact_mod_cast h
        linarith
      rw [h_num, lt_div_iff₀ hpos]
      exact Int.lt_floor_add_one (ω * 2^m)
  obtain ⟨k, hk_range, hω_in_k⟩ := hk_exists
  constructor
  · -- digitSet membership → interval membership
    intro hω_digit
    rw [Set.mem_iUnion₂]
    refine ⟨k, ?_, hω_in_k⟩
    simp only [digitSetInterFinset, Finset.mem_filter, Finset.mem_range]
    refine ⟨hk_range, ?_, ?_⟩
    · -- k % 2 = b₂
      have h := dyadicDigit_of_mem_rankMInterval_interior m k ω hm hω_in_k hk_range
      simp only [digitSet, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω_digit
      rw [← hω_digit.2.2, h]
    · -- (k / 2^(m-n)) % 2 = b₁
      have h := dyadicDigit_lower_of_mem_rankMInterval_interior n m k ω hn hm hnm hω_in_k hk_range
      simp only [digitSet, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω_digit
      rw [← hω_digit.1.2, h]
  · -- interval membership → digitSet membership
    intro hω_interval
    rw [Set.mem_iUnion₂] at hω_interval
    obtain ⟨k', hk'_mem, hω_k'⟩ := hω_interval
    simp only [digitSetInterFinset, Finset.mem_filter, Finset.mem_range] at hk'_mem
    obtain ⟨hk'_range, hk'_mod, hk'_div⟩ := hk'_mem
    simp only [digitSet, halfOpenUnit, Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hω_unit' : ω ∈ halfOpenUnit := by
      simp only [halfOpenUnit, Set.mem_Ioc]
      exact ⟨hω_unit.1, le_of_lt hω_unit.2⟩
    refine ⟨⟨hω_unit', ?_⟩, ⟨hω_unit', ?_⟩⟩
    · -- dyadicDigit n ω = b₁
      have h := dyadicDigit_lower_of_mem_rankMInterval_interior n m k' ω hn hm hnm hω_k' hk'_range
      rw [h, hk'_div]
    · -- dyadicDigit m ω = b₂
      have h := dyadicDigit_of_mem_rankMInterval_interior m k' ω hm hω_k' hk'_range
      rw [h, hk'_mod]

/-- The measure of digitSet n b₁ ∩ digitSet m b₂ equals |digitSetInterFinset| × (1/2^m).

**Proof Strategy:**
1. Volume of interval union = card × (1/2^m) via `volume_iUnion_rankMInterval`
2. Boundary points (dyadic rationals k/2^m) form a finite set with measure zero
3. IooUnion ⊆ digitInter (interior points satisfy digit conditions)
4. digitInter ⊆ IooUnion ∪ boundary (digit set equals interior plus boundaries)
5. IooUnion ⊆ IocUnion (open ⊆ half-open for each interval)
6. IocUnion \ IooUnion ⊆ boundary (difference is right endpoints)
7. volume IooUnion = volume IocUnion (differ by null set)
8. volume digitInter = volume IooUnion (via measure_eq_measure_of_between_null_diff)
9. Combine: volume(digit set) = volume(interval union) = card × (1/2^m)
-/
theorem volume_digitSetInter_eq_card (n m b₁ b₂ : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n < m)
    (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1) :
    volume (digitSet n b₁ ∩ digitSet m b₂) =
    (digitSetInterFinset n m b₁ b₂).card * ((1 : ℝ≥0∞) / 2^m) := by
  -- Define the boundary set (dyadic rationals with denominator 2^m)
  let boundary : Set ℝ := {ω | ∃ j : ℕ, j ≤ 2^m ∧ ω = (j : ℝ) / 2^m}
  -- The boundary is finite
  have h_boundary_finite : boundary.Finite := by
    have h : boundary ⊆ ((Finset.range (2^m + 1)).image (fun j : ℕ => (j : ℝ) / 2^m) : Set ℝ) := by
      intro ω ⟨k, hk_le, hω_eq⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
      exact ⟨k, Nat.lt_add_one_iff.mpr hk_le, hω_eq.symm⟩
    exact Set.Finite.subset (Finset.finite_toSet _) h
  -- The boundary has measure zero (since volume on ℝ has no atoms)
  have h_boundary_null : volume boundary = 0 := h_boundary_finite.measure_zero volume
  -- The IocUnion has volume = card × (1/2^m)
  have h_union_vol : volume (⋃ i ∈ digitSetInterFinset n m b₁ b₂, rankMInterval m i) =
      (digitSetInterFinset n m b₁ b₂).card * ((1 : ℝ≥0∞) / 2^m) := by
    exact volume_iUnion_rankMInterval m (digitSetInterFinset n m b₁ b₂) (digitSetInterFinset_subset n m b₁ b₂)
  -- The digit set and interval union differ only on the null boundary set
  -- This follows from digitSetInter_interior_eq_iUnion and the fact that
  -- Ioo and Ioc intervals differ only at right endpoints (boundary points)
  have h_digit_ae : ((digitSet n b₁ ∩ digitSet m b₂) : Set ℝ) =ᵐ[volume]
      (⋃ i ∈ digitSetInterFinset n m b₁ b₂, rankMInterval m i) := by
    -- The symmetric difference is contained in the boundary (null set)
    -- Using digitSetInter_interior_eq_iUnion for non-boundary ω, membership is equivalent
    -- Boundary points have measure zero since volume has no atoms
    rw [ae_eq_set]
    constructor
    · -- (digitSet ∩ digitSet) \ IocUnion ⊆ boundary
      apply measure_mono_null _ h_boundary_null
      intro ω hω
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion₂] at hω
      obtain ⟨⟨⟨hω_unit, hd_n⟩, ⟨_, hd_m⟩⟩, hω_not_union⟩ := hω
      -- ω is in the digit set but not in any Ioc interval
      -- This means ω must be on a boundary (left endpoints at k/2^m for k > 0 only)
      -- Actually, the digit set is contained in halfOpenUnit = (0,1] which is ⋃ Ioc intervals
      -- So the difference is contained in the set of left endpoints (k/2^m for k ≤ 2^m)
      simp only [boundary, Set.mem_ofPred_eq]
      -- For non-boundary ω, digitSetInter_interior_eq_iUnion gives equivalence
      -- If ω is not a boundary point, then ω ∈ Ioo for some k, hence ω ∈ Ioc
      by_contra h_not_boundary
      push Not at h_not_boundary
      have hω_Ioo : ω ∈ Set.Ioo (0 : ℝ) 1 := by
        simp only [halfOpenUnit, Set.mem_Ioc] at hω_unit
        constructor
        · exact hω_unit.1
        · -- If ω = 1, then ω = 2^m / 2^m is a boundary point
          by_contra h_ge
          push Not at h_ge
          have h_eq : ω = 1 := le_antisymm hω_unit.2 h_ge
          have h_pos : (0 : ℝ) < 2^m := by positivity
          have h_pow : ((2^m : ℕ) : ℝ) / 2^m = 1 := by
            rw [div_eq_one_iff_eq (ne_of_gt h_pos)]; norm_cast
          exact h_not_boundary (2^m) (le_refl _) (by rw [h_eq]; exact h_pow.symm)
      have h_not_bdry : ∀ j : ℕ, j ≤ 2^m → ω * 2^m ≠ j := by
        intro j hj hω_eq
        have h_pos : (0 : ℝ) < 2^m := by positivity
        have h_omega_eq : ω = (j : ℝ) / 2^m := by field_simp [ne_of_gt h_pos] at hω_eq ⊢; linarith
        exact h_not_boundary j hj h_omega_eq
      have h_equiv := digitSetInter_interior_eq_iUnion n m b₁ b₂ hn hm hnm hb₁ hb₂ ω hω_Ioo h_not_bdry
      -- ω ∈ digitSet ∩ digitSet, so by h_equiv, ω ∈ Ioo union
      have hω_digit : ω ∈ digitSet n b₁ ∩ digitSet m b₂ := by
        simp only [digitSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨⟨hω_unit, hd_n⟩, ⟨hω_unit, hd_m⟩⟩
      rw [h_equiv] at hω_digit
      -- ω ∈ Ioo union, so ω ∈ Ioc union (since Ioo ⊆ Ioc)
      rw [Set.mem_iUnion₂] at hω_digit
      obtain ⟨k, hk_mem, hω_Ioo⟩ := hω_digit
      apply hω_not_union
      exact ⟨k, hk_mem, Set.Ioo_subset_Ioc_self hω_Ioo⟩
    · -- IocUnion \ (digitSet ∩ digitSet) ⊆ boundary
      apply measure_mono_null _ h_boundary_null
      intro ω hω
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion₂] at hω
      obtain ⟨⟨k, hk_mem, hω_Ioc⟩, hω_not_digit⟩ := hω
      simp only [boundary, Set.mem_ofPred_eq]
      -- ω is in Ioc(k/2^m, (k+1)/2^m) but not in the digit set
      -- For non-boundary ω in Ioo, digitSetInter_interior_eq_iUnion gives membership
      -- So if ω ∈ Ioc but ω ∉ digitSet, then ω must be the right endpoint (k+1)/2^m
      have hk_lt := digitSetInterFinset_subset n m b₁ b₂ k hk_mem
      simp only [rankMInterval, Set.mem_Ioc] at hω_Ioc
      -- Check if ω = (k+1)/2^m (right endpoint)
      by_cases hω_eq : ω = ((k : ℕ) + 1 : ℝ) / 2^m
      · have h_cast : ((k : ℕ) + 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by norm_cast
        exact ⟨k + 1, by omega, by rw [hω_eq, h_cast]⟩
      · -- ω ∈ Ioo(k/2^m, (k+1)/2^m)
        have hω_Ioo : ω ∈ Set.Ioo ((k : ℝ) / 2^m) (((k : ℕ) + 1 : ℝ) / 2^m) :=
          ⟨hω_Ioc.1, lt_of_le_of_ne hω_Ioc.2 hω_eq⟩
        have hω_Ioo01 : ω ∈ Set.Ioo (0 : ℝ) 1 := by
          have h_pos : (0 : ℝ) < 2^m := by positivity
          constructor
          · rcases Nat.eq_zero_or_pos k with rfl | hk_pos
            · simp at hω_Ioo; exact hω_Ioo.1
            · calc 0 < (k : ℝ) / 2^m := by positivity
              _ < ω := hω_Ioo.1
          · calc ω < ((k : ℕ) + 1 : ℝ) / 2^m := hω_Ioo.2
            _ ≤ (2^m : ℝ) / 2^m := by
                apply div_le_div_of_nonneg_right _ (le_of_lt h_pos)
                have h1 : (k : ℝ) + 1 ≤ 2^m := by exact_mod_cast hk_lt
                have h2 : ((k : ℕ) + 1 : ℝ) = (k : ℝ) + 1 := by norm_cast
                linarith
            _ = 1 := by field_simp
        -- ω is not a boundary point since it's strictly inside the interval
        have h_not_bdry : ∀ j : ℕ, j ≤ 2^m → ω * 2^m ≠ j := by
          intro j hj hω_mul
          have h_pos : (0 : ℝ) < 2^m := by positivity
          have hω_eq' : ω = (j : ℝ) / 2^m := by field_simp [ne_of_gt h_pos] at hω_mul ⊢; linarith
          -- ω = j/2^m but ω ∈ Ioo(k/2^m, (k+1)/2^m), so k < j < k+1, contradiction
          rw [hω_eq'] at hω_Ioo
          simp only [Set.mem_Ioo] at hω_Ioo
          have hk_lt_j : (k : ℝ) < j := by
            have := hω_Ioo.1
            calc (k : ℝ) = (k : ℝ) / 2^m * 2^m := by field_simp
            _ < (j : ℝ) / 2^m * 2^m := by nlinarith
            _ = j := by field_simp
          have hj_lt_k1 : (j : ℝ) < (k : ℕ) + 1 := by
            have := hω_Ioo.2
            calc (j : ℝ) = (j : ℝ) / 2^m * 2^m := by field_simp
            _ < ((k : ℕ) + 1 : ℝ) / 2^m * 2^m := by nlinarith
            _ = (k : ℕ) + 1 := by field_simp
          have : k < j := by exact_mod_cast hk_lt_j
          have : j < k + 1 := by exact_mod_cast hj_lt_k1
          omega
        have h_equiv := digitSetInter_interior_eq_iUnion n m b₁ b₂ hn hm hnm hb₁ hb₂ ω hω_Ioo01 h_not_bdry
        -- ω ∈ Ioo union, so ω ∈ digit set by h_equiv
        have hω_in_Ioo_union : ω ∈ ⋃ i ∈ digitSetInterFinset n m b₁ b₂, Set.Ioo ((i : ℝ) / 2^m) (((i : ℕ) + 1 : ℝ) / 2^m) := by
          rw [Set.mem_iUnion₂]; exact ⟨k, hk_mem, hω_Ioo⟩
        rw [← h_equiv] at hω_in_Ioo_union
        exact absurd hω_in_Ioo_union hω_not_digit
  -- Use measure_congr to conclude equal measures
  calc volume (digitSet n b₁ ∩ digitSet m b₂)
    = volume (⋃ i ∈ digitSetInterFinset n m b₁ b₂, rankMInterval m i) := measure_congr h_digit_ae
    _ = (digitSetInterFinset n m b₁ b₂).card * ((1 : ℝ≥0∞) / 2^m) := h_union_vol

/-- Within digitSet m b₂, exactly half has d_n = 0 and half has d_n = 1.
This is the key symmetry lemma for independence.

The proof proceeds in two stages:
1. We already have the partition: v0 + v1 = 1/2 where v0, v1 are the two volumes
2. We prove v0 = v1 using the Finset cardinality equality from xor_bijection_card_eq

The key insight is that each digit set intersection can be decomposed (up to measure zero)
into a union of rank-M intervals, where M = max(n,m). The intervals have uniform measure
1/2^M, so the total measure equals (count) × (1/2^M). The XOR bijection shows equal counts,
hence equal measures.
-/
theorem volume_digitSet_inter_half (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n ≠ m) (b₂ : ℕ) (hb₂ : b₂ ≤ 1) :
    volume (digitSet n 0 ∩ digitSet m b₂) = volume (digitSet n 1 ∩ digitSet m b₂) := by
  -- Strategy: Express both as unions of dyadic intervals and count.
  -- WLOG assume n < m (the case n > m is symmetric in n, m roles).
  -- For each rank-m interval with d_m = b₂, the value of d_n depends on bit (m-n).
  -- Half of such intervals have d_n = 0, half have d_n = 1.
  --
  -- This is a combinatorial fact about dyadic intervals.
  -- For interval k ∈ {0,...,2^m-1}:
  --   d_m(ω) = k % 2 for ω ∈ (k/2^m, (k+1)/2^m]
  --   d_n(ω) = (k / 2^(m-n)) % 2 (when m > n)
  -- So d_m = b₂ ⟺ k % 2 = b₂, giving 2^(m-1) values of k.
  -- Among these, d_n = 0 ⟺ (k / 2^(m-n)) % 2 = 0.
  -- For m > n, bit 0 and bit (m-n) of k are independent, so half satisfy each.
  --
  -- Rather than prove this combinatorially, we use the four-way partition:
  -- All four intersection sets sum to 1, and by symmetry they're equal.
  -- The symmetry comes from the uniform structure of dyadic intervals.
  by_cases h : n < m
  · -- Case n < m: use interval structure
    -- Within each rank-m interval, d_n is determined by a higher bit
    -- that is uniformly distributed
    have hpos : (0 : ℝ) < 2^m := by positivity
    have hpos_n : (0 : ℝ) < 2^n := by positivity
    -- Count argument: among k with k % 2 = b₂,
    -- half have (k / 2^(m-n)) % 2 = 0 and half have it = 1.
    -- This gives equal volume for both d_n values.
    -- For now, we use a symmetry argument based on structure.
    --
    -- The key observation: the map k ↦ k + 2^(m-n) (mod 2^m)
    -- toggles d_n while preserving d_m (when m > n ≥ 1 and m - n ≥ 1).
    -- This is a bijection on {k : k % 2 = b₂}, so the two sets have equal size.
    -- Formally, we'd show this by induction on m - n.
    --
    -- For the formal proof, we use that both sets have measure ≥ 0 and sum to
    -- vol(digitSet m b₂) = 1/2, combined with the symmetry in the interval structure.
    --
    -- Actually, let's use a more direct approach: the partition tells us
    -- v0 + v1 = 1/2 where v0, v1 are the two volumes.
    -- The symmetry argument (combinatorial counting) gives v0 = v1.
    have h_part : digitSet m b₂ =
        (digitSet n 0 ∩ digitSet m b₂) ∪ (digitSet n 1 ∩ digitSet m b₂) := by
      exact (digitSet_inter_partition_m n m hn hm b₂).symm
    have h_disj : Disjoint (digitSet n 0 ∩ digitSet m b₂) (digitSet n 1 ∩ digitSet m b₂) :=
      digitSet_inter_disjoint_m n m b₂
    have hv : volume (digitSet m b₂) = 1/2 := by
      interval_cases b₂
      · exact volume_digitSet_zero m hm
      · exact volume_digitSet_one m hm
    -- v0 + v1 = 1/2
    have h_sum : volume (digitSet n 0 ∩ digitSet m b₂) + volume (digitSet n 1 ∩ digitSet m b₂) = 1/2 := by
      have h_meas0 : MeasurableSet (digitSet n 0 ∩ digitSet m b₂) := digitSet_inter_measurableSet n m 0 b₂
      have h_meas1 : MeasurableSet (digitSet n 1 ∩ digitSet m b₂) := digitSet_inter_measurableSet n m 1 b₂
      calc volume (digitSet n 0 ∩ digitSet m b₂) + volume (digitSet n 1 ∩ digitSet m b₂)
          = volume ((digitSet n 0 ∩ digitSet m b₂) ∪ (digitSet n 1 ∩ digitSet m b₂)) := by
            rw [measure_union h_disj h_meas1]
        _ = volume (digitSet m b₂) := by rw [← h_part]
        _ = 1/2 := hv
    -- By the interval counting argument (which we accept for now), v0 = v1.
    -- Since v0 + v1 = 1/2 and v0 = v1, we get v0 = v1 = 1/4.
    -- But this theorem just needs v0 = v1, which follows from structure.
    --
    -- We prove this using the explicit interval counting.
    -- For each rank-m interval index k with k % 2 = b₂:
    --   d_n = (k / 2^(m-n)) % 2
    -- The map k ↦ k ⊕ 2^(m-n) (XOR) is a bijection on {k : k % 2 = b₂} that swaps d_n.
    -- This gives equal counts, hence equal measures.
    --
    -- For the formal proof, we use omega/decide on the combinatorial claim.
    -- The claim: |{k < 2^m : k % 2 = b₂ ∧ (k / 2^(m-n)) % 2 = 0}|
    --          = |{k < 2^m : k % 2 = b₂ ∧ (k / 2^(m-n)) % 2 = 1}|
    -- Both equal 2^(m-2) when m ≥ n + 1.
    --
    -- This is a Finset.card equality which we can prove by bijection.
    -- For now, we use the structure directly via a measure argument.
    --
    -- Alternative: use the symmetry that the role of (d_n = 0) vs (d_n = 1)
    -- within digitSet m b₂ is symmetric by reflection about the midpoint.
    --
    -- We'll prove this using the cardinality argument.
    -- The intervals in digitSet m b₂ with d_n = 0 vs d_n = 1 are in bijection
    -- via the shift k ↦ k + 2^(m-n) mod 2^m.
    --
    -- The intersection sets are unions of rank-m intervals.
    -- Since all rank-m intervals have the same measure (1/2^m), and the
    -- xor_bijection_card_eq shows equal cardinalities, the measures are equal.
    --
    -- For the formal proof, we need to:
    -- 1. Express each intersection as a union of rank-m intervals
    -- 2. Show these are disjoint
    -- 3. Compute measure as sum of interval measures
    -- 4. Use cardinality equality to conclude
    --
    -- This requires additional infrastructure connecting digit sets to
    -- explicit interval decompositions. For now, we use the established
    -- cardinality result plus uniformity of intervals.
    --
    -- The key fact: measure = (#intervals) * (1/2^m) for both sets,
    -- and xor_bijection_card_eq shows #intervals are equal.
    -- Both sets decompose into rank-m intervals with equal counts
    -- Use volume_digitSetInter_eq_card to express measures in terms of cardinalities
    have h_vol0 := volume_digitSetInter_eq_card n m 0 b₂ hn hm h (by omega) hb₂
    have h_vol1 := volume_digitSetInter_eq_card n m 1 b₂ hn hm h (by omega) hb₂
    -- xor_bijection_card_eq shows the finset cardinalities are equal
    have hcard : (digitSetInterFinset n m 0 b₂).card = (digitSetInterFinset n m 1 b₂).card := by
      have := xor_bijection_card_eq m n b₂ hm hn h hb₂
      simp only [digitSetInterFinset]
      exact this
    -- Combine to prove equal volumes
    calc volume (digitSet n 0 ∩ digitSet m b₂)
        = (digitSetInterFinset n m 0 b₂).card * ((1 : ℝ≥0∞) / 2^m) := h_vol0
      _ = (digitSetInterFinset n m 1 b₂).card * ((1 : ℝ≥0∞) / 2^m) := by rw [hcard]
      _ = volume (digitSet n 1 ∩ digitSet m b₂) := h_vol1.symm
  · -- Case n > m: symmetric argument
    push Not at h
    have h' : m < n := Nat.lt_of_le_of_ne h (Ne.symm hnm)
    -- Use symmetry: swap the roles of n and m
    -- After swapping, we work at rank n
    rw [Set.inter_comm (digitSet n 0), Set.inter_comm (digitSet n 1)]
    -- Goal: volume (digitSet m b₂ ∩ digitSet n 0) = volume (digitSet m b₂ ∩ digitSet n 1)
    have h_vol0 := volume_digitSetInter_eq_card m n b₂ 0 hm hn h' hb₂ (by omega)
    have h_vol1 := volume_digitSetInter_eq_card m n b₂ 1 hm hn h' hb₂ (by omega)
    -- xor_bijection_card_eq' gives cardinality equality with swapped condition order
    -- Need to show (digitSetInterFinset m n b₂ 0).card = (digitSetInterFinset m n b₂ 1).card
    have hcard : (digitSetInterFinset m n b₂ 0).card = (digitSetInterFinset m n b₂ 1).card := by
      have := xor_bijection_card_eq' n m b₂ hn hm h' hb₂
      -- digitSetInterFinset m n b₂ b = filter (k % 2 = b ∧ (k/2^(n-m)) % 2 = b₂) (range 2^n)
      -- xor_bijection_card_eq' gives filter ((k/2^(n-m)) % 2 = b₂ ∧ k % 2 = 0/1) (range 2^n)
      -- These are equal by commutativity of ∧
      simp only [digitSetInterFinset]
      have h0 : (Finset.filter (fun k => k % 2 = 0 ∧ k / 2 ^ (n - m) % 2 = b₂) (Finset.range (2 ^ n))) =
                (Finset.filter (fun k => k / 2 ^ (n - m) % 2 = b₂ ∧ k % 2 = 0) (Finset.range (2 ^ n))) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, and_comm (a := k % 2 = 0)]
      have h1 : (Finset.filter (fun k => k % 2 = 1 ∧ k / 2 ^ (n - m) % 2 = b₂) (Finset.range (2 ^ n))) =
                (Finset.filter (fun k => k / 2 ^ (n - m) % 2 = b₂ ∧ k % 2 = 1) (Finset.range (2 ^ n))) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, and_comm (a := k % 2 = 1)]
      rw [h0, h1, this]
    -- Combine to prove equal volumes
    calc volume (digitSet m b₂ ∩ digitSet n 0)
        = (digitSetInterFinset m n b₂ 0).card * ((1 : ℝ≥0∞) / 2^n) := h_vol0
      _ = (digitSetInterFinset m n b₂ 1).card * ((1 : ℝ≥0∞) / 2^n) := by rw [hcard]
      _ = volume (digitSet m b₂ ∩ digitSet n 1) := h_vol1.symm

/-- The intersection of distinct digit sets has measure 1/4.
This is the key independence property for binary digits. -/
theorem volume_digitSet_inter (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n ≠ m)
    (b₁ b₂ : ℕ) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1) :
    volume (digitSet n b₁ ∩ digitSet m b₂) = 1/4 := by
  -- Use the partition and symmetry arguments.
  -- vol(digitSet n 0 ∩ digitSet m b₂) = vol(digitSet n 1 ∩ digitSet m b₂) [by symmetry]
  -- vol(digitSet n 0 ∩ digitSet m b₂) + vol(digitSet n 1 ∩ digitSet m b₂) = 1/2 [partition]
  -- Therefore each = 1/4.
  have h_sym : volume (digitSet n 0 ∩ digitSet m b₂) = volume (digitSet n 1 ∩ digitSet m b₂) :=
    volume_digitSet_inter_half n m hn hm hnm b₂ hb₂
  have h_part : digitSet m b₂ =
      (digitSet n 0 ∩ digitSet m b₂) ∪ (digitSet n 1 ∩ digitSet m b₂) := by
    exact (digitSet_inter_partition_m n m hn hm b₂).symm
  have h_disj : Disjoint (digitSet n 0 ∩ digitSet m b₂) (digitSet n 1 ∩ digitSet m b₂) :=
    digitSet_inter_disjoint_m n m b₂
  have hv : volume (digitSet m b₂) = 1/2 := by
    interval_cases b₂
    · exact volume_digitSet_zero m hm
    · exact volume_digitSet_one m hm
  have h_meas0 : MeasurableSet (digitSet n 0 ∩ digitSet m b₂) := digitSet_inter_measurableSet n m 0 b₂
  have h_meas1 : MeasurableSet (digitSet n 1 ∩ digitSet m b₂) := digitSet_inter_measurableSet n m 1 b₂
  have h_sum : volume (digitSet n 0 ∩ digitSet m b₂) + volume (digitSet n 1 ∩ digitSet m b₂) = 1/2 := by
    calc volume (digitSet n 0 ∩ digitSet m b₂) + volume (digitSet n 1 ∩ digitSet m b₂)
        = volume ((digitSet n 0 ∩ digitSet m b₂) ∪ (digitSet n 1 ∩ digitSet m b₂)) := by
          rw [measure_union h_disj h_meas1]
      _ = volume (digitSet m b₂) := by rw [← h_part]
      _ = 1/2 := hv
  -- Since v + v = 1/2 (using h_sym), we get v = 1/4.
  have h_eq : volume (digitSet n 0 ∩ digitSet m b₂) = 1/4 := by
    have h_ne_top : volume (digitSet n 0 ∩ digitSet m b₂) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (by norm_num : (1/2 : ℝ≥0∞) ≠ ⊤)
      calc volume (digitSet n 0 ∩ digitSet m b₂)
          ≤ volume (digitSet m b₂) := measure_mono Set.inter_subset_right
        _ = 1/2 := hv
    -- h_sum : v0 + v1 = 1/2, h_sym : v0 = v1
    -- So v0 + v0 = 1/2, i.e., 2 * v0 = 1/2, i.e., v0 = 1/4
    have h_sum' : volume (digitSet n 0 ∩ digitSet m b₂) + volume (digitSet n 0 ∩ digitSet m b₂) = 1/2 := by
      rw [← h_sym] at h_sum
      exact h_sum
    -- Use the fact that 2 * (1/4) = 1/2, so v = 1/4 from 2*v = 1/2
    have h2v : 2 * volume (digitSet n 0 ∩ digitSet m b₂) = 1/2 := by
      rw [two_mul]; exact h_sum'
    -- Divide both sides by 2 to get v = 1/4
    have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h_div : volume (digitSet n 0 ∩ digitSet m b₂) = (1/2 : ℝ≥0∞) / 2 := by
      rw [ENNReal.eq_div_iff h2ne h2ne_top]
      exact h2v
    rw [h_div]
    -- Show (1/2) / 2 = 1/4 in ENNReal
    -- (1/2) / 2 = (1/2) * (1/2) = 1/4
    simp only [ENNReal.div_eq_inv_mul]
    ring_nf
    -- Goal: 2⁻¹ ^ 2 = 4⁻¹
    have h_sq : (2 : ℝ≥0∞)⁻¹ ^ 2 = (2 ^ 2)⁻¹ := by
      rw [ENNReal.inv_pow]
    rw [h_sq]
    congr 1
    norm_num
  -- Now use b₁ ∈ {0, 1} to conclude
  interval_cases b₁
  · exact h_eq
  · rw [h_sym] at h_eq; exact h_eq

/-- Binary digits are independent: for distinct n, m, the digits d_n and d_m are independent. -/
theorem independent_dyadicDigits (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n ≠ m) :
    ∫ ω in halfOpenUnit, (dyadicDigit n ω : ℝ) * (dyadicDigit m ω : ℝ) ∂volume =
    (1/2) * (1/2) := by
  -- E[d_n * d_m] = P(d_n = 1 ∧ d_m = 1) since d_n, d_m ∈ {0, 1}
  -- = volume(digitSet n 1 ∩ digitSet m 1) = 1/4 (by independence)
  have h_inter : volume (digitSet n 1 ∩ digitSet m 1) = 1/4 :=
    volume_digitSet_inter n m hn hm hnm 1 1 (by norm_num) (by norm_num)
  -- The product d_n * d_m equals 1 on digitSet n 1 ∩ digitSet m 1, and 0 elsewhere on halfOpenUnit
  -- Strategy: Split halfOpenUnit into 4 intersection sets
  -- Product is 1 on (d_n=1 ∩ d_m=1), 0 otherwise
  --
  -- Actually, use that for 0-1 valued functions: f·g = indicator (f=1 ∩ g=1) (fun _ => 1)
  -- The product equals the indicator of the intersection
  have h_prod_eq : ∀ ω ∈ halfOpenUnit,
      (dyadicDigit n ω : ℝ) * (dyadicDigit m ω : ℝ) =
      (digitSet n 1 ∩ digitSet m 1).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω hω
    simp only [Set.indicator]
    split_ifs with h
    · -- Case: ω ∈ digitSet n 1 ∩ digitSet m 1
      simp only [digitSet, Set.mem_ofPred_eq, Set.mem_inter_iff] at h
      simp [h.1.2, h.2.2]
    · -- Case: ω ∉ digitSet n 1 ∩ digitSet m 1
      -- Either d_n ≠ 1 or d_m ≠ 1, so product = 0
      simp only [Set.mem_inter_iff, not_and_or, digitSet, Set.mem_ofPred_eq] at h
      have hdn : dyadicDigit n ω = 0 ∨ dyadicDigit n ω = 1 := dyadicDigit_values n ω
      have hdm : dyadicDigit m ω = 0 ∨ dyadicDigit m ω = 1 := dyadicDigit_values m ω
      -- h : (ω ∉ halfOpenUnit ∨ d_n ≠ 1) ∨ (ω ∉ halfOpenUnit ∨ d_m ≠ 1)
      -- Since hω : ω ∈ halfOpenUnit, this simplifies to d_n ≠ 1 ∨ d_m ≠ 1
      cases h with
      | inl hn_not =>
        -- ω ∉ halfOpenUnit ∨ d_n ≠ 1
        have hdn_ne_one : dyadicDigit n ω ≠ 1 := by
          cases hn_not with
          | inl habs => exact (habs hω).elim
          | inr h => exact h
        have hdn0 : dyadicDigit n ω = 0 := by
          cases hdn with
          | inl h0 => exact h0
          | inr h1 => exact (hdn_ne_one h1).elim
        simp [hdn0]
      | inr hm_not =>
        -- ω ∉ halfOpenUnit ∨ d_m ≠ 1
        have hdm_ne_one : dyadicDigit m ω ≠ 1 := by
          cases hm_not with
          | inl habs => exact (habs hω).elim
          | inr h => exact h
        have hdm0 : dyadicDigit m ω = 0 := by
          cases hdm with
          | inl h0 => exact h0
          | inr h1 => exact (hdm_ne_one h1).elim
        simp [hdm0]
  -- Rewrite the integral
  have h_int_eq : ∫ ω in halfOpenUnit, (dyadicDigit n ω : ℝ) * (dyadicDigit m ω : ℝ) ∂volume =
      ∫ ω in halfOpenUnit, (digitSet n 1 ∩ digitSet m 1).indicator (fun _ => (1 : ℝ)) ω ∂volume := by
    apply setIntegral_congr_ae (measurableSet_Ioc)
    apply Filter.Eventually.of_forall
    intro x hx
    exact h_prod_eq x hx
  rw [h_int_eq]
  -- The intersection is a subset of halfOpenUnit
  have h_sub : digitSet n 1 ∩ digitSet m 1 ⊆ halfOpenUnit := Set.inter_subset_left.trans (digitSet_subset n 1)
  have h_meas : MeasurableSet (digitSet n 1 ∩ digitSet m 1) := digitSet_inter_measurableSet n m 1 1
  -- Use integral_indicator and setIntegral_const
  rw [setIntegral_indicator h_meas]
  -- ∫ x in halfOpenUnit ∩ (digitSet n 1 ∩ digitSet m 1), 1 ∂volume
  -- Since intersection ⊆ halfOpenUnit, this equals ∫ x in intersection, 1
  rw [Set.inter_eq_self_of_subset_right h_sub]
  rw [setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  -- volume.real (digitSet n 1 ∩ digitSet m 1) = 1/4
  have hv : volume.real (digitSet n 1 ∩ digitSet m 1) = (1/4 : ℝ) := by
    simp only [Measure.real]
    rw [h_inter]
    norm_num
  rw [hv]
  norm_num

/-- Distinct Rademacher functions are orthogonal (their product integrates to 0).
For i ≠ j, the four combinations (d_i, d_j) ∈ {0,1}² each have probability 1/4.
The product r_i * r_j equals +1 on {d_i=0, d_j=0} ∪ {d_i=1, d_j=1} and -1 elsewhere.
Expected value: (1/4)(+1 - 1 - 1 + 1) = 0. -/
theorem rademacher_orthogonal (i j : ℕ) (hi : i ≥ 1) (hj : j ≥ 1) (hij : i ≠ j) :
    ∫ ω in halfOpenUnit, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume = 0 := by
  -- Split halfOpenUnit into four intersection sets based on digit values
  have h_part := digitSet_inter_partition i j hi hj
  have h_disj01 : Disjoint (digitSet i 0 ∩ digitSet j 0) (digitSet i 0 ∩ digitSet j 1) := by
    rw [Set.disjoint_iff]; intro x ⟨⟨_, h00⟩, ⟨_, h01⟩⟩
    simp only [digitSet, Set.mem_ofPred_eq] at h00 h01; omega
  have h_disj23 : Disjoint (digitSet i 1 ∩ digitSet j 0) (digitSet i 1 ∩ digitSet j 1) := by
    rw [Set.disjoint_iff]; intro x ⟨⟨_, h10⟩, ⟨_, h11⟩⟩
    simp only [digitSet, Set.mem_ofPred_eq] at h10 h11; omega
  have h_disj : Disjoint ((digitSet i 0 ∩ digitSet j 0) ∪ (digitSet i 0 ∩ digitSet j 1))
                        ((digitSet i 1 ∩ digitSet j 0) ∪ (digitSet i 1 ∩ digitSet j 1)) := by
    rw [Set.disjoint_iff]; intro x ⟨hL, hR⟩
    -- Left side has digit i = 0, right side has digit i = 1
    rcases hL with ⟨⟨_, hd0⟩, _⟩ | ⟨⟨_, hd0⟩, _⟩ <;>
    rcases hR with ⟨⟨_, hd1⟩, _⟩ | ⟨⟨_, hd1⟩, _⟩ <;>
    omega
  -- Measurable sets
  have hm00 := digitSet_inter_measurableSet i j 0 0
  have hm01 := digitSet_inter_measurableSet i j 0 1
  have hm10 := digitSet_inter_measurableSet i j 1 0
  have hm11 := digitSet_inter_measurableSet i j 1 1
  -- Rademacher product is constant on each intersection set
  have hr00 : ∀ ω ∈ digitSet i 0 ∩ digitSet j 0, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) = 1 := by
    intro ω hω; simp only [digitSet, Set.mem_ofPred_eq, Set.mem_inter_iff] at hω
    simp only [rademacher, hω.1.2, hω.2.2]; norm_num
  have hr01 : ∀ ω ∈ digitSet i 0 ∩ digitSet j 1, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) = -1 := by
    intro ω hω; simp only [digitSet, Set.mem_ofPred_eq, Set.mem_inter_iff] at hω
    simp only [rademacher, hω.1.2, hω.2.2]; norm_num
  have hr10 : ∀ ω ∈ digitSet i 1 ∩ digitSet j 0, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) = -1 := by
    intro ω hω; simp only [digitSet, Set.mem_ofPred_eq, Set.mem_inter_iff] at hω
    simp only [rademacher, hω.1.2, hω.2.2]; norm_num
  have hr11 : ∀ ω ∈ digitSet i 1 ∩ digitSet j 1, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) = 1 := by
    intro ω hω; simp only [digitSet, Set.mem_ofPred_eq, Set.mem_inter_iff] at hω
    simp only [rademacher, hω.1.2, hω.2.2]; norm_num
  -- All four sets have measure 1/4
  have hv00 := volume_digitSet_inter i j hi hj hij 0 0 (by omega) (by omega)
  have hv01 := volume_digitSet_inter i j hi hj hij 0 1 (by omega) (by omega)
  have hv10 := volume_digitSet_inter i j hi hj hij 1 0 (by omega) (by omega)
  have hv11 := volume_digitSet_inter i j hi hj hij 1 1 (by omega) (by omega)
  -- Integrability on each set (function is constant, set has finite measure)
  have hint00 : IntegrableOn (fun ω => (rademacher i ω : ℝ) * (rademacher j ω : ℝ)) (digitSet i 0 ∩ digitSet j 0) volume := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := by rw [hv00]; norm_num)).congr_fun (fun x hx => (hr00 x hx).symm) hm00
  have hint01 : IntegrableOn (fun ω => (rademacher i ω : ℝ) * (rademacher j ω : ℝ)) (digitSet i 0 ∩ digitSet j 1) volume := by
    apply (integrableOn_const (C := (-1 : ℝ)) (hs := by rw [hv01]; norm_num)).congr_fun (fun x hx => (hr01 x hx).symm) hm01
  have hint10 : IntegrableOn (fun ω => (rademacher i ω : ℝ) * (rademacher j ω : ℝ)) (digitSet i 1 ∩ digitSet j 0) volume := by
    apply (integrableOn_const (C := (-1 : ℝ)) (hs := by rw [hv10]; norm_num)).congr_fun (fun x hx => (hr10 x hx).symm) hm10
  have hint11 : IntegrableOn (fun ω => (rademacher i ω : ℝ) * (rademacher j ω : ℝ)) (digitSet i 1 ∩ digitSet j 1) volume := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := by rw [hv11]; norm_num)).congr_fun (fun x hx => (hr11 x hx).symm) hm11
  -- Compute each integral using constant function formulas
  have hi00 : ∫ ω in digitSet i 0 ∩ digitSet j 0, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume = 1/4 := by
    rw [setIntegral_congr_ae hm00 (Filter.Eventually.of_forall hr00), setIntegral_const, smul_eq_mul, mul_one]
    simp only [Measure.real, hv00]; norm_num
  have hi01 : ∫ ω in digitSet i 0 ∩ digitSet j 1, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume = -1/4 := by
    rw [setIntegral_congr_ae hm01 (Filter.Eventually.of_forall hr01), setIntegral_const, smul_eq_mul]
    simp only [Measure.real, hv01]; norm_num
  have hi10 : ∫ ω in digitSet i 1 ∩ digitSet j 0, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume = -1/4 := by
    rw [setIntegral_congr_ae hm10 (Filter.Eventually.of_forall hr10), setIntegral_const, smul_eq_mul]
    simp only [Measure.real, hv10]; norm_num
  have hi11 : ∫ ω in digitSet i 1 ∩ digitSet j 1, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume = 1/4 := by
    rw [setIntegral_congr_ae hm11 (Filter.Eventually.of_forall hr11), setIntegral_const, smul_eq_mul, mul_one]
    simp only [Measure.real, hv11]; norm_num
  -- Additional disjointness for the union structure ((A ∪ B) ∪ C) ∪ D
  have h_disj_01_10 : Disjoint (digitSet i 0 ∩ digitSet j 0 ∪ digitSet i 0 ∩ digitSet j 1) (digitSet i 1 ∩ digitSet j 0) := by
    rw [Set.disjoint_union_left]
    constructor
    · -- Disjoint (digitSet i 0 ∩ digitSet j 0) (digitSet i 1 ∩ digitSet j 0)
      rw [Set.disjoint_iff]; intro x ⟨⟨h_i0, _⟩, ⟨h_i1, _⟩⟩
      simp only [digitSet, Set.mem_ofPred_eq] at h_i0 h_i1
      omega
    · -- Disjoint (digitSet i 0 ∩ digitSet j 1) (digitSet i 1 ∩ digitSet j 0)
      rw [Set.disjoint_iff]; intro x ⟨⟨h_i0, _⟩, ⟨h_i1, _⟩⟩
      simp only [digitSet, Set.mem_ofPred_eq] at h_i0 h_i1
      omega
  have h_disj_01_10_11 : Disjoint ((digitSet i 0 ∩ digitSet j 0 ∪ digitSet i 0 ∩ digitSet j 1) ∪ (digitSet i 1 ∩ digitSet j 0)) (digitSet i 1 ∩ digitSet j 1) := by
    rw [Set.disjoint_union_left]
    constructor
    · rw [Set.disjoint_union_left]
      constructor
      · -- Disjoint (digitSet i 0 ∩ digitSet j 0) (digitSet i 1 ∩ digitSet j 1)
        rw [Set.disjoint_iff]; intro x ⟨⟨h0, _⟩, ⟨h1, _⟩⟩
        simp only [digitSet, Set.mem_ofPred_eq] at h0 h1; omega
      · -- Disjoint (digitSet i 0 ∩ digitSet j 1) (digitSet i 1 ∩ digitSet j 1)
        rw [Set.disjoint_iff]; intro x ⟨⟨h0, _⟩, ⟨h1, _⟩⟩
        simp only [digitSet, Set.mem_ofPred_eq] at h0 h1; omega
    · exact h_disj23
  -- Split the integral step by step using calc
  calc ∫ ω in halfOpenUnit, (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume
      = ∫ ω in ((digitSet i 0 ∩ digitSet j 0) ∪ (digitSet i 0 ∩ digitSet j 1) ∪
               (digitSet i 1 ∩ digitSet j 0) ∪ (digitSet i 1 ∩ digitSet j 1)),
          (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume := by rw [← h_part]
    _ = ∫ ω in ((digitSet i 0 ∩ digitSet j 0) ∪ (digitSet i 0 ∩ digitSet j 1) ∪
               (digitSet i 1 ∩ digitSet j 0)), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume +
        ∫ ω in (digitSet i 1 ∩ digitSet j 1), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume := by
          exact setIntegral_union h_disj_01_10_11 hm11
                ((hint00.union hint01).union hint10) hint11
    _ = (∫ ω in ((digitSet i 0 ∩ digitSet j 0) ∪ (digitSet i 0 ∩ digitSet j 1)),
          (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume +
        ∫ ω in (digitSet i 1 ∩ digitSet j 0), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume) +
        ∫ ω in (digitSet i 1 ∩ digitSet j 1), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume := by
          congr 1
          exact setIntegral_union h_disj_01_10 hm10 (hint00.union hint01) hint10
    _ = ((∫ ω in (digitSet i 0 ∩ digitSet j 0), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume +
         ∫ ω in (digitSet i 0 ∩ digitSet j 1), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume) +
        ∫ ω in (digitSet i 1 ∩ digitSet j 0), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume) +
        ∫ ω in (digitSet i 1 ∩ digitSet j 1), (rademacher i ω : ℝ) * (rademacher j ω : ℝ) ∂volume := by
          congr 2
          exact setIntegral_union h_disj01 hm01 hint00 hint01
    _ = ((1/4 + (-1/4)) + (-1/4)) + 1/4 := by rw [hi00, hi01, hi10, hi11]
    _ = 0 := by ring

/-- Cross term integral: ∫ s_n · r_{n+1} = 0.
    Uses orthogonality of Rademacher functions. -/
theorem rademacherSum_cross_integral (n : ℕ) :
    ∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) ∂volume = 0 := by
  have h_eq : ∀ ω, (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) =
              ∑ i ∈ Finset.range n, ((rademacher (i + 1) ω : ℝ) * (rademacher (n + 1) ω : ℝ)) := by
    intro ω
    simp only [rademacherSum, Int.cast_sum, Finset.sum_mul]
  simp_rw [h_eq]
  have h_int : ∀ i ∈ Finset.range n,
      IntegrableOn (fun ω => (rademacher (i + 1) ω : ℝ) * (rademacher (n + 1) ω : ℝ)) halfOpenUnit volume := by
    intro i _hi
    exact rademacher_mul_integrableOn_halfOpenUnit (i + 1) (n + 1) (by omega) (by omega)
  rw [integral_finsetSum _ h_int]
  apply Finset.sum_eq_zero
  intro i hi
  have hi_ne : i + 1 ≠ n + 1 := by simp only [Finset.mem_range] at hi; omega
  exact rademacher_orthogonal (i + 1) (n + 1) (by omega) (by omega) hi_ne

/-- The L² norm of the Rademacher sum: ∫ s_n² dω = n.
    This is equation (1.18) in Billingsley.
    Proof: By induction using s_{n+1}² = s_n² + 2·s_n·r_{n+1} + r_{n+1}².
    - IH: ∫ s_n² = n
    - Cross term: ∫ s_n·r_{n+1} = 0 by orthogonality (rademacherSum_cross_integral)
    - Square term: ∫ r_{n+1}² = 1 (rademacher_sq_integral) -/
theorem rademacherSum_sq_integral (n : ℕ) :
    ∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ)^2 ∂volume = n := by
  induction n with
  | zero =>
    simp only [rademacherSum, Finset.range_zero, Finset.sum_empty, Int.cast_zero, sq, mul_zero,
               setIntegral_const, smul_eq_mul, Nat.cast_zero]
  | succ n ih =>
    -- s_{n+1} = s_n + r_{n+1}, so s_{n+1}² = s_n² + 2·s_n·r_{n+1} + r_{n+1}²
    have h_recur : ∀ ω, rademacherSum (n + 1) ω = rademacherSum n ω + rademacher (n + 1) ω := by
      intro ω; simp [rademacherSum, Finset.sum_range_succ]
    have h_split : ∀ ω, (rademacherSum (n + 1) ω : ℝ)^2 =
        (rademacherSum n ω : ℝ)^2 + 2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) +
        (rademacher (n + 1) ω : ℝ)^2 := by
      intro ω; rw [h_recur]; push_cast; ring
    -- Rewrite the integrand
    have h_int_eq : ∫ ω in halfOpenUnit, (rademacherSum (n + 1) ω : ℝ)^2 ∂volume =
                    ∫ ω in halfOpenUnit, ((rademacherSum n ω : ℝ)^2 +
                      2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) +
                      (rademacher (n + 1) ω : ℝ)^2) ∂volume := by
      congr 1; ext ω; exact h_split ω
    rw [h_int_eq]
    -- Integrability of each term
    have h_sq_n := rademacherSum_sq_integrableOn_halfOpenUnit n
    have h_cross : IntegrableOn (fun ω => 2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ))
                   halfOpenUnit volume := by
      have h := rademacherSum_mul_rademacher_integrableOn_halfOpenUnit n
      have h2 : IntegrableOn (fun ω => (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) * 2) halfOpenUnit volume :=
        h.mul_const 2
      simp only [IntegrableOn] at h2 ⊢
      convert h2 using 1
      ext ω; ring
    have h_sq_r := rademacher_sq_integrableOn_halfOpenUnit (n + 1) (by omega)
    -- Compute each integral separately
    have int_sq_n : ∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ)^2 ∂volume = n := ih
    have int_sq_r : ∫ ω in halfOpenUnit, (rademacher (n + 1) ω : ℝ)^2 ∂volume = 1 :=
      rademacher_sq_integral (n + 1) (by omega)
    -- Cross term: ∫ 2·s_n·r_{n+1} = 2·∫ s_n·r_{n+1} = 2·0 = 0
    have int_cross : ∫ ω in halfOpenUnit, 2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) ∂volume = 0 := by
      have heq : ∀ ω, (2 : ℝ) * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) =
                 (2 : ℝ) * ((rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ)) := fun _ => by ring
      simp_rw [heq, integral_const_mul, rademacherSum_cross_integral n, mul_zero]
    -- Expand the integral of the sum: use integral_add on each pair
    have step1 : ∫ ω in halfOpenUnit, 2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) +
                 (rademacher (n + 1) ω : ℝ)^2 ∂volume =
                 ∫ ω in halfOpenUnit, 2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) ∂volume +
                 ∫ ω in halfOpenUnit, (rademacher (n + 1) ω : ℝ)^2 ∂volume := integral_add h_cross h_sq_r
    have step2 : ∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ)^2 +
                 (2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) + (rademacher (n + 1) ω : ℝ)^2) ∂volume =
                 ∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ)^2 ∂volume +
                 ∫ ω in halfOpenUnit, (2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) +
                 (rademacher (n + 1) ω : ℝ)^2) ∂volume := integral_add h_sq_n (h_cross.add h_sq_r)
    have step3 : ∀ ω, (rademacherSum n ω : ℝ)^2 +
                 2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) + (rademacher (n + 1) ω : ℝ)^2 =
                 (rademacherSum n ω : ℝ)^2 +
                 (2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) + (rademacher (n + 1) ω : ℝ)^2) :=
      fun _ => by ring
    calc ∫ ω in halfOpenUnit, ((rademacherSum n ω : ℝ)^2 +
           2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) +
           (rademacher (n + 1) ω : ℝ)^2) ∂volume
        = ∫ ω in halfOpenUnit, ((rademacherSum n ω : ℝ)^2 +
            (2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) +
             (rademacher (n + 1) ω : ℝ)^2)) ∂volume := by simp_rw [step3]
      _ = ∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ)^2 ∂volume +
          ∫ ω in halfOpenUnit, (2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) +
           (rademacher (n + 1) ω : ℝ)^2) ∂volume := step2
      _ = n + (∫ ω in halfOpenUnit, 2 * (rademacherSum n ω : ℝ) * (rademacher (n + 1) ω : ℝ) ∂volume +
           ∫ ω in halfOpenUnit, (rademacher (n + 1) ω : ℝ)^2 ∂volume) := by rw [int_sq_n, step1]
      _ = n + (0 + 1) := by rw [int_cross, int_sq_r]
      _ = ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The variance of S_n is n/4.
    Proof: By sumDigits_eq_rademacher, S_n - n/2 = s_n/2.
    So Var(S_n) = E[(s_n/2)²] = (1/4)E[s_n²] = (1/4)·n = n/4. -/
theorem variance_sumDigits (n : ℕ) :
    ∫ ω in halfOpenUnit, ((sumDigits n ω : ℝ) - (n : ℝ)/2)^2 ∂volume = (n : ℝ)/4 := by
  -- Use the relation: sumDigits n ω - n/2 = rademacherSum n ω / 2
  have h_relation : ∀ ω, (sumDigits n ω : ℝ) - (n : ℝ)/2 = (rademacherSum n ω : ℝ) / 2 := by
    intro ω
    have h := sumDigits_eq_rademacher n ω
    -- h : 2 * (sumDigits n ω : ℤ) = rademacherSum n ω + n
    -- Convert to ℝ using congrArg
    have h' : (2 : ℝ) * (sumDigits n ω : ℝ) = (rademacherSum n ω : ℝ) + n := by
      have h_cast := congrArg (fun x : ℤ => (x : ℝ)) h
      simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast] at h_cast
      push_cast at h_cast
      exact h_cast
    linarith
  -- Therefore (S_n - n/2)² = (s_n/2)² = s_n²/4
  simp_rw [h_relation, div_pow, sq]
  -- ∫ s_n²/4 = (1/4) ∫ s_n²
  have h_eq : (fun ω => (rademacherSum n ω : ℝ) * (rademacherSum n ω : ℝ) / (2 * 2)) =
              fun ω => (rademacherSum n ω : ℝ)^2 / 4 := by ext; ring
  rw [h_eq]
  -- Use integral_div with proper setup
  have h_sq : ∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ)^2 ∂volume = n := rademacherSum_sq_integral n
  rw [integral_div, h_sq]

/-! ## Weak Law of Large Numbers - Complete Proof

The following lemmas complete the proof of `weakLawOfLargeNumbers_binary`.
-/

/-- Helper: For n ≥ 1, the deviation event is contained in a rademacher squared threshold set. -/
theorem deviationEvent_subset_rademacherSq (n : ℕ) (hn : n ≥ 1) (ε : ℝ) (hε : 0 < ε) :
    deviationEvent n ε ⊆ {ω ∈ halfOpenUnit | (rademacherSum n ω : ℝ)^2 ≥ (2 * n * ε)^2} := by
  intro ω hω
  simp only [deviationEvent, Set.mem_ofPred_eq] at hω
  simp only [Set.mem_ofPred_eq]
  constructor
  · exact hω.1
  · -- |S_n/n - 1/2| ≥ ε implies |s_n|/(2n) ≥ ε, hence |s_n| ≥ 2nε, hence s_n² ≥ (2nε)²
    have h_relation : (sumDigits n ω : ℝ) - (n : ℝ)/2 = (rademacherSum n ω : ℝ) / 2 := by
      have h := sumDigits_eq_rademacher n ω
      have h' : (2 : ℝ) * (sumDigits n ω : ℝ) = (rademacherSum n ω : ℝ) + n := by
        have h_cast := congrArg (fun x : ℤ => (x : ℝ)) h
        simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast] at h_cast
        push_cast at h_cast
        exact h_cast
      linarith
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega : 0 < n)
    -- Key: |S_n/n - 1/2| = |s_n|/(2n)
    have h_dev_eq : |(sumDigits n ω : ℝ) / n - 1/2| = |(rademacherSum n ω : ℝ)| / (2 * n) := by
      have h2n_pos : (0 : ℝ) < 2 * n := by linarith
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      -- (sumDigits n ω / n - 1/2) = ((sumDigits n ω) - n/2) / n
      have h_sub : (sumDigits n ω : ℝ) / n - 1/2 = ((sumDigits n ω : ℝ) - n/2) / n := by
        field_simp
      rw [h_sub, h_relation]
      -- |(s_n/2) / n| = |s_n| / (2n)
      rw [div_div, abs_div, abs_of_pos h2n_pos]
    rw [h_dev_eq] at hω
    have h_abs : |(rademacherSum n ω : ℝ)| ≥ 2 * n * ε := by
      have h2n_pos : (0 : ℝ) < 2 * n := by linarith
      have h := hω.2
      calc |(rademacherSum n ω : ℝ)| = (|(rademacherSum n ω : ℝ)| / (2 * n)) * (2 * n) := by
             field_simp
           _ ≥ ε * (2 * n) := mul_le_mul_of_nonneg_right h (by linarith)
           _ = 2 * n * ε := by ring
    calc (rademacherSum n ω : ℝ)^2 = |(rademacherSum n ω : ℝ)|^2 := by rw [sq_abs]
       _ ≥ (2 * n * ε)^2 := by
         apply sq_le_sq' _ h_abs
         have h_nonneg : 0 ≤ 2 * n * ε := by positivity
         linarith

/-- Helper: The probability bound using Markov's inequality on rademacher sum squared. -/
theorem prob_deviationEvent_le (n : ℕ) (hn : n ≥ 1) (ε : ℝ) (hε : 0 < ε) :
    probMeasureUnit (deviationEvent n ε) ≤ ENNReal.ofReal (1 / (4 * n * ε^2)) := by
  -- Use the subset bound and Markov inequality
  have h_subset := deviationEvent_subset_rademacherSq n hn ε hε
  -- First apply monotonicity
  have h_mono : probMeasureUnit (deviationEvent n ε) ≤
      probMeasureUnit {ω ∈ halfOpenUnit | (rademacherSum n ω : ℝ)^2 ≥ (2 * n * ε)^2} :=
    measure_mono h_subset
  calc probMeasureUnit (deviationEvent n ε)
      ≤ probMeasureUnit {ω ∈ halfOpenUnit | (rademacherSum n ω : ℝ)^2 ≥ (2 * n * ε)^2} := h_mono
    _ ≤ ENNReal.ofReal (1 / (4 * n * ε^2)) := by
      -- Apply Markov: P(X² ≥ a²) ≤ E[X²]/a² = n / (4n²ε²) = 1/(4nε²)
      have h_threshold : (2 * (n : ℝ) * ε)^2 = 4 * n^2 * ε^2 := by ring
      rw [h_threshold]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega : 0 < n)
      have h_threshold_pos : (0 : ℝ) < 4 * n^2 * ε^2 := by positivity
      -- The bound 1/(4nε²) = n/(4n²ε²)
      have h_bound_eq : (1 : ℝ) / (4 * n * ε^2) = n / (4 * n^2 * ε^2) := by field_simp
      rw [h_bound_eq]
      -- Strategy: Use that for any nonneg f, P(f ≥ a) ≤ E[f]/a
      -- Here f = s_n², a = 4n²ε², E[s_n²] = n
      -- So P(s_n² ≥ 4n²ε²) ≤ n / (4n²ε²)
      -- This is Markov's inequality applied to s_n²

      -- Set up the Markov inequality application
      -- probMeasureUnit = volume.restrict halfOpenUnit
      simp only [probMeasureUnit]

      -- The set {ω ∈ halfOpenUnit | s_n² ≥ 4n²ε²} under restricted measure
      -- equals {ω | s_n² ≥ 4n²ε²} ∩ halfOpenUnit = {ω | s_n² ≥ 4n²ε²} under restricted measure
      have h_set_eq : {ω ∈ halfOpenUnit | (rademacherSum n ω : ℝ)^2 ≥ 4 * n^2 * ε^2} =
          {ω | (rademacherSum n ω : ℝ)^2 ≥ 4 * n^2 * ε^2} ∩ halfOpenUnit := by
        ext; simp [Set.mem_ofPred_eq, Set.mem_inter_iff, and_comm]

      -- The ENNReal version of f: f_enn(ω) = ofReal(s_n(ω)²)
      -- Need: (volume.restrict halfOpenUnit) {ω | ofReal(4n²ε²) ≤ ofReal(s_n²)} ≤ ∫⁻ ofReal(s_n²) / ofReal(4n²ε²)
      have h_sq_nonneg : ∀ ω, 0 ≤ (rademacherSum n ω : ℝ)^2 := fun _ => sq_nonneg _

      -- AEMeasurable for ofReal ∘ (rademacherSum n)²
      have h_integrableOn := rademacherSum_sq_integrableOn_halfOpenUnit n
      have h_aestrongly : AEStronglyMeasurable (fun ω => (rademacherSum n ω : ℝ)^2)
          (volume.restrict halfOpenUnit) := h_integrableOn.aestronglyMeasurable
      have h_aemeas_real : AEMeasurable (fun ω => (rademacherSum n ω : ℝ)^2)
          (volume.restrict halfOpenUnit) := h_aestrongly.aemeasurable
      have h_aemeas : AEMeasurable (fun ω => ENNReal.ofReal ((rademacherSum n ω : ℝ)^2))
          (volume.restrict halfOpenUnit) := h_aemeas_real.ennreal_ofReal

      -- Apply Markov's inequality: meas_ge_le_lintegral_div
      have h_threshold_ne_zero : ENNReal.ofReal (4 * n^2 * ε^2) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr h_threshold_pos)
      have h_threshold_ne_top : ENNReal.ofReal (4 * n^2 * ε^2) ≠ ⊤ := ENNReal.ofReal_ne_top

      -- Transform the set to match Markov's form
      have h_set_transform : {ω | (rademacherSum n ω : ℝ)^2 ≥ 4 * n^2 * ε^2} =
          {ω | ENNReal.ofReal (4 * n^2 * ε^2) ≤ ENNReal.ofReal ((rademacherSum n ω : ℝ)^2)} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        rw [ENNReal.ofReal_le_ofReal_iff (h_sq_nonneg ω)]

      -- The restricted measure of {ω ∈ S | P(ω)} equals the restricted measure of {ω | P(ω)}
      have h_restrict_eq : (volume.restrict halfOpenUnit) {ω ∈ halfOpenUnit | (rademacherSum n ω : ℝ)^2 ≥ 4 * n^2 * ε^2}
          = (volume.restrict halfOpenUnit) {ω | (rademacherSum n ω : ℝ)^2 ≥ 4 * n^2 * ε^2} := by
        rw [h_set_eq]
        simp only [Measure.restrict_apply' halfOpenUnit_measurableSet, Set.inter_comm]
        -- Goal: volume (S ∩ (S ∩ T)) = volume (S ∩ T)
        congr 1
        ext x
        simp only [Set.mem_inter_iff]
        tauto

      calc (volume.restrict halfOpenUnit) {ω ∈ halfOpenUnit | (rademacherSum n ω : ℝ)^2 ≥ 4 * n^2 * ε^2}
          = (volume.restrict halfOpenUnit) {ω | (rademacherSum n ω : ℝ)^2 ≥ 4 * n^2 * ε^2} := h_restrict_eq
        _ = (volume.restrict halfOpenUnit) {ω | ENNReal.ofReal (4 * n^2 * ε^2) ≤
              ENNReal.ofReal ((rademacherSum n ω : ℝ)^2)} := by rw [h_set_transform]
        _ ≤ (∫⁻ ω, ENNReal.ofReal ((rademacherSum n ω : ℝ)^2) ∂(volume.restrict halfOpenUnit)) /
              ENNReal.ofReal (4 * n^2 * ε^2) := by
            apply meas_ge_le_lintegral_div h_aemeas h_threshold_ne_zero h_threshold_ne_top
        _ = ENNReal.ofReal (∫ ω in halfOpenUnit, (rademacherSum n ω : ℝ)^2 ∂volume) /
              ENNReal.ofReal (4 * n^2 * ε^2) := by
            congr 1
            rw [← ofReal_integral_eq_lintegral_ofReal h_integrableOn
                (Filter.Eventually.of_forall h_sq_nonneg)]
        _ = ENNReal.ofReal n / ENNReal.ofReal (4 * n^2 * ε^2) := by
            rw [rademacherSum_sq_integral n]
        _ = ENNReal.ofReal (n / (4 * n^2 * ε^2)) := by
            rw [ENNReal.ofReal_div_of_pos h_threshold_pos]

/-- **Theorem 1.1** (Weak Law of Large Numbers for binary digits).  For every
`ε > 0`, `P[|S_n(ω)/n − 1/2| ≥ ε] → 0` on `(0, 1]` with Lebesgue measure. -/
theorem weakLawOfLargeNumbers_binary (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun n => probMeasureUnit (deviationEvent n ε))
      Filter.atTop (nhds 0) := by
  -- Strategy: bound by 1/(4nε²) and show this → 0
  -- Use squeeze theorem with the bound from prob_deviationEvent_le
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  -- We need: eventually, probMeasureUnit (deviationEvent n ε) ≤ δ
  -- Since probMeasureUnit (deviationEvent n ε) ≤ ofReal(1/(4nε²)) for n ≥ 1,
  -- and ofReal(1/(4nε²)) → 0, eventually ofReal(1/(4nε²)) ≤ δ
  -- Find N such that for n ≥ N, 1/(4nε²) < δ (as a real)
  have h4ε2_pos : (0 : ℝ) < 4 * ε^2 := by positivity
  -- 1/(4nε²) < δ.toReal when n > 1/(4ε²δ.toReal)
  -- For δ = ⊤, any n works. For δ < ⊤, use explicit bound.
  by_cases hδ_top : δ = ⊤
  · simp [hδ_top]
  · have hδ_real : δ.toReal > 0 := ENNReal.toReal_pos hδ.ne' hδ_top
    -- Compute N = ⌈1/(4ε²δ.toReal)⌉ + 1
    set N := Nat.ceil (1 / (4 * ε^2 * δ.toReal)) + 1 with hN_def
    use N
    intro n hn
    -- For n ≥ N, we have 1/(4nε²) < δ.toReal, hence ofReal(1/(4nε²)) < δ
    have hn_ge_1 : n ≥ 1 := by
      have hN_pos : N ≥ 1 := by simp only [hN_def]; omega
      omega
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega : 0 < n)
    -- Show 1/(4nε²) ≤ δ.toReal
    have h_bound : (1 : ℝ) / (4 * n * ε^2) ≤ δ.toReal := by
      -- n ≥ N = ⌈1/(4ε²δ.toReal)⌉ + 1 > 1/(4ε²δ.toReal)
      -- Hence 4nε² > 1/δ.toReal, so 1/(4nε²) < δ.toReal
      have h1 : (1 : ℝ) / (4 * ε^2 * δ.toReal) < N := by
        calc (1 : ℝ) / (4 * ε^2 * δ.toReal)
            ≤ ↑(Nat.ceil (1 / (4 * ε^2 * δ.toReal))) := Nat.le_ceil _
          _ < ↑(Nat.ceil (1 / (4 * ε^2 * δ.toReal)) + 1) := by
              push_cast; linarith
      have h2 : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      have h3 : (1 : ℝ) / (4 * ε^2 * δ.toReal) < n := lt_of_lt_of_le h1 h2
      -- Rearrange: 1 < n * 4 * ε^2 * δ.toReal, so 1/(4nε²) < δ.toReal
      have h4 : 1 < n * (4 * ε^2 * δ.toReal) := by
        have h_prod_pos : 0 < 4 * ε^2 * δ.toReal := by positivity
        calc (1 : ℝ) = (1 / (4 * ε^2 * δ.toReal)) * (4 * ε^2 * δ.toReal) := by field_simp
          _ < n * (4 * ε^2 * δ.toReal) := by
              apply mul_lt_mul_of_pos_right h3 h_prod_pos
      have h_denom_pos : (0 : ℝ) < n * (4 * ε^2) := by positivity
      have hδ_pos2 : (0 : ℝ) < δ.toReal := by positivity
      -- From h4: 1 < n * (4 * ε^2 * δ.toReal), so 1/δ.toReal < n * (4 * ε^2)
      have h5 : (1 : ℝ) / δ.toReal < n * (4 * ε^2) := by
        have step1 : (1 : ℝ) / δ.toReal < (n * (4 * ε^2 * δ.toReal)) / δ.toReal :=
          div_lt_div_of_pos_right h4 hδ_pos2
        have step2 : (n * (4 * ε^2 * δ.toReal)) / δ.toReal = n * (4 * ε^2) := by field_simp
        linarith
      -- Now 1/(n * (4 * ε^2)) < δ.toReal follows from h5 via reciprocal
      have h6 : 1 / (n * (4 * ε^2)) < δ.toReal := by
        rwa [one_div_lt h_denom_pos hδ_pos2]
      -- Finally: 1/(4 * n * ε²) = 1/(n * (4 * ε²)) ≤ δ.toReal
      have h7 : (1 : ℝ) / (4 * n * ε^2) = 1 / (n * (4 * ε^2)) := by ring_nf
      linarith
    calc probMeasureUnit (deviationEvent n ε)
        ≤ ENNReal.ofReal (1 / (4 * n * ε^2)) := prob_deviationEvent_le n hn_ge_1 ε hε
      _ ≤ δ := by
          rw [ENNReal.ofReal_le_iff_le_toReal hδ_top]
          exact h_bound

/-! ## Borel's Normal Number Theorem - Supporting Lemmas

The full proof uses the subsequence method with Borel-Cantelli.
Key steps:
1. Along squares k², prob(deviationEvent k² ε) ≤ 1/(4k²ε²) is summable
2. Borel-Cantelli gives a.e. convergence along squares
3. Interpolation extends convergence to all n
-/

/-- The sum ∑_k 1/(k+1)² converges. This is the Basel series shifted by 1.
This is a standard result: ∑_{n≥1} 1/n² = π²/6. -/
theorem summable_one_div_sq : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1)^2 : ℕ)) := by
  -- Use the p-series result with p = 2 > 1, shifted by 1
  have h1 : (1 : ℕ) < 2 := by norm_num
  have h2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr h1
  have h3 : Summable (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2) := (summable_nat_add_iff 1).mpr h2
  refine h3.congr (fun k => ?_)
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- For the subsequence of squares, the deviation probabilities are summable.
This follows from prob(deviationEvent k² ε) ≤ 1/(4k²ε²) and ∑ 1/k² < ∞. -/
theorem tsum_prob_deviationEvent_sq_ne_top (ε : ℝ) (hε : 0 < ε) :
    (∑' k : ℕ, probMeasureUnit (deviationEvent ((k + 1)^2) ε)) ≠ ⊤ := by
  -- Bound each term by 1/(4(k+1)²ε²)
  have h_bound : ∀ k : ℕ, probMeasureUnit (deviationEvent ((k + 1)^2) ε)
      ≤ ENNReal.ofReal (1 / (4 * ((k + 1)^2 : ℕ) * ε^2)) := fun k => by
    have hk2_ge1 : (k + 1)^2 ≥ 1 := Nat.one_le_pow 2 (k + 1) (by omega)
    exact prob_deviationEvent_le ((k + 1)^2) hk2_ge1 ε hε
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum h_bound)
  -- Show the bound sum is finite using Summable.tsum_ofReal_ne_top
  have h_summable := summable_one_div_sq
  have hε2_pos : (0 : ℝ) < 4 * ε^2 := by positivity
  -- The function k ↦ 1/(4 * (k+1)² * ε²) is summable since 1/(k+1)² is summable
  have h_summable_scaled : Summable (fun k => (1 : ℝ) / (4 * ((k + 1)^2 : ℕ) * ε^2)) := by
    have h_eq : ∀ k, (1 : ℝ) / (4 * ((k + 1)^2 : ℕ) * ε^2) = (1/(4*ε^2)) * (1/((k+1)^2 : ℕ)) := by
      intro k; field_simp
    simp_rw [h_eq]
    exact h_summable.mul_left (1/(4*ε^2))
  exact h_summable_scaled.tsum_ofReal_ne_top

/-- The limsup of deviation events along squares has measure zero by Borel-Cantelli. -/
theorem measure_limsup_deviationEvent_sq_eq_zero (ε : ℝ) (hε : 0 < ε) :
    probMeasureUnit (Filter.limsup (fun k => deviationEvent ((k + 1)^2) ε) Filter.atTop) = 0 :=
  measure_limsup_atTop_eq_zero (tsum_prob_deviationEvent_sq_ne_top ε hε)

/-! ## Interpolation from squares to all n

For k² ≤ n < (k+1)², the ratio S_n/n is controlled by S_{k²}/k² with error O(1/k).
-/

/-- For k ≥ 1 and k² ≤ n < (k+1)², we have |S_n/n - S_{k²}/k²| ≤ 4/k.
This is the key interpolation bound for the subsequence argument.

Proof sketch:
- |S_n - S_{k²}| ≤ n - k² ≤ 2k (difference of at most 2k digits, each 0 or 1)
- S_{k²} ≤ k² (sum of k² digits, each ≤ 1)
- |S_n/n - S_{k²}/k²| ≤ |S_n - S_{k²}|/n + S_{k²}|1/n - 1/k²|
                      ≤ 2k/k² + k² · (n-k²)/(n·k²) ≤ 2/k + 2k/k² = 4/k -/
theorem interpolation_bound_sq (k : ℕ) (hk : k ≥ 1) (n : ℕ) (hlo : k^2 ≤ n) (hhi : n < (k+1)^2)
    (ω : ℝ) :
    |((sumDigits n ω : ℝ) / n) - ((sumDigits (k^2) ω : ℝ) / k^2)| ≤ 4 / k := by
  -- Establish positivity facts
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk2_pos : (0 : ℝ) < k^2 := by positivity
  have hn_pos : (0 : ℝ) < n := by
    have : n ≥ k^2 := hlo
    have : k^2 ≥ 1 := Nat.one_le_pow 2 k hk
    exact Nat.cast_pos.mpr (by omega)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hk2_ne : (k : ℝ)^2 ≠ 0 := ne_of_gt hk2_pos
  -- Cast k^2 correctly
  have hk2_real : ((k^2 : ℕ) : ℝ) = (k : ℝ)^2 := by norm_cast
  -- Key bounds from helper lemmas
  -- 1. Gap bound: n - k² ≤ 2k (from n < (k+1)² = k² + 2k + 1)
  have h_gap : n - k^2 ≤ 2 * k := by
    have h1 : (k + 1)^2 = k^2 + 2 * k + 1 := by ring
    omega
  -- 2. sumDigits difference bound
  have h_diff : sumDigits n ω - sumDigits (k^2) ω ≤ n - k^2 := sumDigits_diff_le hlo ω
  have h_diff_2k : sumDigits n ω - sumDigits (k^2) ω ≤ 2 * k := by omega
  -- 3. sumDigits bound
  have h_sk2_le : sumDigits (k^2) ω ≤ k^2 := sumDigits_le (k^2) ω
  -- 4. Monotonicity: S_n ≥ S_k²
  have h_mono : sumDigits (k^2) ω ≤ sumDigits n ω := sumDigits_mono hlo ω
  -- Set up the real-valued expressions
  let Sn : ℝ := sumDigits n ω
  let Sk2 : ℝ := sumDigits (k^2) ω
  -- The difference S_n - S_k² is non-negative
  have h_Sn_ge_Sk2 : Sk2 ≤ Sn := by simp only [Sn, Sk2]; exact Nat.cast_le.mpr h_mono
  -- The difference S_n - S_k² ≤ 2k
  have h_real_diff : Sn - Sk2 ≤ 2 * k := by
    simp only [Sn, Sk2]
    have : (sumDigits n ω : ℝ) - (sumDigits (k^2) ω : ℝ) = ((sumDigits n ω - sumDigits (k^2) ω : ℕ) : ℝ) := by
      rw [Nat.cast_sub h_mono]
    rw [this]
    exact_mod_cast h_diff_2k
  -- S_k² ≤ k²
  have h_Sk2_le : Sk2 ≤ (k : ℝ)^2 := by
    simp only [Sk2]
    calc (sumDigits (k^2) ω : ℝ) ≤ ((k^2 : ℕ) : ℝ) := Nat.cast_le.mpr h_sk2_le
      _ = (k : ℝ)^2 := by norm_cast
  have h_n_ge_k2 : (k : ℝ)^2 ≤ n := by exact_mod_cast hlo
  have h_gap_real : n - (k : ℝ)^2 ≤ 2 * k := by
    have : (n : ℝ) - (k : ℝ)^2 = ((n - k^2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hlo]; norm_cast
    rw [this]
    exact_mod_cast h_gap
  -- Sk2 is non-negative
  have h_Sk2_nonneg : 0 ≤ Sk2 := by simp only [Sk2]; exact Nat.cast_nonneg _
  -- Sn - Sk2 is non-negative
  have h_diff_nonneg : 0 ≤ Sn - Sk2 := by linarith
  -- n - k² is non-negative
  have h_gap_nonneg : 0 ≤ n - (k : ℝ)^2 := by linarith
  -- Rewrite the target using common denominator
  have h_expr : Sn / n - Sk2 / (k : ℝ)^2 = (Sn * (k : ℝ)^2 - Sk2 * n) / (n * (k : ℝ)^2) := by
    field_simp
  rw [h_expr]
  rw [abs_div, abs_of_pos (by positivity : 0 < n * (k : ℝ)^2)]
  rw [div_le_iff₀ (by positivity : 0 < n * (k : ℝ)^2)]
  -- Rewrite numerator
  have h_rewrite : Sn * (k : ℝ)^2 - Sk2 * n = (Sn - Sk2) * (k : ℝ)^2 - Sk2 * (n - (k : ℝ)^2) := by
    ring
  rw [h_rewrite]
  -- Let X = (Sn - Sk2) * k² and Y = Sk2 * (n - k²). Both are non-negative.
  -- |X - Y| ≤ max(X, Y) ≤ X + Y
  set X := (Sn - Sk2) * (k : ℝ)^2 with hX_def
  set Y := Sk2 * (n - (k : ℝ)^2) with hY_def
  have hX_nonneg : 0 ≤ X := mul_nonneg h_diff_nonneg (by positivity)
  have hY_nonneg : 0 ≤ Y := mul_nonneg h_Sk2_nonneg h_gap_nonneg
  -- |X - Y| ≤ X + Y when both non-negative
  have h_abs_bound : |X - Y| ≤ X + Y := by
    by_cases hXY : X ≤ Y
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · push Not at hXY
      rw [abs_of_pos (by linarith)]
      linarith
  -- The goal RHS is 4 / k * (n * k²). Let's compute: 4/k * n * k² = 4 * n * k.
  -- Show X + Y ≤ 4 * k³ ≤ 4 * n * k (using k² ≤ n from hlo)
  have h_k2_le_n : (k : ℝ)^2 ≤ n := by exact_mod_cast hlo
  have h_bound : X + Y ≤ 4 * n * k := by
    calc X + Y
        = (Sn - Sk2) * (k : ℝ)^2 + Sk2 * (n - (k : ℝ)^2) := rfl
      _ ≤ (2 * k) * (k : ℝ)^2 + (k : ℝ)^2 * (2 * k) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_right h_real_diff (by positivity)
          · apply mul_le_mul h_Sk2_le h_gap_real h_gap_nonneg (by positivity)
      _ = 4 * k^3 := by ring
      _ = 4 * k * (k : ℝ)^2 := by ring
      _ ≤ 4 * k * n := by nlinarith [h_k2_le_n]
      _ = 4 * n * k := by ring
  -- 4 / k * (n * k²) = 4 * n * k, so the bound suffices
  have h_rhs_eq : 4 / k * (n * (k : ℝ)^2) = 4 * n * k := by
    have hk_ne : (k : ℝ) ≠ 0 := by linarith
    field_simp
  linarith [h_abs_bound, h_bound, h_rhs_eq]

/-- For ω ∈ halfOpenUnit, if |S_{k²}/k² - 1/2| < ε for all sufficiently large k,
then S_n/n → 1/2 as n → ∞.

This uses the interpolation bound: for k² ≤ n < (k+1)², |S_n/n - S_k²/k²| ≤ 4/k. -/
theorem tendsto_of_sq_convergence (ω : ℝ) (_hω : ω ∈ halfOpenUnit)
    (h : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, |((sumDigits (k^2) ω : ℝ) / k^2) - 1/2| < ε) :
    Filter.Tendsto (fun n => (sumDigits n ω : ℝ) / n) Filter.atTop (nhds (1/2 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get K₁ such that for k ≥ K₁, |S_{k²}/k² - 1/2| < ε/2
  obtain ⟨K₁, hK₁⟩ := h (ε/2) (by linarith)
  -- Get K₂ such that K₂ ≥ 1 and for k ≥ K₂, 4/k < ε/2
  have h_arch : ∃ K₂ : ℕ, K₂ ≥ 1 ∧ (4 : ℝ) / K₂ < ε / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (8 / ε)
    use N + 1
    constructor
    · omega
    · -- From hN : 8/ε < N, we get 8 < ε * N
      have h2 : 8 < ε * N := by
        have := (div_lt_iff₀ hε).mp hN
        linarith
      -- Goal: 4 / (N+1 : ℕ) < ε/2
      -- Need to show: 4 < (ε/2) * (N+1)
      have hN1_pos : (0 : ℝ) < (N + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
      rw [div_lt_iff₀ hN1_pos]
      -- Goal: 4 < (ε/2) * (N+1)
      simp only [Nat.cast_add, Nat.cast_one]
      calc (4 : ℝ) = 8 / 2 := by ring
        _ < ε * N / 2 := by linarith
        _ ≤ ε * (N + 1) / 2 := by nlinarith
        _ = ε / 2 * (↑N + 1) := by ring
  obtain ⟨K₂, hK₂_ge_1, hK₂⟩ := h_arch
  -- Take K = max(K₁, K₂) + 1, so for k ≥ K we have both properties
  let K := max K₁ K₂ + 1
  have hK_ge_K1 : K ≥ K₁ + 1 := by simp only [K]; omega
  have hK_ge_K2 : K ≥ K₂ + 1 := by simp only [K]; omega
  -- For n ≥ K², we have the desired bound
  use K^2
  intro n hn
  rw [Real.dist_eq]
  -- Find k such that k² ≤ n < (k+1)²
  let k := Nat.sqrt n
  have hk_sq_le : k^2 ≤ n := Nat.sqrt_le' n
  have hn_lt_k1_sq : n < (k + 1)^2 := Nat.lt_succ_sqrt' n
  -- k ≥ K (since n ≥ K² implies sqrt(n) ≥ K)
  have hk_ge : k ≥ K := by
    have h1 : K^2 ≤ n := hn
    -- sqrt(K^2) = K and sqrt is monotone
    have h2 : K ≤ Nat.sqrt (K^2) := Nat.le_sqrt'.mpr (le_refl _)
    have h3 : Nat.sqrt (K^2) ≤ Nat.sqrt n := Nat.sqrt_le_sqrt h1
    exact le_trans h2 h3
  have hk_ge_1 : k ≥ 1 := by omega
  have hk_ge_K1 : k ≥ K₁ := by omega
  have hk_ge_K2 : k ≥ K₂ := by omega
  -- Apply triangle inequality
  calc |((sumDigits n ω : ℝ) / n) - 1/2|
      ≤ |((sumDigits n ω : ℝ) / n) - ((sumDigits (k^2) ω : ℝ) / k^2)|
        + |((sumDigits (k^2) ω : ℝ) / k^2) - 1/2| := abs_sub_le _ _ _
    _ ≤ 4 / k + |((sumDigits (k^2) ω : ℝ) / k^2) - 1/2| := by
        have h_interp := interpolation_bound_sq k hk_ge_1 n hk_sq_le hn_lt_k1_sq ω
        linarith
    _ < 4 / k + ε / 2 := by
        have h_conv := hK₁ k hk_ge_K1
        linarith
    _ ≤ 4 / K₂ + ε / 2 := by
        have hK₂_le_k : (K₂ : ℝ) ≤ k := Nat.cast_le.mpr hk_ge_K2
        have hK₂_pos : (0 : ℝ) < K₂ := Nat.cast_pos.mpr (by omega : 0 < K₂)
        have h_div : (4 : ℝ) / k ≤ 4 / K₂ := by
          apply div_le_div_of_nonneg_left
          · norm_num
          · exact hK₂_pos
          · exact hK₂_le_k
        linarith
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- The set of ω where S_{k²}/k² → 1/2 along squares, for a fixed ε, has full measure.
This follows from Borel-Cantelli: the complement has measure zero.

The key insight: {ω | eventually |S_{k²}/k² - 1/2| < ε} is the complement of
limsup_k {ω | |S_{k²}/k² - 1/2| ≥ ε}, and this limsup has measure 0 by Borel-Cantelli
since ∑_k P(deviationEvent k² ε) < ∞. -/
-- Helper: deviationEvent is a subset of halfOpenUnit
theorem deviationEvent_subset_halfOpenUnit (n : ℕ) (ε : ℝ) :
    deviationEvent n ε ⊆ halfOpenUnit := fun _ω hω => hω.1

-- Helper: the limsup of deviationEvents along squares is in halfOpenUnit
theorem limsup_deviationEvent_sq_subset_halfOpenUnit (ε : ℝ) :
    Filter.limsup (fun k => deviationEvent ((k + 1)^2) ε) Filter.atTop ⊆ halfOpenUnit := by
  intro ω hω
  -- ω ∈ limsupE ↔ ω ∈ infinitely many E(k)
  rw [Filter.mem_limsup_iff_frequently_mem] at hω
  -- ∃ᶠ k in atTop, ω ∈ E(k) means ω is in E(k) for some k, hence in halfOpenUnit
  obtain ⟨k, hk⟩ := hω.exists
  exact deviationEvent_subset_halfOpenUnit ((k + 1)^2) ε hk

theorem ae_convergence_along_sq (ε : ℝ) (hε : 0 < ε) :
    probMeasureUnit {ω ∈ halfOpenUnit | ∃ K : ℕ, ∀ k ≥ K,
        |((sumDigits ((k+1)^2) ω : ℝ) / ((k+1)^2 : ℕ)) - 1/2| < ε} = 1 := by
  -- Define abbreviations for readability
  let E := fun k => deviationEvent ((k + 1)^2) ε
  let limsupE := Filter.limsup E Filter.atTop
  let goodSet := {ω ∈ halfOpenUnit | ∃ K : ℕ, ∀ k ≥ K,
      |((sumDigits ((k+1)^2) ω : ℝ) / ((k+1)^2 : ℕ)) - 1/2| < ε}
  -- Step 1: limsupE ⊆ halfOpenUnit
  have h_limsup_subset : limsupE ⊆ halfOpenUnit := limsup_deviationEvent_sq_subset_halfOpenUnit ε
  -- Step 2: goodSet = halfOpenUnit \ limsupE
  have h_set_eq : goodSet = halfOpenUnit \ limsupE := by
    ext ω
    simp only [Set.mem_sdiff]
    constructor
    · intro ⟨hω_unit, K, hK⟩
      refine ⟨hω_unit, ?_⟩
      -- Show ω ∉ limsupE
      rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently, Filter.eventually_atTop]
      use K
      intro k hk
      simp only [E, deviationEvent, Set.mem_ofPred_eq]
      intro ⟨_, h_ge⟩
      have h_lt := hK k hk
      linarith
    · intro ⟨hω_unit, hω_not_limsup⟩
      refine ⟨hω_unit, ?_⟩
      rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently, Filter.eventually_atTop]
        at hω_not_limsup
      obtain ⟨K, hK⟩ := hω_not_limsup
      use K
      intro k hk
      have h_not_in := hK k hk
      simp only [E, deviationEvent, Set.mem_ofPred_eq] at h_not_in
      push Not at h_not_in
      exact h_not_in hω_unit
  -- Step 3: P(limsupE) = 0 by Borel-Cantelli
  have h_limsup_zero : probMeasureUnit limsupE = 0 :=
    measure_limsup_deviationEvent_sq_eq_zero ε hε
  -- Step 4: P(goodSet) = P(halfOpenUnit \ limsupE) = P(halfOpenUnit) - P(limsupE) = 1 - 0 = 1
  have h_limsup_meas : MeasurableSet limsupE := by
    -- Use the @[measurability]-tagged lemma from MeasurableSet namespace
    exact MeasurableSet.measurableSet_limsup fun k => deviationEvent_measurableSet ((k+1)^2) ε
  calc probMeasureUnit goodSet
      = probMeasureUnit (halfOpenUnit \ limsupE) := by rw [h_set_eq]
    _ = probMeasureUnit halfOpenUnit - probMeasureUnit limsupE := by
        apply measure_sdiff h_limsup_subset h_limsup_meas.nullMeasurableSet
        rw [h_limsup_zero]; exact ENNReal.zero_ne_top
    _ = 1 - 0 := by
        rw [h_limsup_zero]
        simp only [probMeasureUnit, halfOpenUnit]
        norm_num
    _ = 1 := by norm_num

/-- The set of normal numbers is exactly the intersection over all positive rationals. -/
theorem normalNumbers_eq_iInter :
    normalNumbers = ⋂ q ∈ {q : ℚ | 0 < q},
      {ω ∈ halfOpenUnit | ∃ K : ℕ, ∀ k ≥ K,
        |((sumDigits ((k+1)^2) ω : ℝ) / ((k+1)^2 : ℕ)) - 1/2| < (q : ℝ)} := by
  ext ω
  constructor
  · -- LHS ⊆ RHS: normal implies eventually close along squares for all q
    intro hω
    simp only [normalNumbers, Set.mem_ofPred_eq] at hω
    obtain ⟨hω_unit, hω_normal⟩ := hω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro q hq
    refine ⟨hω_unit, ?_⟩
    -- IsNormal means S_n/n → 1/2, which implies eventually |S_n/n - 1/2| < q
    unfold IsNormal at hω_normal
    rw [Metric.tendsto_atTop] at hω_normal
    obtain ⟨N, hN⟩ := hω_normal (q : ℝ) (Rat.cast_pos.mpr hq)
    -- For k ≥ N, (k+1)² ≥ N, so the deviation is < q
    use N
    intro k hk
    have h_n_ge : (k+1)^2 ≥ N := by nlinarith
    specialize hN ((k+1)^2) h_n_ge
    simp only [Real.dist_eq] at hN
    convert hN using 2
  · -- RHS ⊆ LHS: eventually close along squares for all q implies normal
    intro h
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h
    -- First extract membership in halfOpenUnit from q = 1
    have hω_unit : ω ∈ halfOpenUnit := (h 1 (by norm_num : (0 : ℚ) < 1)).1
    simp only [normalNumbers, Set.mem_ofPred_eq]
    refine ⟨hω_unit, ?_⟩
    -- Apply tendsto_of_sq_convergence
    apply tendsto_of_sq_convergence ω hω_unit
    intro ε hε
    -- Find a rational q with 0 < q < ε
    obtain ⟨q, hq_pos_real, hq_lt⟩ := exists_rat_btwn hε
    have hq_pos : (0 : ℚ) < q := Rat.cast_pos.mp hq_pos_real
    -- Get K from the hypothesis for this q
    obtain ⟨_, K, hK⟩ := h q hq_pos
    -- For j ≥ K+1, we have j = k+1 for some k ≥ K
    use K + 1
    intro j hj
    have hj_pos : j ≥ 1 := by omega
    -- j ≥ K+1, so j-1 ≥ K, and j = (j-1)+1
    have hk : j - 1 ≥ K := by omega
    specialize hK (j - 1) hk
    -- The statement hK is about (j-1+1)² = j²
    have hj_eq : ((j - 1) + 1) = j := by omega
    calc |((sumDigits (j^2) ω : ℝ) / j^2) - 1/2|
        = |((sumDigits (j^2) ω : ℝ) / (j^2 : ℕ)) - 1/2| := by
            congr 1; congr 1; simp only [Nat.cast_pow]
      _ = |((sumDigits (((j-1)+1)^2) ω : ℝ) / (((j-1)+1)^2 : ℕ)) - 1/2| := by rw [hj_eq]
      _ < (q : ℝ) := hK
      _ < ε := hq_lt

/-- Full proof of Borel's Normal Number Theorem.
This theorem follows from:
1. `normalNumbers_eq_iInter`: Normal numbers = ⋂_{q > 0} {ω | eventually |S_{(k+1)²}/(k+1)² - 1/2| < q}
2. `ae_convergence_along_sq`: Each set in the intersection has measure 1
3. Countable intersection of measure-1 sets in a probability space has measure 1

The proof requires showing that ⋃_{q>0} (good_set q)ᶜ has measure 0, which follows from
each (good_set q)ᶜ having measure 0 (since good_set q has measure 1) and the countability of ℚ. -/
theorem borelNormalNumberTheorem : probMeasureUnit normalNumbers = 1 := by
  rw [normalNumbers_eq_iInter]
  -- Define good_set for convenience
  let good_set := fun (q : ℚ) => {ω ∈ halfOpenUnit | ∃ K : ℕ, ∀ k ≥ K,
      |((sumDigits ((k+1)^2) ω : ℝ) / ((k+1)^2 : ℕ)) - 1/2| < (q : ℝ)}
  -- Each good_set q has measure 1 for positive q
  have h_each_full : ∀ q : ℚ, 0 < q → probMeasureUnit (good_set q) = 1 :=
    fun q hq => ae_convergence_along_sq (q : ℝ) (Rat.cast_pos.mpr hq)
  -- Each good_set q is a subset of halfOpenUnit
  have h_subset : ∀ q : ℚ, good_set q ⊆ halfOpenUnit := fun q ω hω => hω.1
  -- good_set is measurable (it's halfOpenUnit \ limsup, and limsup of measurable sets is measurable)
  have h_good_meas : ∀ q : ℚ, 0 < q → NullMeasurableSet (good_set q) probMeasureUnit := by
    intro q hq
    -- Define the limsup of deviation events
    let E := fun k => deviationEvent ((k + 1)^2) (q : ℝ)
    let limsupE := Filter.limsup E Filter.atTop
    -- Prove good_set q = halfOpenUnit \ limsupE (same proof as in ae_convergence_along_sq)
    have h_set_eq : good_set q = halfOpenUnit \ limsupE := by
      ext ω
      simp only [Set.mem_sdiff]
      constructor
      · intro ⟨hω_unit, K, hK⟩
        refine ⟨hω_unit, ?_⟩
        rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently, Filter.eventually_atTop]
        use K
        intro k hk
        simp only [E, deviationEvent, Set.mem_ofPred_eq]
        intro ⟨_, h_ge⟩
        have h_lt := hK k hk
        linarith
      · intro ⟨hω_unit, hω_not_limsup⟩
        refine ⟨hω_unit, ?_⟩
        rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently, Filter.eventually_atTop]
          at hω_not_limsup
        obtain ⟨K, hK⟩ := hω_not_limsup
        use K
        intro k hk
        have h_not_in := hK k hk
        simp only [E, deviationEvent, Set.mem_ofPred_eq] at h_not_in
        push Not at h_not_in
        exact h_not_in hω_unit
    -- limsupE is measurable
    have h_limsup_meas : MeasurableSet limsupE :=
      MeasurableSet.measurableSet_limsup fun k => deviationEvent_measurableSet ((k+1)^2) (q : ℝ)
    -- halfOpenUnit \ limsupE is measurable
    have h_diff_meas : MeasurableSet (halfOpenUnit \ limsupE) :=
      halfOpenUnit_measurableSet.diff h_limsup_meas
    -- Transport measurability via the equality
    rw [h_set_eq]
    exact h_diff_meas.nullMeasurableSet
  -- The complement of each good_set within halfOpenUnit has measure 0
  have h_each_compl_null : ∀ q : ℚ, 0 < q → probMeasureUnit (halfOpenUnit \ good_set q) = 0 := by
    intro q hq
    have hfull := h_each_full q hq
    have hmeas := h_good_meas q hq
    calc probMeasureUnit (halfOpenUnit \ good_set q)
        = probMeasureUnit halfOpenUnit - probMeasureUnit (good_set q) := by
          apply measure_sdiff (h_subset q) hmeas
          rw [hfull]; exact ENNReal.one_ne_top
      _ = 1 - 1 := by
          rw [hfull]
          simp only [probMeasureUnit, halfOpenUnit]
          norm_num
      _ = 0 := by norm_num
  -- The intersection complement is the union of complements (within halfOpenUnit)
  have h_compl_eq : (⋂ q ∈ {q : ℚ | 0 < q}, good_set q)ᶜ ∩ halfOpenUnit =
      ⋃ q ∈ {q : ℚ | 0 < q}, (halfOpenUnit \ good_set q) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_sdiff]
    constructor
    · intro ⟨h_not_in, h_unit⟩
      push Not at h_not_in
      obtain ⟨q, hq_pos, h_not_good⟩ := h_not_in
      exact ⟨q, hq_pos, h_unit, h_not_good⟩
    · intro ⟨q, hq_pos, h_unit, h_not_good⟩
      refine ⟨?_, h_unit⟩
      push Not
      exact ⟨q, hq_pos, h_not_good⟩
  -- The union of null sets is null (countable union)
  have h_union_null : probMeasureUnit (⋃ q ∈ {q : ℚ | 0 < q}, (halfOpenUnit \ good_set q)) = 0 := by
    have h_countable : {q : ℚ | 0 < q}.Countable := Set.to_countable _
    rw [measure_biUnion_null_iff h_countable]
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq
    exact h_each_compl_null q hq
  -- The union is contained in halfOpenUnit
  have h_union_subset : (⋃ q ∈ {q : ℚ | 0 < q}, (halfOpenUnit \ good_set q)) ⊆ halfOpenUnit := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_sdiff] at hω
    obtain ⟨q, _, hω_unit, _⟩ := hω
    exact hω_unit
  -- The complement of the intersection (restricted to halfOpenUnit) has measure 0
  have h_compl_null : probMeasureUnit ((⋂ q ∈ {q : ℚ | 0 < q}, good_set q)ᶜ) = 0 := by
    -- The complement restricted to halfOpenUnit equals the union
    have h_restrict_compl : probMeasureUnit ((⋂ q ∈ {q : ℚ | 0 < q}, good_set q)ᶜ) =
        probMeasureUnit ((⋂ q ∈ {q : ℚ | 0 < q}, good_set q)ᶜ ∩ halfOpenUnit) := by
      simp only [probMeasureUnit]
      rw [Measure.restrict_apply' halfOpenUnit_measurableSet,
          Measure.restrict_apply' halfOpenUnit_measurableSet]
      congr 1
      rw [Set.inter_assoc, Set.inter_self]
    rw [h_restrict_compl, h_compl_eq]
    exact h_union_null
  -- Therefore the intersection has full measure
  have h_eq_univ := measure_of_measure_compl_eq_zero h_compl_null
  -- h_eq_univ : probMeasureUnit (⋂ ...) = probMeasureUnit Set.univ
  -- We need probMeasureUnit Set.univ = 1
  have h_univ_eq_one : probMeasureUnit Set.univ = 1 := by
    simp only [probMeasureUnit, Measure.restrict_apply_univ, halfOpenUnit, Real.volume_Ioc]
    norm_num
  rw [h_eq_univ, h_univ_eq_one]

end Mettapedia.ProbabilityTheory.NormalNumbers

end
