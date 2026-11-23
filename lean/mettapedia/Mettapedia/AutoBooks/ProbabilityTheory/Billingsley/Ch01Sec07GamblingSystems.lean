/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Independence.Basic

/-!
# Billingsley Chapter 1, Section 7: Gambling Systems

The closed forms of the gambler's-ruin problem in Section 7 of Billingsley's
"Probability and Measure" (3rd Edition).

## Main theorems

* Formula (7.7): the success probability s_c(a)
  - s_c(a) = (ρ^a - 1)/(ρ^c - 1) if p ≠ q, where ρ = q/p
  - s_c(a) = a/c if p = q = 1/2
* `probSuccess_recursion` and `probSuccess_boundary`: the closed form solves the
  difference equation s_c(a) = p s_c(a+1) + q s_c(a-1) with s_c(0) = 0 and s_c(c) = 1
* `success_plus_ruin_eq_one`: the closed forms of success and ruin sum to 1

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 7][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Mettapedia.AutoBooks.Billingsley.Ch01Sec07

/-! ## The Gambler's Ruin Problem -/

/-- The odds against the gambler: ρ = q/p where q = 1-p. -/
def oddsAgainst (p : ℝ) : ℝ := (1 - p) / p

/-- Probability of ultimate success from initial capital a with goal c.
Formula (7.7): s_c(a) = (ρ^a - 1)/(ρ^c - 1) if ρ ≠ 1, else a/c. -/
def probSuccess (p : ℝ) (a c : ℕ) : ℝ :=
  if oddsAgainst p = 1 then (a : ℝ) / c
  else ((oddsAgainst p)^a - 1) / ((oddsAgainst p)^c - 1)

/-- Probability of ruin from initial capital a with goal c.
Note: This is r_c(a) = (ρ^c - ρ^a)/(ρ^c - 1) for ρ ≠ 1.
Equivalently, r_c(a) = 1 - s_c(a). -/
def probRuin (p : ℝ) (a c : ℕ) : ℝ :=
  if oddsAgainst p = 1 then ((c : ℝ) - a) / c
  else ((oddsAgainst p)^c - (oddsAgainst p)^a) / ((oddsAgainst p)^c - 1)

/-- The closed forms of success and ruin sum to 1. -/
theorem success_plus_ruin_eq_one (p : ℝ) (_hp : 0 < p ∧ p < 1) (a c : ℕ)
    (_ha : 0 < a) (hac : a < c) :
    probSuccess p a c + probRuin p a c = 1 := by
  unfold probSuccess probRuin
  split_ifs with h
  · -- Fair game: a/c + (c-a)/c = c/c = 1
    have hc : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le a) hac))
    field_simp
    ring
  · -- Unfair game: (ρ^a - 1)/(ρ^c - 1) + (ρ^c - ρ^a)/(ρ^c - 1) = 1
    have hρc : (oddsAgainst p)^c - 1 ≠ 0 := by
      intro heq
      have hρc_eq : (oddsAgainst p)^c = 1 := sub_eq_zero.mp heq
      have hc_pos : 0 < c := Nat.lt_of_le_of_lt (Nat.zero_le a) hac
      have hρ_one : oddsAgainst p = 1 ∨ (oddsAgainst p = -1 ∧ Even c) :=
        (pow_eq_one_iff_of_ne_zero (Nat.one_le_iff_ne_zero.mp hc_pos)).mp hρc_eq
      rcases hρ_one with h1 | ⟨hρ_neg, _⟩
      · exact h h1
      · -- oddsAgainst ≥ 0, can't be -1
        have hp_pos : 0 < p := _hp.1
        have hp1 : p < 1 := _hp.2
        unfold oddsAgainst at hρ_neg
        have h_nonneg : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (le_of_lt hp_pos)
        linarith
    field_simp [hρc]
    ring

/-- The recursion relation for s_c(a):
s_c(a) = p · s_c(a+1) + q · s_c(a-1). Billingsley's (7.5). -/
theorem probSuccess_recursion (p : ℝ) (hp : 0 < p ∧ p < 1) (a c : ℕ)
    (ha : 0 < a) (hac : a < c) :
    probSuccess p a c = p * probSuccess p (a + 1) c + (1 - p) * probSuccess p (a - 1) c := by
  obtain ⟨hp_pos, hp_lt⟩ := hp
  have hq_pos : 0 < 1 - p := by linarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have ha1 : (a - 1) + 1 = a := Nat.sub_add_cancel ha
  have hc_pos : 0 < c := lt_of_le_of_lt (Nat.zero_le _) hac
  have hc_ne : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc_pos.ne'
  have ha1_cast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha]; push_cast; rfl
  unfold probSuccess
  split_ifs with h
  · -- Fair case: oddsAgainst p = 1 forces p = 1/2, so 1 - p = p.
    have hq_eq : 1 - p = p := by
      have heq : (1 - p) / p = 1 := h
      field_simp at heq; linarith
    have hp_half : p = 1 / 2 := by linarith
    rw [ha1_cast, hp_half]
    push_cast
    field_simp
    ring
  · -- Unfair case: ρ = oddsAgainst p ≠ 1.
    set ρ : ℝ := oddsAgainst p with hρ_def
    have hρ_val : ρ = (1 - p) / p := rfl
    have hρ_nonneg : 0 ≤ ρ := by
      rw [hρ_val]; exact div_nonneg hq_pos.le hp_pos.le
    have hρc_ne : ρ^c - 1 ≠ 0 := by
      intro heq
      have hρc_eq : ρ^c = 1 := sub_eq_zero.mp heq
      have hρ_one := (pow_eq_one_iff_of_ne_zero hc_pos.ne').mp hρc_eq
      rcases hρ_one with h1 | ⟨hρ_neg, _⟩
      · exact h h1
      · linarith
    -- Fundamental identity: p ρ² + (1-p) = ρ (from ρ = (1-p)/p).
    have hρ_eq : p * ρ^2 + (1 - p) = ρ := by
      rw [hρ_val]; field_simp; ring
    have hpow_a : ρ^a = ρ^(a-1) * ρ := by
      conv_lhs => rw [← ha1, pow_succ]
    have hpow_ap1 : ρ^(a+1) = ρ^(a-1) * ρ^2 := by
      rw [pow_succ, hpow_a]; ring
    -- Polynomial identity in ρ:
    have key : ρ^a - 1 = p * (ρ^(a+1) - 1) + (1 - p) * (ρ^(a-1) - 1) := by
      rw [hpow_a, hpow_ap1]
      linear_combination -ρ^(a-1) * hρ_eq
    have combine :
        p * ((ρ^(a+1) - 1) / (ρ^c - 1)) + (1 - p) * ((ρ^(a-1) - 1) / (ρ^c - 1))
          = (ρ^a - 1) / (ρ^c - 1) := by
      rw [key]
      field_simp
    exact combine.symm

/-- Boundary conditions: s_c(0) = 0 and s_c(c) = 1. -/
theorem probSuccess_boundary (p : ℝ) (hp : 0 < p ∧ p < 1) (c : ℕ) (hc : 0 < c) :
    probSuccess p 0 c = 0 ∧ probSuccess p c c = 1 := by
  constructor
  · -- s_c(0) = 0
    unfold probSuccess
    split_ifs with h
    · simp
    · simp [pow_zero]
  · -- s_c(c) = 1
    unfold probSuccess
    split_ifs with h
    · -- Fair game: c/c = 1 when c > 0
      simp [ne_of_gt hc]
    · -- Not fair game: (ρ^c - 1)/(ρ^c - 1) = 1
      have hne : oddsAgainst p ^ c - 1 ≠ 0 := by
        intro heq
        have hρc : oddsAgainst p ^ c = 1 := sub_eq_zero.mp heq
        have hρ_ne : oddsAgainst p ≠ 1 := h
        have hρ_one : oddsAgainst p = 1 ∨ (oddsAgainst p = -1 ∧ Even c) :=
          (pow_eq_one_iff_of_ne_zero (Nat.one_le_iff_ne_zero.mp hc)).mp hρc
        rcases hρ_one with h1 | ⟨hρ_neg, _⟩
        · exact hρ_ne h1
        · -- oddsAgainst p = (1-p)/p ≥ 0 when p ∈ (0,1], so can't be -1
          unfold oddsAgainst at hρ_neg
          have hp_pos : 0 < p := hp.1
          have hp1 : p < 1 := hp.2
          have h_nonneg : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (le_of_lt hp_pos)
          linarith
      exact div_self hne

/-! ## Fair Games -/

/-- A game is fair if p = 1/2 (odds against = 1). -/
def IsFairGame (p : ℝ) : Prop := p = 1/2

/-- A game is favorable to the gambler if p > 1/2. -/
def IsFavorableGame (p : ℝ) : Prop := p > 1/2

/-- A game is subfair (unfavorable) if p < 1/2. -/
def IsSubfairGame (p : ℝ) : Prop := p < 1/2

/-- For fair games, success probability is a/c. -/
theorem fair_game_success_prob (a c : ℕ) (_hac : a ≤ c) (_hc : 0 < c) :
    probSuccess (1/2) a c = (a : ℝ) / c := by
  unfold probSuccess oddsAgainst
  -- oddsAgainst (1/2) = (1 - 1/2) / (1/2) = 1
  have h : (1 - (1:ℝ)/2) / (1/2) = 1 := by norm_num
  simp only [h, ↓reduceIte]

end Mettapedia.AutoBooks.Billingsley.Ch01Sec07

end
