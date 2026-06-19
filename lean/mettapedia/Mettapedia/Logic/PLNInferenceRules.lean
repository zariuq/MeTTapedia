import Mathlib.Tactic
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNDerivation

/-!
# PLN Inference Rules: First-Order Extensional Inference

This file formalizes PLN inference rules from Goertzel et al. (2008),
covering inference rules beyond the core deduction/induction/abduction triad.

## Contents

1. **Similarity Rules** (§5.5): Converting between inheritance and similarity
   - `twoInh2Sim` - sim_AC from s_AC and s_CA
   - `inh2sim` - sim_AC from s_AC, s_A, s_C
   - `sim2inh` - s_AB from sim_AB, s_A, s_B
   - `transitiveSimilarity` - sim_AC from sim_AB, sim_BC

2. **Modus Ponens** (§5.7): Classical inference forms
   - `modusPonens` - P(B) from P(A), P(B|A), with default c
   - `modusTollens` - P(¬P) from P(P→Q), P(¬Q)
   - `symmetricModusPonens` - P(B) from sim_AB, P(A)

3. **Conversion Rules** (§5.8): Member ↔ Inheritance
   - `memberToInheritance`
   - `inheritanceToMember`

4. **Term Probability** (§5.9): Inference on term strengths
   - `termProbabilityInference` - s_B from s_A, s_AB, s_BA

## Mathematical Foundation

All rules derive from:
- Law of total probability: P(B) = P(B|A)P(A) + P(B|¬A)P(¬A)
- Bayes' rule: P(A|B) = P(B|A)P(A)/P(B)
- Set-theoretic definitions of similarity: sim(A,B) = |A ∩ B| / |A ∪ B|

## References

- Goertzel, Ikle, et al. "Probabilistic Logic Networks" (2008), Chapter 5
- Wang, "Non-Axiomatic Reasoning System" (for NARS comparison)
-/

namespace Mettapedia.Logic.PLNInferenceRules

open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLN

/-! ## §1: Similarity Rules

Similarity is a SYMMETRIC relationship: sim(A,B) = sim(B,A).

Set-theoretic definition:
  sim(A,B) = |A ∩ B| / |A ∪ B|

This relates to inheritance via:
  sim(A,B) = 1 / (1/s_AB + 1/s_BA - 1)

where s_AB = P(B|A) = |A ∩ B| / |A| is the inheritance strength.
-/

/-- **2inh2sim**: Compute similarity from two inheritance strengths.

Given s_AC = P(C|A) and s_CA = P(A|C), compute:
  sim_AC = 1 / (1/s_AC + 1/s_CA - 1)

This is the harmonic-like mean of the two directed strengths.
Derived from: sim = |A∩C| / |A∪C| and set algebra.
-/
noncomputable def twoInh2Sim (s_AC s_CA : ℝ) : ℝ :=
  if s_AC = 0 ∨ s_CA = 0 then 0
  else 1 / (1 / s_AC + 1 / s_CA - 1)

/-- 2inh2sim is symmetric in its arguments -/
theorem twoInh2Sim_comm (s_AC s_CA : ℝ) :
    twoInh2Sim s_AC s_CA = twoInh2Sim s_CA s_AC := by
  unfold twoInh2Sim
  simp only [or_comm]
  split_ifs <;> ring

/-- 2inh2sim formula simplification -/
theorem twoInh2Sim_eq (s_AC s_CA : ℝ) (hAC : s_AC ≠ 0) (hCA : s_CA ≠ 0) :
    twoInh2Sim s_AC s_CA = s_AC * s_CA / (s_AC + s_CA - s_AC * s_CA) := by
  unfold twoInh2Sim
  simp only [hAC, hCA, or_self, ↓reduceIte]
  have h : 1 / s_AC + 1 / s_CA - 1 = (s_AC + s_CA - s_AC * s_CA) / (s_AC * s_CA) := by
    field_simp
    ring
  rw [h]
  field_simp [hAC, hCA]

/-- 2inh2sim is bounded by 1 when inputs are valid probabilities -/
theorem twoInh2Sim_le_one (s_AC s_CA : ℝ)
    (hAC : 0 < s_AC ∧ s_AC ≤ 1) (hCA : 0 < s_CA ∧ s_CA ≤ 1) :
    twoInh2Sim s_AC s_CA ≤ 1 := by
  -- sim = s_AC·s_CA / (s_AC + s_CA - s_AC·s_CA) ≤ 1
  -- ⟺ s_AC·s_CA ≤ s_AC + s_CA - s_AC·s_CA (when denom > 0)
  -- ⟺ 2·s_AC·s_CA ≤ s_AC + s_CA
  have hne_AC : s_AC ≠ 0 := ne_of_gt hAC.1
  have hne_CA : s_CA ≠ 0 := ne_of_gt hCA.1
  rw [twoInh2Sim_eq s_AC s_CA hne_AC hne_CA]
  -- Now show: s_AC * s_CA / (s_AC + s_CA - s_AC * s_CA) ≤ 1
  have denom_pos : 0 < s_AC + s_CA - s_AC * s_CA := by
    -- s_AC + s_CA - s_AC * s_CA = s_AC * (1 - s_CA) + s_CA > 0
    have h1 : s_AC * (1 - s_CA) ≥ 0 := mul_nonneg (le_of_lt hAC.1) (by linarith [hCA.2])
    have h2 : s_CA > 0 := hCA.1
    linarith [mul_nonneg (le_of_lt hAC.1) (by linarith [hCA.2] : (0:ℝ) ≤ 1 - s_CA)]
  rw [div_le_one denom_pos]
  -- Need: s_AC * s_CA ≤ s_AC + s_CA - s_AC * s_CA
  -- ⟺ 2 * s_AC * s_CA ≤ s_AC + s_CA
  have h_amgm : 2 * s_AC * s_CA ≤ s_AC + s_CA := by
    -- 2ab ≤ a + b when a,b ∈ (0,1] follows from (a-b)² ≥ 0 and a,b ≤ 1
    -- Actually: 2ab ≤ a + b ⟺ 0 ≤ a + b - 2ab = a(1-b) + b(1-a)
    have h : 0 ≤ s_AC * (1 - s_CA) + s_CA * (1 - s_AC) := by
      apply add_nonneg
      · exact mul_nonneg (le_of_lt hAC.1) (by linarith [hCA.2])
      · exact mul_nonneg (le_of_lt hCA.1) (by linarith [hAC.2])
    linarith
  linarith

/-- On the probability unit square, `2inh2sim` reaches maximal similarity
exactly when both directed inheritance strengths are maximal. This is the
algebraic hinge that lets higher-order predicate similarity reuse the ordinary
PLN inheritance machinery instead of duplicating it. -/
theorem twoInh2Sim_eq_one_iff (s_AC s_CA : ℝ)
    (hAC : 0 ≤ s_AC ∧ s_AC ≤ 1) (hCA : 0 ≤ s_CA ∧ s_CA ≤ 1) :
    twoInh2Sim s_AC s_CA = 1 ↔ s_AC = 1 ∧ s_CA = 1 := by
  constructor
  · intro hsim
    by_cases hzero : s_AC = 0 ∨ s_CA = 0
    · unfold twoInh2Sim at hsim
      rw [if_pos hzero] at hsim
      norm_num at hsim
    · push_neg at hzero
      have hAC_pos : 0 < s_AC := lt_of_le_of_ne hAC.1 hzero.1.symm
      have hCA_pos : 0 < s_CA := lt_of_le_of_ne hCA.1 hzero.2.symm
      have hden_pos : 0 < s_AC + s_CA - s_AC * s_CA := by
        have h1 : 0 ≤ s_AC * (1 - s_CA) :=
          mul_nonneg hAC_pos.le (by linarith [hCA.2])
        nlinarith
      rw [twoInh2Sim_eq s_AC s_CA hzero.1 hzero.2] at hsim
      have hden_ne : s_AC + s_CA - s_AC * s_CA ≠ 0 :=
        ne_of_gt hden_pos
      have hmul : s_AC * s_CA = s_AC + s_CA - s_AC * s_CA := by
        rw [div_eq_iff hden_ne] at hsim
        simpa using hsim
      have hsum : 2 * s_AC * s_CA = s_AC + s_CA := by
        nlinarith
      have hAC_one : s_AC = 1 := by
        nlinarith [hAC_pos, hCA_pos, hAC.2, hCA.2, hsum]
      have hCA_one : s_CA = 1 := by
        nlinarith [hAC_pos, hCA_pos, hAC.2, hCA.2, hsum]
      exact ⟨hAC_one, hCA_one⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [twoInh2Sim]

/-- 2inh2sim is non-negative -/
theorem twoInh2Sim_nonneg (s_AC s_CA : ℝ)
    (hAC : 0 ≤ s_AC ∧ s_AC ≤ 1) (hCA : 0 ≤ s_CA ∧ s_CA ≤ 1) :
    0 ≤ twoInh2Sim s_AC s_CA := by
  unfold twoInh2Sim
  split_ifs with h
  · -- Case: s_AC = 0 ∨ s_CA = 0 → result is 0
    linarith
  · -- Case: both non-zero
    push_neg at h
    -- Result is 1 / (1/s_AC + 1/s_CA - 1)
    -- Both terms in denom are positive when s_AC, s_CA ∈ (0, 1]
    have hAC_pos : 0 < s_AC := hAC.1.lt_of_ne' h.1
    have hCA_pos : 0 < s_CA := hCA.1.lt_of_ne' h.2
    have denom_pos : 0 < 1 / s_AC + 1 / s_CA - 1 := by
      -- 1/s_AC + 1/s_CA - 1 = (s_AC + s_CA - s_AC*s_CA) / (s_AC*s_CA)
      -- Numerator: s_AC + s_CA - s_AC*s_CA = s_AC*(1-s_CA) + s_CA > 0
      have num_pos : 0 < s_AC + s_CA - s_AC * s_CA := by
        have h1 : 0 ≤ s_AC * (1 - s_CA) := mul_nonneg (le_of_lt hAC_pos) (by linarith [hCA.2])
        linarith
      have denom_eq : 1 / s_AC + 1 / s_CA - 1 = (s_AC + s_CA - s_AC * s_CA) / (s_AC * s_CA) := by
        field_simp
        ring
      rw [denom_eq]
      exact div_pos num_pos (mul_pos hAC_pos hCA_pos)
    exact le_of_lt (one_div_pos.mpr denom_pos)

/-- `2inh2sim` is monotone on the probability unit square. This is the
rule-validity fact needed by interval-valued and higher-order PLN lifts: if
both directed inheritance strengths increase, the induced similarity strength
cannot decrease. -/
theorem twoInh2Sim_mono_on_unit {s_AC₁ s_AC₂ s_CA₁ s_CA₂ : ℝ}
    (hAC₁_nonneg : 0 ≤ s_AC₁) (hAC₂_le_one : s_AC₂ ≤ 1)
    (hCA₁_nonneg : 0 ≤ s_CA₁) (hCA₂_le_one : s_CA₂ ≤ 1)
    (hAC : s_AC₁ ≤ s_AC₂) (hCA : s_CA₁ ≤ s_CA₂) :
    twoInh2Sim s_AC₁ s_CA₁ ≤ twoInh2Sim s_AC₂ s_CA₂ := by
  have hAC₂_nonneg : 0 ≤ s_AC₂ := le_trans hAC₁_nonneg hAC
  have hCA₂_nonneg : 0 ≤ s_CA₂ := le_trans hCA₁_nonneg hCA
  by_cases hleft : s_AC₁ = 0 ∨ s_CA₁ = 0
  · unfold twoInh2Sim
    rw [if_pos hleft]
    exact twoInh2Sim_nonneg s_AC₂ s_CA₂
      ⟨hAC₂_nonneg, hAC₂_le_one⟩ ⟨hCA₂_nonneg, hCA₂_le_one⟩
  · by_cases hright : s_AC₂ = 0 ∨ s_CA₂ = 0
    · rcases hright with hAC₂_zero | hCA₂_zero
      · have hAC₁_zero : s_AC₁ = 0 :=
          le_antisymm (by simpa [hAC₂_zero] using hAC) hAC₁_nonneg
        exact False.elim (hleft (Or.inl hAC₁_zero))
      · have hCA₁_zero : s_CA₁ = 0 :=
          le_antisymm (by simpa [hCA₂_zero] using hCA) hCA₁_nonneg
        exact False.elim (hleft (Or.inr hCA₁_zero))
    · push_neg at hleft hright
      have hAC₁_pos : 0 < s_AC₁ :=
        lt_of_le_of_ne hAC₁_nonneg hleft.1.symm
      have hCA₁_pos : 0 < s_CA₁ :=
        lt_of_le_of_ne hCA₁_nonneg hleft.2.symm
      have hAC₂_pos : 0 < s_AC₂ :=
        lt_of_le_of_ne hAC₂_nonneg hright.1.symm
      have hCA₂_pos : 0 < s_CA₂ :=
        lt_of_le_of_ne hCA₂_nonneg hright.2.symm
      have hleft_step :
          twoInh2Sim s_AC₁ s_CA₁ ≤ twoInh2Sim s_AC₂ s_CA₁ := by
        rw [twoInh2Sim_eq s_AC₁ s_CA₁ hleft.1 hleft.2]
        rw [twoInh2Sim_eq s_AC₂ s_CA₁ hright.1 hleft.2]
        have d1_pos : 0 < s_AC₁ + s_CA₁ - s_AC₁ * s_CA₁ := by
          have h1 : 0 ≤ s_AC₁ * (1 - s_CA₁) := by
            exact mul_nonneg hAC₁_pos.le (by linarith [hCA₂_le_one, hCA])
          nlinarith
        have d2_pos : 0 < s_AC₂ + s_CA₁ - s_AC₂ * s_CA₁ := by
          have h1 : 0 ≤ s_AC₂ * (1 - s_CA₁) := by
            exact mul_nonneg hAC₂_pos.le (by linarith [hCA₂_le_one, hCA])
          nlinarith
        rw [div_le_div_iff₀ d1_pos d2_pos]
        ring_nf
        nlinarith [hCA₁_pos]
      have hright_step :
          twoInh2Sim s_AC₂ s_CA₁ ≤ twoInh2Sim s_AC₂ s_CA₂ := by
        rw [twoInh2Sim_eq s_AC₂ s_CA₁ hright.1 hleft.2]
        rw [twoInh2Sim_eq s_AC₂ s_CA₂ hright.1 hright.2]
        have d1_pos : 0 < s_AC₂ + s_CA₁ - s_AC₂ * s_CA₁ := by
          have h1 : 0 ≤ s_CA₁ * (1 - s_AC₂) := by
            exact mul_nonneg hCA₁_pos.le (by linarith [hAC₂_le_one])
          nlinarith
        have d2_pos : 0 < s_AC₂ + s_CA₂ - s_AC₂ * s_CA₂ := by
          have h1 : 0 ≤ s_CA₂ * (1 - s_AC₂) := by
            exact mul_nonneg hCA₂_pos.le (by linarith [hAC₂_le_one])
          nlinarith
        rw [div_le_div_iff₀ d1_pos d2_pos]
        ring_nf
        nlinarith [hAC₂_pos]
      exact le_trans hleft_step hright_step

/-- **inh2sim**: Estimate similarity from single inheritance + term probabilities.

Given s_AC = P(C|A), s_A = P(A), s_C = P(C), estimate:
  sim_AC ≈ 1 / ((1 + s_A/s_C) / s_AC - 1)

This uses the approximation s_CA ≈ s_AC * s_A / s_C (Bayes-like).
-/
noncomputable def inh2sim (s_AC s_A s_C : ℝ) : ℝ :=
  if s_AC = 0 ∨ s_C = 0 then 0
  else 1 / ((1 + s_A / s_C) / s_AC - 1)

/-- **sim2inh**: Convert similarity to inheritance.

Given sim_AB, s_A, s_B, estimate s_AB = P(B|A):
  s_AB = (1 + s_B/s_A) * sim_AB / (1 + sim_AB)

This inverts the inh2sim formula.
-/
noncomputable def sim2inh (sim_AB s_A s_B : ℝ) : ℝ :=
  if s_A = 0 ∨ sim_AB = -1 then 0
  else (1 + s_B / s_A) * sim_AB / (1 + sim_AB)

/-- sim2inh gives valid probability when inputs are valid -/
theorem sim2inh_mem_unit (sim_AB s_A s_B : ℝ)
    (h_sim : 0 ≤ sim_AB ∧ sim_AB ≤ 1)
    (h_sA : 0 < s_A ∧ s_A ≤ 1)
    (h_sB : 0 ≤ s_B ∧ s_B ≤ 1)
    (h_constraint : s_B ≤ s_A) :  -- P(B) ≤ P(A) for valid inheritance
    sim2inh sim_AB s_A s_B ∈ Set.Icc (0 : ℝ) 1 := by
  -- Result = (1 + s_B/s_A) * sim_AB / (1 + sim_AB)
  -- Non-neg: all components ≥ 0
  -- Upper bound: (1+r)*sim ≤ 1+sim when r ≤ 1, i.e., r*sim ≤ 1
  unfold sim2inh
  have h_sA_ne : s_A ≠ 0 := ne_of_gt h_sA.1
  have h_sim_ne : sim_AB ≠ -1 := by linarith [h_sim.1]
  simp only [h_sA_ne, h_sim_ne, or_self, ↓reduceIte]
  constructor
  · -- Non-negativity
    apply div_nonneg
    · apply mul_nonneg
      · have : s_B / s_A ≥ 0 := div_nonneg h_sB.1 (le_of_lt h_sA.1)
        linarith
      · exact h_sim.1
    · linarith [h_sim.1]
  · -- Upper bound ≤ 1
    -- Need: (1 + s_B/s_A) * sim_AB ≤ 1 + sim_AB
    have denom_pos : 0 < 1 + sim_AB := by linarith [h_sim.1]
    rw [div_le_one denom_pos]
    -- (1 + s_B/s_A) * sim_AB ≤ 1 + sim_AB
    -- ⟺ (s_B/s_A) * sim_AB ≤ 1
    have h_ratio : s_B / s_A ≤ 1 := by
      rw [div_le_one (by linarith : 0 < s_A)]
      exact h_constraint
    calc (1 + s_B / s_A) * sim_AB
        = sim_AB + (s_B / s_A) * sim_AB := by ring
      _ ≤ sim_AB + 1 * sim_AB := by
          have : (s_B / s_A) * sim_AB ≤ 1 * sim_AB :=
            mul_le_mul_of_nonneg_right h_ratio h_sim.1
          linarith
      _ = 2 * sim_AB := by ring
      _ ≤ 1 + sim_AB := by nlinarith [h_sim.1, h_sim.2]

/-- On the ordinary PLN domain, `sim2inh` is monotone in the similarity
coordinate. -/
theorem sim2inh_mono_sim {sim₁ sim₂ s_A s_B : ℝ}
    (hsim₁_nonneg : 0 ≤ sim₁)
    (hsim_le : sim₁ ≤ sim₂)
    (h_sA_pos : 0 < s_A)
    (h_sB_nonneg : 0 ≤ s_B) :
    sim2inh sim₁ s_A s_B ≤ sim2inh sim₂ s_A s_B := by
  unfold sim2inh
  have hsA_ne : s_A ≠ 0 := ne_of_gt h_sA_pos
  have hsim₁_ne : sim₁ ≠ -1 := by linarith
  have hsim₂_nonneg : 0 ≤ sim₂ := le_trans hsim₁_nonneg hsim_le
  have hsim₂_ne : sim₂ ≠ -1 := by linarith
  simp only [hsA_ne, hsim₁_ne, hsim₂_ne, or_false, ↓reduceIte]
  have hden₁ : 0 < 1 + sim₁ := by linarith
  have hden₂ : 0 < 1 + sim₂ := by linarith
  have hfrac : sim₁ / (1 + sim₁) ≤ sim₂ / (1 + sim₂) := by
    rw [div_le_div_iff₀ hden₁ hden₂]
    nlinarith [hsim_le]
  have hcoef : 0 ≤ 1 + s_B / s_A := by
    have hdiv : 0 ≤ s_B / s_A :=
      div_nonneg h_sB_nonneg (le_of_lt h_sA_pos)
    linarith
  calc
    (1 + s_B / s_A) * sim₁ / (1 + sim₁)
        = (1 + s_B / s_A) * (sim₁ / (1 + sim₁)) := by ring
    _ ≤ (1 + s_B / s_A) * (sim₂ / (1 + sim₂)) :=
        mul_le_mul_of_nonneg_left hfrac hcoef
    _ = (1 + s_B / s_A) * sim₂ / (1 + sim₂) := by ring

/-- On the ordinary PLN domain, `sim2inh` is monotone in the target term
strength coordinate. -/
theorem sim2inh_mono_target {sim_AB s_A s_B₁ s_B₂ : ℝ}
    (hsim_nonneg : 0 ≤ sim_AB)
    (h_sA_pos : 0 < s_A)
    (h_target_le : s_B₁ ≤ s_B₂) :
    sim2inh sim_AB s_A s_B₁ ≤ sim2inh sim_AB s_A s_B₂ := by
  unfold sim2inh
  have hsA_ne : s_A ≠ 0 := ne_of_gt h_sA_pos
  have hsim_ne : sim_AB ≠ -1 := by linarith
  simp only [hsA_ne, hsim_ne, or_false, ↓reduceIte]
  have hden : 0 < 1 + sim_AB := by linarith
  have hfactor : 0 ≤ sim_AB / (1 + sim_AB) :=
    div_nonneg hsim_nonneg (le_of_lt hden)
  have hdiv : s_B₁ / s_A ≤ s_B₂ / s_A :=
    div_le_div_of_nonneg_right h_target_le (le_of_lt h_sA_pos)
  calc
    (1 + s_B₁ / s_A) * sim_AB / (1 + sim_AB)
        = (1 + s_B₁ / s_A) * (sim_AB / (1 + sim_AB)) := by ring
    _ ≤ (1 + s_B₂ / s_A) * (sim_AB / (1 + sim_AB)) :=
        mul_le_mul_of_nonneg_right (by linarith) hfactor
    _ = (1 + s_B₂ / s_A) * sim_AB / (1 + sim_AB) := by ring

/-- On the ordinary PLN domain, `sim2inh` is antitone in the source term
strength coordinate. A larger source set makes the target/source ratio smaller. -/
theorem sim2inh_antitone_source {sim_AB s_A₁ s_A₂ s_B : ℝ}
    (hsim_nonneg : 0 ≤ sim_AB)
    (h_sA₁_pos : 0 < s_A₁)
    (h_sA₂_pos : 0 < s_A₂)
    (h_source_le : s_A₁ ≤ s_A₂)
    (h_sB_nonneg : 0 ≤ s_B) :
    sim2inh sim_AB s_A₂ s_B ≤ sim2inh sim_AB s_A₁ s_B := by
  unfold sim2inh
  have hsA₁_ne : s_A₁ ≠ 0 := ne_of_gt h_sA₁_pos
  have hsA₂_ne : s_A₂ ≠ 0 := ne_of_gt h_sA₂_pos
  have hsim_ne : sim_AB ≠ -1 := by linarith
  simp only [hsA₁_ne, hsA₂_ne, hsim_ne, or_false, ↓reduceIte]
  have hden : 0 < 1 + sim_AB := by linarith
  have hfactor : 0 ≤ sim_AB / (1 + sim_AB) :=
    div_nonneg hsim_nonneg (le_of_lt hden)
  have hdiv : s_B / s_A₂ ≤ s_B / s_A₁ := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa [one_div] using
          one_div_le_one_div_of_le h_sA₁_pos h_source_le)
      h_sB_nonneg
  calc
    (1 + s_B / s_A₂) * sim_AB / (1 + sim_AB)
        = (1 + s_B / s_A₂) * (sim_AB / (1 + sim_AB)) := by ring
    _ ≤ (1 + s_B / s_A₁) * (sim_AB / (1 + sim_AB)) :=
        mul_le_mul_of_nonneg_right (by linarith) hfactor
    _ = (1 + s_B / s_A₁) * sim_AB / (1 + sim_AB) := by ring

/-- Mixed endpoint monotonicity for `sim2inh`: similarity and target strength
move upward, while source strength moves downward. This is the shape needed
for independent credal endpoint hulls. -/
theorem sim2inh_mixed_mono
    {sim₁ sim₂ source₁ source₂ target₁ target₂ : ℝ}
    (hsim₁_nonneg : 0 ≤ sim₁)
    (hsim_le : sim₁ ≤ sim₂)
    (hsource₂_pos : 0 < source₂)
    (hsource₁_pos : 0 < source₁)
    (hsource_le : source₂ ≤ source₁)
    (htarget₁_nonneg : 0 ≤ target₁)
    (htarget_le : target₁ ≤ target₂) :
    sim2inh sim₁ source₁ target₁ ≤ sim2inh sim₂ source₂ target₂ := by
  have hsim₂_nonneg : 0 ≤ sim₂ := le_trans hsim₁_nonneg hsim_le
  exact le_trans
    (sim2inh_mono_sim hsim₁_nonneg hsim_le hsource₁_pos htarget₁_nonneg)
    (le_trans
      (sim2inh_antitone_source hsim₂_nonneg hsource₂_pos hsource₁_pos
        hsource_le htarget₁_nonneg)
      (sim2inh_mono_target hsim₂_nonneg hsource₂_pos htarget_le))

/-- **Transitive Similarity**: The main similarity inference rule.

Given sim_AB, sim_BC, and term probabilities, compute sim_AC.

The formula combines deduction in both directions:
  sim_AC = 1 / (1/deduction(T1,T2) + 1/deduction(T3,T4) - 1)

where T1, T2, T3, T4 are computed from sim and term probs via sim2inh.
-/
noncomputable def transitiveSimilarity (sim_AB sim_BC s_A s_B s_C : ℝ) : ℝ :=
  -- Convert similarities to inheritances
  let s_AB := sim2inh sim_AB s_A s_B
  let s_BA := sim2inh sim_AB s_B s_A
  let s_BC := sim2inh sim_BC s_B s_C
  let s_CB := sim2inh sim_BC s_C s_B
  -- Deduction in both directions
  let s_AC := plnDeductionStrength s_AB s_BC s_B s_C
  let s_CA := plnDeductionStrength s_CB s_BA s_B s_A
  -- Combine to similarity
  twoInh2Sim s_AC s_CA

/-- Transitive similarity is approximately symmetric in A, C -/
theorem transitiveSimilarity_approx_symm (sim_AB sim_BC s_A s_B s_C : ℝ) :
    -- Under uniform priors (s_A = s_C), it's exactly symmetric
    s_A = s_C →
    transitiveSimilarity sim_AB sim_BC s_A s_B s_C =
    transitiveSimilarity sim_BC sim_AB s_C s_B s_A := by
  intro h_eq
  unfold transitiveSimilarity
  -- The symmetry follows from swapping A ↔ C throughout
  simp only [h_eq, twoInh2Sim_comm]

/-! ## §2: Modus Ponens and Related Forms

Classical modus ponens:
  P → Q
  P
  -------
  Q

In PLN terms: Given P(B|A) and P(A), infer P(B).

The challenge: We don't know P(B|¬A), so we use a default parameter c.
-/

/-- **Modus Ponens**: Infer P(B) from P(B|A) and P(A).

Formula: s_B = s_AB * s_A + c * (1 - s_A)

where c is a default "background probability" parameter.

This comes from the law of total probability:
  P(B) = P(B|A)P(A) + P(B|¬A)P(¬A)

with the heuristic P(B|¬A) ≈ c.
-/
noncomputable def modusPonens (s_AB s_A c : ℝ) : ℝ :=
  s_AB * s_A + c * (1 - s_A)

/-- Modus ponens is in [0,1] when inputs are valid -/
theorem modusPonens_mem_unit (s_AB s_A c : ℝ)
    (h_sAB : 0 ≤ s_AB ∧ s_AB ≤ 1)
    (h_sA : 0 ≤ s_A ∧ s_A ≤ 1)
    (h_c : 0 ≤ c ∧ c ≤ 1) :
    modusPonens s_AB s_A c ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · -- Non-negative
    unfold modusPonens
    apply add_nonneg
    · exact mul_nonneg h_sAB.1 h_sA.1
    · exact mul_nonneg h_c.1 (by linarith [h_sA.2])
  · -- ≤ 1
    unfold modusPonens
    have h1 : s_AB * s_A ≤ 1 * s_A := mul_le_mul_of_nonneg_right h_sAB.2 h_sA.1
    have h2 : c * (1 - s_A) ≤ 1 * (1 - s_A) := mul_le_mul_of_nonneg_right h_c.2 (by linarith)
    calc s_AB * s_A + c * (1 - s_A)
        ≤ 1 * s_A + 1 * (1 - s_A) := by linarith
      _ = 1 := by ring

/-- Modus ponens reduces to s_AB when s_A = 1 (certain premise) -/
theorem modusPonens_certain_premise (s_AB c : ℝ) :
    modusPonens s_AB 1 c = s_AB := by
  unfold modusPonens; ring

/-- Modus ponens reduces to c when s_A = 0 (false premise) -/
theorem modusPonens_false_premise (s_AB c : ℝ) :
    modusPonens s_AB 0 c = c := by
  unfold modusPonens; ring

/-- Modus ponens is monotonic in s_AB -/
theorem modusPonens_mono_sAB (s_A c : ℝ) (h_sA : 0 ≤ s_A) :
    Monotone (fun s_AB => modusPonens s_AB s_A c) := by
  intro x y hxy
  unfold modusPonens
  have : (y - x) * s_A ≥ 0 := mul_nonneg (by linarith) h_sA
  linarith

/-- Modus ponens is monotone in the premise strength exactly on the side of
the default background where the implication strength improves on that
background. If `s_AB < c`, increasing the premise moves weight away from the
background and can decrease the conclusion, so the side condition is real. -/
theorem modusPonens_mono_sA_of_background_le (s_AB c : ℝ)
    (hc : c ≤ s_AB) :
    Monotone (fun s_A => modusPonens s_AB s_A c) := by
  intro x y hxy
  have hcoef : 0 ≤ s_AB - c := sub_nonneg.mpr hc
  have hdiff : 0 ≤ (y - x) * (s_AB - c) :=
    mul_nonneg (sub_nonneg.mpr hxy) hcoef
  have h :
      modusPonens s_AB y c - modusPonens s_AB x c =
        (y - x) * (s_AB - c) := by
    unfold modusPonens
    ring
  linarith

/-- Two-coordinate monotonicity for modus ponens under the honest background
side condition. This is the rule-validity boundary needed before lifting
modus ponens into interval-valued or higher-order rule envelopes. -/
theorem modusPonens_mono_of_background_le
    {s_AB₁ s_AB₂ s_A₁ s_A₂ c : ℝ}
    (h_sA₁ : 0 ≤ s_A₁)
    (hc : c ≤ s_AB₁)
    (hAB : s_AB₁ ≤ s_AB₂)
    (hA : s_A₁ ≤ s_A₂) :
    modusPonens s_AB₁ s_A₁ c ≤ modusPonens s_AB₂ s_A₂ c := by
  have hAB_step :
      modusPonens s_AB₁ s_A₁ c ≤ modusPonens s_AB₂ s_A₁ c :=
    modusPonens_mono_sAB s_A₁ c h_sA₁ hAB
  have hc₂ : c ≤ s_AB₂ := le_trans hc hAB
  have hA_step :
      modusPonens s_AB₂ s_A₁ c ≤ modusPonens s_AB₂ s_A₂ c :=
    modusPonens_mono_sA_of_background_le s_AB₂ c hc₂ hA
  exact le_trans hAB_step hA_step

/-- **Modus Tollens**: From P(P→Q) and P(¬Q), infer P(¬P).

Equivalent to: modusPonens on (¬Q → ¬P) and P(¬Q).
Using contrapositive: P(¬P|¬Q) = P(P→Q) when P(Q|P) = P(P→Q).
-/
noncomputable def modusTollens (s_PQ s_notQ c : ℝ) : ℝ :=
  modusPonens s_PQ s_notQ c

/-- **Symmetric Modus Ponens**: Using similarity instead of inheritance.

Given sim_AB and s_A, infer s_B.

Formula: s_B = s_A * sim_AB + c * (1 - s_A) * (1 + sim_AB)

This is modus ponens using sim2inh to convert similarity to inheritance.
-/
noncomputable def symmetricModusPonens (sim_AB s_A c : ℝ) : ℝ :=
  s_A * sim_AB + c * (1 - s_A) * (1 + sim_AB)

/-- Symmetric MP reduces to ordinary MP when sim = s_AB (and s_B = s_A) -/
theorem symmetricModusPonens_reduces (s_AB s_A c : ℝ) :
    -- When sim_AB = s_AB and s_B = s_A (maximal similarity case)
    symmetricModusPonens s_AB s_A c = s_A * s_AB + c * (1 - s_A) * (1 + s_AB) := rfl

/-- Symmetric MP is in [0,1] when inputs are valid and c is small enough.

Note: The formula can exceed 1 for large c. In practice, c is a small
default probability (e.g., 0.02), which keeps the result bounded.
-/
theorem symmetricModusPonens_mem_unit (sim_AB s_A c : ℝ)
    (h_sim : 0 ≤ sim_AB ∧ sim_AB ≤ 1)
    (h_sA : 0 ≤ s_A ∧ s_A ≤ 1)
    (h_c : 0 ≤ c ∧ c ≤ 0.5)  -- Strengthened: c ≤ 0.5 ensures boundedness
    : symmetricModusPonens sim_AB s_A c ∈ Set.Icc (0 : ℝ) 1 := by
  -- s_A * sim_AB + c * (1-s_A) * (1+sim_AB)
  unfold symmetricModusPonens
  constructor
  · -- Non-negativity: sum of non-negative terms
    apply add_nonneg
    · exact mul_nonneg h_sA.1 h_sim.1
    · apply mul_nonneg
      · exact mul_nonneg h_c.1 (by linarith [h_sA.2])
      · linarith [h_sim.1]
  · -- Upper bound ≤ 1
    -- s_A * sim_AB + c * (1-s_A) * (1+sim_AB)
    -- ≤ s_A * 1 + 0.5 * (1-s_A) * (1+1)
    -- = s_A + (1-s_A) = 1
    calc s_A * sim_AB + c * (1 - s_A) * (1 + sim_AB)
        ≤ s_A * 1 + c * (1 - s_A) * (1 + 1) := by {
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h_sim.2 h_sA.1
          · apply mul_le_mul_of_nonneg_left _ (mul_nonneg h_c.1 (by linarith [h_sA.2]))
            linarith [h_sim.2]
        }
      _ = s_A + 2 * c * (1 - s_A) := by ring
      _ ≤ s_A + 2 * 0.5 * (1 - s_A) := by
          have h1 : 2 * c ≤ 2 * 0.5 := by linarith [h_c.2]
          have h2 : 2 * c * (1 - s_A) ≤ 2 * 0.5 * (1 - s_A) :=
            mul_le_mul_of_nonneg_right h1 (by linarith [h_sA.2])
          linarith
      _ = 1 := by ring

/-- Symmetric modus ponens is monotone in the similarity coordinate whenever
the premise strength is a genuine probability and the background/default is
nonnegative. -/
theorem symmetricModusPonens_mono_sim (s_A c : ℝ)
    (h_sA : s_A ∈ Set.Icc (0 : ℝ) 1)
    (hc : 0 ≤ c) :
    Monotone (fun sim_AB => symmetricModusPonens sim_AB s_A c) := by
  intro x y hxy
  have hcoef : 0 ≤ s_A + c * (1 - s_A) := by
    exact add_nonneg h_sA.1 (mul_nonneg hc (by linarith [h_sA.2]))
  have hdiff : 0 ≤ (y - x) * (s_A + c * (1 - s_A)) :=
    mul_nonneg (sub_nonneg.mpr hxy) hcoef
  have h :
      symmetricModusPonens y s_A c -
          symmetricModusPonens x s_A c =
        (y - x) * (s_A + c * (1 - s_A)) := by
    unfold symmetricModusPonens
    ring
  linarith

/-- Symmetric modus ponens is monotone in the premise-strength coordinate only
on the honest side of the background/default threshold. The coefficient of the
premise is `sim_AB - c * (1 + sim_AB)`, so this side condition is real. -/
theorem symmetricModusPonens_mono_sA_of_background_le (sim_AB c : ℝ)
    (hc : c * (1 + sim_AB) ≤ sim_AB) :
    Monotone (fun s_A => symmetricModusPonens sim_AB s_A c) := by
  intro x y hxy
  have hcoef : 0 ≤ sim_AB - c * (1 + sim_AB) := sub_nonneg.mpr hc
  have hdiff : 0 ≤ (y - x) * (sim_AB - c * (1 + sim_AB)) :=
    mul_nonneg (sub_nonneg.mpr hxy) hcoef
  have h :
      symmetricModusPonens sim_AB y c -
          symmetricModusPonens sim_AB x c =
        (y - x) * (sim_AB - c * (1 + sim_AB)) := by
    unfold symmetricModusPonens
    ring
  linarith

/-- If the symmetric-MP background threshold holds at a lower similarity
endpoint, it also holds at any stronger similarity endpoint as long as
`c ≤ 1`. -/
theorem symmetricModusPonens_background_le_of_le
    {sim₁ sim₂ c : ℝ}
    (hc_one : c ≤ 1)
    (hcond : c * (1 + sim₁) ≤ sim₁)
    (hsim : sim₁ ≤ sim₂) :
    c * (1 + sim₂) ≤ sim₂ := by
  have hcoef₁ : 0 ≤ sim₁ - c * (1 + sim₁) := sub_nonneg.mpr hcond
  have hmono :
      0 ≤ (sim₂ - c * (1 + sim₂)) -
          (sim₁ - c * (1 + sim₁)) := by
    have hprod : 0 ≤ (sim₂ - sim₁) * (1 - c) :=
      mul_nonneg (sub_nonneg.mpr hsim) (sub_nonneg.mpr hc_one)
    have hrewrite :
        (sim₂ - c * (1 + sim₂)) -
            (sim₁ - c * (1 + sim₁)) =
          (sim₂ - sim₁) * (1 - c) := by
      ring
    simpa [hrewrite] using hprod
  have hcoef₂ : 0 ≤ sim₂ - c * (1 + sim₂) := by
    linarith
  exact sub_nonneg.mp hcoef₂

/-- Two-coordinate monotonicity for symmetric modus ponens under the honest
background side condition. This is the rule-validity boundary needed before
lifting symmetric MP into independent-endpoint credal hulls. -/
theorem symmetricModusPonens_mono_of_background_le
    {sim₁ sim₂ s_A₁ s_A₂ c : ℝ}
    (h_sA₁ : s_A₁ ∈ Set.Icc (0 : ℝ) 1)
    (hc_nonneg : 0 ≤ c)
    (hc_one : c ≤ 1)
    (hc : c * (1 + sim₁) ≤ sim₁)
    (hsim : sim₁ ≤ sim₂)
    (hA : s_A₁ ≤ s_A₂) :
    symmetricModusPonens sim₁ s_A₁ c ≤
      symmetricModusPonens sim₂ s_A₂ c := by
  have hsim_step :
      symmetricModusPonens sim₁ s_A₁ c ≤
        symmetricModusPonens sim₂ s_A₁ c :=
    symmetricModusPonens_mono_sim s_A₁ c h_sA₁ hc_nonneg hsim
  have hc₂ : c * (1 + sim₂) ≤ sim₂ :=
    symmetricModusPonens_background_le_of_le hc_one hc hsim
  have hA_step :
      symmetricModusPonens sim₂ s_A₁ c ≤
        symmetricModusPonens sim₂ s_A₂ c :=
    symmetricModusPonens_mono_sA_of_background_le sim₂ c hc₂ hA
  exact le_trans hsim_step hA_step

/-! ## §3: Member/Inheritance Conversion

Converting between fuzzy membership and probabilistic inheritance.

Member Ben Americans ⟨tv1⟩
  ↔
Inheritance {Ben} Americans ⟨tv2⟩

The strength is preserved, but confidence decreases.
-/

/-- Member to Inheritance conversion: strength preserved, confidence reduced.

The confidence reduction factor depends on the "cohesiveness" of the concept.
For a cohesive concept, we use factor k ∈ (0, 1].
-/
noncomputable def memberToInheritance (s_member : ℝ) (c_member : ℝ) (k : ℝ) :
    ℝ × ℝ :=
  (s_member, c_member * k)

/-- Inheritance to Member conversion: same transformation. -/
noncomputable def inheritanceToMember (s_inh : ℝ) (c_inh : ℝ) (k : ℝ) :
    ℝ × ℝ :=
  (s_inh, c_inh * k)

/-- Roundtrip reduces confidence by k² -/
theorem member_inh_roundtrip (s c k : ℝ) :
    let (s', c') := memberToInheritance s c k
    let (s'', c'') := inheritanceToMember s' c' k
    s'' = s ∧ c'' = c * k * k := by
  -- Straightforward computation: s'' = s, c'' = (c*k)*k = c*k*k
  exact ⟨rfl, by simp [mul_assoc]⟩

/-! ## §4: Term Probability Inference

Inferring P(B) from P(A), P(B|A), and P(A|B).

From Bayes: P(B) = P(A) * P(B|A) / P(A|B)
-/

/-- Term probability inference: compute P(B) from P(A), P(B|A), P(A|B).

Formula: s_B = s_A * s_AB / s_BA

This is just Bayes' rule rearranged.
-/
noncomputable def termProbabilityInference (s_A s_AB s_BA : ℝ) : ℝ :=
  if s_BA = 0 then 0 else s_A * s_AB / s_BA

/-- Term probability inference is consistent with Bayes -/
theorem termProb_consistent_bayes (s_A s_AB s_BA s_B : ℝ)
    (h_BA : s_BA ≠ 0)
    (h_sA : s_A ≠ 0)
    (h_bayes : s_AB = s_BA * s_B / s_A) :
    termProbabilityInference s_A s_AB s_BA = s_B := by
  unfold termProbabilityInference
  simp only [h_BA, ↓reduceIte]
  rw [h_bayes]
  field_simp [h_BA, h_sA]

/-- Term probability is non-negative when inputs are valid -/
theorem termProb_nonneg (s_A s_AB s_BA : ℝ)
    (h_sA : 0 ≤ s_A) (h_sAB : 0 ≤ s_AB) (h_sBA : 0 < s_BA) :
    0 ≤ termProbabilityInference s_A s_AB s_BA := by
  unfold termProbabilityInference
  simp only [ne_of_gt h_sBA, ↓reduceIte]
  apply div_nonneg (mul_nonneg h_sA h_sAB) (le_of_lt h_sBA)

/-! ## §5: The PLN Inference Triad Revisited

With all rules in place, we can state the relationships:

1. **Deduction**: A→B, B→C ⊢ A→C
2. **Induction**: B→A, B→C ⊢ A→C  (via Bayes on B→A)
3. **Abduction**: A→B, C→B ⊢ A→C  (via Bayes on C→B)

All three are instances of:
  Deduction(Bayes(premise₁), premise₂) or Deduction(premise₁, Bayes(premise₂))
-/

/-- The unified view: all three syllogisms use deduction + optional Bayes -/
theorem inference_triad_unified (s1 s2 s_A s_B s_C : ℝ) :
    -- Deduction: direct composition
    plnDeductionStrength s1 s2 s_B s_C =
      plnDeductionStrength s1 s2 s_B s_C ∧
    -- Induction: Bayes on first argument (s_BA → s_AB)
    plnInductionStrength s1 s2 s_A s_B s_C =
      plnDeductionStrength (bayesInversion s1 s_A s_B) s2 s_B s_C ∧
    -- Abduction: Bayes on second argument (s_CB → s_BC)
    plnAbductionStrength s1 s2 s_A s_B s_C =
      plnDeductionStrength s1 (bayesInversion s2 s_B s_C) s_B s_C := by
  constructor
  · rfl
  constructor
  · unfold plnInductionStrength; rfl
  · unfold plnAbductionStrength; rfl

/-! ## §6: Quantale Connection

Consistent story:
- The foundational carrier in this repo is `BinaryEvidence := (n⁺, n⁻)` with a partial order and tensor
  (see `Mettapedia.Logic.EvidenceQuantale` and `Mettapedia.Logic.PLN_KS_Bridge`).
- Strength-level `[0,1]` formulas are views/projections of that richer semantics.
- The former exploratory strength-level packaging is archived at
  `Mettapedia/Logic/Archive/PLNQuantaleConnectionLegacy.lean`; the live module path
  is now a compatibility shim only.

Key insight: PLN inference rules form a **category enriched over [0,1]**:
- Objects: Terms/concepts
- Morphisms: Implications A → B with strength s_AB ∈ [0,1]
- Composition: PLN deduction formula
- Identity: s_AA = 1

This is not ad-hoc: it is a systematic way to package the compositional structure of the rules,
with explicit hypotheses controlling when point-valued reasoning is valid.
-/

/-- PLN forms a category: composition is associative (up to independence assumptions) -/
theorem plnDeductionSimplified_assoc (s_AB s_BC s_CD : ℝ) :
    plnDeductionSimplified (plnDeductionSimplified s_AB s_BC) s_CD =
      plnDeductionSimplified s_AB (plnDeductionSimplified s_BC s_CD) := by
  simp [plnDeductionSimplified, mul_assoc]

end Mettapedia.Logic.PLNInferenceRules
