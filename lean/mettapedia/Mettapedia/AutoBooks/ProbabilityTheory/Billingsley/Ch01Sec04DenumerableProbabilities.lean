/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.BorelCantelli

/-!
# Billingsley Chapter 1, Section 4: Denumerable Probabilities

This file formalizes Section 4 of Billingsley's "Probability and Measure" (3rd Edition),
which covers probability concepts for infinite sequences of events.

## Main concepts

* Conditional probability
* Chain rule
* Limit sets (limsup, liminf)
* Independence of events
* Borel-Cantelli lemmas

## Notes

Many results in this section are already in mathlib:
- `MeasureTheory.Measure.cond` for conditional probability
- `Filter.limsup` and `Filter.liminf` for limit sets
- `ProbabilityTheory.iIndepSet` for independence
- `MeasureTheory.measure_limsup_atTop_eq_zero` for first Borel-Cantelli
- `ProbabilityTheory.measure_limsup_eq_one` for second Borel-Cantelli

We present the results following Billingsley's exposition for pedagogical clarity.

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 4][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Mettapedia.AutoBooks.Billingsley.Ch01Sec04

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-! ## Conditional Probability

Formula (4.1): P(B|A) = P(A ∩ B) / P(A) for P(A) > 0.

In mathlib, conditional probability is defined via `ProbabilityTheory.cond`.
-/

/-- Billingsley's conditional probability formula (4.1).
In mathlib, `μ[B|A] = (μ A)⁻¹ * μ (A ∩ B)`.
See `ProbabilityTheory.cond_apply` for the mathlib statement. -/
theorem condProb_eq_inter_div (A B : Set Ω) (hA_meas : MeasurableSet A) :
    μ[B|A] = (μ A)⁻¹ * μ (A ∩ B) :=
  cond_apply hA_meas μ B

/-! ## Limit Sets

Definitions (4.4) and (4.5):
- lim sup Aₙ = ⋂ₙ ⋃_{k≥n} Aₖ (ω lies in infinitely many Aₙ)
- lim inf Aₙ = ⋃ₙ ⋂_{k≥n} Aₖ (ω lies in all but finitely many Aₙ)

These are `Filter.limsup` and `Filter.liminf` in mathlib.
-/

/-- ω lies in lim sup Aₙ iff ω lies in infinitely many Aₙ.
This is Billingsley's characterization of (4.4). -/
theorem mem_limsup_iff_frequently (A : ℕ → Set Ω) (ω : Ω) :
    ω ∈ Filter.limsup A atTop ↔ ∃ᶠ n in atTop, ω ∈ A n :=
  Filter.mem_limsup_iff_frequently_mem

/-- ω lies in lim inf Aₙ iff ω lies in all but finitely many Aₙ.
This is Billingsley's characterization of (4.5). -/
theorem mem_liminf_iff_eventually (A : ℕ → Set Ω) (ω : Ω) :
    ω ∈ Filter.liminf A atTop ↔ ∀ᶠ n in atTop, ω ∈ A n :=
  Filter.mem_liminf_iff_eventually_mem

/-- lim inf ⊆ lim sup always holds.
Billingsley notes: if ω lies in all but finitely many Aₙ,
then of course it lies in infinitely many of them. -/
theorem liminf_subset_limsup (A : ℕ → Set Ω) :
    Filter.liminf A atTop ⊆ Filter.limsup A atTop :=
  Filter.liminf_le_limsup

/-! ## Facts about Sets of Measure 0 and 1 -/

/-- Countable union of null sets is null (Billingsley p.52).
"If A₁, A₂, ... are sets of probability 0, so is ⋃ₙ Aₙ." -/
theorem measure_iUnion_null' {ι : Type*} [Countable ι] {A : ι → Set Ω}
    (hA : ∀ i, μ (A i) = 0) : μ (⋃ i, A i) = 0 :=
  measure_iUnion_null_iff.mpr hA

/-- Countable intersection of measure-1 sets has measure 1 (Billingsley p.52).
"If A₁, A₂, ... are sets of probability 1, so is ⋂ₙ Aₙ." -/
theorem measure_iInter_full {ι : Type*} [Countable ι] {A : ι → Set Ω}
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, μ (A i) = 1) : μ (⋂ i, A i) = 1 := by
  -- Complement: μ((⋂ᵢ Aᵢ)ᶜ) = μ(⋃ᵢ Aᵢᶜ)
  have h_compl : (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ := Set.compl_iInter _
  -- Each Aᵢᶜ has measure 0
  have hAc : ∀ i, μ (A i)ᶜ = 0 := by
    intro i
    rw [prob_compl_eq_one_sub (hA_meas i), hA i]
    simp
  -- Union of null sets is null
  have h_union_null : μ (⋃ i, (A i)ᶜ) = 0 := measure_iUnion_null' μ hAc
  -- Therefore complement of intersection is null
  rw [← h_compl] at h_union_null
  -- μ(⋂ᵢ Aᵢ) = 1 - μ((⋂ᵢ Aᵢ)ᶜ) = 1 - 0 = 1
  have h_meas : MeasurableSet (⋂ i, A i) := MeasurableSet.iInter hA_meas
  have h1 : μ (⋂ i, A i) + μ (⋂ i, A i)ᶜ = 1 := by
    rw [← measure_union disjoint_compl_right h_meas.compl, Set.union_compl_self,
        measure_univ]
  rw [h_union_null] at h1
  simp at h1
  exact h1

/-! ## Independence

Two events A, B are independent if P(A ∩ B) = P(A) · P(B).

In mathlib, this is handled by `ProbabilityTheory.IndepSet`.
-/

/-- Two events are independent if P(A ∩ B) = P(A) · P(B).
This is Billingsley's definition following (4.8). -/
def AreIndependent (A B : Set Ω) : Prop :=
  μ (A ∩ B) = μ A * μ B

/-- Independence is symmetric. -/
theorem AreIndependent.symm {A B : Set Ω} (h : AreIndependent μ A B) :
    AreIndependent μ B A := by
  unfold AreIndependent at *
  rw [Set.inter_comm, mul_comm]
  exact h

/-- If A and B are independent, then so are A and Bᶜ.
This is Billingsley's remark below (4.8).

The proof uses: μ(A ∩ Bᶜ) = μ(A) - μ(A ∩ B) = μ(A) - μ(A)μ(B) = μ(A)(1 - μ(B)) = μ(A)μ(Bᶜ).
ENNReal subtraction arithmetic. -/
theorem indep_compl_right {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : AreIndependent μ A B) : AreIndependent μ A Bᶜ := by
  unfold AreIndependent at *
  -- Key: A ∩ Bᶜ = A \ (A ∩ B)
  have h_set : A ∩ Bᶜ = A \ (A ∩ B) := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_diff]
    tauto
  rw [h_set]
  -- Use measure_diff: μ(A \ (A ∩ B)) = μ(A) - μ(A ∩ B)
  have h_subset : A ∩ B ⊆ A := inter_subset_left
  have h_meas : MeasurableSet (A ∩ B) := hA.inter hB
  have h_fin : μ (A ∩ B) ≠ ⊤ := measure_ne_top μ (A ∩ B)
  rw [measure_diff h_subset h_meas.nullMeasurableSet h_fin]
  -- Use independence: μ(A ∩ B) = μ(A) * μ(B)
  rw [h]
  -- ENNReal: μ(A) - μ(A) * μ(B) = μ(A) * (1 - μ(B)) = μ(A) * μ(Bᶜ)
  rw [prob_compl_eq_one_sub hB]
  -- Need: μ(A) - μ(A) * μ(B) = μ(A) * (1 - μ(B))
  have hA_ne : μ A ≠ ⊤ := measure_ne_top μ A
  have hB_ne : μ B ≠ ⊤ := measure_ne_top μ B
  have hB_le : μ B ≤ 1 := prob_le_one
  -- Use: a - a * b = a * (1 - b) when b ≤ 1 and a ≠ ⊤
  rw [ENNReal.mul_sub (fun _ _ => hA_ne), mul_one]

/-! ## Borel-Cantelli Lemmas -/

/-- First Borel-Cantelli Lemma (Billingsley Theorem 4.3):
If Σₙ P(Aₙ) < ∞, then P(lim sup Aₙ) = 0.

In other words: if the sum of probabilities is finite, then almost surely
only finitely many of the events occur.

This is `MeasureTheory.measure_limsup_atTop_eq_zero` in mathlib. -/
theorem first_borel_cantelli {A : ℕ → Set Ω}
    (hA_summable : ∑' n, μ (A n) ≠ ⊤) :
    μ (Filter.limsup A atTop) = 0 :=
  measure_limsup_atTop_eq_zero hA_summable

/-- Second Borel-Cantelli Lemma (Billingsley Theorem 4.4):
If the Aₙ are independent and Σₙ P(Aₙ) = ∞, then P(lim sup Aₙ) = 1.

In other words: if the events are independent and the sum of probabilities
diverges, then almost surely infinitely many of the events occur.

This is `ProbabilityTheory.measure_limsup_eq_one` in mathlib. -/
theorem second_borel_cantelli {A : ℕ → Set Ω}
    (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_indep : iIndepSet A μ)
    (hA_diverge : ∑' n, μ (A n) = ⊤) :
    μ (Filter.limsup A atTop) = 1 :=
  measure_limsup_eq_one hA_meas hA_indep hA_diverge

/-! ## Example 4.1: Run lengths in binary expansion

Example 4.1 concerns the run lengths lₙ(ω) of 0's starting at position n
in the dyadic expansion. This uses the machinery from Section 1 and is
developed there via `dyadicDigit`.

Key results:
- P[lₙ(ω) ≥ r] = 2⁻ʳ (formula 4.7)
- Application of Borel-Cantelli to run lengths
-/

/-! ## Zero-One Law

Kolmogorov's Zero-One Law states that any event in the tail σ-algebra
has probability 0 or 1. This will be developed in Section 22 where
the tail σ-algebra is properly defined.
-/

end Mettapedia.AutoBooks.Billingsley.Ch01Sec04

end
