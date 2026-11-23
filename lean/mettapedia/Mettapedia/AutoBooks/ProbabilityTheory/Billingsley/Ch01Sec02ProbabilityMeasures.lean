/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Billingsley Chapter 1, Section 2: Probability Measures

This file formalizes Section 2 of Billingsley's "Probability and Measure" (3rd Edition),
which introduces the fundamental concepts of probability spaces, σ-algebras, and
probability measures.

## Main concepts

* Sample spaces (Ω)
* Fields and σ-fields (algebras and σ-algebras)
* Probability measures
* Lebesgue measure on the unit interval

## Notes

Much of the foundational material in this section is provided by mathlib's
`MeasureTheory` library. We focus on Billingsley-specific examples and
pedagogical connections.

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 2][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Mettapedia.AutoBooks.Billingsley.Ch01Sec02

/-! ## Sample Spaces

A sample space Ω consists of all possible outcomes ω of an experiment.
In Lean/mathlib, this is simply a type.
-/

/-- Example 2.1: The sample space for n coin tosses is `Fin 2 → Fin n`. -/
example (n : ℕ) : Type := Fin n → Fin 2

/-- Example: The sample space for infinitely many coin tosses. -/
example : Type := ℕ → Fin 2

/-- Example: The sample space for particle position is ℝ³. -/
example : Type := Fin 3 → ℝ

/-! ## Classes of Sets

Billingsley introduces fields (algebras) and σ-fields (σ-algebras) as classes of
sets closed under certain operations.
-/

/-- The Borel σ-field on ℝ is the smallest σ-field containing all open sets.
This is `borel ℝ` in mathlib.

Note: A field (algebra) is closed under complement and finite union.
A σ-field (σ-algebra) is closed under complement and countable union.
In mathlib, this is captured by `MeasurableSpace`. -/
example : MeasurableSpace ℝ := borel ℝ

/-- For the unit interval (0,1], we use the Borel σ-field restricted to this set. -/
def unitIntervalSigmaAlgebra : MeasurableSpace (Set.Ioc (0 : ℝ) 1) :=
  Subtype.instMeasurableSpace

/-! ## Definition of Probability Measure

A probability measure P on (Ω, F) satisfies:
1. P(Ω) = 1
2. P is countably additive

In mathlib, this is `ProbabilityMeasure` or equivalently `IsProbabilityMeasure μ`.
-/

/-- The defining properties of a probability measure.
Billingsley's axioms (2.3)-(2.5) correspond to mathlib's IsProbabilityMeasure. -/
theorem probability_axioms (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [hμ : IsProbabilityMeasure μ] :
    μ Set.univ = 1 ∧
    (∀ s, MeasurableSet s → μ s ≥ 0) ∧
    (∀ (f : ℕ → Set Ω), (∀ n, MeasurableSet (f n)) →
      (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      μ (⋃ n, f n) = ∑' n, μ (f n)) := by
  refine ⟨hμ.measure_univ, ?_, ?_⟩
  · intro s _; exact zero_le
  · intro f hf_meas hf_disj
    exact measure_iUnion hf_disj hf_meas

/-! ## Properties of Probability Measures

The following properties follow from the axioms.
-/

/-- P(∅) = 0. Billingsley's formula (2.6). -/
theorem prob_empty (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) :
    μ ∅ = 0 := measure_empty

/-- Finite additivity: P(A ∪ B) = P(A) + P(B) for disjoint A, B.
Billingsley's formula (2.7). -/
theorem prob_union_disjoint (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : Disjoint A B) :
    μ (A ∪ B) = μ A + μ B := measure_union h hB

/-- Monotonicity: A ⊆ B implies P(A) ≤ P(B).
Billingsley's formula (2.9). -/
theorem prob_mono (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    {A B : Set Ω} (h : A ⊆ B) : μ A ≤ μ B := measure_mono h

/-- P(Aᶜ) = 1 - P(A). Billingsley's formula (2.10). -/
theorem prob_compl (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [hμ : IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    μ Aᶜ = 1 - μ A := by
  have h : μ A + μ Aᶜ = 1 := by
    rw [← measure_union disjoint_compl_right hA.compl, Set.union_compl_self, hμ.measure_univ]
  have hfin : μ A ≠ ⊤ := measure_ne_top μ A
  rw [← h, ENNReal.add_sub_cancel_left hfin]

/-- Subadditivity: P(A ∪ B) ≤ P(A) + P(B).
Billingsley's formula (2.12). -/
theorem prob_union_le (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Set Ω) : μ (A ∪ B) ≤ μ A + μ B := measure_union_le A B

/-- Countable subadditivity (Boole's inequality): P(⋃ᵢ Aᵢ) ≤ Σᵢ P(Aᵢ).
Billingsley's formula (2.13). -/
theorem prob_countable_union_le (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Set Ω) : μ (⋃ n, f n) ≤ ∑' n, μ (f n) := measure_iUnion_le f

/-! ## Continuity of Probability Measures

Probability measures are continuous from below and from above.
-/

/-- Continuity from below: if Aₙ ↑ A, then P(Aₙ) → P(A).
Billingsley's Theorem 2.1(i). -/
theorem continuity_from_below (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → Set Ω} (hf_mono : Monotone f) :
    Filter.Tendsto (fun n => μ (f n)) Filter.atTop (nhds (μ (⋃ n, f n))) :=
  tendsto_measure_iUnion_atTop hf_mono

/-- Continuity from above: if Aₙ ↓ A and P(A₁) < ∞, then P(Aₙ) → P(A).
Billingsley's Theorem 2.1(ii). -/
theorem continuity_from_above (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → Set Ω} (hf_anti : Antitone f) (hf_meas : ∀ n, NullMeasurableSet (f n) μ)
    (hf_fin : μ (f 0) ≠ ⊤) :
    Filter.Tendsto (fun n => μ (f n)) Filter.atTop (nhds (μ (⋂ n, f n))) :=
  tendsto_measure_iInter_atTop hf_meas hf_anti ⟨0, hf_fin⟩

/-! ## Lebesgue Measure on the Unit Interval

Lebesgue measure on (0,1] is the unique probability measure satisfying
P((a,b]) = b - a for all 0 ≤ a < b ≤ 1.
-/

/-- The restriction of Lebesgue measure to (0,1] is a probability measure. -/
theorem lebesgue_unit_isProbability :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  constructor
  simp only [Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

/-- Lebesgue measure of an interval (a,b] is b - a.
This is Billingsley's starting axiom for probability on (0,1]. -/
theorem lebesgue_interval_measure {a b : ℝ} :
    volume (Set.Ioc a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Ioc

/-! ## Example: Product Spaces

For a sequence of experiments, the sample space is the product.
-/

/-- The product σ-algebra on ℕ → Fin 2 (infinite coin tosses).
This is the σ-algebra generated by cylinder sets. -/
example : MeasurableSpace (ℕ → Fin 2) := inferInstance

/-! ## Theorem 2.2: Uniqueness

Two probability measures that agree on a π-system generating the σ-algebra are equal.
-/

/-- Billingsley's Theorem 2.2 (uniqueness): if two finite measures agree on a
π-system that generates the σ-algebra, they are equal on the whole σ-algebra.
This follows from mathlib's `ext_of_generate_finite`. -/
theorem uniqueness_of_measures {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {P : Set (Set Ω)} (h_gen : mΩ = MeasurableSpace.generateFrom P)
    (h_pi : IsPiSystem P) (h_eq : ∀ s ∈ P, μ s = ν s)
    (h_univ : μ Set.univ = ν Set.univ) : μ = ν :=
  ext_of_generate_finite P h_gen h_pi h_eq h_univ

end Mettapedia.AutoBooks.Billingsley.Ch01Sec02

end
