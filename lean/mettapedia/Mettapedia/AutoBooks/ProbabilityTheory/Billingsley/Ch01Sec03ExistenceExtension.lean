/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.MeasureTheory.PiSystem

/-!
# Billingsley Chapter 1, Section 3: Existence and Extension

This file formalizes Section 3 of Billingsley's "Probability and Measure" (3rd Edition),
which covers the extension of probability measures from a field to a σ-field.

## Main results

* The Carathéodory extension theorem (Theorem 3.1)
* Uniqueness of measure extension (Theorem 3.3)
* The π-λ theorem

## Notes

The Carathéodory construction is implemented in mathlib via `MeasureTheory.OuterMeasure`.
We present the key results following Billingsley's exposition.

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 3][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Mettapedia.AutoBooks.Billingsley.Ch01Sec03

/-! ## Outer Measure

The outer measure P*(A) is defined as the infimum of Σ P(Aₙ) over all
coverings of A by sets from the field F₀.
-/

/-- P*(∅) = 0 -/
theorem outerMeasure_empty {α : Type*} (μ : OuterMeasure α) : μ ∅ = 0 := μ.empty

/-- P* is monotone -/
theorem outerMeasure_mono {α : Type*} (μ : OuterMeasure α) {A B : Set α} (h : A ⊆ B) :
    μ A ≤ μ B := μ.mono h

/-- P* is countably subadditive -/
theorem outerMeasure_iUnion_le {α : Type*} (μ : OuterMeasure α) (f : ℕ → Set α) :
    μ (⋃ n, f n) ≤ ∑' n, μ (f n) :=
  measure_iUnion_le f

/-! ## The Extension Theorem

Theorem 3.1 (Carathéodory): A probability measure on a field has a unique
extension to the generated σ-field.

Note: The hypothesis requires P to be *countably* additive on the field F₀
(Billingsley p.37: "the set function P on it must be assumed countably additive").
Finite additivity alone is not sufficient for the extension to work.
-/

/-- Billingsley's Theorem 3.1: Existence of measure extension.
Given a countably additive probability measure P on a field F₀, there exists
a measure Q on σ(F₀) that agrees with P on F₀.

In mathlib, this is handled by the Carathéodory extension via `AddContent.measure`.
The key hypotheses are:
1. F₀ is a field (closed under complement and finite union)
2. P is countably additive on F₀ (not just finitely additive)
3. P(Ω) = 1 (probability measure) -/
theorem extension_theorem_existence {α : Type*}
    (F₀ : Set (Set α)) (hF₀_univ : Set.univ ∈ F₀)
    (hF₀_compl : ∀ A ∈ F₀, Aᶜ ∈ F₀)
    (hF₀_union : ∀ A B, A ∈ F₀ → B ∈ F₀ → A ∪ B ∈ F₀)
    (P : Set α → ℝ≥0∞) (hP_empty : P ∅ = 0)
    (hP_additive : ∀ A B, A ∈ F₀ → B ∈ F₀ → Disjoint A B → P (A ∪ B) = P A + P B)
    (hP_sigma_additive : ∀ f : ℕ → Set α, (∀ n, f n ∈ F₀) →
        (∀ i j, i ≠ j → Disjoint (f i) (f j)) → (⋃ n, f n) ∈ F₀ → P (⋃ n, f n) = ∑' n, P (f n))
    (hP_one : P Set.univ = 1) :
    ∃ (μ : @Measure α (MeasurableSpace.generateFrom F₀)),
      ∀ A, A ∈ F₀ → μ A = P A := by
  classical
  -- Step 1: F₀ is a set algebra (hence ring, hence semiring).
  have hF₀_empty : (∅ : Set α) ∈ F₀ := by
    have := hF₀_compl _ hF₀_univ; simpa using this
  have halg : IsSetAlgebra F₀ := by
    refine ⟨hF₀_empty, ?_, ?_⟩
    · intro s hs; exact hF₀_compl s hs
    · intro s t hs ht; exact hF₀_union s t hs ht
  have hring : IsSetRing F₀ := halg.isSetRing
  have hsemi : IsSetSemiring F₀ := hring.isSetSemiring
  -- Step 2: Build an AddContent from P using binary additivity on the ring.
  let m : AddContent ℝ≥0∞ F₀ :=
    hring.addContent_of_union P hP_empty
      (fun {s t} hs ht hdis => hP_additive s t hs ht hdis)
  -- Step 3: σ-subadditivity from σ-additivity on disjoint sequences with union in F₀.
  have m_sigma_sub : m.IsSigmaSubadditive :=
    isSigmaSubadditive_of_addContent_iUnion_eq_tsum hring
      (fun f hf hunion hdisj =>
        hP_sigma_additive f hf
          (fun i j hij => hdisj hij) hunion)
  -- Step 4: Construct the measure via AddContent.measure.
  letI mα : MeasurableSpace α := MeasurableSpace.generateFrom F₀
  refine ⟨m.measure hsemi le_rfl m_sigma_sub, ?_⟩
  intro A hA
  exact m.measure_eq hsemi rfl m_sigma_sub hA

/-! ## Uniqueness: The π-λ Theorem -/

/-- Billingsley's Theorem 3.3 (uniqueness of extension):
Two probability measures that agree on a π-system generating the σ-algebra
must be equal on the entire σ-algebra. -/
theorem uniqueness_of_extension {α : Type*} [m : MeasurableSpace α]
    {P : Set (Set α)} (hP_pi : IsPiSystem P)
    (hP_gen : m = MeasurableSpace.generateFrom P)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_agree : ∀ s, s ∈ P → μ s = ν s) :
    μ = ν := by
  -- IsProbabilityMeasure → IsZeroOrProbabilityMeasure → IsFiniteMeasure
  apply ext_of_generate_finite P hP_gen hP_pi h_agree
  simp only [IsProbabilityMeasure.measure_univ]

end Mettapedia.AutoBooks.Billingsley.Ch01Sec03

end
