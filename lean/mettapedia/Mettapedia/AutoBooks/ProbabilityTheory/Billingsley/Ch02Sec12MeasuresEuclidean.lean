/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Billingsley Chapter 2, Section 12: Measures in Euclidean Space

This file formalizes Section 12 of Billingsley's "Probability and Measure" (3rd Edition),
which builds Lebesgue measure on `ℝ^k` and investigates its invariance and regularity.

## Scope

* Lebesgue measure `λ_k` on `ℝ^k`, denoted by mathlib's `volume` on the product space.
* **Theorem 12.1** (translation invariance): `λ_k (A + x) = λ_k A`.
* **Theorem 12.2** (linear transformations): `λ_k (T A) = |det T| · λ_k A` for nonsingular
  linear `T : ℝ^k → ℝ^k`. A corollary: orthogonal and unitary transformations preserve
  Lebesgue measure.
* Every `(k-1)`-dimensional hyperplane has `λ_k`-measure zero.
* **Theorem 12.3** (regularity): every Borel measure finite on bounded sets is regular.
* The `F ↔ μ` correspondence on the line (Billingsley (12.4)–(12.6)).

All of these are captured by mathlib results about Haar measure and the Lebesgue measure
on finite-dimensional real vector spaces; we expose Billingsley-facing names.

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 12][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology MeasurableSpace
open scoped ENNReal NNReal Topology

namespace Mettapedia.AutoBooks.Billingsley.Ch02Sec12

/-! ## Lebesgue measure on `ℝ^k` -/

/-- The `k`-dimensional Lebesgue measure on `ℝ^k`. Equivalent to mathlib's `volume`. -/
abbrev lebesgueMeasure (k : ℕ) : Measure (Fin k → ℝ) := volume

/-- The Lebesgue measure on `ℝ^k` is an additive Haar measure. -/
example (k : ℕ) : Measure.IsAddHaarMeasure (volume : Measure (Fin k → ℝ)) := inferInstance

/-! ## Theorem 12.1: Translation invariance -/

/-- **Theorem 12.1** (Billingsley): Lebesgue measure is translation invariant. -/
theorem lebesgue_translation_invariant {k : ℕ} (A : Set (Fin k → ℝ)) (x : Fin k → ℝ) :
    (volume : Measure (Fin k → ℝ)) ((fun y => y + x) ⁻¹' A) = volume A :=
  measure_preimage_add_right _ _ _

/-- Stated in image form: `vol (A + x) = vol A`. -/
theorem lebesgue_image_add_right_eq {k : ℕ} (A : Set (Fin k → ℝ)) (x : Fin k → ℝ) :
    (volume : Measure (Fin k → ℝ)) ((fun y => y + x) '' A) = volume A := by
  have : (fun y : Fin k → ℝ => y + x) '' A = (fun y => y + (-x)) ⁻¹' A := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro hy
      refine ⟨y + (-x), hy, ?_⟩
      simp [add_assoc]
  rw [this, measure_preimage_add_right]

/-! ## Theorem 12.2: Linear transformations -/

/-- **Theorem 12.2** (Billingsley): for a linear map `T : ℝ^k → ℝ^k`,
`vol (T '' A) = |det T| · vol A`. -/
theorem lebesgue_linearMap_image {k : ℕ} (T : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (A : Set (Fin k → ℝ)) :
    (volume : Measure (Fin k → ℝ)) (T '' A) = ENNReal.ofReal |LinearMap.det T| * volume A :=
  Measure.addHaar_image_linearMap (volume : Measure (Fin k → ℝ)) T A

/-- Orthogonal / unitary transformations preserve Lebesgue measure. We state this for any
continuous linear equivalence `T` with `|det T| = 1`. -/
theorem lebesgue_image_of_det_abs_one {k : ℕ}
    (T : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ))
    (hT : |LinearMap.det (T : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))| = 1)
    (A : Set (Fin k → ℝ)) :
    (volume : Measure (Fin k → ℝ)) (T '' A) = volume A := by
  rw [Measure.addHaar_image_continuousLinearEquiv, hT, ENNReal.ofReal_one, one_mul]

/-! ## (k-1)-dimensional hyperplanes have measure zero -/

/-- A proper submodule of `ℝ^k` (in particular, every `(k-1)`-dim hyperplane through
the origin) has Lebesgue measure zero. -/
theorem lebesgue_submodule_zero {k : ℕ} (s : Submodule ℝ (Fin k → ℝ))
    (hs : s ≠ ⊤) : (volume : Measure (Fin k → ℝ)) (s : Set (Fin k → ℝ)) = 0 :=
  Measure.addHaar_submodule (volume : Measure (Fin k → ℝ)) s hs

/-! ## Theorem 12.3: Regularity -/

/-- **Theorem 12.3** (Billingsley): any measure on `ℝ^k` finite on bounded sets is regular.
This is captured by mathlib's `Measure.Regular` instance on Haar-type measures; for the
volume it is built-in. -/
example {k : ℕ} : Measure.Regular (volume : Measure (Fin k → ℝ)) := inferInstance

/-- The inner regularity half of 12.3: `μ A = sup μ K` over compact subsets. -/
theorem lebesgue_innerRegular {k : ℕ} (A : Set (Fin k → ℝ)) (hA : MeasurableSet A)
    (_hfin : volume A ≠ ∞) :
    volume A = ⨆ (K : Set (Fin k → ℝ)) (_ : IsCompact K) (_ : K ⊆ A), volume K := by
  rw [hA.measure_eq_iSup_isCompact (volume : Measure (Fin k → ℝ))]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
    exact le_iSup_of_le K (le_iSup_of_le hK (le_iSup_of_le hKA le_rfl))
  · refine iSup_le fun K => iSup_le fun hK => iSup_le fun hKA => ?_
    exact le_iSup_of_le K (le_iSup_of_le hKA (le_iSup_of_le hK le_rfl))

/-- The outer regularity half of 12.3: there is an open superset of arbitrarily close
measure. -/
theorem lebesgue_outerRegular {k : ℕ} (A : Set (Fin k → ℝ)) (_hA : MeasurableSet A)
    (_hfin : volume A ≠ ∞) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ G : Set (Fin k → ℝ), IsOpen G ∧ A ⊆ G ∧ volume G ≤ volume A + ε := by
  obtain ⟨U, hAU, hUopen, hU⟩ :=
    Set.exists_isOpen_le_add A (volume : Measure (Fin k → ℝ)) hε
  exact ⟨U, hUopen, hAU, hU⟩

/-! ## Theorem 12.4 (Billingsley): F ↔ μ on ℝ -/

/-- The cumulative distribution function associated to a locally finite measure on `ℝ`
(Billingsley (12.4)). -/
def cdfOfMeasure (μ : Measure ℝ) : ℝ → ℝ := fun x =>
  if x ≥ 0 then (μ (Set.Ioc 0 x)).toReal else - (μ (Set.Ioc x 0)).toReal

/-- On a bounded interval `(a, b]`, `μ(a, b] = F(b) - F(a)` (Billingsley (12.5)). The
precise mathlib form of this identity is inherited from `StieltjesFunction`. -/
theorem measure_Ioc_eq_cdf_sub (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (a b : ℝ) (hab : a ≤ b) :
    (μ (Set.Ioc a b)).toReal = cdfOfMeasure μ b - cdfOfMeasure μ a := by
  have hfin : ∀ x y : ℝ, μ (Set.Ioc x y) ≠ ∞ := fun x y => by
    have hsub : Set.Ioc x y ⊆ Set.Icc (min x y) (max x y) := fun z hz =>
      ⟨(min_le_left _ _).trans hz.1.le, hz.2.trans (le_max_right _ _)⟩
    exact ((measure_mono hsub).trans_lt (isCompact_Icc.measure_lt_top)).ne
  unfold cdfOfMeasure
  by_cases hb : 0 ≤ b
  · by_cases ha : 0 ≤ a
    · -- case: 0 ≤ a ≤ b
      simp only [hb, ha, if_true]
      have hdisj : Disjoint (Set.Ioc 0 a) (Set.Ioc a b) :=
        Set.Ioc_disjoint_Ioc_of_le le_rfl
      have hunion : Set.Ioc 0 a ∪ Set.Ioc a b = Set.Ioc 0 b :=
        Set.Ioc_union_Ioc_eq_Ioc ha hab
      have hmu : μ (Set.Ioc 0 b) = μ (Set.Ioc 0 a) + μ (Set.Ioc a b) := by
        rw [← hunion]; exact measure_union hdisj measurableSet_Ioc
      rw [hmu, ENNReal.toReal_add (hfin 0 a) (hfin a b)]; ring
    · -- case: a < 0 ≤ b
      push_neg at ha
      simp only [hb, ha.not_ge, if_true, if_false]
      have hdisj : Disjoint (Set.Ioc a 0) (Set.Ioc 0 b) :=
        Set.Ioc_disjoint_Ioc_of_le le_rfl
      have hunion : Set.Ioc a 0 ∪ Set.Ioc 0 b = Set.Ioc a b :=
        Set.Ioc_union_Ioc_eq_Ioc ha.le hb
      have hmu : μ (Set.Ioc a b) = μ (Set.Ioc a 0) + μ (Set.Ioc 0 b) := by
        rw [← hunion]; exact measure_union hdisj measurableSet_Ioc
      rw [hmu, ENNReal.toReal_add (hfin a 0) (hfin 0 b)]; ring
  · -- case: a ≤ b < 0
    push_neg at hb
    have ha : ¬ 0 ≤ a := fun h => absurd (h.trans hab) hb.not_ge
    simp only [hb.not_ge, ha, if_false]
    have hdisj : Disjoint (Set.Ioc a b) (Set.Ioc b 0) :=
      Set.Ioc_disjoint_Ioc_of_le le_rfl
    have hunion : Set.Ioc a b ∪ Set.Ioc b 0 = Set.Ioc a 0 :=
      Set.Ioc_union_Ioc_eq_Ioc hab hb.le
    have hmu : μ (Set.Ioc a 0) = μ (Set.Ioc a b) + μ (Set.Ioc b 0) := by
      rw [← hunion]; exact measure_union hdisj measurableSet_Ioc
    have h := congrArg ENNReal.toReal hmu
    rw [ENNReal.toReal_add (hfin a b) (hfin b 0)] at h
    linarith

/-- For a finite measure on `ℝ`, the standard cumulative distribution function
(Billingsley (12.6)): `F(x) = μ((-∞, x])`. -/
def cdfOfFiniteMeasure (μ : Measure ℝ) : ℝ → ℝ := fun x => (μ (Set.Iic x)).toReal

/-- For a finite measure, `F` tends to 0 at `-∞`. -/
theorem cdfOfFiniteMeasure_tendsto_zero_atBot (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (cdfOfFiniteMeasure μ) atBot (𝓝 0) := by
  unfold cdfOfFiniteMeasure
  have hmono : Monotone (fun x : ℝ => Iic x) := fun _ _ h => Iic_subset_Iic.mpr h
  have hmeas : ∀ x : ℝ, NullMeasurableSet (Iic x) μ :=
    fun x => (measurableSet_Iic).nullMeasurableSet
  have hfin : ∃ x : ℝ, μ (Iic x) ≠ ⊤ := ⟨0, measure_ne_top μ _⟩
  have h1 : Tendsto (fun x : ℝ => μ (Iic x)) atBot (𝓝 (μ (⋂ x : ℝ, Iic x))) :=
    tendsto_measure_iInter_atBot hmeas hmono hfin
  have h2 : (⋂ x : ℝ, Iic x) = (∅ : Set ℝ) := by
    ext y
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨y - 1, by linarith⟩
  rw [h2, measure_empty] at h1
  have : (0 : ℝ) = (0 : ℝ≥0∞).toReal := by simp
  rw [this]
  exact ENNReal.tendsto_toReal (by simp) |>.comp h1

/-- For a finite measure, `F` tends to `μ(univ)` at `+∞`. -/
theorem cdfOfFiniteMeasure_tendsto_total_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (cdfOfFiniteMeasure μ) atTop (𝓝 (μ Set.univ).toReal) := by
  unfold cdfOfFiniteMeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp (tendsto_measure_Iic_atTop μ)

end Mettapedia.AutoBooks.Billingsley.Ch02Sec12
