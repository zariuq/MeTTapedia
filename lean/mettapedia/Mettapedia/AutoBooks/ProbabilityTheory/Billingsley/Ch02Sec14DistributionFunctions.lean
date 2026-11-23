/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Billingsley Chapter 2, Section 14: Distribution Functions

This file formalizes Section 14 of Billingsley's "Probability and Measure" (3rd Edition).
It develops the one-to-one correspondence between probability measures on `ℝ` and
right-continuous nondecreasing functions `F : ℝ → ℝ` with `lim_{-∞} F = 0` and
`lim_{+∞} F = 1`.

## Scope

* Definition: the distribution function of a random variable `X` / a probability measure
  `μ` on `(ℝ, 𝓑)` via `F(x) = μ(-∞, x]`.
* `F` is right-continuous (Billingsley (14.2) + Theorem 10.2(ii)).
* Countably many discontinuities.
* Limits (Billingsley (14.4)): `lim_{x→-∞} F = 0`, `lim_{x→+∞} F = 1`.
* **Theorem 14.1** (Billingsley): every right-continuous nondecreasing function with the
  two limits is the distribution function of some probability measure.
* Exponential distribution and the Cauchy-functional lack-of-memory property
  (Billingsley (14.6)).

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 14][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology MeasurableSpace
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace Mettapedia.AutoBooks.Billingsley.Ch02Sec14

/-! ## Distribution function of a probability measure -/

/-- **Billingsley (14.2)**: the distribution function `F(x) = μ(-∞, x]` of a probability
measure `μ` on `ℝ`. -/
def distributionFunction (μ : Measure ℝ) : ℝ → ℝ := fun x => (μ (Set.Iic x)).toReal

/-- Right continuity of `F` (Billingsley (14.2), from `tendsto_measure_biInter_gt`). -/
theorem distributionFunction_rightContinuous (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ x, ContinuousWithinAt (distributionFunction μ) (Set.Ici x) x := by
  intro x
  unfold distributionFunction
  have hmono : ∀ i j : ℝ, x < i → i ≤ j → (Iic i : Set ℝ) ⊆ Iic j :=
    fun _ _ _ hij => Iic_subset_Iic.mpr hij
  have hmeas : ∀ r > x, NullMeasurableSet (Iic r) μ :=
    fun r _ => (measurableSet_Iic).nullMeasurableSet
  have hfin : ∃ r > x, μ (Iic r) ≠ ⊤ := ⟨x + 1, by linarith, measure_ne_top μ _⟩
  have hbiInter : (⋂ r ∈ Ioi x, Iic r) = Iic x := by
    ext y
    simp only [mem_iInter, mem_Iic, mem_Ioi]
    refine ⟨fun h => ?_, fun hy r hr => hy.trans hr.le⟩
    by_contra hlt
    push_neg at hlt
    have := h ((x + y) / 2) (by linarith)
    linarith
  have htendsto_Ioi : Tendsto (fun y => μ (Iic y)) (𝓝[Ioi x] x) (𝓝 (μ (Iic x))) := by
    have h := tendsto_measure_biInter_gt (s := fun y : ℝ => Iic y) (a := x) hmeas hmono hfin
    rw [show (⋂ r, ⋂ (_ : r > x), Iic r) = Iic x from hbiInter] at h
    exact h
  have hsplit : 𝓝[Ici x] x = 𝓝[Ioi x] x ⊔ pure x := by
    rw [show (Ici x : Set ℝ) = Ioi x ∪ {x} from (Ioi_union_left).symm,
        nhdsWithin_union, nhdsWithin_singleton]
  have htendsto_Ici : Tendsto (fun y => μ (Iic y)) (𝓝[Ici x] x) (𝓝 (μ (Iic x))) := by
    rw [hsplit]
    refine Tendsto.sup htendsto_Ioi ?_
    simpa using (tendsto_pure_nhds (f := fun y : ℝ => μ (Iic y)) (a := x))
  have hcont : ContinuousWithinAt (fun y => (μ (Iic y)).toReal) (Ici x) x :=
    (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htendsto_Ici
  exact hcont

/-- Monotonicity: `x ≤ y` implies `F x ≤ F y`. -/
theorem distributionFunction_mono (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (distributionFunction μ) := by
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Iic_subset_Iic.mpr hxy))

/-- Billingsley (14.3): `F(x⁻) = μ(-∞, x)`. -/
theorem distributionFunction_leftLim (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Filter.Tendsto (distributionFunction μ) (𝓝[<] x) (𝓝 ((μ (Set.Iio x)).toReal)) := by
  let F : StieltjesFunction ℝ :=
    { toFun := distributionFunction μ
      mono' := distributionFunction_mono μ
      right_continuous' := distributionFunction_rightContinuous μ }
  have hbot : Tendsto (distributionFunction μ) atBot (𝓝 0) := by
    unfold distributionFunction
    have hmono : Monotone (fun y : ℝ => Iic y) := fun _ _ h => Iic_subset_Iic.mpr h
    have hmeas : ∀ y : ℝ, NullMeasurableSet (Iic y) μ :=
      fun y => measurableSet_Iic.nullMeasurableSet
    have hfin : ∃ y : ℝ, μ (Iic y) ≠ ⊤ := ⟨0, measure_ne_top μ _⟩
    have h1 : Tendsto (fun y : ℝ => μ (Iic y)) atBot (𝓝 (μ (⋂ y : ℝ, Iic y))) :=
      tendsto_measure_iInter_atBot hmeas hmono hfin
    have h2 : (⋂ y : ℝ, Iic y) = (∅ : Set ℝ) := by
      ext y
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
      exact ⟨y - 1, by linarith⟩
    rw [h2, measure_empty] at h1
    have : (0 : ℝ) = (0 : ℝ≥0∞).toReal := by simp
    rw [this]
    exact ENNReal.tendsto_toReal (by simp) |>.comp h1
  have htop : Tendsto (distributionFunction μ) atTop (𝓝 (μ Set.univ).toReal) := by
    unfold distributionFunction
    exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp (tendsto_measure_Iic_atTop μ)
  have hFbot : Tendsto F atBot (𝓝 0) := hbot
  have hFtop : Tendsto F atTop (𝓝 (μ Set.univ).toReal) := htop
  haveI : IsFiniteMeasure F.measure := F.isFiniteMeasure hFbot hFtop
  have hFmeasure : F.measure = μ := by
    apply Measure.ext_of_Iic
    intro t
    rw [F.measure_Iic hFbot]
    simp [F, distributionFunction, measure_ne_top μ _]
  have hleft_nonneg : 0 ≤ Function.leftLim F x := by
    have hy : x - 1 < x := by linarith
    exact (Monotone.le_of_tendsto F.mono hFbot (x - 1)).trans (F.mono.le_leftLim hy)
  have hleft :
      Function.leftLim F x = (μ (Set.Iio x)).toReal := by
    have hIio : ENNReal.ofReal (Function.leftLim F x) = μ (Set.Iio x) := by
      simpa [hFmeasure] using (F.measure_Iio hFbot x).symm
    have := congrArg ENNReal.toReal hIio
    simpa [ENNReal.toReal_ofReal hleft_nonneg, measure_ne_top μ _] using this
  simpa [F, hleft] using F.mono.tendsto_leftLim x

/-- Jump = point mass: `F(x) - F(x⁻) = μ {x}`. -/
theorem distributionFunction_jump (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    distributionFunction μ x - (μ (Set.Iio x)).toReal = (μ ({x} : Set ℝ)).toReal := by
  unfold distributionFunction
  have hdisj : Disjoint (Iio x) ({x} : Set ℝ) := by
    rw [Set.disjoint_singleton_right]
    simp [mem_Iio]
  have hunion : Iio x ∪ ({x} : Set ℝ) = Iic x := by
    ext y
    simp only [mem_union, mem_Iio, mem_singleton_iff, mem_Iic]
    exact le_iff_lt_or_eq.symm
  have h1 : μ (Iic x) = μ (Iio x) + μ ({x} : Set ℝ) := by
    rw [← hunion]
    exact measure_union hdisj (MeasurableSet.singleton x)
  rw [h1, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  ring

/-- `lim_{x → -∞} F(x) = 0` (Billingsley (14.4)). -/
theorem distributionFunction_tendsto_zero_atBot (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (distributionFunction μ) atBot (𝓝 0) := by
  unfold distributionFunction
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

/-- `lim_{x → +∞} F(x) = μ(univ)` (Billingsley (14.4) for probability measures gives `1`). -/
theorem distributionFunction_tendsto_total_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (distributionFunction μ) atTop (𝓝 (μ Set.univ).toReal) := by
  unfold distributionFunction
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp (tendsto_measure_Iic_atTop μ)

/-! ## Theorem 14.1: converse — every such F is a distribution function -/

/-- **Theorem 14.1** (Billingsley): every right-continuous nondecreasing `F : ℝ → ℝ` with
the two limits `lim_{-∞} F = 0` and `lim_{+∞} F = 1` is the distribution function of a
probability measure on `(ℝ, 𝓑)`. In mathlib this is the `StieltjesFunction.measure`
construction restricted to normalized `F`. -/
theorem exists_measure_of_distributionFunction
    (F : ℝ → ℝ) (hmono : Monotone F)
    (hrc : ∀ x, ContinuousWithinAt F (Set.Ici x) x)
    (hatBot : Tendsto F atBot (𝓝 0)) (hatTop : Tendsto F atTop (𝓝 1)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ x, (μ (Set.Iic x)).toReal = F x := by
  let sf : StieltjesFunction ℝ :=
    { toFun := F, mono' := hmono, right_continuous' := hrc }
  have hF_nonneg : ∀ x, 0 ≤ F x := by
    intro x
    refine le_of_tendsto hatBot ?_
    filter_upwards [Iic_mem_atBot x] with y hy
    exact hmono hy
  refine ⟨sf.measure, sf.isProbabilityMeasure hatBot hatTop, ?_⟩
  intro x
  have hmIic : sf.measure (Iic x) = ENNReal.ofReal (F x) := by
    have := sf.measure_Iic hatBot x
    simpa [sf, sub_zero] using this
  rw [hmIic, ENNReal.toReal_ofReal (hF_nonneg x)]

/-! ## Exponential distribution -/

/-- **Billingsley (14.7)**: exponential distribution function with rate `a > 0`. -/
def exponentialCdf (a : ℝ) : ℝ → ℝ := fun x =>
  if x < 0 then 0 else 1 - Real.exp (-(a * x))

/-- Billingsley (14.6): the lack-of-memory equation `1 - F(x + y) = (1 - F x)(1 - F y)`
on the positive axis for the exponential CDF. -/
theorem exponentialCdf_lack_of_memory (a x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 - exponentialCdf a (x + y) = (1 - exponentialCdf a x) * (1 - exponentialCdf a y) := by
  have hxy : ¬ (x + y < 0) := not_lt.mpr (add_nonneg hx hy)
  have hx' : ¬ (x < 0) := not_lt.mpr hx
  have hy' : ¬ (y < 0) := not_lt.mpr hy
  simp only [exponentialCdf, hxy, hx', hy', if_false]
  rw [show (1 : ℝ) - (1 - Real.exp (-(a * (x + y)))) = Real.exp (-(a * (x + y))) from by ring,
      show (1 : ℝ) - (1 - Real.exp (-(a * x))) = Real.exp (-(a * x)) from by ring,
      show (1 : ℝ) - (1 - Real.exp (-(a * y))) = Real.exp (-(a * y)) from by ring,
      ← Real.exp_add]
  congr 1; ring

end Mettapedia.AutoBooks.Billingsley.Ch02Sec14
