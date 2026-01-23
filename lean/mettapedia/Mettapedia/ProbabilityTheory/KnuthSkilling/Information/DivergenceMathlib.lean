import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Mathlib bridge: KL divergence for countable discrete measures ↔ K&S `divergenceInf`

This file connects the project's countable K&S divergence sum
`divergenceInf : (α → ℝ) → (α → ℝ) → ℝ` (defined as a `tsum` of per-atom contributions)
to mathlib's measure-theoretic KL divergence `InformationTheory.klDiv`.

## Main results

### General countable types

For any countable type `α` with `MeasurableSingletonClass α`:

- `Countable.toMeasure`: Convert weight function `w : α → ℝ` to measure `∑' a, w a • δ_a`
- `Countable.klDiv_toMeasure_eq_divergenceInfTop`: `klDiv μ_w μ_u = divergenceInfTop w u` (in `ℝ≥0∞`)
- `Countable.klDiv_toMeasure_eq_ofReal_divergenceInf`: When finite, equals `ofReal (divergenceInf w u)`

### Specialization to ℕ (with explicit ⊤ measurable space)

The `Seq` namespace provides versions using `@Measure ℕ ⊤` to avoid measurable space instance
ambiguity on `ℕ`:

- `Seq.toMeasureTop`: Convert `w : ℕ → ℝ` to measure on `(ℕ, ⊤)`
- `Seq.klDiv_toMeasureTop_eq_divergenceInfTop`: The `ℕ`-specialized bridge theorem

## Design notes

- Under the discrete support-positivity condition `w a ≠ 0 → 0 < u a`, we have
  `μ_w ≪ μ_u` and can compute `klDiv μ_w μ_u` as a countable sum.
- When the real series defining `divergenceInf w u` is summable, we obtain the finite-value identity
  `klDiv μ_w μ_u = ENNReal.ofReal (divergenceInf w u)`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence

open scoped BigOperators ENNReal

open Classical MeasureTheory Real

/-! ## General countable types -/

namespace Countable

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Interpret a weight function as a measure on a countable type. -/
noncomputable def toMeasure (w : α → ℝ) : Measure α :=
  Measure.sum fun a => (ENNReal.ofReal (w a)) • Measure.dirac a

omit [Countable α] in
@[simp]
theorem toMeasure_apply_singleton (w : α → ℝ) (a : α) :
    toMeasure w {a} = ENNReal.ofReal (w a) := by
  classical
  have hmeas : MeasurableSet ({a} : Set α) := measurableSet_singleton a
  rw [toMeasure, Measure.sum_apply _ hmeas]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hmeas]
  -- Only the `a` term contributes
  have h : ∀ b : α, (ENNReal.ofReal (w b)) * (Set.indicator {a} 1 b) =
      if b = a then ENNReal.ofReal (w a) else 0 := fun b => by
    simp only [Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
    split_ifs <;> simp_all
  simp_rw [h]
  rw [tsum_ite_eq]

omit [Countable α] [MeasurableSingletonClass α] in
@[simp]
theorem toMeasure_univ (w : α → ℝ) :
    toMeasure w Set.univ = ∑' a, ENNReal.ofReal (w a) := by
  classical
  rw [toMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one]

omit [Countable α] [MeasurableSingletonClass α] in
theorem isFiniteMeasure_toMeasure (w : α → ℝ) (hw : Summable w) :
    IsFiniteMeasure (toMeasure w) := by
  classical
  refine ⟨?_⟩
  have h : toMeasure w Set.univ = ∑' a, ENNReal.ofReal (w a) := by simp
  have hne : (toMeasure w Set.univ) ≠ (⊤ : ℝ≥0∞) := by
    simpa [h] using hw.tsum_ofReal_ne_top
  exact lt_top_iff_ne_top.mpr hne

/-- The `ENNReal`-valued countable divergence sum. -/
noncomputable def divergenceInfTop (w u : α → ℝ) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal (atomDivergenceExt (w a) (u a))

/-- The `ℝ`-valued countable divergence sum (generalization of `divergenceInf` to arbitrary countable types). -/
noncomputable def divergenceInfCountable (w u : α → ℝ) : ℝ :=
  ∑' a, atomDivergenceExt (w a) (u a)

theorem toMeasure_eq_withDensity (w u : α → ℝ)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a) :
    toMeasure w = (toMeasure u).withDensity (fun a => ENNReal.ofReal (w a) / ENNReal.ofReal (u a)) := by
  classical
  let dens : α → ℝ≥0∞ := fun a => ENNReal.ofReal (w a) / ENNReal.ofReal (u a)
  apply Measure.ext_of_singleton
  intro a
  by_cases hwa : w a = 0
  · -- `w a = 0`: both sides are 0 on `{a}`.
    simp [hwa, toMeasure_apply_singleton, withDensity_apply]
  · -- `w a ≠ 0`: support-positivity gives `0 < u a`, so we can cancel.
    have hu_pos : 0 < u a := hSupport a hwa
    have hu_ne0 : ENNReal.ofReal (u a) ≠ 0 := (ENNReal.ofReal_ne_zero_iff).2 hu_pos
    have hu_ne_top : ENNReal.ofReal (u a) ≠ (⊤ : ℝ≥0∞) := by simp
    have hmuldiv :
        ENNReal.ofReal (u a) * (ENNReal.ofReal (w a) / ENNReal.ofReal (u a)) =
          ENNReal.ofReal (w a) := by
      simpa [dens] using
        (ENNReal.mul_div_cancel (a := ENNReal.ofReal (u a)) (b := ENNReal.ofReal (w a)) hu_ne0 hu_ne_top)
    simp [toMeasure_apply_singleton, withDensity_apply, hmuldiv]

theorem klDiv_toMeasure_eq_divergenceInfTop (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hu : ∀ a, 0 ≤ u a)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a)
    (hw_sum : Summable w)
    (hu_sum : Summable u) :
    InformationTheory.klDiv (toMeasure w) (toMeasure u) = divergenceInfTop w u := by
  classical
  let μ : Measure α := toMeasure w
  let ν : Measure α := toMeasure u
  let dens : α → ℝ≥0∞ := fun a => ENNReal.ofReal (w a) / ENNReal.ofReal (u a)
  have hdens_meas : Measurable dens := measurable_of_countable dens
  have h_withDensity : μ = ν.withDensity dens := by
    simpa [μ, ν, dens] using (toMeasure_eq_withDensity (w := w) (u := u) hSupport)
  have hAC : μ ≪ ν := by
    simpa [h_withDensity] using (MeasureTheory.withDensity_absolutelyContinuous (μ := ν) dens)
  -- Install finiteness instances required for `klDiv_eq_lintegral_klFun`.
  letI : IsFiniteMeasure μ := (isFiniteMeasure_toMeasure (w := w) hw_sum)
  letI : IsFiniteMeasure ν := (isFiniteMeasure_toMeasure (w := u) hu_sum)
  have hrn : μ.rnDeriv ν =ᵐ[ν] dens := by
    simpa [h_withDensity] using (Measure.rnDeriv_withDensity (ν := ν) hdens_meas)
  -- Expand `klDiv` as a `lintegral`, then rewrite it as a countable sum.
  have hklDiv :
      InformationTheory.klDiv μ ν =
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν := by
    simp [InformationTheory.klDiv_eq_lintegral_klFun, hAC]
  have hcongr :
      (fun x : α => ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal))) =ᵐ[ν]
        fun x : α => ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) := by
    filter_upwards [hrn] with x hx
    simp [hx]
  have hlin :
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν) =
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) ∂ν := by
    exact lintegral_congr_ae hcongr
  rw [hklDiv, hlin]
  -- Turn the `lintegral` into a `tsum` over singletons.
  have hcount :
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) ∂ν) =
        ∑' a : α, ENNReal.ofReal (InformationTheory.klFun ((dens a).toReal)) * ν {a} := by
    simpa using
      (MeasureTheory.lintegral_countable' (μ := ν)
        (f := fun a : α => ENNReal.ofReal (InformationTheory.klFun ((dens a).toReal))))
  rw [hcount]
  -- Rewrite `ν{a}` as the weight `u a`.
  simp only [ν, toMeasure_apply_singleton]
  -- Now show term-wise equality with `atomDivergenceExt`.
  refine tsum_congr fun a => ?_
  by_cases hua : u a = 0
  · -- If `u a = 0`, support positivity forces `w a = 0`, so both sides are 0.
    have hwa : w a = 0 := by
      by_contra hwa
      have hu_pos : 0 < u a := hSupport a hwa
      exact (ne_of_gt hu_pos) hua
    simp [hua, hwa]
  · have hu_pos : 0 < u a := (hu a).lt_of_ne' hua
    have htoReal_dens : (dens a).toReal = w a / u a := by
      simp [dens, ENNReal.toReal_div, ENNReal.toReal_ofReal (hw a), ENNReal.toReal_ofReal (hu a)]
    have hkl_nonneg :
        0 ≤ InformationTheory.klFun (w a / u a) :=
      InformationTheory.klFun_nonneg (div_nonneg (hw a) (hu a))
    have hAtom :
        atomDivergenceExt (w a) (u a) = u a * InformationTheory.klFun (w a / u a) :=
      atomDivergenceExt_eq_mul_klFun (w a) (u a) (hw a) hu_pos
    calc
      ENNReal.ofReal (InformationTheory.klFun ((dens a).toReal)) * ENNReal.ofReal (u a)
          = ENNReal.ofReal (InformationTheory.klFun (w a / u a)) * ENNReal.ofReal (u a) := by
              simp [htoReal_dens]
      _ = ENNReal.ofReal (InformationTheory.klFun (w a / u a) * u a) := by
          symm
          simpa using (ENNReal.ofReal_mul hkl_nonneg)
      _ = ENNReal.ofReal (u a * InformationTheory.klFun (w a / u a)) := by
          simp [mul_comm]
      _ = ENNReal.ofReal (atomDivergenceExt (w a) (u a)) := by
          simp [hAtom]

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem divergenceInfTop_eq_ofReal_divergenceInfCountable (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hu : ∀ a, 0 ≤ u a)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a)
    (hSum : Summable (fun a => atomDivergenceExt (w a) (u a))) :
    divergenceInfTop w u = ENNReal.ofReal (divergenceInfCountable w u) := by
  classical
  have hnonneg : ∀ a, 0 ≤ atomDivergenceExt (w a) (u a) := by
    intro a
    by_cases hua : u a = 0
    · have hwa : w a = 0 := by
        by_contra hwa
        have hu_pos : 0 < u a := hSupport a hwa
        exact (ne_of_gt hu_pos) hua
      simp [hua, hwa]
    · have hu_pos : 0 < u a := (hu a).lt_of_ne' hua
      exact atomDivergenceExt_nonneg (w a) (u a) (hw a) hu_pos
  have h :=
    (ENNReal.ofReal_tsum_of_nonneg (f := fun a => atomDivergenceExt (w a) (u a)) hnonneg hSum).symm
  simpa [divergenceInfTop, divergenceInfCountable] using h

theorem klDiv_toMeasure_eq_ofReal_divergenceInfCountable (w u : α → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hu : ∀ a, 0 ≤ u a)
    (hSupport : ∀ a, w a ≠ 0 → 0 < u a)
    (hw_sum : Summable w)
    (hu_sum : Summable u)
    (hSum : Summable (fun a => atomDivergenceExt (w a) (u a))) :
    InformationTheory.klDiv (toMeasure w) (toMeasure u) =
      ENNReal.ofReal (divergenceInfCountable w u) := by
  have h1 :=
    klDiv_toMeasure_eq_divergenceInfTop (w := w) (u := u) hw hu hSupport hw_sum hu_sum
  have h2 :=
    divergenceInfTop_eq_ofReal_divergenceInfCountable (w := w) (u := u) hw hu hSupport hSum
  simpa [h2] using h1

end Countable

/-! ## Specialization to ℕ with explicit ⊤ measurable space

This namespace provides versions using `@Measure ℕ ⊤` to avoid measurable space instance
ambiguity on `ℕ`. This is useful when working with raw sequences. -/

namespace Seq

local instance instMeasurableSingletonClassNatTop : @MeasurableSingletonClass ℕ ⊤ := by
  constructor
  intro n
  simp

/-- Interpret a weight sequence as a measure on `ℕ` (with measurable space `⊤`). -/
noncomputable def toMeasureTop (w : ℕ → ℝ) : @Measure ℕ ⊤ :=
  Measure.sum fun n => (ENNReal.ofReal (w n)) • Measure.dirac n

@[simp]
theorem toMeasureTop_apply_singleton (w : ℕ → ℝ) (n : ℕ) :
    toMeasureTop w {n} = ENNReal.ofReal (w n) := by
  classical
  have hmeas : MeasurableSet ({n} : Set ℕ) := by simp
  rw [toMeasureTop, Measure.sum_apply _ hmeas]
  simp [Measure.smul_apply, Set.indicator, Set.mem_singleton_iff]

@[simp]
theorem toMeasureTop_univ (w : ℕ → ℝ) :
    toMeasureTop w Set.univ = ∑' n, ENNReal.ofReal (w n) := by
  classical
  rw [toMeasureTop, Measure.sum_apply _ (by simp)]
  simp [Measure.smul_apply]

theorem isFiniteMeasure_toMeasureTop (w : ℕ → ℝ) (hw : Summable w) :
    IsFiniteMeasure (toMeasureTop w) := by
  classical
  refine ⟨?_⟩
  have h : toMeasureTop w Set.univ = ∑' n, ENNReal.ofReal (w n) := by simp
  have hne : (toMeasureTop w Set.univ) ≠ (⊤ : ℝ≥0∞) := by
    simpa [h] using hw.tsum_ofReal_ne_top
  exact lt_top_iff_ne_top.mpr hne

/-- The `ENNReal`-valued countable divergence sum corresponding to `divergenceInf`. -/
noncomputable def divergenceInfTop (w u : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (atomDivergenceExt (w n) (u n))

theorem toMeasureTop_eq_withDensity (w u : ℕ → ℝ)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n) :
    toMeasureTop w = (toMeasureTop u).withDensity (fun n => ENNReal.ofReal (w n) / ENNReal.ofReal (u n)) := by
  classical
  let dens : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (w n) / ENNReal.ofReal (u n)
  have hdens_meas : Measurable dens := by simp [dens, Measurable]
  apply Measure.ext_of_singleton
  intro n
  by_cases hwn : w n = 0
  · simp [hwn, toMeasureTop_apply_singleton, withDensity_apply]
  · have hu_pos : 0 < u n := hSupport n hwn
    have hu_ne0 : ENNReal.ofReal (u n) ≠ 0 := (ENNReal.ofReal_ne_zero_iff).2 hu_pos
    have hu_ne_top : ENNReal.ofReal (u n) ≠ (⊤ : ℝ≥0∞) := by simp
    have hmuldiv :
        ENNReal.ofReal (u n) * (ENNReal.ofReal (w n) / ENNReal.ofReal (u n)) =
          ENNReal.ofReal (w n) := by
      simpa [dens] using
        (ENNReal.mul_div_cancel (a := ENNReal.ofReal (u n)) (b := ENNReal.ofReal (w n)) hu_ne0 hu_ne_top)
    simp [toMeasureTop_apply_singleton, withDensity_apply, hmuldiv]

theorem klDiv_toMeasureTop_eq_divergenceInfTop (w u : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hu : ∀ n, 0 ≤ u n)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n)
    (hw_sum : Summable w)
    (hu_sum : Summable u) :
    @InformationTheory.klDiv ℕ ⊤ (toMeasureTop w) (toMeasureTop u) = divergenceInfTop w u := by
  classical
  let μ : @Measure ℕ ⊤ := toMeasureTop w
  let ν : @Measure ℕ ⊤ := toMeasureTop u
  let dens : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (w n) / ENNReal.ofReal (u n)
  have hdens_meas : Measurable dens := by simp [dens, Measurable]
  have h_withDensity : μ = ν.withDensity dens := by
    simpa [μ, ν, dens] using (toMeasureTop_eq_withDensity (w := w) (u := u) hSupport)
  have hAC : μ ≪ ν := by
    simpa [h_withDensity] using (MeasureTheory.withDensity_absolutelyContinuous (μ := ν) dens)
  letI : IsFiniteMeasure μ := (isFiniteMeasure_toMeasureTop (w := w) hw_sum)
  letI : IsFiniteMeasure ν := (isFiniteMeasure_toMeasureTop (w := u) hu_sum)
  have hrn : μ.rnDeriv ν =ᵐ[ν] dens := by
    simpa [h_withDensity] using (Measure.rnDeriv_withDensity (ν := ν) hdens_meas)
  have hklDiv :
      @InformationTheory.klDiv ℕ ⊤ μ ν =
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν := by
    simp [InformationTheory.klDiv_eq_lintegral_klFun, hAC]
  have hcongr :
      (fun x : ℕ => ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal))) =ᵐ[ν]
        fun x : ℕ => ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) := by
    filter_upwards [hrn] with x hx
    simp [hx]
  have hlin :
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν) =
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) ∂ν := by
    exact lintegral_congr_ae hcongr
  rw [hklDiv, hlin]
  have hcount :
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((dens x).toReal)) ∂ν) =
        ∑' n : ℕ, ENNReal.ofReal (InformationTheory.klFun ((dens n).toReal)) * ν {n} := by
    simpa using
      (MeasureTheory.lintegral_countable' (μ := ν)
        (f := fun n : ℕ => ENNReal.ofReal (InformationTheory.klFun ((dens n).toReal))))
  rw [hcount]
  simp only [ν, toMeasureTop_apply_singleton]
  refine tsum_congr fun n => ?_
  by_cases hun : u n = 0
  · have hwn : w n = 0 := by
      by_contra hwn
      have hu_pos : 0 < u n := hSupport n hwn
      exact (ne_of_gt hu_pos) hun
    simp [hun, hwn]
  · have hu_pos : 0 < u n := (hu n).lt_of_ne' hun
    have htoReal_dens : (dens n).toReal = w n / u n := by
      simp [dens, ENNReal.toReal_div, ENNReal.toReal_ofReal (hw n), ENNReal.toReal_ofReal (hu n)]
    have hkl_nonneg :
        0 ≤ InformationTheory.klFun (w n / u n) :=
      InformationTheory.klFun_nonneg (div_nonneg (hw n) (hu n))
    have hAtom :
        atomDivergenceExt (w n) (u n) = u n * InformationTheory.klFun (w n / u n) :=
      atomDivergenceExt_eq_mul_klFun (w n) (u n) (hw n) hu_pos
    calc
      ENNReal.ofReal (InformationTheory.klFun ((dens n).toReal)) * ENNReal.ofReal (u n)
          = ENNReal.ofReal (InformationTheory.klFun (w n / u n)) * ENNReal.ofReal (u n) := by
              simp [htoReal_dens]
      _ = ENNReal.ofReal (InformationTheory.klFun (w n / u n) * u n) := by
          symm
          simpa using (ENNReal.ofReal_mul hkl_nonneg)
      _ = ENNReal.ofReal (u n * InformationTheory.klFun (w n / u n)) := by
          simp [mul_comm]
      _ = ENNReal.ofReal (atomDivergenceExt (w n) (u n)) := by
          simp [hAtom]

theorem divergenceInfTop_eq_ofReal_divergenceInf (w u : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hu : ∀ n, 0 ≤ u n)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n)
    (hSum : Summable (fun n => atomDivergenceExt (w n) (u n))) :
    divergenceInfTop w u = ENNReal.ofReal (divergenceInf w u) := by
  classical
  have hnonneg : ∀ n, 0 ≤ atomDivergenceExt (w n) (u n) := by
    intro n
    by_cases hun : u n = 0
    · have hwn : w n = 0 := by
        by_contra hwn
        have hu_pos : 0 < u n := hSupport n hwn
        exact (ne_of_gt hu_pos) hun
      simp [hun, hwn]
    · have hu_pos : 0 < u n := (hu n).lt_of_ne' hun
      exact atomDivergenceExt_nonneg (w n) (u n) (hw n) hu_pos
  have h :=
    (ENNReal.ofReal_tsum_of_nonneg (f := fun n => atomDivergenceExt (w n) (u n)) hnonneg hSum).symm
  simpa [divergenceInfTop, divergenceInf] using h

theorem klDiv_toMeasureTop_eq_ofReal_divergenceInf (w u : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hu : ∀ n, 0 ≤ u n)
    (hSupport : ∀ n, w n ≠ 0 → 0 < u n)
    (hw_sum : Summable w)
    (hu_sum : Summable u)
    (hSum : Summable (fun n => atomDivergenceExt (w n) (u n))) :
    @InformationTheory.klDiv ℕ ⊤ (toMeasureTop w) (toMeasureTop u) =
      ENNReal.ofReal (divergenceInf w u) := by
  have h1 :=
    klDiv_toMeasureTop_eq_divergenceInfTop (w := w) (u := u) hw hu hSupport hw_sum hu_sum
  have h2 :=
    divergenceInfTop_eq_ofReal_divergenceInf (w := w) (u := u) hw hu hSupport hSum
  simpa [h2] using h1

end Seq

end Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence
