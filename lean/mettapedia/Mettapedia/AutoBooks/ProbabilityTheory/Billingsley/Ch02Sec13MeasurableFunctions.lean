/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Billingsley Chapter 2, Section 13: Measurable Functions and Mappings

This file formalizes Section 13 of Billingsley's "Probability and Measure" (3rd Edition).
A measurable mapping between measurable spaces is a mapping whose preimage of any
measurable set is measurable — this is `Measurable` in mathlib.

## Scope

* Definition of measurable mapping `T : (Ω, 𝓕) → (Ω', 𝓕')`.
* **Theorem 13.1**: generator-level measurability; composition of measurable maps.
* **Theorem 13.2**: continuous mappings between topological spaces (with Borel σ-fields)
  are measurable.
* **Theorem 13.3**: pushforward by a continuous (or measurable) `g : ℝ^k → ℝ^l`.
* **Theorem 13.4**: measurability of `sup`, `inf`, `limsup`, `liminf`, pointwise limits.
* **Theorem 13.5**: every nonnegative measurable function is a pointwise limit of an
  increasing sequence of simple functions.
* Simple-function representation (Billingsley (13.3)).

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 13][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology MeasurableSpace
open scoped ENNReal NNReal

namespace Mettapedia.AutoBooks.Billingsley.Ch02Sec13

variable {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']

/-! ## Definition: measurable mapping -/

/-- A mapping `T : Ω → Ω'` is measurable `𝓕/𝓕'` iff the preimage of every `𝓕'`-measurable
set is `𝓕`-measurable. This is mathlib's `Measurable`. -/
example (T : Ω → Ω') : Prop := Measurable T

/-! ## Theorem 13.1: generator-level measurability; composition -/

/-- **Theorem 13.1 (i)**: if `T⁻¹ A' ∈ 𝓕` for each `A'` in a generating class of `𝓕'`,
then `T` is measurable. -/
theorem measurable_of_generatorOf {mΩ' : MeasurableSpace Ω'}
    (T : Ω → Ω') (𝒜 : Set (Set Ω'))
    (h_gen : mΩ' = MeasurableSpace.generateFrom 𝒜)
    (h : ∀ A ∈ 𝒜, MeasurableSet (T ⁻¹' A)) : Measurable T := by
  intro s hs
  rw [h_gen] at hs
  induction hs with
  | basic u hu => exact h u hu
  | empty => simp
  | compl u hu ihu => simpa [Set.preimage_compl] using ihu.compl
  | iUnion f _ ihf => simpa [Set.preimage_iUnion] using MeasurableSet.iUnion ihf

/-- **Theorem 13.1 (ii)**: composition of measurable mappings is measurable. -/
theorem measurable_comp (T' : Ω' → Ω'') (T : Ω → Ω')
    (hT' : Measurable T') (hT : Measurable T) : Measurable (T' ∘ T) :=
  hT'.comp hT

/-! ## Theorem 13.2: continuous implies measurable -/

/-- **Theorem 13.2** (Billingsley): every continuous map between Borel spaces is
measurable. -/
theorem measurable_of_continuous {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Continuous f) : Measurable f :=
  hf.measurable

/-! ## Theorem 13.3: g ∘ (f₁, …, f_k) is measurable -/

/-- **Theorem 13.3** (Billingsley): a measurable function composed with a tuple of
measurable components is measurable. -/
theorem measurable_comp_tuple {k : ℕ}
    (f : Fin k → Ω → ℝ) (hf : ∀ j, Measurable (f j))
    (g : (Fin k → ℝ) → ℝ) (hg : Measurable g) :
    Measurable (fun ω => g (fun j => f j ω)) :=
  hg.comp (measurable_pi_lambda _ hf)

/-! ## Theorem 13.4: limits of measurable functions -/

/-- **Theorem 13.4 (i)**: the `sup` of a countable family of measurable real-valued
functions is measurable. -/
theorem measurable_iSup {ι : Type*} [Countable ι] {f : ι → Ω → ℝ}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => ⨆ i, f i ω) :=
  Measurable.iSup hf

/-- **Theorem 13.4 (i)**: the `inf` of a countable family of measurable real-valued
functions is measurable. -/
theorem measurable_iInf {ι : Type*} [Countable ι] {f : ι → Ω → ℝ}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => ⨅ i, f i ω) :=
  Measurable.iInf hf

/-- **Theorem 13.4 (ii)**: the pointwise limit (when it exists everywhere) of a sequence
of measurable functions is measurable. We state this via `limsup`. -/
theorem measurable_limsup {f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun ω => Filter.limsup (fun n => f n ω) Filter.atTop) :=
  Measurable.limsup hf

/-- Dual form using `liminf`. -/
theorem measurable_liminf {f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun ω => Filter.liminf (fun n => f n ω) Filter.atTop) :=
  Measurable.liminf hf

/-! ## Simple functions (Billingsley (13.3), Theorem 13.5) -/

/-- Simple real functions: a finite linear combination of characteristic functions of a
measurable partition. In mathlib this is `MeasureTheory.SimpleFunc`. -/
example (Ω : Type) [MeasurableSpace Ω] : Type := MeasureTheory.SimpleFunc Ω ℝ

/-- **Theorem 13.5** (Billingsley): for every measurable `f : Ω → [0, ∞)` there is a
nondecreasing sequence of measurable simple functions converging pointwise to `f`. -/
theorem exists_simpleFunc_tendsto_of_measurable_nonneg
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∃ (s : ℕ → MeasureTheory.SimpleFunc Ω ℝ≥0∞),
      (∀ ω n, s n ω ≤ s (n+1) ω) ∧ (∀ ω, Filter.Tendsto (fun n => s n ω) Filter.atTop (𝓝 (f ω))) := by
  classical
  refine ⟨MeasureTheory.SimpleFunc.eapprox f, ?_, ?_⟩
  · intro ω n; exact MeasureTheory.SimpleFunc.monotone_eapprox f (Nat.le_succ n) ω
  · intro ω; exact MeasureTheory.SimpleFunc.tendsto_eapprox hf ω

end Mettapedia.AutoBooks.Billingsley.Ch02Sec13
