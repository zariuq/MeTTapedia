import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic
import Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
import Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNNoisyOr
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
import Mettapedia.PLN.TruthValues.PLNConfidenceWeight
import Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

/-!
# Multi-path Frechet envelopes

This module gives the WM-PLN convergent-evidence frequency envelope for a
nonempty finite family of paths.  The frequency coordinate is real-valued and
uses the finite union Frechet envelope

`[max_i f_i, min 1 (sum_i f_i)]`.

The confidence coordinate is kept orthogonal and routed through the existing
ENNReal confidence-weight functions.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet

open scoped BigOperators ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Asymptotics
open Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNNoisyOr
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

noncomputable section

/-! ## Phase 1: nonempty finite Frechet envelope -/

/-- Multi-path convergent evidence input.  Frequencies live in the real unit
interval.  Confidences live in ENNReal and are accumulated separately through
the existing PLN confidence-weight coordinate. -/
structure MultiPathInput (n : ℕ) where
  frequency : Fin (n + 1) → ℝ
  frequency_mem_unit : ∀ i, frequency i ∈ Set.Icc (0 : ℝ) 1
  confidence : Fin (n + 1) → ℝ≥0∞
  confidence_le_one : ∀ i, confidence i ≤ 1

/-- Sum of a finite real frequency family. -/
def sumFrequency {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  Finset.univ.sum f

/-- Maximum of a nonempty real frequency family indexed by `Fin (n+1)`. -/
def maxFrequency (n : ℕ) (f : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- The capped Frechet upper endpoint for a nonempty finite union. -/
def frechetUnionUpper (n : ℕ) (f : Fin (n + 1) → ℝ) : ℝ :=
  min 1 (sumFrequency f)

/-- The lower Frechet endpoint is one of the path frequencies. -/
theorem frequency_le_maxFrequency {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    f i ≤ maxFrequency n f := by
  unfold maxFrequency
  exact Finset.le_sup' f (by simp)

theorem maxFrequency_nonneg {n : ℕ} {f : Fin (n + 1) → ℝ}
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ maxFrequency n f := by
  exact le_trans (hf 0).1 (frequency_le_maxFrequency f 0)

theorem maxFrequency_le_one {n : ℕ} {f : Fin (n + 1) → ℝ}
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    maxFrequency n f ≤ 1 := by
  unfold maxFrequency
  exact Finset.sup'_le Finset.univ_nonempty f (fun i _ => (hf i).2)

theorem maxFrequency_le_sumFrequency {n : ℕ} {f : Fin (n + 1) → ℝ}
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    maxFrequency n f ≤ sumFrequency f := by
  unfold maxFrequency sumFrequency
  exact Finset.sup'_le Finset.univ_nonempty f (fun i _ =>
    Finset.single_le_sum (fun j _ => (hf j).1) (by simp))

theorem maxFrequency_le_frechetUnionUpper {n : ℕ} {f : Fin (n + 1) → ℝ}
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    maxFrequency n f ≤ frechetUnionUpper n f := by
  unfold frechetUnionUpper
  exact le_min (maxFrequency_le_one hf) (maxFrequency_le_sumFrequency hf)

theorem sumFrequency_nonneg {n : ℕ} {f : Fin n → ℝ}
    (hf : ∀ i, 0 ≤ f i) :
    0 ≤ sumFrequency f := by
  unfold sumFrequency
  exact Finset.sum_nonneg (fun i _ => hf i)

theorem frechetUnionUpper_mem_unit {n : ℕ} {f : Fin (n + 1) → ℝ}
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    frechetUnionUpper n f ∈ Set.Icc (0 : ℝ) 1 := by
  unfold frechetUnionUpper
  constructor
  · exact le_min zero_le_one (sumFrequency_nonneg fun i => (hf i).1)
  · exact min_le_left _ _

/-- Existing PLN confidence accumulation at scale `k = 1`: convert each
confidence to evidence weight, add weights, then convert back. -/
def accumulatedConfidence (input : MultiPathInput n) : ℝ≥0∞ :=
  w2c (Finset.univ.sum (fun i => c2w (input.confidence i) 1)) 1

theorem accumulatedConfidence_le_one (input : MultiPathInput n) :
    accumulatedConfidence input ≤ 1 := by
  exact w2c_le_one _ _ (by simp)

theorem accumulatedConfidenceReal_mem_unit (input : MultiPathInput n) :
    (accumulatedConfidence input).toReal ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have h := accumulatedConfidence_le_one input
    have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h1] at h
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h

/-- Current ENNReal boundary behavior of the reused confidence functions. -/
theorem c2w_one_one_eq_top : c2w (1 : ℝ≥0∞) 1 = ⊤ := by
  simp [c2w]

/-- Infinite evidence weight is saturated confidence in the reused coordinate. -/
theorem w2c_top_one_eq_one : w2c (⊤ : ℝ≥0∞) 1 = 1 := by
  simp [w2c]

/-- The nonempty finite Frechet envelope as an existing ITV record. -/
def frechetUnionITV (input : MultiPathInput n) : ITV where
  lower := maxFrequency n input.frequency
  upper := frechetUnionUpper n input.frequency
  credibility := (accumulatedConfidence input).toReal
  lower_le_upper := maxFrequency_le_frechetUnionUpper input.frequency_mem_unit
  lower_in_unit :=
    ⟨maxFrequency_nonneg input.frequency_mem_unit,
      maxFrequency_le_one input.frequency_mem_unit⟩
  upper_in_unit := frechetUnionUpper_mem_unit input.frequency_mem_unit
  credibility_in_unit := accumulatedConfidenceReal_mem_unit input

theorem frechetUnionITV_lower (input : MultiPathInput n) :
    (frechetUnionITV input).lower = maxFrequency n input.frequency := rfl

theorem frechetUnionITV_upper (input : MultiPathInput n) :
    (frechetUnionITV input).upper = frechetUnionUpper n input.frequency := rfl

theorem frechetUnionITV_credibility (input : MultiPathInput n) :
    (frechetUnionITV input).credibility = (accumulatedConfidence input).toReal := rfl

theorem measureReal_mem_unit_of_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) :
    μ.real A ∈ Set.Icc (0 : ℝ) 1 := by
  have hUniv_ne : μ Set.univ ≠ ⊤ := by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_ne_top
  constructor
  · exact measureReal_nonneg
  · have h := measureReal_mono (μ := μ) (Set.subset_univ A) hUniv_ne
    rw [probReal_univ] at h
    exact h

/-- Build a multi-path input from measured events and supplied confidence
coordinates. -/
def MultiPathInput.ofEvents
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Fin (n + 1) → Set Ω)
    (confidence : Fin (n + 1) → ℝ≥0∞)
    (confidence_le_one : ∀ i, confidence i ≤ 1) :
    MultiPathInput n where
  frequency := fun i => μ.real (A i)
  frequency_mem_unit := fun i => measureReal_mem_unit_of_probability μ (A i)
  confidence := confidence
  confidence_le_one := confidence_le_one

/-- Membership-first Frechet soundness: the measured finite union lies in the
nonempty finite union envelope. -/
theorem measureReal_iUnion_mem_frechetBounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin (n + 1) → Set Ω) :
    let f : Fin (n + 1) → ℝ := fun i => μ.real (A i)
    maxFrequency n f ≤ μ.real (⋃ i, A i) ∧
      μ.real (⋃ i, A i) ≤ frechetUnionUpper n f := by
  intro f
  have hUnion_ne : μ (⋃ i, A i) ≠ ⊤ := by finiteness
  have hUniv_ne : μ Set.univ ≠ ⊤ := by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_ne_top
  constructor
  · unfold maxFrequency
    apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    exact measureReal_mono (μ := μ) (Set.subset_iUnion A i) hUnion_ne
  · unfold frechetUnionUpper sumFrequency
    apply le_min
    · have h := measureReal_mono (μ := μ) (Set.subset_univ (⋃ i, A i)) hUniv_ne
      rw [probReal_univ] at h
      exact h
    · simpa using measureReal_iUnion_fintype_le (μ := μ) A

theorem measureReal_iUnion_mem_frechetUnionITV_ofEvents
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin (n + 1) → Set Ω)
    (confidence : Fin (n + 1) → ℝ≥0∞)
    (confidence_le_one : ∀ i, confidence i ≤ 1) :
    let input := MultiPathInput.ofEvents (n := n) μ A confidence confidence_le_one
    (frechetUnionITV input).lower ≤ μ.real (⋃ i, A i) ∧
      μ.real (⋃ i, A i) ≤ (frechetUnionITV input).upper := by
  intro input
  simpa [input, MultiPathInput.ofEvents, frechetUnionITV_lower, frechetUnionITV_upper]
    using measureReal_iUnion_mem_frechetBounds (μ := μ) A

/-! ## Phase 2: endpoint exactness and revision comparison -/

theorem measureReal_iUnion_eq_sum_of_pairwise_aedisjoint
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {n : ℕ} (A : Fin n → Set Ω)
    (hAE : Pairwise (fun i j => AEDisjoint μ (A i) (A j)))
    (hNull : ∀ i, NullMeasurableSet (A i) μ) :
    μ.real (⋃ i, A i) = ∑ i, μ.real (A i) := by
  have h := measureReal_biUnion_finset₀ (μ := μ)
    (s := (Finset.univ : Finset (Fin n))) (f := A)
    (hd := fun i _ j _ hij => hAE hij)
    (hm := fun i _ => hNull i)
    (h := by finiteness)
  simpa using h

theorem measureReal_iUnion_eq_sum_iff_pairwise_aedisjoint
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin (n + 1) → Set Ω)
    (hNull : ∀ i, NullMeasurableSet (A i) μ) :
    μ.real (⋃ i, A i) = ∑ i, μ.real (A i) ↔
      Pairwise (fun i j => AEDisjoint μ (A i) (A j)) := by
  constructor
  · intro heq i j hij
    let R : Set Ω := ⋃ k ∈ (Finset.univ.erase i), A k
    have hRnull : NullMeasurableSet R μ := by
      dsimp [R]
      exact NullMeasurableSet.biUnion
        (Finset.countable_toSet (Finset.univ.erase i))
        (fun k _ => hNull k)
    have hUniv_ne : μ Set.univ ≠ ∞ := by
      rw [IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_ne_top
    have hAi_ne : μ (A i) ≠ ∞ :=
      measure_ne_top_of_subset (Set.subset_univ (A i)) hUniv_ne
    have hR_ne : μ R ≠ ∞ :=
      measure_ne_top_of_subset (Set.subset_univ R) hUniv_ne
    have hUnion : A i ∪ R = ⋃ k, A k := by
      ext x
      simp [R]
      constructor
      · intro hx
        rcases hx with hx | ⟨k, _hk, hxk⟩
        · exact ⟨i, hx⟩
        · exact ⟨k, hxk⟩
      · intro hx
        rcases hx with ⟨k, hxk⟩
        by_cases hki : k = i
        · left
          simpa [hki] using hxk
        · right
          exact ⟨k, hki, hxk⟩
    have hUnionAdd :
        μ.real (A i ∪ R) + μ.real (A i ∩ R) =
          μ.real (A i) + μ.real R :=
      measureReal_union_add_inter₀ (μ := μ) hRnull hAi_ne hR_ne
    have hUnionAdd' :
        (∑ k, μ.real (A k)) + μ.real (A i ∩ R) =
          μ.real (A i) + μ.real R := by
      simpa [hUnion, heq] using hUnionAdd
    have hR_le :
        μ.real R ≤ ∑ k ∈ Finset.univ.erase i, μ.real (A k) := by
      simpa [R] using
        (measureReal_biUnion_finset_le
          (μ := μ) (s := Finset.univ.erase i) (f := A))
    have hright_le :
        μ.real (A i) + μ.real R ≤ ∑ k, μ.real (A k) := by
      rw [← Finset.add_sum_erase
        (Finset.univ : Finset (Fin (n + 1)))
        (fun k => μ.real (A k)) (Finset.mem_univ i)]
      exact add_le_add (le_refl _) hR_le
    have hAiR_real_zero : μ.real (A i ∩ R) = 0 := by
      apply le_antisymm
      · nlinarith
      · exact measureReal_nonneg
    have hAj_subset_R : A j ⊆ R := by
      intro x hx
      simp [R]
      exact ⟨j, hij.symm, hx⟩
    have hInter_subset : A i ∩ A j ⊆ A i ∩ R :=
      Set.inter_subset_inter_right _ hAj_subset_R
    have hInter_real_zero : μ.real (A i ∩ A j) = 0 :=
      measureReal_mono_null hInter_subset hAiR_real_zero (by finiteness)
    simpa [AEDisjoint] using
      (measureReal_eq_zero_iff (μ := μ) (s := A i ∩ A j) (by finiteness)).1
        hInter_real_zero
  · intro hAE
    exact measureReal_iUnion_eq_sum_of_pairwise_aedisjoint (μ := μ) A hAE hNull

theorem frechetUnionUpper_eq_sum_of_sum_le_one
    {n : ℕ} {f : Fin (n + 1) → ℝ}
    (hsum : sumFrequency f ≤ 1) :
    frechetUnionUpper n f = sumFrequency f := by
  unfold frechetUnionUpper
  exact min_eq_right hsum

theorem measureReal_iUnion_eq_frechetUpper_of_aedisjoint_unsaturated
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin (n + 1) → Set Ω)
    (hAE : Pairwise (fun i j => AEDisjoint μ (A i) (A j)))
    (hNull : ∀ i, NullMeasurableSet (A i) μ)
    (hsum : sumFrequency (fun i => μ.real (A i)) ≤ 1) :
    μ.real (⋃ i, A i) =
      frechetUnionUpper n (fun i => μ.real (A i)) := by
  rw [measureReal_iUnion_eq_sum_of_pairwise_aedisjoint (μ := μ) A hAE hNull]
  exact (frechetUnionUpper_eq_sum_of_sum_le_one (n := n) hsum).symm

theorem measureReal_iUnion_eq_frechetUpper_iff_aedisjoint_of_unsaturated
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin (n + 1) → Set Ω)
    (hNull : ∀ i, NullMeasurableSet (A i) μ)
    (hsum : sumFrequency (fun i => μ.real (A i)) < 1) :
    μ.real (⋃ i, A i) =
        frechetUnionUpper n (fun i => μ.real (A i)) ↔
      Pairwise (fun i j => AEDisjoint μ (A i) (A j)) := by
  rw [frechetUnionUpper_eq_sum_of_sum_le_one (n := n) (le_of_lt hsum)]
  exact measureReal_iUnion_eq_sum_iff_pairwise_aedisjoint (μ := μ) A hNull

theorem frechetUnionUpper_eq_one_of_one_le_sum
    {n : ℕ} {f : Fin (n + 1) → ℝ}
    (hsum : 1 ≤ sumFrequency f) :
    frechetUnionUpper n f = 1 := by
  unfold frechetUnionUpper
  exact min_eq_left hsum

theorem measureReal_iUnion_eq_frechetUpper_of_cover_saturated
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin (n + 1) → Set Ω)
    (hcover : (⋃ i, A i) = Set.univ)
    (hsum : 1 ≤ sumFrequency (fun i => μ.real (A i))) :
    μ.real (⋃ i, A i) =
      frechetUnionUpper n (fun i => μ.real (A i)) := by
  rw [hcover, probReal_univ, frechetUnionUpper_eq_one_of_one_le_sum hsum]

/-- Equal-weight binary revision of two displayed frequencies. -/
def revisionFrequency₂ (f₁ f₂ : ℝ) : ℝ :=
  (f₁ + f₂) / 2

theorem revisionFrequency₂_le_max (f₁ f₂ : ℝ) :
    revisionFrequency₂ f₁ f₂ ≤ max f₁ f₂ := by
  unfold revisionFrequency₂
  have h1 : f₁ ≤ max f₁ f₂ := le_max_left _ _
  have h2 : f₂ ≤ max f₁ f₂ := le_max_right _ _
  nlinarith

theorem revisionFrequency₂_canary :
    revisionFrequency₂ (9 / 10 : ℝ) (1 / 10 : ℝ) = (1 / 2 : ℝ) ∧
      revisionFrequency₂ (9 / 10 : ℝ) (1 / 10 : ℝ) <
        max (9 / 10 : ℝ) (1 / 10 : ℝ) := by
  constructor <;> norm_num [revisionFrequency₂]

theorem cap_active_constant_pair_canary :
    frechetUnionUpper 1 (fun _ : Fin 2 => (7 / 10 : ℝ)) = 1 ∧
      sumFrequency (fun _ : Fin 2 => (7 / 10 : ℝ)) = (7 / 5 : ℝ) := by
  constructor <;> norm_num [frechetUnionUpper, sumFrequency]

/-! ## Phase 3: noisy-OR bridge and independence point -/

/-- Finset-product noisy-OR for a finite family of real frequencies. -/
def noisyOrFrequency {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  1 - Finset.univ.prod (fun i => 1 - p i)

theorem foldl_one_sub_eq_list_prod (xs : List ℝ) :
    xs.foldl (fun acc s => acc * (1 - s)) 1 =
      (xs.map fun s => 1 - s).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, one_mul, List.map_cons, List.prod_cons]
      rw [foldl_mul_one_sub_init (init := (1 - x)) (xs := xs)]
      rw [ih]

theorem foldl_one_sub_ofFn_eq_finset_prod {n : ℕ} (p : Fin n → ℝ) :
    (List.ofFn p).foldl (fun acc s => acc * (1 - s)) 1 =
      Finset.univ.prod (fun i => 1 - p i) := by
  rw [foldl_one_sub_eq_list_prod]
  have hmap : ((List.ofFn p).map fun s => 1 - s) =
      List.ofFn (fun i => 1 - p i) := by
    ext k x
    simp
  rw [hmap]
  exact List.prod_ofFn

theorem noisyOrFrequency_eq_noisyOrMulti {n : ℕ} (p : Fin n → ℝ) :
    noisyOrFrequency p = noisyOrMulti (List.ofFn p) := by
  unfold noisyOrFrequency noisyOrMulti
  rw [foldl_one_sub_ofFn_eq_finset_prod]

theorem one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, p i ∈ Set.Icc (0 : ℝ) 1) :
    1 - ∏ i ∈ s, (1 - p i) ≤ ∑ i ∈ s, p i := by
  classical
  revert hp
  refine Finset.induction_on s ?base ?step
  · intro _
    simp
  · intro a s ha ih hp
    have hpa0 : 0 ≤ p a := (hp a (Finset.mem_insert_self a s)).1
    have hp_s : ∀ i ∈ s, p i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i hi
      exact hp i (Finset.mem_insert_of_mem hi)
    have ihs : 1 - ∏ i ∈ s, (1 - p i) ≤ ∑ i ∈ s, p i := ih hp_s
    have hprod_le_one : ∏ i ∈ s, (1 - p i) ≤ 1 := by
      exact Finset.prod_le_one (fun i hi => sub_nonneg.mpr (hp_s i hi).2)
        (fun i hi => by linarith [(hp_s i hi).1])
    have hscale : (1 - p a) * (1 - ∏ i ∈ s, (1 - p i)) ≤
        1 - ∏ i ∈ s, (1 - p i) := by
      have hnonneg : 0 ≤ 1 - ∏ i ∈ s, (1 - p i) := sub_nonneg.mpr hprod_le_one
      have hcoef_le : 1 - p a ≤ 1 := by linarith
      exact mul_le_of_le_one_left hnonneg hcoef_le
    calc
      1 - ∏ i ∈ insert a s, (1 - p i)
          = p a + (1 - p a) * (1 - ∏ i ∈ s, (1 - p i)) := by
              rw [Finset.prod_insert ha]
              ring
      _ ≤ p a + (1 - ∏ i ∈ s, (1 - p i)) := add_le_add (le_refl _) hscale
      _ ≤ p a + ∑ i ∈ s, p i := by linarith
      _ = ∑ i ∈ insert a s, p i := by rw [Finset.sum_insert ha]

theorem frequency_le_noisyOrFrequency {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (i : Fin (n + 1)) :
    p i ≤ noisyOrFrequency p := by
  have hprod_le : Finset.univ.prod (fun j : Fin (n + 1) => 1 - p j) ≤ 1 - p i := by
    have h := Finset.prod_le_prod_of_subset_of_le_one
      (s := ({i} : Finset (Fin (n + 1)))) (t := Finset.univ)
      (f := fun j : Fin (n + 1) => 1 - p j)
      (by intro j hj; simp)
      (fun j _ => sub_nonneg.mpr (hp j).2)
      (fun j _ _ => by linarith [(hp j).1])
    simpa using h
  unfold noisyOrFrequency
  linarith

theorem noisyOrFrequency_mem_frechetBounds {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    maxFrequency n p ≤ noisyOrFrequency p ∧
      noisyOrFrequency p ≤ frechetUnionUpper n p := by
  constructor
  · unfold maxFrequency
    apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    exact frequency_le_noisyOrFrequency p hp i
  · unfold frechetUnionUpper noisyOrFrequency sumFrequency
    apply le_min
    · have hprod_nonneg : 0 ≤ Finset.univ.prod (fun i : Fin (n + 1) => 1 - p i) := by
        exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hp i).2)
      linarith
    · simpa using one_sub_prod_one_sub_le_sum (Finset.univ : Finset (Fin (n + 1))) p
        (fun i _ => hp i)

theorem noisyOrFrequency_mem_frechetUnionITV
    (input : MultiPathInput n) :
    (frechetUnionITV input).lower ≤ noisyOrFrequency input.frequency ∧
      noisyOrFrequency input.frequency ≤ (frechetUnionITV input).upper := by
  simpa [frechetUnionITV_lower, frechetUnionITV_upper]
    using noisyOrFrequency_mem_frechetBounds input.frequency input.frequency_mem_unit

/-- Rare-event linearization: scaled noisy-OR differs from the exclusive sum by
`o(t)` as the shared scale `t` tends to zero. -/
theorem noisyOrFrequency_scaled_sub_linear_isLittleO {n : ℕ} (p : Fin n → ℝ) :
    (fun t : ℝ => noisyOrFrequency (fun i => t * p i) - t * sumFrequency p) =o[𝓝 0]
      (fun t : ℝ => t) := by
  have hderiv : @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      NormedField.toNormedSpace.toModule _ _
      (fun t : ℝ => 1 - (∏ i : Fin n, fun t : ℝ => 1 - t * p i) t)
      (sumFrequency p) 0 := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
          NormedField.toNormedSpace.toModule _ _
          (fun t : ℝ => 1 - t * p i) (-p i) 0 := by
      intro i _
      convert HasDerivAt.sub
        (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ)))
        (hasDerivAt_mul_const (c := p i) (x := (0 : ℝ))) using 1
      · funext t
        simp only [Pi.sub_apply]
      · ring_nf
    have hprod : @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
        NormedField.toNormedSpace.toModule _ _
        (∏ i : Fin n, fun t : ℝ => 1 - t * p i)
        (Finset.univ.sum (fun i : Fin n => -p i)) 0 := by
      simpa using HasDerivAt.finsetProd (u := (Finset.univ : Finset (Fin n))) hi
    have h := HasDerivAt.sub
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))) hprod
    convert h using 1
    · funext t
      simp only [Pi.sub_apply]
    · simp [sumFrequency]
  have h := hderiv.isLittleO
  simpa [noisyOrFrequency, sumFrequency] using h

/-- ENNReal Boole upper bound, reused from the ProbLog compilation surface. -/
theorem noisyOrFrequencyENNReal_le_sum {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, p i ≤ 1) :
    1 - Finset.univ.prod (fun i => 1 - p i) ≤ Finset.univ.sum p :=
  noisyOr_le_sum p hp

theorem independent_pair_noisyOr_strictly_below_exclusive_sum_canary :
    noisyOrFrequency (fun _ : Fin 2 => (1 / 2 : ℝ)) = (3 / 4 : ℝ) ∧
      sumFrequency (fun _ : Fin 2 => (1 / 2 : ℝ)) = (1 : ℝ) ∧
        noisyOrFrequency (fun _ : Fin 2 => (1 / 2 : ℝ)) <
          sumFrequency (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  constructor
  · norm_num [noisyOrFrequency]
  · constructor <;> norm_num [sumFrequency, noisyOrFrequency]

theorem duplicate_pair_interval_widens_canary :
    maxFrequency 1 (fun _ : Fin 2 => (1 / 2 : ℝ)) = (1 / 2 : ℝ) ∧
      frechetUnionUpper 1 (fun _ : Fin 2 => (1 / 2 : ℝ)) = (1 : ℝ) ∧
        noisyOrFrequency (fun _ : Fin 2 => (1 / 2 : ℝ)) = (3 / 4 : ℝ) := by
  constructor
  · norm_num [maxFrequency]
  · constructor <;> norm_num [frechetUnionUpper, sumFrequency, noisyOrFrequency]

/-- Independence of events implies independence of their complements. -/
theorem iIndepSet_compl
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} {A : ι → Set Ω}
    (h : ProbabilityTheory.iIndepSet A μ) :
    ProbabilityTheory.iIndepSet (fun i => (A i)ᶜ) μ := by
  have hi : ProbabilityTheory.iIndep (fun i => MeasurableSpace.generateFrom {A i}) μ :=
    (ProbabilityTheory.iIndepSet_iff_iIndep A μ).1 h
  have hle :
      ∀ i, MeasurableSpace.generateFrom {(A i)ᶜ} ≤
        MeasurableSpace.generateFrom {A i} := by
    intro i
    apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact (MeasurableSpace.measurableSet_generateFrom
      (by simp : A i ∈ ({A i} : Set (Set Ω)))).compl
  exact (ProbabilityTheory.iIndepSet_iff_iIndep (fun i => (A i)ᶜ) μ).2
    (ProbabilityTheory.iIndep_of_iIndep_of_le hi hle)

theorem measureReal_iUnion_eq_noisyOrFrequency_of_iIndepSet
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin n → Set Ω)
    (hA : ∀ i, MeasurableSet (A i))
    (hind : ProbabilityTheory.iIndepSet A μ) :
    μ.real (⋃ i, A i) = noisyOrFrequency (fun i => μ.real (A i)) := by
  have hUnionMeas : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  have hcomplInd : ProbabilityTheory.iIndepSet (fun i => (A i)ᶜ) μ :=
    iIndepSet_compl hind
  have hinter := hcomplInd.meas_biInter Finset.univ
  have hcomplUnion : (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ := by
    ext x
    simp
  have hprodReal : μ.real (⋂ i, (A i)ᶜ) =
      Finset.univ.prod (fun i => μ.real ((A i)ᶜ)) := by
    have h := hinter
    simp only [Finset.mem_univ, Set.iInter_true] at h
    simp only [Measure.real, h, ENNReal.toReal_prod]
  have hcomp : μ.real (⋃ i, A i) = 1 - μ.real ((⋃ i, A i)ᶜ) := by
    have hc := probReal_compl_eq_one_sub hUnionMeas (μ := μ)
    linarith
  unfold noisyOrFrequency
  rw [hcomp, hcomplUnion, hprodReal]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [probReal_compl_eq_one_sub (hA i)]

/-! ## Phase 4: confidence remains orthogonal to frequency endpoints -/

noncomputable abbrev plnUnitOddsCoordinate : EvidenceWeightCoordinate :=
  EvidenceWeightCoordinate.plnOddsCoordinate 1 (by norm_num)

noncomputable def finiteConfidenceWeight (c : ℝ) : ℝ :=
  plnUnitOddsCoordinate.decode c

noncomputable def finiteAccumulatedConfidence {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  plnUnitOddsCoordinate.encode (Finset.univ.sum fun i => finiteConfidenceWeight (c i))

theorem finiteConfidenceWeight_eq_odds (c : ℝ) :
    finiteConfidenceWeight c = c / (1 - c) := by
  simp [finiteConfidenceWeight, plnUnitOddsCoordinate,
    EvidenceWeightCoordinate.plnOddsCoordinate]

theorem finiteAccumulatedConfidence_eq_standard {n : ℕ} (c : Fin (n + 1) → ℝ) :
    finiteAccumulatedConfidence c =
      (Finset.univ.sum fun i => c i / (1 - c i)) /
        ((Finset.univ.sum fun i => c i / (1 - c i)) + 1) := by
  simp [finiteAccumulatedConfidence, finiteConfidenceWeight, plnUnitOddsCoordinate,
    EvidenceWeightCoordinate.plnOddsCoordinate]

theorem finiteAccumulatedConfidence_decode_eq_weight_sum {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, c i ∈ Set.Ico (0 : ℝ) 1) :
    plnUnitOddsCoordinate.decode (finiteAccumulatedConfidence c) =
      Finset.univ.sum fun i => finiteConfidenceWeight (c i) := by
  have hnonneg : 0 ≤ Finset.univ.sum fun i => finiteConfidenceWeight (c i) := by
    apply Finset.sum_nonneg
    intro i _
    unfold finiteConfidenceWeight plnUnitOddsCoordinate
    dsimp [EvidenceWeightCoordinate.plnOddsCoordinate]
    simpa using div_nonneg (show 0 ≤ c i by exact (hc i).1)
      (show 0 ≤ 1 - c i by exact le_of_lt (sub_pos.mpr (hc i).2))
  unfold finiteAccumulatedConfidence
  exact plnUnitOddsCoordinate.decode_encode_of_nonneg hnonneg

theorem frechetUnionITV_frequency_endpoints_independent_of_confidence
    {n : ℕ} (frequency : Fin (n + 1) → ℝ)
    (hfrequency : ∀ i, frequency i ∈ Set.Icc (0 : ℝ) 1)
    (confidence₁ confidence₂ : Fin (n + 1) → ℝ≥0∞)
    (hc₁ : ∀ i, confidence₁ i ≤ 1)
    (hc₂ : ∀ i, confidence₂ i ≤ 1) :
    let input₁ : MultiPathInput n :=
      ⟨frequency, hfrequency, confidence₁, hc₁⟩
    let input₂ : MultiPathInput n :=
      ⟨frequency, hfrequency, confidence₂, hc₂⟩
    (frechetUnionITV input₁).lower = (frechetUnionITV input₂).lower ∧
      (frechetUnionITV input₁).upper = (frechetUnionITV input₂).upper := by
  intro input₁ input₂
  constructor <;> rfl

/-! ## Phase 5: selector-facing combinator -/

abbrev MultiPathFrequencySelection := EnvelopeSelector

/-- A selector may choose any certified point in the Frechet envelope and mix it
with the ITV midpoint. -/
def selectedMultiPathFrequency
    (selector : MultiPathFrequencySelection)
    (input : MultiPathInput n) (point : ℝ) : ℝ :=
  selector.select point (frechetUnionITV input).strength

def selectedNoisyOrMultiPathFrequency
    (selector : MultiPathFrequencySelection)
    (input : MultiPathInput n) : ℝ :=
  selectedMultiPathFrequency selector input (noisyOrFrequency input.frequency)

theorem selectedMultiPathFrequency_mem_frechetUnionITV
    (selector : MultiPathFrequencySelection)
    (input : MultiPathInput n) {point : ℝ}
    (hpoint :
      (frechetUnionITV input).lower ≤ point ∧
        point ≤ (frechetUnionITV input).upper) :
    (frechetUnionITV input).lower ≤
        selectedMultiPathFrequency selector input point ∧
      selectedMultiPathFrequency selector input point ≤
        (frechetUnionITV input).upper := by
  unfold selectedMultiPathFrequency
  exact selector.select_point_midpoint_mem_ITV (frechetUnionITV input) hpoint

theorem selectedNoisyOrMultiPathFrequency_mem_frechetUnionITV
    (selector : MultiPathFrequencySelection)
    (input : MultiPathInput n) :
    (frechetUnionITV input).lower ≤
        selectedNoisyOrMultiPathFrequency selector input ∧
      selectedNoisyOrMultiPathFrequency selector input ≤
        (frechetUnionITV input).upper := by
  unfold selectedNoisyOrMultiPathFrequency
  exact selectedMultiPathFrequency_mem_frechetUnionITV selector input
    (noisyOrFrequency_mem_frechetUnionITV input)

def selectedNoisyOrByIndependenceEvent
    (w : BooleanEventWeights) (input : MultiPathInput n) : ℝ :=
  selectedMultiPathFrequency w.toSelector input (noisyOrFrequency input.frequency)

theorem selectedNoisyOrByIndependenceEvent_eq_twoBranchExpectation
    (w : BooleanEventWeights) (input : MultiPathInput n) :
    selectedNoisyOrByIndependenceEvent w input =
      twoBranchExpectation w
        (fun holdsIndependent =>
          if holdsIndependent then noisyOrFrequency input.frequency else (frechetUnionITV input).strength) := by
  unfold selectedNoisyOrByIndependenceEvent selectedMultiPathFrequency
  exact EnvelopeSelector.select_eq_twoBranchExpectation w
    (fun holdsIndependent =>
      if holdsIndependent then noisyOrFrequency input.frequency else (frechetUnionITV input).strength)
    (noisyOrFrequency input.frequency) (frechetUnionITV input).strength (by simp) (by simp)

theorem selectedMeasuredUnion_mem_frechetUnionITV
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (selector : MultiPathFrequencySelection)
    (A : Fin (n + 1) → Set Ω)
    (confidence : Fin (n + 1) → ℝ≥0∞)
    (confidence_le_one : ∀ i, confidence i ≤ 1) :
    let input := MultiPathInput.ofEvents (n := n) μ A confidence confidence_le_one
    (frechetUnionITV input).lower ≤
        selectedMultiPathFrequency selector input (μ.real (⋃ i, A i)) ∧
      selectedMultiPathFrequency selector input (μ.real (⋃ i, A i)) ≤
        (frechetUnionITV input).upper := by
  intro input
  exact selectedMultiPathFrequency_mem_frechetUnionITV selector input
    (measureReal_iUnion_mem_frechetUnionITV_ofEvents
      (μ := μ) A confidence confidence_le_one)

end

end Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet
