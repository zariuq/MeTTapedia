import Mathlib.Probability.Independence.InfinitePi
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet
import Mettapedia.ProbabilityTheory.Common.FrechetBounds
import Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite

/-!
# Multi-path dependency interiors

This module proves the two-path dependency parameterization inside the
multi-path Frechet union envelope and a source-overlap model that computes the
parameter from shared independent Bernoulli sources.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet
open Mettapedia.ProbabilityTheory.Common.FrechetBounds

noncomputable section

abbrev probLogBernoulliMeasure :=
  Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite.bernoulliMeasure

abbrev infiniteFactMeasure :=
  Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite.infiniteFactMeasure

/-! ## T-A: two-path dependency interval -/

/-- Two-event real inclusion-exclusion, derived from Mathlib's measure theorem. -/
theorem pair_union_measureReal_eq_add_sub_inter
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B : Set Ω} (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ.real (A ∪ B) = μ.real A + μ.real B - μ.real (A ∩ B) := by
  have h := measureReal_union_add_inter hB (μ := μ) (s := A)
  linarith

/-- The intersection parameter has the usual binary Frechet bounds. -/
theorem pair_intersection_measureReal_mem_frechet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ.real (A ∩ B) ∈
      Set.Icc (max 0 (μ.real A + μ.real B - 1))
        (min (μ.real A) (μ.real B)) := by
  exact ⟨frechet_lower_bound_real μ A B hA hB,
    frechet_upper_bound_real μ A B⟩

theorem pair_dependency_intersection_interval_nonempty
    {f1 f2 : ℝ}
    (hf1 : f1 ∈ Set.Icc (0 : ℝ) 1) (hf2 : f2 ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (f1 + f2 - 1) ≤ min f1 f2 := by
  apply max_le
  · exact le_min hf1.1 hf2.1
  · apply le_min <;> linarith [hf1.2, hf2.2]

theorem pair_dependency_unionValue_antitoneOn
    {f1 f2 : ℝ}
    (_hf1 : f1 ∈ Set.Icc (0 : ℝ) 1) (_hf2 : f2 ∈ Set.Icc (0 : ℝ) 1) :
    AntitoneOn (fun c => f1 + f2 - c)
      (Set.Icc (max 0 (f1 + f2 - 1)) (min f1 f2)) := by
  intro a _ha b _hb hab
  dsimp
  linarith

theorem pair_dependency_unionValue_mapsTo
    {f1 f2 : ℝ}
    (_hf1 : f1 ∈ Set.Icc (0 : ℝ) 1) (_hf2 : f2 ∈ Set.Icc (0 : ℝ) 1) :
    Set.MapsTo (fun c => f1 + f2 - c)
      (Set.Icc (max 0 (f1 + f2 - 1)) (min f1 f2))
      (Set.Icc (max f1 f2) (min 1 (f1 + f2))) := by
  intro c hc
  constructor
  · apply max_le
    · have hc2 : c ≤ f2 := le_trans hc.2 (min_le_right _ _)
      linarith
    · have hc1 : c ≤ f1 := le_trans hc.2 (min_le_left _ _)
      linarith
  · apply le_min
    · have hlow : f1 + f2 - 1 ≤ c := le_trans (le_max_right _ _) hc.1
      linarith
    · have hnonneg : 0 ≤ c := le_trans (le_max_left _ _) hc.1
      linarith

theorem pair_dependency_unionValue_inverse_mapsTo
    {f1 f2 : ℝ}
    (_hf1 : f1 ∈ Set.Icc (0 : ℝ) 1) (_hf2 : f2 ∈ Set.Icc (0 : ℝ) 1) :
    Set.MapsTo (fun u => f1 + f2 - u)
      (Set.Icc (max f1 f2) (min 1 (f1 + f2)))
      (Set.Icc (max 0 (f1 + f2 - 1)) (min f1 f2)) := by
  intro u hu
  constructor
  · apply max_le
    · have husum : u ≤ f1 + f2 := le_trans hu.2 (min_le_right _ _)
      linarith
    · have hu1 : u ≤ 1 := le_trans hu.2 (min_le_left _ _)
      linarith
  · apply le_min
    · have huf2 : f2 ≤ u := le_trans (le_max_right _ _) hu.1
      linarith
    · have huf1 : f1 ≤ u := le_trans (le_max_left _ _) hu.1
      linarith

/-- The dependency parameter sweeps the whole two-path union envelope. -/
theorem pair_dependency_unionValue_bijOn
    {f1 f2 : ℝ}
    (hf1 : f1 ∈ Set.Icc (0 : ℝ) 1) (hf2 : f2 ∈ Set.Icc (0 : ℝ) 1) :
    Set.BijOn (fun c => f1 + f2 - c)
      (Set.Icc (max 0 (f1 + f2 - 1)) (min f1 f2))
      (Set.Icc (max f1 f2) (min 1 (f1 + f2))) := by
  refine ⟨pair_dependency_unionValue_mapsTo hf1 hf2, ?_, ?_⟩
  · intro a ha b hb h
    linarith
  · intro u hu
    refine ⟨f1 + f2 - u, pair_dependency_unionValue_inverse_mapsTo hf1 hf2 hu, ?_⟩
    ring

theorem pair_dependency_lower_c_maps_to_frechet_upper (f1 f2 : ℝ) :
    f1 + f2 - max 0 (f1 + f2 - 1) = min 1 (f1 + f2) := by
  by_cases h : f1 + f2 - 1 ≤ 0
  · rw [max_eq_left h]
    rw [min_eq_right]
    · ring
    · linarith
  · have hpos : 0 ≤ f1 + f2 - 1 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hpos]
    rw [min_eq_left]
    · ring
    · linarith

theorem pair_dependency_upper_c_maps_to_max (f1 f2 : ℝ) :
    f1 + f2 - min f1 f2 = max f1 f2 := by
  by_cases h : f1 ≤ f2
  · rw [min_eq_left h, max_eq_right h]
    ring
  · have hle : f2 ≤ f1 := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right hle, max_eq_left hle]
    ring

theorem pair_dependency_independent_c_maps_to_noisyOr
    {f1 f2 : ℝ}
    (_hf1 : f1 ∈ Set.Icc (0 : ℝ) 1) (_hf2 : f2 ∈ Set.Icc (0 : ℝ) 1) :
    f1 + f2 - f1 * f2 =
      noisyOrFrequency (fun i : Fin 2 => if i = 0 then f1 else f2) := by
  norm_num [noisyOrFrequency]
  ring

theorem pair_dependency_three_tenths_canary :
    ((3 / 10 : ℝ) + (3 / 10 : ℝ) - 0 = (3 / 5 : ℝ)) ∧
      ((3 / 10 : ℝ) + (3 / 10 : ℝ) - (9 / 100 : ℝ) = (51 / 100 : ℝ)) ∧
        ((3 / 10 : ℝ) + (3 / 10 : ℝ) - (3 / 10 : ℝ) = (3 / 10 : ℝ)) := by
  norm_num

theorem pair_dependency_three_tenths_half_not_mem_intersection_interval :
    ¬ ((1 / 2 : ℝ) ∈
      Set.Icc (max 0 ((3 / 10 : ℝ) + (3 / 10 : ℝ) - 1))
        (min (3 / 10 : ℝ) (3 / 10 : ℝ))) := by
  norm_num

/-! ## T-B: source-overlap model -/

def sourceHolds (s : ℕ) : Set (ℕ → Bool) :=
  {world | world s = true}

/-- A path supported by a finite source set succeeds when every source holds. -/
def sourceEvent (S : Finset ℕ) : Set (ℕ → Bool) :=
  Set.pi S (fun _ => ({true} : Set Bool))

theorem sourceEvent_measurable (S : Finset ℕ) :
    MeasurableSet (sourceEvent S) := by
  unfold sourceEvent
  exact MeasurableSet.pi (Finset.countable_toSet S)
    (by intro _ _; exact measurableSet_singleton true)

set_option linter.deprecated false in
theorem probLogBernoulliMeasure_true (p : ℝ≥0) (hp : p ≤ 1) :
    probLogBernoulliMeasure p hp ({true} : Set Bool) = (p : ℝ≥0∞) := by
  rw [probLogBernoulliMeasure,
    Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite.bernoulliMeasure]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true)]
  simp [PMF.bernoulli_apply]

theorem sourceEvent_measure
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1) (S : Finset ℕ) :
    infiniteFactMeasure p hp (sourceEvent S) =
      ∏ s ∈ S, (p s : ℝ≥0∞) := by
  unfold sourceEvent infiniteFactMeasure
  rw [Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite.infiniteFactMeasure_cylinder]
  · apply Finset.prod_congr rfl
    intro i _hi
    exact probLogBernoulliMeasure_true (p i) (hp i)
  · intro _ _
    exact measurableSet_singleton true

theorem sourceEvent_measureReal
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1) (S : Finset ℕ) :
    (infiniteFactMeasure p hp).real (sourceEvent S) =
      ∏ s ∈ S, ((p s : ℝ≥0) : ℝ) := by
  unfold Measure.real
  rw [sourceEvent_measure p hp S]
  rw [ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro _ _
  simp

theorem sourceEvent_inter (S1 S2 : Finset ℕ) :
    sourceEvent S1 ∩ sourceEvent S2 = sourceEvent (S1 ∪ S2) := by
  ext world
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    simp [sourceEvent] at h1 h2 ⊢
    intro i hi
    rcases hi with hi | hi
    · exact h1 i hi
    · exact h2 i hi
  · intro h
    constructor
    · simp [sourceEvent] at h ⊢
      intro i hi
      exact h i (Or.inl hi)
    · simp [sourceEvent] at h ⊢
      intro i hi
      exact h i (Or.inr hi)

theorem sourcePair_intersection_measureReal
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    (S1 S2 : Finset ℕ) :
    (infiniteFactMeasure p hp).real
        (sourceEvent S1 ∩ sourceEvent S2) =
      ∏ s ∈ S1 ∪ S2, ((p s : ℝ≥0) : ℝ) := by
  rw [sourceEvent_inter]
  exact sourceEvent_measureReal p hp (S1 ∪ S2)

theorem sourcePair_prod_union_inter
    (q : ℕ → ℝ) (S1 S2 : Finset ℕ) :
    (∏ s ∈ S1 ∪ S2, q s) * (∏ s ∈ S1 ∩ S2, q s) =
      (∏ s ∈ S1, q s) * (∏ s ∈ S2, q s) := by
  exact Finset.prod_union_inter

theorem sourcePair_disjoint_c_eq_mul
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    {S1 S2 : Finset ℕ} (hdisj : Disjoint S1 S2) :
    (infiniteFactMeasure p hp).real
        (sourceEvent S1 ∩ sourceEvent S2) =
      (infiniteFactMeasure p hp).real (sourceEvent S1) *
        (infiniteFactMeasure p hp).real (sourceEvent S2) := by
  rw [sourcePair_intersection_measureReal, sourceEvent_measureReal,
    sourceEvent_measureReal]
  rw [← Finset.prod_union hdisj]

theorem sourcePair_union_eq_add_sub_intersection
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    (S1 S2 : Finset ℕ) :
    (infiniteFactMeasure p hp).real
        (sourceEvent S1 ∪ sourceEvent S2) =
      (infiniteFactMeasure p hp).real (sourceEvent S1) +
        (infiniteFactMeasure p hp).real (sourceEvent S2) -
          (infiniteFactMeasure p hp).real
            (sourceEvent S1 ∩ sourceEvent S2) := by
  exact pair_union_measureReal_eq_add_sub_inter
    (infiniteFactMeasure p hp)
    (sourceEvent_measurable S1) (sourceEvent_measurable S2)

/-- The weld theorem: the two-path union point is selected by the measured
overlap product, not by an independent new operator. -/
theorem sourcePair_union_eq_add_sub_overlap
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    (S1 S2 : Finset ℕ) :
    (infiniteFactMeasure p hp).real
        (sourceEvent S1 ∪ sourceEvent S2) =
      (infiniteFactMeasure p hp).real (sourceEvent S1) +
        (infiniteFactMeasure p hp).real (sourceEvent S2) -
          (∏ s ∈ S1 ∪ S2, ((p s : ℝ≥0) : ℝ)) := by
  rw [sourcePair_union_eq_add_sub_intersection p hp S1 S2,
    sourcePair_intersection_measureReal p hp S1 S2]

theorem sourcePair_disjoint_union_eq_noisyOr
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    {S1 S2 : Finset ℕ} (hdisj : Disjoint S1 S2) :
    (infiniteFactMeasure p hp).real
        (sourceEvent S1 ∪ sourceEvent S2) =
      noisyOrFrequency
        (fun i : Fin 2 =>
          if i = 0 then
            (infiniteFactMeasure p hp).real (sourceEvent S1)
          else
            (infiniteFactMeasure p hp).real (sourceEvent S2)) := by
  rw [sourcePair_union_eq_add_sub_intersection p hp S1 S2,
    sourcePair_disjoint_c_eq_mul p hp hdisj]
  exact pair_dependency_independent_c_maps_to_noisyOr
    (measureReal_mem_unit_of_probability
      (infiniteFactMeasure p hp) (sourceEvent S1))
    (measureReal_mem_unit_of_probability
      (infiniteFactMeasure p hp) (sourceEvent S2))

theorem sourceEvent_subset_of_subset {S1 S2 : Finset ℕ} (h : S1 ⊆ S2) :
    sourceEvent S2 ⊆ sourceEvent S1 := by
  intro world hw
  simp [sourceEvent] at hw ⊢
  intro s hs
  exact hw s (h hs)

theorem sourceEvent_union_eq_left_of_subset {S1 S2 : Finset ℕ} (h : S1 ⊆ S2) :
    sourceEvent S1 ∪ sourceEvent S2 = sourceEvent S1 := by
  exact Set.union_eq_left.mpr (sourceEvent_subset_of_subset h)

theorem sourcePair_subset_union_eq_max
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    {S1 S2 : Finset ℕ} (h : S1 ⊆ S2) :
    (infiniteFactMeasure p hp).real
        (sourceEvent S1 ∪ sourceEvent S2) =
      max ((infiniteFactMeasure p hp).real (sourceEvent S1))
        ((infiniteFactMeasure p hp).real (sourceEvent S2)) := by
  rw [sourceEvent_union_eq_left_of_subset h]
  rw [max_eq_left]
  exact measureReal_mono (μ := infiniteFactMeasure p hp)
    (sourceEvent_subset_of_subset h)

theorem sourcePair_equal_union_eq_max
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    {S1 S2 : Finset ℕ} (hEq : S1 = S2) :
    (infiniteFactMeasure p hp).real
        (sourceEvent S1 ∪ sourceEvent S2) =
      max ((infiniteFactMeasure p hp).real (sourceEvent S1))
        ((infiniteFactMeasure p hp).real (sourceEvent S2)) := by
  exact sourcePair_subset_union_eq_max p hp (by intro s hs; simpa [hEq] using hs)

theorem sourcePair_same_source_not_noisyOr_canary :
    let p : ℕ → ℝ≥0 := fun _ => (1 / 2 : ℝ≥0)
    let hp : ∀ s, p s ≤ 1 := by intro _; norm_num
    (infiniteFactMeasure p hp).real
        (sourceEvent {0} ∪ sourceEvent {0}) = (1 / 2 : ℝ) ∧
      noisyOrFrequency (fun _ : Fin 2 => (1 / 2 : ℝ)) = (3 / 4 : ℝ) := by
  intro p hp
  constructor
  · rw [sourcePair_equal_union_eq_max p hp (hEq := rfl)]
    rw [sourceEvent_measureReal]
    norm_num
  · norm_num [noisyOrFrequency]

/-! ## T-C: bounded n-path source-overlap facts -/

theorem sourceEvents_iInter_eq_sourceEvent_biUnion
    {ι : Type*} [DecidableEq ι] (T : Finset ι) (S : ι → Finset ℕ) :
    (Set.iInter fun i => Set.iInter fun _ : i ∈ T => sourceEvent (S i)) =
      sourceEvent (T.biUnion S) := by
  ext world
  constructor
  · intro h
    rw [Set.mem_iInter] at h
    change ∀ s, s ∈ (T.biUnion S : Finset ℕ) → world s ∈ ({true} : Set Bool)
    intro s hs
    rcases Finset.mem_biUnion.mp hs with ⟨i, hiT, his⟩
    have hi : world ∈ sourceEvent (S i) := by
      have h' := h i
      rw [Set.mem_iInter] at h'
      exact h' hiT
    change ∀ t, t ∈ S i → world t ∈ ({true} : Set Bool) at hi
    exact hi s his
  · intro h
    change ∀ s, s ∈ (T.biUnion S : Finset ℕ) → world s ∈ ({true} : Set Bool) at h
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hiT
    change ∀ s, s ∈ S i → world s ∈ ({true} : Set Bool)
    intro s his
    exact h s (Finset.mem_biUnion.mpr ⟨i, hiT, his⟩)

theorem sourceEvents_iIndepSet_of_pairwiseDisjoint_supports
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    {n : ℕ} (S : Fin n → Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ProbabilityTheory.iIndepSet
      (fun i => sourceEvent (S i)) (infiniteFactMeasure p hp) := by
  apply (ProbabilityTheory.iIndepSet_iff_meas_biInter
    (μ := infiniteFactMeasure p hp) (f := fun i => sourceEvent (S i))
    (fun i => sourceEvent_measurable (S i))).2
  intro T
  rw [sourceEvents_iInter_eq_sourceEvent_biUnion]
  rw [sourceEvent_measure]
  rw [Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro i _hi
    rw [sourceEvent_measure]
  · intro i _hi j _hj hij
    exact hdisj hij

theorem sourceEvents_pairwiseDisjoint_union_eq_noisyOrFrequency
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    {n : ℕ} (S : Fin n → Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j))) :
    (infiniteFactMeasure p hp).real (Set.iUnion fun i => sourceEvent (S i)) =
      noisyOrFrequency
        (fun i => (infiniteFactMeasure p hp).real (sourceEvent (S i))) := by
  exact measureReal_iUnion_eq_noisyOrFrequency_of_iIndepSet
    (μ := infiniteFactMeasure p hp)
    (fun i => sourceEvent (S i))
    (fun i => sourceEvent_measurable (S i))
    (sourceEvents_iIndepSet_of_pairwiseDisjoint_supports p hp S hdisj)

theorem sourceEvents_iUnion_eq_sourceEvent_zero_of_allEqual
    {n : ℕ} (S : Fin (n + 1) → Finset ℕ)
    (hEq : ∀ i j, S i = S j) :
    (Set.iUnion fun i => sourceEvent (S i)) = sourceEvent (S 0) := by
  ext world
  constructor
  · intro h
    rw [Set.mem_iUnion] at h
    rcases h with ⟨i, hi⟩
    simpa [hEq i 0] using hi
  · intro h
    rw [Set.mem_iUnion]
    exact ⟨0, h⟩

theorem sourceEvents_allEqual_union_eq_maxFrequency
    (p : ℕ → ℝ≥0) (hp : ∀ s, p s ≤ 1)
    {n : ℕ} (S : Fin (n + 1) → Finset ℕ)
    (hEq : ∀ i j, S i = S j) :
    (infiniteFactMeasure p hp).real (Set.iUnion fun i => sourceEvent (S i)) =
      maxFrequency n
        (fun i => (infiniteFactMeasure p hp).real (sourceEvent (S i))) := by
  rw [sourceEvents_iUnion_eq_sourceEvent_zero_of_allEqual S hEq]
  unfold maxFrequency
  rw [Finset.sup'_eq_of_forall]
  intro i _hi
  rw [hEq i 0]

/-!
For three or more paths, pairwise overlap data alone does not determine the
union probability: the triple intersection remains an independent degree of
freedom. This module therefore proves only the n-path landmarks above, not a
pairwise-data-only interior sweep theorem.
-/

end

end Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency
