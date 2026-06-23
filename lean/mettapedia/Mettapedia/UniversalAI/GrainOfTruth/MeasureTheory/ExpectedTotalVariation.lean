import Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PrefixMeasure
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.TotalVariation
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ValueContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Expected Total Variation Distance (Leike, Thesis Ch. 5)

This file starts the “learning theory” layer used in Leike’s asymptotic-optimality proof for
Thompson sampling:

* define the (conditional) total-variation distance `D_m(ρ^π, ξ^π | a e_{<t})`,
* define its posterior expectation `F_m^π(a e_{<t})`.

We work on finite prefix types `Fin n → Step`, so conditional laws can be expressed by restricting
and renormalizing the finite-dimensional marginals.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ExpectedTotalVariation

open scoped BigOperators
open MeasureTheory ProbabilityTheory

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PrefixMeasure
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.TotalVariation
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ValueContinuity
open Mettapedia.UniversalAI.ReflectiveOracles

open scoped ENNReal NNReal MeasureTheory

/-! ## Generic conditioning on finite prefix spaces -/

noncomputable def headSet (t m : ℕ) (p : Fin t → Step) : Set (Fin (t + m) → Step) :=
  {q | headPrefix (t := t) (m := m) q = p}

/-! ### Joining a head and tail prefix -/

noncomputable def appendPrefix {t m : ℕ} (p : Fin t → Step) (q : Fin m → Step) : Fin (t + m) → Step :=
  fun i =>
    if h : i.val < t then
      p ⟨i.val, h⟩
    else
      q ⟨i.val - t, (Nat.sub_lt_iff_lt_add (Nat.le_of_not_gt h)).2 (by
        exact lt_of_lt_of_eq i.isLt (Nat.add_comm t m))⟩

theorem headPrefix_appendPrefix {t m : ℕ} (p : Fin t → Step) (q : Fin m → Step) :
    headPrefix (t := t) (m := m) (appendPrefix (t := t) (m := m) p q) = p := by
  funext i
  simp [headPrefix, appendPrefix]

theorem tailPrefix_appendPrefix {t m : ℕ} (p : Fin t → Step) (q : Fin m → Step) :
    tailPrefix (t := t) (m := m) (appendPrefix (t := t) (m := m) p q) = q := by
  funext j
  have hlt : ¬t + j.val < t := by
    exact not_lt_of_ge (Nat.le_add_right t j.val)
  have hsub : t + j.val - t = j.val := by
    exact Nat.add_sub_cancel_left t j.val
  simp [tailPrefix, appendPrefix, hlt, hsub]

theorem appendPrefix_headPrefix_tailPrefix {t m : ℕ} (r : Fin (t + m) → Step) :
    appendPrefix (t := t) (m := m) (headPrefix (t := t) (m := m) r) (tailPrefix (t := t) (m := m) r) = r := by
  funext i
  by_cases h : i.val < t
  · simp [appendPrefix, headPrefix, h]
  · have hle : t ≤ i.val := Nat.le_of_not_gt h
    have hsub_lt : i.val - t < m :=
      (Nat.sub_lt_iff_lt_add hle).2 (lt_of_lt_of_eq i.isLt (Nat.add_comm t m))
    have hsub : t + (i.val - t) = i.val := Nat.add_sub_of_le hle
    have hi : (⟨t + (i.val - t), Nat.add_lt_add_left hsub_lt t⟩ : Fin (t + m)) = i := by
      ext
      simp [hsub]
    simp [appendPrefix, tailPrefix, h, hi]

theorem headSet_inter_tailPrefix_preimage_singleton {t m : ℕ} (p : Fin t → Step) (q : Fin m → Step) :
    headSet t m p ∩ tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step)) =
      ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
  classical
  ext r
  constructor
  · rintro ⟨hrHead, hrTail⟩
    have hrHead' : headPrefix (t := t) (m := m) r = p := hrHead
    have hrTail' : tailPrefix (t := t) (m := m) r = q := by
      -- `hrTail : r ∈ tailPrefix ⁻¹' {q}`.
      have : tailPrefix (t := t) (m := m) r ∈ ({q} : Set (Fin m → Step)) :=
        (Set.mem_preimage).1 hrTail
      exact Set.mem_singleton_iff.1 this
    -- Rebuild `r` from its head and tail.
    have : appendPrefix (t := t) (m := m) p q = r := by
      -- Use the reconstruction lemma and the equalities above.
      calc
        appendPrefix (t := t) (m := m) p q
            = appendPrefix (t := t) (m := m) (headPrefix (t := t) (m := m) r)
                (tailPrefix (t := t) (m := m) r) := by
                  simp [hrHead', hrTail']
        _ = r := appendPrefix_headPrefix_tailPrefix (t := t) (m := m) r
    exact Set.mem_singleton_iff.2 this.symm
  · intro hr
    have hr' : r = appendPrefix (t := t) (m := m) p q := by
      exact Set.mem_singleton_iff.1 hr
    subst hr'
    refine ⟨?_, ?_⟩
    · -- head part
      simp [headSet, headPrefix_appendPrefix]
    · -- tail part
      simp [tailPrefix_appendPrefix]

noncomputable def conditionalTailMeasure (t m : ℕ) (μ : MeasureTheory.Measure (Fin (t + m) → Step))
    (p : Fin t → Step) : MeasureTheory.Measure (Fin m → Step) :=
  let A : Set (Fin (t + m) → Step) := headSet t m p
  let denom : ℝ≥0∞ := μ A
  if denom = 0 then
    MeasureTheory.Measure.dirac default
  else
    ((denom⁻¹) • (μ.restrict A)).map (tailPrefix (t := t) (m := m))

instance conditionalTailMeasure_isProbability (t m : ℕ) (μ : MeasureTheory.Measure (Fin (t + m) → Step))
    [MeasureTheory.IsFiniteMeasure μ] (p : Fin t → Step) :
    MeasureTheory.IsProbabilityMeasure (conditionalTailMeasure (t := t) (m := m) μ p) := by
  classical
  set A : Set (Fin (t + m) → Step) := headSet t m p
  by_cases h0 : μ A = 0
  · constructor
    simp [conditionalTailMeasure, A, h0]
  · have hA_ne_top : μ A ≠ ∞ := by
      have hle : μ A ≤ μ Set.univ :=
        MeasureTheory.measure_mono (show A ⊆ Set.univ from Set.subset_univ _)
      exact (lt_of_le_of_lt hle (MeasureTheory.measure_lt_top μ Set.univ)).ne
    constructor
    -- Compute the mass on `univ` directly.
    have :
        (conditionalTailMeasure (t := t) (m := m) μ p) Set.univ = 1 := by
      simp [conditionalTailMeasure, A, h0, MeasureTheory.Measure.map_apply, tailPrefix_measurable,
        MeasureTheory.Measure.smul_apply, smul_eq_mul, MeasureTheory.Measure.restrict_apply]
      simpa [mul_comm] using (ENNReal.mul_inv_cancel h0 hA_ne_top)
    simpa using this

/-! ### Product rule on singleton tails -/

theorem measure_headSet_mul_conditionalTailMeasure_singleton (t m : ℕ)
    (μ : MeasureTheory.Measure (Fin (t + m) → Step)) [MeasureTheory.IsFiniteMeasure μ]
    (p : Fin t → Step) (q : Fin m → Step) :
    μ (headSet t m p) *
        conditionalTailMeasure (t := t) (m := m) μ p ({q} : Set (Fin m → Step)) =
      μ ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
  classical
  set A : Set (Fin (t + m) → Step) := headSet t m p
  set denom : ℝ≥0∞ := μ A
  by_cases hden : denom = 0
  · -- Then `μ A = 0`, and the singleton is contained in `A`, so it also has measure `0`.
    have hsub :
        ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) ⊆ A := by
      intro r hr
      have hr' : r = appendPrefix (t := t) (m := m) p q := by
        simpa [Set.mem_singleton_iff] using hr
      subst hr'
      simp [A, headSet, headPrefix_appendPrefix]
    have hμ_singleton : μ ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) = 0 := by
      have hle : μ ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) ≤ μ A :=
        MeasureTheory.measure_mono hsub
      exact le_antisymm (le_trans hle (by simp [denom, A, hden])) zero_le
    simp [conditionalTailMeasure, A, denom, hden, hμ_singleton]
  · -- The regular conditioning case: multiply out the scalar and unfold the map.
    have hden_ne_top : denom ≠ ∞ :=
      MeasureTheory.measure_ne_top μ A
    -- Evaluate `conditionalTailMeasure` on a singleton.
    have h_apply :
        conditionalTailMeasure (t := t) (m := m) μ p ({q} : Set (Fin m → Step)) =
          denom⁻¹ * μ (A ∩ tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step))) := by
      have hmeas :
          MeasurableSet (tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step))) := by
        exact (tailPrefix_measurable (t := t) (m := m)) (by simp)
      have h_restrict :
          (μ.restrict A) (tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step))) =
            μ (A ∩ tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step))) := by
        -- `restrict` introduces an intersection on the right; swap it into the desired order.
        simp [MeasureTheory.Measure.restrict_apply, hmeas, Set.inter_comm]
      -- Unfold conditioning, map, and then rewrite the restricted mass using `h_restrict`.
      simp [conditionalTailMeasure, A, denom, hden, MeasureTheory.Measure.map_apply,
        tailPrefix_measurable, MeasureTheory.Measure.smul_apply, smul_eq_mul, h_restrict]
    -- Identify the intersection as the corresponding singleton.
    have h_inter :
        A ∩ tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step)) =
          ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
      simpa [A] using (headSet_inter_tailPrefix_preimage_singleton (t := t) (m := m) p q)
    calc
      μ A * conditionalTailMeasure (t := t) (m := m) μ p ({q} : Set (Fin m → Step))
          = denom * (denom⁻¹ * μ (A ∩ tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step)))) := by
              simp [denom, h_apply]
      _ = (denom * denom⁻¹) * μ (A ∩ tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step))) := by
              ring
      _ = μ (A ∩ tailPrefix (t := t) (m := m) ⁻¹' ({q} : Set (Fin m → Step))) := by
              simp [ENNReal.mul_inv_cancel hden hden_ne_top]
      _ = μ ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
              simp [h_inter]

theorem measureReal_headSet_mul_conditionalTailMeasure_singleton (t m : ℕ)
    (μ : MeasureTheory.Measure (Fin (t + m) → Step)) [MeasureTheory.IsFiniteMeasure μ]
    (p : Fin t → Step) (q : Fin m → Step) :
    μ.real (headSet t m p) *
        (conditionalTailMeasure (t := t) (m := m) μ p).real ({q} : Set (Fin m → Step)) =
      μ.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
  classical
  have hENN :=
    measure_headSet_mul_conditionalTailMeasure_singleton (t := t) (m := m) (μ := μ) p q
  have hENN_real := congrArg ENNReal.toReal hENN
  have hμ_ne_top : μ (headSet t m p) ≠ ∞ :=
    MeasureTheory.measure_ne_top μ (headSet t m p)
  haveI : MeasureTheory.IsFiniteMeasure (conditionalTailMeasure (t := t) (m := m) μ p) := inferInstance
  have hcond_ne_top :
      conditionalTailMeasure (t := t) (m := m) μ p ({q} : Set (Fin m → Step)) ≠ ∞ :=
    MeasureTheory.measure_ne_top (conditionalTailMeasure (t := t) (m := m) μ p) ({q} : Set (Fin m → Step))
  have happ_ne_top :
      μ ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) ≠ ∞ :=
    MeasureTheory.measure_ne_top μ ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step))
  -- Unfold `Measure.real` and split `toReal` across products.
  simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul, hμ_ne_top, hcond_ne_top, happ_ne_top, mul_assoc,
    mul_left_comm, mul_comm] using hENN_real

/-! ## Total variation distance on finite spaces -/

noncomputable def tvDistanceReal {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : MeasureTheory.Measure α) : ℝ :=
  (1 / 2 : ℝ) * l1DistanceReal μ ν

theorem tvDistanceReal_nonneg {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : MeasureTheory.Measure α) : 0 ≤ tvDistanceReal μ ν := by
  classical
  have hhalf : 0 ≤ (1 / 2 : ℝ) :=
    div_nonneg zero_le_one (le_of_lt (show (0 : ℝ) < 2 from two_pos))
  have hl1 : 0 ≤ l1DistanceReal μ ν := by
    dsimp [l1DistanceReal]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  simpa [tvDistanceReal] using mul_nonneg hhalf hl1

theorem tvDistanceReal_le_one_of_isProbability {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν] : tvDistanceReal μ ν ≤ 1 := by
  have hhalf : 0 ≤ (1 / 2 : ℝ) :=
    div_nonneg zero_le_one (le_of_lt (show (0 : ℝ) < 2 from two_pos))
  have hl1 : l1DistanceReal μ ν ≤ 2 :=
    l1DistanceReal_le_two_of_isProbability (μ := μ) (ν := ν)
  calc
    tvDistanceReal μ ν = (1 / 2 : ℝ) * l1DistanceReal μ ν := rfl
    _ ≤ (1 / 2 : ℝ) * 2 := mul_le_mul_of_nonneg_left hl1 hhalf
    _ = 1 := by simp

/-! ## `D_m` and `F_m` (prefix-based versions) -/

noncomputable def D_m (t m : ℕ) (ρ ξ : MeasureTheory.Measure (Fin (t + m) → Step)) (p : Fin t → Step) : ℝ :=
  tvDistanceReal
    (conditionalTailMeasure (t := t) (m := m) ρ p)
    (conditionalTailMeasure (t := t) (m := m) ξ p)

noncomputable def prefixMeasureMixtureWithPolicy (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (n : ℕ) :
    MeasureTheory.Measure (Fin n → Step) :=
  (mixtureMeasureWithPolicy O M prior envs π h_stoch).map (truncate n)

instance prefixMeasureMixtureWithPolicy_isFinite (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (n : ℕ) :
    MeasureTheory.IsFiniteMeasure (prefixMeasureMixtureWithPolicy O M prior envs π h_stoch n) := by
  dsimp [prefixMeasureMixtureWithPolicy]
  infer_instance

/-! ### Compatibility of `t`- and `(t+m)`-prefix marginals -/

theorem prefixMeasureWithPolicy_map_headPrefix (μ : Environment) (π : Agent) (h_stoch : isStochastic μ)
    (t m : ℕ) :
    (prefixMeasureWithPolicy μ π h_stoch (t + m)).map (headPrefix (t := t) (m := m)) =
      prefixMeasureWithPolicy μ π h_stoch t := by
  classical
  -- Both sides are pushforwards of the same trajectory law under two equivalent truncations.
  have hcomp :
      (headPrefix (t := t) (m := m) ∘ truncate (t + m)) = truncate t := by
    funext traj
    simpa using (headPrefix_truncate (t := t) (m := m) traj)
  -- `map_map` turns the double pushforward into the pushforward along the composition.
  simpa [prefixMeasureWithPolicy, hcomp] using
    (MeasureTheory.Measure.map_map (μ := environmentMeasureWithPolicy μ π h_stoch)
      (hg := headPrefix_measurable (t := t) (m := m)) (hf := truncate_measurable (t + m)))

theorem prefixMeasureMixtureWithPolicy_map_headPrefix (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (t m : ℕ) :
    (prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)).map (headPrefix (t := t) (m := m)) =
      prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t := by
  classical
  have hcomp :
      (headPrefix (t := t) (m := m) ∘ truncate (t + m)) = truncate t := by
    funext traj
    simpa using (headPrefix_truncate (t := t) (m := m) traj)
  simpa [prefixMeasureMixtureWithPolicy, hcomp] using
    (MeasureTheory.Measure.map_map (μ := mixtureMeasureWithPolicy O M prior envs π h_stoch)
      (hg := headPrefix_measurable (t := t) (m := m)) (hf := truncate_measurable (t + m)))

/-! ### Posterior cancellation on prefix atoms -/

theorem bayesianPosteriorWeight_mul_prefixMeasureMixtureWithPolicy_singleton (O : Oracle)
    (M : ReflectiveEnvironmentClass O) (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ν_idx : EnvironmentIndex) (t : ℕ)
    (p : Fin t → Step) :
    bayesianPosteriorWeight O M prior envs ν_idx (prefixToHistory t p) *
        prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t ({p} : Set (Fin t → Step)) =
      prior.weight ν_idx *
        prefixMeasureWithPolicy (envs ν_idx) π (h_stoch ν_idx) t ({p} : Set (Fin t → Step)) := by
  classical
  set h : History := prefixToHistory t p
  have h_wf : h.wellFormed := by
    dsimp [h]
    exact Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.prefixToHistory_wellFormed t p
  have h_complete : Even h.length := by
    dsimp [h]
    exact Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.prefixToHistory_even t p
  have h_pre :
      truncate t ⁻¹' ({p} : Set (Fin t → Step)) = cylinderSet h := by
    simpa [h] using
      (Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.truncate_preimage_singleton_eq_cylinderSet
        t p)
  -- Reduce to the cylinder cancellation lemma.
  simpa [prefixMeasureMixtureWithPolicy, prefixMeasureWithPolicy, MeasureTheory.Measure.map_apply, truncate_measurable,
    h_pre, h] using
    (Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PolicyFactorization.bayesianPosteriorWeight_mul_mixtureMeasureWithPolicy_cylinderSet
        (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) (ν_idx := ν_idx) (h := h)
        (h_wf := h_wf) (h_complete := h_complete))

noncomputable def D_m_env (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (ρ_idx : EnvironmentIndex) (t m : ℕ) (p : Fin t → Step) : ℝ :=
  D_m (t := t) (m := m)
    (prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) (t + m))
    (prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m))
    p

noncomputable def F_m (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (t m : ℕ) (p : Fin t → Step) : ℝ :=
  ∑' ρ_idx : EnvironmentIndex,
    (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
      D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p

/-! ## Basic bounds for `D_m` and `F_m` -/

theorem D_m_nonneg (t m : ℕ) (ρ ξ : MeasureTheory.Measure (Fin (t + m) → Step)) (p : Fin t → Step) :
    0 ≤ D_m (t := t) (m := m) ρ ξ p := by
  simpa [D_m] using
    (tvDistanceReal_nonneg
      (μ := conditionalTailMeasure (t := t) (m := m) ρ p)
      (ν := conditionalTailMeasure (t := t) (m := m) ξ p))

theorem D_m_le_one (t m : ℕ) (ρ ξ : MeasureTheory.Measure (Fin (t + m) → Step))
    [MeasureTheory.IsFiniteMeasure ρ] [MeasureTheory.IsFiniteMeasure ξ] (p : Fin t → Step) :
    D_m (t := t) (m := m) ρ ξ p ≤ 1 := by
  simpa [D_m] using
    (tvDistanceReal_le_one_of_isProbability
      (μ := conditionalTailMeasure (t := t) (m := m) ρ p)
      (ν := conditionalTailMeasure (t := t) (m := m) ξ p))

theorem D_m_env_nonneg (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (ρ_idx : EnvironmentIndex) (t m : ℕ) (p : Fin t → Step) :
    0 ≤ D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p := by
  simpa [D_m_env] using
    (D_m_nonneg (t := t) (m := m)
      (ρ := prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) (t + m))
      (ξ := prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)) p)

theorem D_m_env_le_one (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (ρ_idx : EnvironmentIndex) (t m : ℕ) (p : Fin t → Step) :
    D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p ≤ 1 := by
  classical
  -- Both prefix measures are probability measures, hence finite.
  haveI : MeasureTheory.IsFiniteMeasure (prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) (t + m)) :=
    inferInstance
  haveI :
      MeasureTheory.IsFiniteMeasure (prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)) :=
    inferInstance
  simpa [D_m_env] using
    (D_m_le_one (t := t) (m := m)
      (ρ := prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) (t + m))
      (ξ := prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)) p)

theorem F_m_nonneg (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (t m : ℕ) (p : Fin t → Step) :
    0 ≤ F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p := by
  classical
  dsimp [F_m]
  refine tsum_nonneg ?_
  intro ρ_idx
  refine mul_nonneg ?_ ?_
  · exact ENNReal.toReal_nonneg
  · exact D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
      ρ_idx t m p

theorem F_m_le_one (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (t m : ℕ) (p : Fin t → Step) :
    F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p ≤ 1 := by
  classical
  -- Abbreviate the posterior weights (ENNReal and Real).
  let wENN : EnvironmentIndex → ℝ≥0∞ :=
    fun ρ_idx => bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)
  let w : EnvironmentIndex → ℝ :=
    fun ρ_idx => (wENN ρ_idx).toReal

  -- The posterior weights always sum to ≤ 1 (fallback to the prior when the mixture probability is 0).
  have hsumENN_le_one : (∑' ρ_idx, wENN ρ_idx) ≤ 1 := by
    classical
    by_cases hden : mixtureProbability O M prior envs (prefixToHistory t p) = 0
    · have h_eq : (∑' ρ_idx, wENN ρ_idx) = ∑' ρ_idx, prior.weight ρ_idx := by
        refine tsum_congr fun ρ_idx => ?_
        simp [wENN, FixedPoint.bayesianPosteriorWeight, hden]
      simpa [h_eq] using prior.tsum_le_one
    · have hden_pos :
          mixtureProbability O M prior envs (prefixToHistory t p) > 0 :=
        lt_of_le_of_ne zero_le (Ne.symm hden)
      have h_sum : (∑' ρ_idx, wENN ρ_idx) = 1 :=
        bayesianPosterior_sum_one O M prior envs (prefixToHistory t p) hden_pos
      exact le_of_eq h_sum

  have hsumENN_ne_top : (∑' ρ_idx, wENN ρ_idx) ≠ ∞ :=
    (lt_of_le_of_lt hsumENN_le_one ENNReal.one_lt_top).ne

  have hwENN_ne_top : ∀ ρ_idx, wENN ρ_idx ≠ ∞ :=
    fun ρ_idx => ENNReal.ne_top_of_tsum_ne_top hsumENN_ne_top ρ_idx

  have hsum_w_le_one : (∑' ρ_idx, w ρ_idx) ≤ 1 := by
    have hsum_w :
        (∑' ρ_idx, w ρ_idx) = (∑' ρ_idx, wENN ρ_idx).toReal := by
      -- `toReal (tsum wENN) = tsum (toReal ∘ wENN)`
      symm
      simpa [w] using (ENNReal.tsum_toReal_eq (f := wENN) hwENN_ne_top)
    have : (∑' ρ_idx, wENN ρ_idx).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top hsumENN_le_one
    simpa [hsum_w] using this

  have hSummable_w : Summable w :=
    ENNReal.summable_toReal hsumENN_ne_top

  -- Compare `F_m` termwise to `∑ w` using `D_m_env ≤ 1`.
  let f : EnvironmentIndex → ℝ :=
    fun ρ_idx =>
      w ρ_idx *
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p

  have hSummable_f : Summable f := by
    refine Summable.of_nonneg_of_le ?_ ?_ (hSummable_w.mul_right (1 : ℝ))
    · intro ρ_idx
      refine mul_nonneg ?_ ?_
      · exact ENNReal.toReal_nonneg
      · exact D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p
    · intro ρ_idx
      have hw : 0 ≤ w ρ_idx := ENNReal.toReal_nonneg
      have hD : D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                  ρ_idx t m p ≤ 1 :=
        D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p
      simpa [f, mul_assoc] using (mul_le_mul_of_nonneg_left hD hw)

  have h_termwise : ∀ ρ_idx, f ρ_idx ≤ w ρ_idx := by
    intro ρ_idx
    have hw : 0 ≤ w ρ_idx := ENNReal.toReal_nonneg
    have hD :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ≤ 1 :=
      D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    simpa [f, mul_assoc] using (mul_le_mul_of_nonneg_left hD hw)

  have h_tsum_le : (∑' ρ_idx, f ρ_idx) ≤ ∑' ρ_idx, w ρ_idx :=
    hSummable_f.tsum_le_tsum h_termwise hSummable_w

  -- Conclude `F_m ≤ 1` by the weight-sum bound.
  have : F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p ≤
      ∑' ρ_idx, w ρ_idx := by
    simpa [F_m, f, w, wENN] using h_tsum_le
  exact this.trans hsum_w_le_one

/-! ## Value continuity via `D_m` (finite-horizon reward sums) -/

theorem abs_integral_rewardSum_sub_integral_rewardSum_le_two_mul_D_m (t m : ℕ)
    (ρ ξ : MeasureTheory.Measure (Fin (t + m) → Step)) (p : Fin t → Step)
    (hρ : MeasureTheory.Integrable (rewardSum m)
      (conditionalTailMeasure (t := t) (m := m) ρ p))
    (hξ : MeasureTheory.Integrable (rewardSum m)
      (conditionalTailMeasure (t := t) (m := m) ξ p)) :
    |(∫ q, rewardSum m q ∂(conditionalTailMeasure (t := t) (m := m) ρ p)) -
        (∫ q, rewardSum m q ∂(conditionalTailMeasure (t := t) (m := m) ξ p))|
      ≤ (2 * m : ℝ) * D_m (t := t) (m := m) ρ ξ p := by
  -- Start from the `l¹`-distance bound and rewrite `l¹ = 2·tv = 2·D_m`.
  have h :=
    abs_integral_rewardSum_sub_integral_rewardSum_le (t := m)
      (μ := conditionalTailMeasure (t := t) (m := m) ρ p)
      (ν := conditionalTailMeasure (t := t) (m := m) ξ p)
      hρ hξ
  -- `t * l1DistanceReal = (2*t) * ((1/2) * l1DistanceReal)` and `(1/2) * l1DistanceReal` is `tvDistanceReal`.
  simpa [D_m, tvDistanceReal, mul_assoc, mul_left_comm, mul_comm] using h

/-! ## Leike Lemma 5.28: swapping posterior weights into component expectations -/

section LeikeExpectation

open scoped BigOperators

private theorem integrable_of_pointwise_norm_le_const {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] (f : α → ℝ) (B : ℝ)
    (hf : ∀ a, ‖f a‖ ≤ B) : MeasureTheory.Integrable f μ := by
  classical
  have hmeas : MeasureTheory.AEStronglyMeasurable f μ :=
    (measurable_of_countable f).aestronglyMeasurable
  have hbound : ∀ᵐ a ∂μ, ‖f a‖ ≤ B := Filter.Eventually.of_forall hf
  have hconst : MeasureTheory.Integrable (fun _ : α => B) μ :=
    MeasureTheory.integrable_const (μ := μ) (c := B)
  exact hconst.mono' hmeas hbound

theorem integral_posteriorWeight_toReal_mul_D_m_env_prefix (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (ρ_idx : EnvironmentIndex) (t m : ℕ) :
    (∫ p : Fin t → Step,
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
      =
      (prior.weight ρ_idx).toReal *
        (∫ p : Fin t → Step,
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ∂(prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t)) := by
  classical
  let μξ : MeasureTheory.Measure (Fin t → Step) :=
    prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t
  let μρ : MeasureTheory.Measure (Fin t → Step) :=
    prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t
  haveI : MeasureTheory.IsFiniteMeasure μξ := inferInstance
  haveI : MeasureTheory.IsFiniteMeasure μρ := by
    infer_instance

  -- Integrability (both functions are bounded by `1`).
  have hInt_left :
      MeasureTheory.Integrable
          (fun p : Fin t → Step =>
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p)
          μξ := by
    refine integrable_of_pointwise_norm_le_const (μ := μξ) (B := (1 : ℝ))
      (f := fun p : Fin t → Step =>
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p) ?_
    intro p
    have hwENN :
        bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) ≤ (1 : ℝ≥0∞) :=
      Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.bayesianPosteriorWeight_le_one
        (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (h := prefixToHistory t p)
    have hw : (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal ≤ 1 := by
      simpa using (ENNReal.toReal_mono (by simp) hwENN)
    have hD :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ≤ 1 :=
      D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    have hnonneg :
        0 ≤
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p :=
      mul_nonneg ENNReal.toReal_nonneg
        (D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p)
    have hmul :
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ≤ 1 := by
      calc
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ≤ 1 * 1 := by
              refine mul_le_mul hw hD ?_ ?_
              · exact D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
                  (h_stoch := h_stoch) ρ_idx t m p
              · linarith
        _ = 1 := by ring
    have hnorm :
        ‖(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p‖ =
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p := by
      simpa [Real.norm_eq_abs] using (abs_of_nonneg hnonneg)
    simpa [hnorm] using hmul

  have hInt_right :
      MeasureTheory.Integrable
          (fun p : Fin t → Step =>
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p)
          μρ := by
    refine integrable_of_pointwise_norm_le_const (μ := μρ) (B := (1 : ℝ))
      (f := fun p : Fin t → Step =>
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p) ?_
    intro p
    have hnonneg :
        0 ≤
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p :=
      D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    have hle :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ≤ 1 :=
      D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

  -- Expand both integrals as finite sums over singletons and use the cancellation lemma termwise.
  have h_left_sum :
      (∫ p : Fin t → Step,
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ∂μξ)
        =
        ∑ p : Fin t → Step,
          μξ.real {p} *
            ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p) := by
    simpa [μξ, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.integral_fintype (μ := μξ)
        (f := fun p : Fin t → Step =>
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p) hInt_left)

  have h_right_sum :
      (∫ p : Fin t → Step,
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂μρ)
        =
        ∑ p : Fin t → Step,
          μρ.real {p} *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p := by
    simpa [μρ, smul_eq_mul] using
      (MeasureTheory.integral_fintype (μ := μρ)
        (f := fun p : Fin t → Step =>
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p) hInt_right)

  -- Use the singleton cancellation lemma to rewrite each term of the left sum.
  have h_term :
      ∀ p : Fin t → Step,
        μξ.real {p} * (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal =
          (prior.weight ρ_idx).toReal * μρ.real {p} := by
    intro p
    have hENN :
        bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) * μξ {p} =
          prior.weight ρ_idx * μρ {p} := by
      simpa [μξ, μρ] using
        (bayesianPosteriorWeight_mul_prefixMeasureMixtureWithPolicy_singleton (O := O) (M := M) (prior := prior)
          (envs := envs) (π := π) (h_stoch := h_stoch) (ν_idx := ρ_idx) (t := t) p)
    have hENN_real := congrArg ENNReal.toReal hENN
    -- Convert `toReal` of products into products of `toReal`.
    have hμξ_ne_top : μξ {p} ≠ ∞ :=
      MeasureTheory.measure_ne_top μξ ({p} : Set (Fin t → Step))
    have hμρ_ne_top : μρ {p} ≠ ∞ :=
      MeasureTheory.measure_ne_top μρ ({p} : Set (Fin t → Step))
    have hw_ne_top : bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) ≠ ∞ := by
      have hle :
          bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) ≤ (1 : ℝ≥0∞) :=
        Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.bayesianPosteriorWeight_le_one
          (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (h := prefixToHistory t p)
      exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
    have hprior_ne_top : prior.weight ρ_idx ≠ ∞ := by
      have hle : prior.weight ρ_idx ≤ ∑' i, prior.weight i :=
        ENNReal.le_tsum ρ_idx
      have hle1 : prior.weight ρ_idx ≤ 1 :=
        le_trans hle prior.tsum_le_one
      exact (lt_of_le_of_lt hle1 ENNReal.one_lt_top).ne
    -- Now extract the real multiplication identity.
    -- `μ.real {p} = (μ {p}).toReal`.
    -- `ENNReal.toReal_mul` needs both factors to be finite.
    have :
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal * (μξ {p}).toReal =
          (prior.weight ρ_idx).toReal * (μρ {p}).toReal := by
      simpa [ENNReal.toReal_mul, hw_ne_top, hμξ_ne_top, hprior_ne_top, hμρ_ne_top, mul_comm, mul_left_comm, mul_assoc]
        using hENN_real
    simpa [MeasureTheory.measureReal_def, mul_comm, mul_left_comm, mul_assoc] using this

  -- Put everything together.
  calc
    (∫ p : Fin t → Step,
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂μξ)
        =
      ∑ p : Fin t → Step,
        μξ.real {p} *
          ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p) := h_left_sum
    _ =
      ∑ p : Fin t → Step,
        ((prior.weight ρ_idx).toReal * μρ.real {p}) *
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        have := congrArg (fun r : ℝ => r *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p) (h_term p)
        -- simplify the multiplication rearrangement
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ =
      (prior.weight ρ_idx).toReal *
        ∑ p : Fin t → Step,
          μρ.real {p} *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p := by
        -- factor out the constant
        simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ =
      (prior.weight ρ_idx).toReal *
        (∫ p : Fin t → Step,
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂μρ) := by
        simp [h_right_sum]

/-- Expected total variation identity: integrate `F_m` under the mixture prefix measure and swap the
posterior weights into component expectations.

This is the finite-prefix version of Leike’s “expectation swap” step:

`E_{ξ^π}[F_m^π(h_{<t})] = ∑_ρ w(ρ) · E_{ρ^π}[D_m(ρ^π, ξ^π | h_{<t})]`. -/
theorem integral_F_m_prefix_eq_tsum_prior_toReal_mul_integral_D_m_env_prefix (O : Oracle)
    (M : ReflectiveEnvironmentClass O) (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (t m : ℕ) :
    (∫ p : Fin t → Step,
        F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p
          ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
      =
      ∑' ρ_idx : EnvironmentIndex,
        (prior.weight ρ_idx).toReal *
          (∫ p : Fin t → Step,
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂(prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t)) := by
  classical
  let μξ : MeasureTheory.Measure (Fin t → Step) :=
    prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t
  haveI : MeasureTheory.IsFiniteMeasure μξ := inferInstance

  -- `F_m` is integrable since it is bounded by `1`.
  have hInt_F :
      MeasureTheory.Integrable
        (fun p : Fin t → Step =>
          F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p)
        μξ := by
    refine integrable_of_pointwise_norm_le_const (μ := μξ) (B := (1 : ℝ))
      (f := fun p : Fin t → Step =>
        F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p) ?_
    intro p
    have h0 :
        0 ≤
          F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p :=
      F_m_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p
    have hle :
        F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p ≤ 1 :=
      F_m_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle

  -- Summability for swapping `∑ p` and `∑' ρ`.
  have hSummable_g :
      ∀ p : Fin t → Step,
        Summable fun ρ_idx : EnvironmentIndex =>
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p := by
    intro p
    -- Posterior weights on this prefix.
    let wENN : EnvironmentIndex → ℝ≥0∞ :=
      fun ρ_idx => bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)
    let w : EnvironmentIndex → ℝ := fun ρ_idx => (wENN ρ_idx).toReal

    -- The posterior weights always sum to ≤ 1 (fallback to prior if the mixture mass is 0).
    have hsumENN_le_one : (∑' ρ_idx, wENN ρ_idx) ≤ 1 := by
      classical
      by_cases hden : mixtureProbability O M prior envs (prefixToHistory t p) = 0
      · have h_eq : (∑' ρ_idx, wENN ρ_idx) = ∑' ρ_idx, prior.weight ρ_idx := by
          refine tsum_congr fun ρ_idx => ?_
          simp [wENN, FixedPoint.bayesianPosteriorWeight, hden]
        simpa [h_eq] using prior.tsum_le_one
      · have hden_pos :
            mixtureProbability O M prior envs (prefixToHistory t p) > 0 :=
          lt_of_le_of_ne zero_le (Ne.symm hden)
        have h_sum : (∑' ρ_idx, wENN ρ_idx) = 1 :=
          bayesianPosterior_sum_one O M prior envs (prefixToHistory t p) hden_pos
        exact le_of_eq h_sum

    have hsumENN_ne_top : (∑' ρ_idx, wENN ρ_idx) ≠ ∞ :=
      (lt_of_le_of_lt hsumENN_le_one ENNReal.one_lt_top).ne

    have hSummable_w : Summable w :=
      ENNReal.summable_toReal hsumENN_ne_top

    -- Dominate `w * D_m_env` by `w`.
    let g : EnvironmentIndex → ℝ :=
      fun ρ_idx =>
        w ρ_idx *
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p
    have hSummable_g' : Summable g := by
      refine Summable.of_nonneg_of_le ?_ ?_ (hSummable_w.mul_right (1 : ℝ))
      · intro ρ_idx
        refine mul_nonneg ?_ ?_
        · exact ENNReal.toReal_nonneg
        · exact D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
            (h_stoch := h_stoch) ρ_idx t m p
      · intro ρ_idx
        have hw : 0 ≤ w ρ_idx := ENNReal.toReal_nonneg
        have hD :
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ≤ 1 :=
          D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p
        simpa [g, w, wENN, mul_assoc] using (mul_le_mul_of_nonneg_left hD hw)

    -- Unfold back to the required form.
    simpa [g, w, wENN, mul_assoc] using hSummable_g'

  -- Rewrite the integral of `F_m` as a finite sum over singleton atoms.
  have hInt_as_sum :
      (∫ p : Fin t → Step,
          F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p ∂μξ)
        =
        ∑ p : Fin t → Step,
          μξ.real {p} *
            F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p := by
    simpa [smul_eq_mul, μξ] using
      (MeasureTheory.integral_fintype (μ := μξ)
        (f := fun p : Fin t → Step =>
          F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p)
        hInt_F)

  -- Swap `∑ p` and `∑' ρ` using `Summable.tsum_finsetSum`.
  let f : (Fin t → Step) → EnvironmentIndex → ℝ :=
    fun p ρ_idx =>
      μξ.real {p} *
        ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p)

  have hf : ∀ p ∈ (Finset.univ : Finset (Fin t → Step)), Summable (f p) := by
    intro p hp
    -- constant factor `μξ.real {p}` preserves summability
    refine (Summable.mul_left (μξ.real {p})) ?_
    simpa [f] using hSummable_g p

  have h_swap :
      (∑ p : Fin t → Step, ∑' ρ_idx : EnvironmentIndex, f p ρ_idx)
        =
        ∑' ρ_idx : EnvironmentIndex, ∑ p : Fin t → Step, f p ρ_idx := by
    -- Expand `Fintype.sum` as `Finset.sum` and apply `Summable.tsum_finsetSum`.
    simpa using (Summable.tsum_finsetSum (s := (Finset.univ : Finset (Fin t → Step))) hf).symm

  -- Convert each inner finite sum back to the corresponding integral and apply Lemma 5.28 termwise.
  have h_integrable_term :
      ∀ ρ_idx : EnvironmentIndex,
        MeasureTheory.Integrable
          (fun p : Fin t → Step =>
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p)
          μξ := by
    intro ρ_idx
    refine integrable_of_pointwise_norm_le_const (μ := μξ) (B := (1 : ℝ))
      (f := fun p : Fin t → Step =>
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p) ?_
    intro p
    have hwENN :
        bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) ≤ (1 : ℝ≥0∞) :=
      Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.bayesianPosteriorWeight_le_one
        (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (h := prefixToHistory t p)
    have hw : (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal ≤ 1 := by
      simpa using (ENNReal.toReal_mono (by simp) hwENN)
    have hD :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ≤ 1 :=
      D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    have hnonneg :
        0 ≤
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p :=
      mul_nonneg ENNReal.toReal_nonneg
        (D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p)
    have hmul :
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ≤ 1 := by
      calc
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ≤ 1 * 1 := by
              refine mul_le_mul hw hD ?_ ?_
              · exact D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
                  (h_stoch := h_stoch) ρ_idx t m p
              · linarith
        _ = 1 := by ring
    have hnorm :
        ‖(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p‖ =
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p := by
      simpa [Real.norm_eq_abs] using (abs_of_nonneg hnonneg)
    simpa [hnorm] using hmul

  have hSum_to_integral :
      ∀ ρ_idx : EnvironmentIndex,
        (∑ p : Fin t → Step, f p ρ_idx) =
          (∫ p : Fin t → Step,
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                  ρ_idx t m p ∂μξ) := by
    intro ρ_idx
    have hInt_term := h_integrable_term ρ_idx
    -- `integral_fintype` gives exactly the singleton-atom expansion.
    have :
        (∫ p : Fin t → Step,
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ∂μξ)
          =
          ∑ p : Fin t → Step,
            μξ.real {p} *
              ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                  ρ_idx t m p) := by
      simpa [smul_eq_mul, μξ, mul_assoc, mul_left_comm, mul_comm] using
        (MeasureTheory.integral_fintype (μ := μξ)
          (f := fun p : Fin t → Step =>
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p)
          hInt_term)
    -- The RHS is exactly `∑ p, f p ρ_idx`.
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using this.symm

  -- Assemble the chain of rewrites.
  calc
    (∫ p : Fin t → Step,
        F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p ∂μξ)
        =
      ∑ p : Fin t → Step,
        μξ.real {p} *
          F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p := hInt_as_sum
    _ =
      ∑ p : Fin t → Step,
        ∑' ρ_idx : EnvironmentIndex, f p ρ_idx := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        -- Expand `F_m` and push the singleton weight inside the `tsum`.
        dsimp [F_m, f]
        -- `μξ.real {p} * tsum g = tsum (μξ.real {p} * g)`
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (tsum_mul_left (f := fun ρ_idx : EnvironmentIndex =>
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                  ρ_idx t m p)
            (a := μξ.real {p})).symm
    _ =
      ∑' ρ_idx : EnvironmentIndex, ∑ p : Fin t → Step, f p ρ_idx := h_swap
    _ =
      ∑' ρ_idx : EnvironmentIndex,
        (∫ p : Fin t → Step,
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ∂μξ) := by
        refine tsum_congr ?_
        intro ρ_idx
        simpa using hSum_to_integral ρ_idx
    _ =
      ∑' ρ_idx : EnvironmentIndex,
        (prior.weight ρ_idx).toReal *
          (∫ p : Fin t → Step,
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂(prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t)) := by
        refine tsum_congr ?_
        intro ρ_idx
        -- Lemma 5.28.
        simpa [μξ] using
          (integral_posteriorWeight_toReal_mul_D_m_env_prefix (O := O) (M := M) (prior := prior) (envs := envs)
            (π := π) (h_stoch := h_stoch) (ρ_idx := ρ_idx) (t := t) (m := m))

/-- Real-valued version of the posterior cancellation on singleton prefixes:
`w_t(ρ) * ξ_t({p}) = w(ρ) * ρ_t({p})`, with all weights coerced to `ℝ`. -/
theorem bayesianPosteriorWeight_toReal_mul_prefixMeasureMixtureWithPolicy_real_singleton (O : Oracle)
    (M : ReflectiveEnvironmentClass O) (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ρ_idx : EnvironmentIndex) (t : ℕ)
    (p : Fin t → Step) :
    (prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t).real ({p} : Set (Fin t → Step)) *
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal
      =
      (prior.weight ρ_idx).toReal *
        (prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t).real ({p} : Set (Fin t → Step)) := by
  classical
  set μξ : MeasureTheory.Measure (Fin t → Step) := prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t
  set μρ : MeasureTheory.Measure (Fin t → Step) := prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t
  have hENN :
      bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) * μξ ({p} : Set (Fin t → Step)) =
        prior.weight ρ_idx * μρ ({p} : Set (Fin t → Step)) := by
    simpa [μξ, μρ] using
      (bayesianPosteriorWeight_mul_prefixMeasureMixtureWithPolicy_singleton (O := O) (M := M) (prior := prior)
        (envs := envs) (π := π) (h_stoch := h_stoch) (ν_idx := ρ_idx) (t := t) p)
  have hENN_real := congrArg ENNReal.toReal hENN
  have hμξ_ne_top : μξ ({p} : Set (Fin t → Step)) ≠ ∞ :=
    MeasureTheory.measure_ne_top μξ ({p} : Set (Fin t → Step))
  have hμρ_ne_top : μρ ({p} : Set (Fin t → Step)) ≠ ∞ :=
    MeasureTheory.measure_ne_top μρ ({p} : Set (Fin t → Step))
  have hw_ne_top :
      bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) ≠ ∞ := by
    have hle :
        bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) ≤ (1 : ℝ≥0∞) :=
      Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.bayesianPosteriorWeight_le_one
        (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (h := prefixToHistory t p)
    exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
  have hprior_ne_top : prior.weight ρ_idx ≠ ∞ := by
    have hle : prior.weight ρ_idx ≤ ∑' i, prior.weight i :=
      ENNReal.le_tsum ρ_idx
    have hle1 : prior.weight ρ_idx ≤ 1 :=
      le_trans hle prior.tsum_le_one
    exact (lt_of_le_of_lt hle1 ENNReal.one_lt_top).ne
  have :
      (μξ ({p} : Set (Fin t → Step))).toReal *
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal
        =
        (μρ ({p} : Set (Fin t → Step))).toReal * (prior.weight ρ_idx).toReal := by
    -- Convert `toReal` of products into products of `toReal` and rearrange.
    have h :
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            (μξ ({p} : Set (Fin t → Step))).toReal
          =
          (prior.weight ρ_idx).toReal * (μρ ({p} : Set (Fin t → Step))).toReal := by
      simpa [ENNReal.toReal_mul, hw_ne_top, hμξ_ne_top, hprior_ne_top, hμρ_ne_top, mul_assoc, mul_left_comm,
        mul_comm] using hENN_real
    calc
      (μξ ({p} : Set (Fin t → Step))).toReal *
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal
          =
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            (μξ ({p} : Set (Fin t → Step))).toReal := by
            simp [mul_comm]
      _ = (prior.weight ρ_idx).toReal * (μρ ({p} : Set (Fin t → Step))).toReal := h
      _ =
          (μρ ({p} : Set (Fin t → Step))).toReal * (prior.weight ρ_idx).toReal := by
            simp [mul_comm]
  simpa [μξ, μρ, MeasureTheory.measureReal_def, mul_assoc, mul_left_comm, mul_comm] using this

theorem prefixMeasureWithPolicy_real_headSet (μ : Environment) (π : Agent) (h_stoch : isStochastic μ) (t m : ℕ)
    (p : Fin t → Step) :
    (prefixMeasureWithPolicy μ π h_stoch (t + m)).real (headSet t m p) =
      (prefixMeasureWithPolicy μ π h_stoch t).real ({p} : Set (Fin t → Step)) := by
  classical
  have hmap :=
    prefixMeasureWithPolicy_map_headPrefix (μ := μ) (π := π) (h_stoch := h_stoch) (t := t) (m := m)
  -- Apply both measures to `{p}` and unfold `headSet` as a preimage.
  have hENN :=
    congrArg (fun ν : MeasureTheory.Measure (Fin t → Step) => ν ({p} : Set (Fin t → Step))) hmap
  have hReal := congrArg ENNReal.toReal hENN
  have hHead :
      headSet t m p = headPrefix (t := t) (m := m) ⁻¹' ({p} : Set (Fin t → Step)) := by
    ext q
    simp [headSet]
  simpa [MeasureTheory.Measure.map_apply, hHead, headPrefix_measurable, MeasureTheory.measureReal_def]
    using hReal

theorem prefixMeasureMixtureWithPolicy_real_headSet (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (t m : ℕ) (p : Fin t → Step) :
    (prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)).real (headSet t m p) =
      (prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t).real ({p} : Set (Fin t → Step)) := by
  classical
  have hmap :=
    prefixMeasureMixtureWithPolicy_map_headPrefix (O := O) (M := M) (prior := prior) (envs := envs)
      (π := π) (h_stoch := h_stoch) (t := t) (m := m)
  have hENN :=
    congrArg (fun ν : MeasureTheory.Measure (Fin t → Step) => ν ({p} : Set (Fin t → Step))) hmap
  have hReal := congrArg ENNReal.toReal hENN
  have hHead :
      headSet t m p = headPrefix (t := t) (m := m) ⁻¹' ({p} : Set (Fin t → Step)) := by
    ext q
    simp [headSet]
  simpa [MeasureTheory.Measure.map_apply, hHead, headPrefix_measurable, MeasureTheory.measureReal_def]
    using hReal

/-- Key identity behind “expected TV vanishes”: the weighted TV distance can be rewritten as an
expectation of posterior-weight increments. -/
theorem integral_posteriorWeight_toReal_mul_D_m_env_prefix_eq_half_integral_abs_diff (O : Oracle)
    (M : ReflectiveEnvironmentClass O) (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ρ_idx : EnvironmentIndex) (t m : ℕ) :
    (∫ p : Fin t → Step,
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
      =
      (1 / 2 : ℝ) *
        (∫ r : Fin (t + m) → Step,
          |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m))) := by
  classical
  let μξ_t : MeasureTheory.Measure (Fin t → Step) := prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t
  let μξ_tm : MeasureTheory.Measure (Fin (t + m) → Step) :=
    prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)
  let μρ_t : MeasureTheory.Measure (Fin t → Step) := prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t
  let μρ_tm : MeasureTheory.Measure (Fin (t + m) → Step) :=
    prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) (t + m)
  haveI : MeasureTheory.IsFiniteMeasure μξ_t := inferInstance
  haveI : MeasureTheory.IsFiniteMeasure μξ_tm := inferInstance
  haveI : MeasureTheory.IsFiniteMeasure μρ_t := by infer_instance
  haveI : MeasureTheory.IsFiniteMeasure μρ_tm := by infer_instance

  -- Integrability of both sides (bounded by a constant on a finite measure space).
  have hInt_left :
      MeasureTheory.Integrable
        (fun p : Fin t → Step =>
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p)
        μξ_t := by
    -- Same bound as in Lemma 5.28.
    refine integrable_of_pointwise_norm_le_const (μ := μξ_t) (B := (1 : ℝ))
      (f := fun p : Fin t → Step =>
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p) ?_
    intro p
    have hwENN :
        bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p) ≤ (1 : ℝ≥0∞) :=
      Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.bayesianPosteriorWeight_le_one
        (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (h := prefixToHistory t p)
    have hw : (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal ≤ 1 := by
      simpa using (ENNReal.toReal_mono (by simp) hwENN)
    have hD :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ≤ 1 :=
      D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    have hnonneg :
        0 ≤
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p :=
      mul_nonneg ENNReal.toReal_nonneg
        (D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p)
    have hmul :
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ≤ 1 := by
      calc
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ≤ 1 * 1 := by
              refine mul_le_mul hw hD ?_ ?_
              · exact D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
                  (h_stoch := h_stoch) ρ_idx t m p
              · linarith
        _ = 1 := by ring
    have hnorm :
        ‖(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p‖ =
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p := by
      simpa [Real.norm_eq_abs] using (abs_of_nonneg hnonneg)
    simpa [hnorm] using hmul

  have hInt_right :
      MeasureTheory.Integrable
        (fun r : Fin (t + m) → Step =>
          |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|)
        μξ_tm := by
    refine integrable_of_pointwise_norm_le_const (μ := μξ_tm) (B := (2 : ℝ))
      (f := fun r : Fin (t + m) → Step =>
        |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
            (bayesianPosteriorWeight O M prior envs ρ_idx
              (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|) ?_
    intro r
    have hw1 :
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal ≤ 1 := by
      have hle :
          bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r) ≤ (1 : ℝ≥0∞) :=
        Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.bayesianPosteriorWeight_le_one
          (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (h := prefixToHistory (t + m) r)
      simpa using (ENNReal.toReal_mono (by simp) hle)
    have hw2 :
        (bayesianPosteriorWeight O M prior envs ρ_idx
              (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal ≤ 1 := by
      have hle :
          bayesianPosteriorWeight O M prior envs ρ_idx
              (prefixToHistory t (headPrefix (t := t) (m := m) r)) ≤ (1 : ℝ≥0∞) :=
        Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale.bayesianPosteriorWeight_le_one
          (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx)
          (h := prefixToHistory t (headPrefix (t := t) (m := m) r))
      simpa using (ENNReal.toReal_mono (by simp) hle)
    -- crude bound `|a - b| ≤ |a| + |b| ≤ 2`
    have : |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
            (bayesianPosteriorWeight O M prior envs ρ_idx
              (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| ≤ 2 := by
      have h_abs :
          |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
            ≤
            |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal| +
              |(bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| := by
        simpa using
          (abs_sub_le
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal
            0
            (bayesianPosteriorWeight O M prior envs ρ_idx
              (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal)
      have h1' : |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal| ≤ 1 := by
        have h0 : 0 ≤ (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal :=
          ENNReal.toReal_nonneg
        simpa [abs_of_nonneg h0] using hw1
      have h2' :
          |(bayesianPosteriorWeight O M prior envs ρ_idx
            (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| ≤ 1 := by
        have h0 :
            0 ≤
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal :=
          ENNReal.toReal_nonneg
        simpa [abs_of_nonneg h0] using hw2
      linarith
    -- `‖|a-b|‖ = |a-b|`.
    simpa [Real.norm_eq_abs, abs_nonneg] using this

  -- Expand the integrals as sums over singleton atoms.
  have h_left_sum :
      (∫ p : Fin t → Step,
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p ∂μξ_t)
        =
        ∑ p : Fin t → Step,
          μξ_t.real ({p} : Set (Fin t → Step)) *
            ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p) := by
    simpa [smul_eq_mul, μξ_t] using
      (MeasureTheory.integral_fintype (μ := μξ_t)
        (f := fun p : Fin t → Step =>
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p)
        hInt_left)

  have h_right_sum :
      (∫ r : Fin (t + m) → Step,
          |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| ∂μξ_tm)
        =
        ∑ r : Fin (t + m) → Step,
          μξ_tm.real ({r} : Set (Fin (t + m) → Step)) *
            |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| := by
    simpa [smul_eq_mul, μξ_tm] using
      (MeasureTheory.integral_fintype (μ := μξ_tm)
        (f := fun r : Fin (t + m) → Step =>
          |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|)
        hInt_right)

  -- Main arithmetic rewrite: expand `D_m_env` and use the singleton product lemmas.
  have h_pointwise :
      ∀ p : Fin t → Step,
        μξ_t.real ({p} : Set (Fin t → Step)) *
            ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p)
          =
          (1 / 2 : ℝ) *
            ∑ q : Fin m → Step,
              μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
                |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal| := by
    intro p
    -- Expand `D_m_env` as `1/2 * ∑ |P - Q|`.
    let P : MeasureTheory.Measure (Fin m → Step) :=
      conditionalTailMeasure (t := t) (m := m) μρ_tm p
    let Q : MeasureTheory.Measure (Fin m → Step) :=
      conditionalTailMeasure (t := t) (m := m) μξ_tm p
    have hD :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p = (1 / 2 : ℝ) * ∑ q : Fin m → Step, |P.real ({q} : Set (Fin m → Step)) - Q.real ({q} : Set (Fin m → Step))| := by
      simp [D_m_env, D_m, tvDistanceReal, l1DistanceReal, P, Q, μρ_tm, μξ_tm]

    -- Helper: chain rule for `P` and `Q` on singleton tails.
    have hP (q : Fin m → Step) :
        (μρ_t.real ({p} : Set (Fin t → Step))) *
            P.real ({q} : Set (Fin m → Step)) =
          μρ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
      -- `μρ_tm.real(headSet p) * P.real{q} = μρ_tm.real{append p q}` and `μρ_tm.real(headSet p) = μρ_t.real{p}`.
      have h1 :
          μρ_tm.real (headSet t m p) * P.real ({q} : Set (Fin m → Step)) =
            μρ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
        simpa [P, MeasureTheory.measureReal_def] using
          (measureReal_headSet_mul_conditionalTailMeasure_singleton (t := t) (m := m) (μ := μρ_tm) p q)
      have h2 :
          μρ_tm.real (headSet t m p) = μρ_t.real ({p} : Set (Fin t → Step)) := by
        simpa [μρ_tm, μρ_t] using prefixMeasureWithPolicy_real_headSet (μ := envs ρ_idx) (π := π)
          (h_stoch := h_stoch ρ_idx) (t := t) (m := m) p
      simpa [h2] using h1

    have hQ (q : Fin m → Step) :
        (μξ_t.real ({p} : Set (Fin t → Step))) *
            Q.real ({q} : Set (Fin m → Step)) =
          μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
      have h1 :
          μξ_tm.real (headSet t m p) * Q.real ({q} : Set (Fin m → Step)) =
            μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
        simpa [Q, MeasureTheory.measureReal_def] using
          (measureReal_headSet_mul_conditionalTailMeasure_singleton (t := t) (m := m) (μ := μξ_tm) p q)
      have h2 :
          μξ_tm.real (headSet t m p) = μξ_t.real ({p} : Set (Fin t → Step)) := by
        simpa [μξ_tm, μξ_t] using
          prefixMeasureMixtureWithPolicy_real_headSet (O := O) (M := M) (prior := prior) (envs := envs)
            (π := π) (h_stoch := h_stoch) (t := t) (m := m) p
      simpa [h2] using h1

    -- Posterior cancellation for `{p}` and `{append p q}`.
    have hW_t :
        μξ_t.real ({p} : Set (Fin t → Step)) *
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal
          =
          (prior.weight ρ_idx).toReal * μρ_t.real ({p} : Set (Fin t → Step)) := by
      simpa [μξ_t, μρ_t, mul_assoc, mul_left_comm, mul_comm] using
        (bayesianPosteriorWeight_toReal_mul_prefixMeasureMixtureWithPolicy_real_singleton (O := O) (M := M)
          (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) (ρ_idx := ρ_idx) (t := t) p)

    have hW_tm (q : Fin m → Step) :
        μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
            (bayesianPosteriorWeight O M prior envs ρ_idx
              (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal
          =
          (prior.weight ρ_idx).toReal *
            μρ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
      simpa [μξ_tm, μρ_tm, mul_assoc, mul_left_comm, mul_comm] using
        (bayesianPosteriorWeight_toReal_mul_prefixMeasureMixtureWithPolicy_real_singleton (O := O) (M := M)
          (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) (ρ_idx := ρ_idx) (t := t + m)
          (appendPrefix (t := t) (m := m) p q))

    -- Now rewrite the weighted distance termwise using the cancellation identities.
    have h_atom (q : Fin m → Step) :
        μξ_t.real ({p} : Set (Fin t → Step)) *
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              (P.real ({q} : Set (Fin m → Step)) - Q.real ({q} : Set (Fin m → Step)))
          =
          μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
            ((bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal) := by
      -- Expand the LHS into `... * P - ... * Q` and rewrite each piece.
      have hP' :
          μξ_t.real ({p} : Set (Fin t → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                P.real ({q} : Set (Fin m → Step))
            =
            μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal := by
        -- LHS = `w(ρ).toReal * μρ_tm{append p q}` = RHS by `hW_tm`.
        calc
          μξ_t.real ({p} : Set (Fin t → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                P.real ({q} : Set (Fin m → Step))
              =
              (prior.weight ρ_idx).toReal * μρ_t.real ({p} : Set (Fin t → Step)) *
                P.real ({q} : Set (Fin m → Step)) := by
                  -- replace `μξ_t.real{p} * posterior_t` by `w(ρ) * μρ_t.real{p}`
                  have hW_t' := congrArg (fun x => x * P.real ({q} : Set (Fin m → Step))) hW_t
                  simpa [mul_assoc, mul_left_comm, mul_comm] using hW_t'
          _ =
              (prior.weight ρ_idx).toReal *
                μρ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) := by
                  simp [mul_assoc, hP q]
          _ =
              μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
                (bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal := by
                  -- rewrite using `hW_tm`
                  simpa [mul_assoc, mul_left_comm, mul_comm] using (hW_tm q).symm
      have hQ' :
          μξ_t.real ({p} : Set (Fin t → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                Q.real ({q} : Set (Fin m → Step))
            =
            μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal := by
        -- `μξ_t.real{p} * Q.real{q} = μξ_tm.real{append p q}`.
        simp [mul_assoc, mul_comm, hQ q]
      -- Combine `hP'` and `hQ'`.
      calc
        μξ_t.real ({p} : Set (Fin t → Step)) *
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              (P.real ({q} : Set (Fin m → Step)) - Q.real ({q} : Set (Fin m → Step)))
            =
          (μξ_t.real ({p} : Set (Fin t → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                P.real ({q} : Set (Fin m → Step))) -
            (μξ_t.real ({p} : Set (Fin t → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                Q.real ({q} : Set (Fin m → Step))) := by
            ring
        _ =
          (μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal) -
            (μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal) := by
            simp [hP', hQ']
        _ =
          μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
            ((bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal) := by
            ring

    -- Move from the signed identity to absolute values, then sum.
    have h_abs (q : Fin m → Step) :
        μξ_t.real ({p} : Set (Fin t → Step)) *
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              |P.real ({q} : Set (Fin m → Step)) - Q.real ({q} : Set (Fin m → Step))|
          =
          μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
            |(bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal| := by
      have hμξ_nonneg : 0 ≤ μξ_t.real ({p} : Set (Fin t → Step)) := MeasureTheory.measureReal_nonneg
      have hw_nonneg : 0 ≤ (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal :=
        ENNReal.toReal_nonneg
      have hμξtm_nonneg :
          0 ≤ μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) :=
        MeasureTheory.measureReal_nonneg
      -- Take `abs` of `h_atom` and simplify using nonnegativity of the scalar weights.
      have := congrArg abs (h_atom q)
      simpa [abs_mul, abs_of_nonneg hμξ_nonneg, abs_of_nonneg hw_nonneg, abs_of_nonneg hμξtm_nonneg,
        mul_assoc, mul_left_comm, mul_comm] using this

    -- Finish by rewriting the `Finset.sum` form.
    -- LHS: `μξ_t.real{p} * (posterior_t * D)` where `D = 1/2 * ∑ |...|`.
    calc
      μξ_t.real ({p} : Set (Fin t → Step)) *
          ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p)
          =
        (1 / 2 : ℝ) *
          ∑ q : Fin m → Step,
            μξ_t.real ({p} : Set (Fin t → Step)) *
              (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                |P.real ({q} : Set (Fin m → Step)) - Q.real ({q} : Set (Fin m → Step))| := by
            -- unfold `D_m_env` and distribute
            simp [hD, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        (1 / 2 : ℝ) *
          ∑ q : Fin m → Step,
            μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal| := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro q _hq
            simpa [mul_assoc, mul_left_comm, mul_comm] using h_abs q

  -- Turn the double sum over `(p,q)` into a sum over length-`t+m` prefixes.
  let e : (Fin (t + m) → Step) ≃ (Fin t → Step) × (Fin m → Step) :=
    { toFun := fun r => (headPrefix (t := t) (m := m) r, tailPrefix (t := t) (m := m) r)
      invFun := fun pq => appendPrefix (t := t) (m := m) pq.1 pq.2
      left_inv := fun r => by
        simpa using appendPrefix_headPrefix_tailPrefix (t := t) (m := m) r
      right_inv := fun pq => by
        rcases pq with ⟨p, q⟩
        ext <;> simp [headPrefix_appendPrefix, tailPrefix_appendPrefix] }

  have h_swap_sum :
      (∑ p : Fin t → Step,
          (1 / 2 : ℝ) *
            ∑ q : Fin m → Step,
              μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
                |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal|)
        =
        (1 / 2 : ℝ) *
          ∑ r : Fin (t + m) → Step,
            μξ_tm.real ({r} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| := by
    -- Rewrite the RHS sum using the equivalence `e` to a sum over pairs `(p,q)`.
    have hR :
        (∑ r : Fin (t + m) → Step,
            μξ_tm.real ({r} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|)
          =
          ∑ pq : (Fin t → Step) × (Fin m → Step),
            μξ_tm.real ({appendPrefix (t := t) (m := m) pq.1 pq.2} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) pq.1 pq.2))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t pq.1)).toReal| := by
      -- Change variables `r ↦ (headPrefix r, tailPrefix r)` in the `Fintype.sum`.
      simpa [e] using
        (Fintype.sum_equiv e (fun r : Fin (t + m) → Step =>
          μξ_tm.real ({r} : Set (Fin (t + m) → Step)) *
            |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|)
          (fun pq : (Fin t → Step) × (Fin m → Step) =>
            μξ_tm.real ({appendPrefix (t := t) (m := m) pq.1 pq.2} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) pq.1 pq.2))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t pq.1)).toReal|)
          (fun r => by
            simp [e, appendPrefix_headPrefix_tailPrefix]))
    -- Now expand the pair-sum as an iterated sum.
    -- `∑ pq, ...` is `∑ p, ∑ q, ...`.
    have hPair :
        (∑ pq : (Fin t → Step) × (Fin m → Step),
            μξ_tm.real ({appendPrefix (t := t) (m := m) pq.1 pq.2} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) pq.1 pq.2))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t pq.1)).toReal|)
          =
          ∑ p : Fin t → Step,
            ∑ q : Fin m → Step,
              μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
                |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal| := by
      -- `Fintype` sum over a product is nested sums.
      classical
      simp [Fintype.sum_prod_type]
    -- Put it together.
    -- The outer `1/2` factor can be pulled out.
    -- LHS is exactly the iterated sum from `h_pointwise`.
    calc
      (∑ p : Fin t → Step,
          (1 / 2 : ℝ) *
            ∑ q : Fin m → Step,
              μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
                |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal|)
          =
          (1 / 2 : ℝ) *
            ∑ p : Fin t → Step,
              ∑ q : Fin m → Step,
                μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
                  |(bayesianPosteriorWeight O M prior envs ρ_idx
                      (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
                    (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal| := by
            simp [Finset.mul_sum]
      _ =
          (1 / 2 : ℝ) *
            ∑ pq : (Fin t → Step) × (Fin m → Step),
              μξ_tm.real ({appendPrefix (t := t) (m := m) pq.1 pq.2} : Set (Fin (t + m) → Step)) *
                |(bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) pq.1 pq.2))).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t pq.1)).toReal| := by
            simpa using congrArg (fun S : ℝ => (1 / 2 : ℝ) * S) hPair.symm
      _ =
          (1 / 2 : ℝ) *
            ∑ r : Fin (t + m) → Step,
              μξ_tm.real ({r} : Set (Fin (t + m) → Step)) *
                |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                  (bayesianPosteriorWeight O M prior envs ρ_idx
                    (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| := by
            simp [hR]

  -- Final assembly.
  calc
    (∫ p : Fin t → Step,
        (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p ∂μξ_t)
        =
      ∑ p : Fin t → Step,
        μξ_t.real ({p} : Set (Fin t → Step)) *
          ((bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p) := h_left_sum
    _ =
      ∑ p : Fin t → Step,
        (1 / 2 : ℝ) *
          ∑ q : Fin m → Step,
            μξ_tm.real ({appendPrefix (t := t) (m := m) p q} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory (t + m) (appendPrefix (t := t) (m := m) p q))).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal| := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        simpa [μξ_t, μξ_tm] using h_pointwise p
    _ =
      (1 / 2 : ℝ) *
        ∑ r : Fin (t + m) → Step,
            μξ_tm.real ({r} : Set (Fin (t + m) → Step)) *
              |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| := by
        simpa using h_swap_sum
    _ =
      (1 / 2 : ℝ) *
        (∫ r : Fin (t + m) → Step,
          |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal| ∂μξ_tm) := by
        simp [h_right_sum]
    _ =
      (1 / 2 : ℝ) *
        (∫ r : Fin (t + m) → Step,
          |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
              (bayesianPosteriorWeight O M prior envs ρ_idx
                (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m))) := by
        rfl

/-! ## Expected posterior increments vanish -/

open Filter

open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale

/-- On the mixture trajectory space `ξ^π`, the expected absolute increment of the posterior process
over a fixed lag `m` tends to `0`. -/
theorem tendsto_integral_abs_posteriorReal_sub_shift (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (ρ_idx : EnvironmentIndex) (m : ℕ) :
    Tendsto
        (fun t =>
          ∫ traj,
            |posteriorReal O M prior envs ρ_idx (t + m) traj -
                posteriorReal O M prior envs ρ_idx t traj|
            ∂(mixtureMeasureWithPolicy O M prior envs π h_stoch))
        atTop (nhds 0) := by
  classical
  -- Work with the `ξ` abbreviation so we can reuse the martingale convergence lemma.
  let μ : MeasureTheory.Measure Trajectory := ξ O M prior envs π h_stoch
  haveI : MeasureTheory.IsFiniteMeasure μ := by infer_instance

  have h_ae_tendsto :
      ∀ᵐ traj ∂μ,
        Tendsto (fun t =>
          ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
              posteriorReal O M prior envs ρ_idx t traj‖) atTop (nhds 0) := by
    have h_conv :
        ∀ᵐ traj ∂μ,
          Tendsto (fun t => posteriorReal O M prior envs ρ_idx t traj) atTop
            (nhds
              (trajectoryFiltration.limitProcess (posteriorReal O M prior envs ρ_idx) μ traj)) := by
      simpa [μ] using
        (posteriorReal_ae_tendsto_limitProcess (O := O) (M := M) (prior := prior) (envs := envs) (pi := π)
          (h_stoch := h_stoch) (ν_idx := ρ_idx))
    filter_upwards [h_conv] with traj htraj
    have h_shift :
        Tendsto (fun t => posteriorReal O M prior envs ρ_idx (t + m) traj) atTop
          (nhds
            (trajectoryFiltration.limitProcess (posteriorReal O M prior envs ρ_idx) μ traj)) :=
      (tendsto_add_atTop_iff_nat m).2 htraj
    have h_sub :
        Tendsto (fun t =>
            posteriorReal O M prior envs ρ_idx (t + m) traj -
              posteriorReal O M prior envs ρ_idx t traj) atTop (nhds 0) := by
      simpa using (h_shift.sub htraj)
    simpa using h_sub.norm

  have h_meas :
      ∀ t : ℕ,
        MeasureTheory.AEStronglyMeasurable
          (fun traj =>
            ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
                posteriorReal O M prior envs ρ_idx t traj‖)
          μ := by
    intro t
    have hInt₁ : MeasureTheory.Integrable (posteriorReal O M prior envs ρ_idx (t + m)) μ := by
      simpa [μ] using
        (posteriorReal_integrable (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
          (h_stoch := h_stoch) (ν_idx := ρ_idx) (t := t + m))
    have hInt₂ : MeasureTheory.Integrable (posteriorReal O M prior envs ρ_idx t) μ := by
      simpa [μ] using
        (posteriorReal_integrable (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
          (h_stoch := h_stoch) (ν_idx := ρ_idx) (t := t))
    exact (hInt₁.aestronglyMeasurable.sub hInt₂.aestronglyMeasurable).norm

  have h_bound :
      ∀ t : ℕ,
        ∀ᵐ traj ∂μ,
          ‖(fun traj =>
              ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
                  posteriorReal O M prior envs ρ_idx t traj‖) traj‖
            ≤ (fun _ : Trajectory => (2 : ℝ)) traj := by
    intro t
    refine Filter.Eventually.of_forall (fun traj => ?_)
    have hle_tm : posteriorReal O M prior envs ρ_idx (t + m) traj ≤ 1 :=
      posteriorReal_le_one (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (t := t + m) traj
    have hle_t : posteriorReal O M prior envs ρ_idx t traj ≤ 1 :=
      posteriorReal_le_one (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ρ_idx) (t := t) traj
    have h0_tm : 0 ≤ posteriorReal O M prior envs ρ_idx (t + m) traj := ENNReal.toReal_nonneg
    have h0_t : 0 ≤ posteriorReal O M prior envs ρ_idx t traj := ENNReal.toReal_nonneg
    have h_triangle :
        ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
              posteriorReal O M prior envs ρ_idx t traj‖
          ≤ ‖posteriorReal O M prior envs ρ_idx (t + m) traj‖ +
              ‖posteriorReal O M prior envs ρ_idx t traj‖ := by
      simpa [sub_eq_add_neg] using norm_add_le (posteriorReal O M prior envs ρ_idx (t + m) traj)
        (-posteriorReal O M prior envs ρ_idx t traj)
    have h_sum_le : ‖posteriorReal O M prior envs ρ_idx (t + m) traj‖ +
          ‖posteriorReal O M prior envs ρ_idx t traj‖ ≤ 2 := by
      -- both posterior values are nonnegative and ≤ 1
      have hnorm_tm : ‖posteriorReal O M prior envs ρ_idx (t + m) traj‖ = posteriorReal O M prior envs ρ_idx (t + m) traj := by
        simp [Real.norm_eq_abs, abs_of_nonneg h0_tm]
      have hnorm_t : ‖posteriorReal O M prior envs ρ_idx t traj‖ = posteriorReal O M prior envs ρ_idx t traj := by
        simp [Real.norm_eq_abs, abs_of_nonneg h0_t]
      calc
        ‖posteriorReal O M prior envs ρ_idx (t + m) traj‖ + ‖posteriorReal O M prior envs ρ_idx t traj‖
            = posteriorReal O M prior envs ρ_idx (t + m) traj + posteriorReal O M prior envs ρ_idx t traj := by
                simp [hnorm_tm, hnorm_t]
        _ ≤ (1 : ℝ) + 1 := add_le_add hle_tm hle_t
        _ = 2 := by ring
    have h_le_two :
        ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
              posteriorReal O M prior envs ρ_idx t traj‖ ≤ 2 :=
      le_trans h_triangle h_sum_le
    -- `‖‖x‖‖ = ‖x‖`
    simpa [norm_norm] using h_le_two

  have h_bound_int : MeasureTheory.Integrable (fun _ : Trajectory => (2 : ℝ)) μ := by
    simp

  have h_tendsto_norm :
      Tendsto
          (fun t =>
            ∫ traj,
              ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
                  posteriorReal O M prior envs ρ_idx t traj‖
              ∂μ)
          atTop (nhds 0) := by
    simpa using
      (MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
        (F := fun t traj =>
          ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
              posteriorReal O M prior envs ρ_idx t traj‖)
        (f := fun _ : Trajectory => (0 : ℝ))
        (bound := fun _ : Trajectory => (2 : ℝ)) h_meas h_bound_int h_bound h_ae_tendsto)

  -- Translate back from `‖x‖` to `|x|` and unfold `μ`.
  have h_eq :
      (fun t =>
          ∫ traj,
            |posteriorReal O M prior envs ρ_idx (t + m) traj -
                posteriorReal O M prior envs ρ_idx t traj|
            ∂(mixtureMeasureWithPolicy O M prior envs π h_stoch))
        =
        (fun t =>
          ∫ traj,
            ‖posteriorReal O M prior envs ρ_idx (t + m) traj -
                posteriorReal O M prior envs ρ_idx t traj‖
            ∂μ) := by
    funext t
    simp [μ, ξ, Real.norm_eq_abs]
  simpa [h_eq] using h_tendsto_norm

/-- The RHS prefix integral from
`integral_posteriorWeight_toReal_mul_D_m_env_prefix_eq_half_integral_abs_diff` is just an
expectation of posterior increments on the trajectory space, hence also tends to `0`. -/
theorem tendsto_integral_abs_diff_bayesianPosteriorWeight_prefix (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (ρ_idx : EnvironmentIndex) (m : ℕ) :
    Tendsto
        (fun t =>
          ∫ r : Fin (t + m) → Step,
            |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)))
        atTop (nhds 0) := by
  classical
  have h_traj :=
    tendsto_integral_abs_posteriorReal_sub_shift (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
      (h_stoch := h_stoch) (ρ_idx := ρ_idx) (m := m)

  -- Identify the prefix marginal integral with the corresponding trajectory expectation.
  have h_eq :
      (fun t =>
          ∫ r : Fin (t + m) → Step,
            |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)))
        =
        (fun t =>
          ∫ traj,
            |posteriorReal O M prior envs ρ_idx (t + m) traj -
                posteriorReal O M prior envs ρ_idx t traj|
            ∂(mixtureMeasureWithPolicy O M prior envs π h_stoch)) := by
    funext t
    let f : (Fin (t + m) → Step) → ℝ :=
      fun r =>
        |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
            (bayesianPosteriorWeight O M prior envs ρ_idx
              (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
    have hφ :
        AEMeasurable (truncate (t + m)) (mixtureMeasureWithPolicy O M prior envs π h_stoch) :=
      (truncate_measurable (t + m)).aemeasurable
    have hfm :
        MeasureTheory.AEStronglyMeasurable f
          ((mixtureMeasureWithPolicy O M prior envs π h_stoch).map (truncate (t + m))) :=
      (measurable_of_countable f).aestronglyMeasurable
    -- `integral_map` identifies the prefix integral with the trajectory expectation.
    have hmap :=
      MeasureTheory.integral_map (μ := mixtureMeasureWithPolicy O M prior envs π h_stoch) (φ := truncate (t + m)) hφ
        hfm
    -- Rewrite the pulled-back integrand into the posterior increment form.
    simpa [prefixMeasureMixtureWithPolicy, f, posteriorReal, PosteriorProcess.posteriorWeight,
      prefixToHistory_eq_trajectoryToHistory, headPrefix_truncate, Real.norm_eq_abs] using hmap

  simpa [h_eq] using h_traj

/-- For each `ρ`, the mixed expected conditional TV term (the LHS of
`integral_posteriorWeight_toReal_mul_D_m_env_prefix_eq_half_integral_abs_diff`) tends to `0`. -/
theorem tendsto_integral_posteriorWeight_toReal_mul_D_m_env_prefix (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ρ_idx : EnvironmentIndex) (m : ℕ) :
    Tendsto
        (fun t =>
          ∫ p : Fin t → Step,
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                  ρ_idx t m p
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
        atTop (nhds 0) := by
  classical
  have h_rhs :=
    tendsto_integral_abs_diff_bayesianPosteriorWeight_prefix (O := O) (M := M) (prior := prior) (envs := envs)
      (π := π) (h_stoch := h_stoch) (ρ_idx := ρ_idx) (m := m)
  have h_mul :
      Tendsto
          (fun t =>
            (1 / 2 : ℝ) *
              (∫ r : Fin (t + m) → Step,
                |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                    (bayesianPosteriorWeight O M prior envs ρ_idx
                      (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
                ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m))))
          atTop (nhds 0) := by
    simpa [mul_zero] using (tendsto_const_nhds.mul h_rhs)
  have h_eq :
      (fun t =>
        ∫ p : Fin t → Step,
          (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p
          ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
        =
      (fun t =>
        (1 / 2 : ℝ) *
          (∫ r : Fin (t + m) → Step,
            |(bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory (t + m) r)).toReal -
                (bayesianPosteriorWeight O M prior envs ρ_idx
                  (prefixToHistory t (headPrefix (t := t) (m := m) r))).toReal|
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch (t + m)))) := by
    funext t
    simpa using
      (integral_posteriorWeight_toReal_mul_D_m_env_prefix_eq_half_integral_abs_diff (O := O) (M := M)
        (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) (ρ_idx := ρ_idx) (t := t) (m := m))
  simpa [h_eq] using h_mul

private theorem integral_D_m_env_prefix_le_one (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (ρ_idx : EnvironmentIndex) (t m : ℕ) :
    (∫ p : Fin t → Step,
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p
        ∂(prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t)) ≤ 1 := by
  classical
  let μρ : MeasureTheory.Measure (Fin t → Step) := prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t
  haveI : MeasureTheory.IsFiniteMeasure μρ := by infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μρ := by infer_instance
  -- Integrability since the integrand is bounded by `1`.
  have hInt :
      MeasureTheory.Integrable
        (fun p : Fin t → Step =>
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p) μρ := by
    refine integrable_of_pointwise_norm_le_const (μ := μρ) (B := (1 : ℝ))
      (f := fun p : Fin t → Step =>
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p) ?_
    intro p
    have h0 :
        0 ≤
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p :=
      D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    have hle :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ≤ 1 :=
      D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle

  have h_sum :
      (∫ p : Fin t → Step,
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ∂μρ)
        =
        ∑ p : Fin t → Step,
          μρ.real {p} *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p := by
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_fintype (μ := μρ)
        (f := fun p : Fin t → Step =>
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p) hInt)

  have h_le :
      (∑ p : Fin t → Step,
          μρ.real {p} *
            D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
              ρ_idx t m p)
        ≤ ∑ p : Fin t → Step, μρ.real {p} * (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hμ0 : 0 ≤ μρ.real {p} := MeasureTheory.measureReal_nonneg
    have hD :
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p ≤ 1 :=
      D_m_env_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
        ρ_idx t m p
    simpa using (mul_le_mul_of_nonneg_left hD hμ0)

  have h_sum_one : (∑ p : Fin t → Step, μρ.real {p} * (1 : ℝ)) = 1 := by
    -- `μρ` is a probability measure, so the real mass of `univ` is `1`.
    simp [MeasureTheory.probReal_univ (μ := μρ)]

  calc
    (∫ p : Fin t → Step,
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p ∂μρ)
        = ∑ p : Fin t → Step,
            μρ.real {p} *
              D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                ρ_idx t m p := h_sum
    _ ≤ ∑ p : Fin t → Step, μρ.real {p} * (1 : ℝ) := h_le
    _ = 1 := h_sum_one

/-- Leike’s “expected TV vanishes” statement: the expected `F_m` term under the mixture prefix marginal
tends to `0`. -/
theorem tendsto_integral_F_m_prefix (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (m : ℕ) :
    Tendsto
        (fun t =>
          ∫ p : Fin t → Step,
            F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
        atTop (nhds 0) := by
  classical
  -- Use the series expansion from `integral_F_m_prefix_eq_tsum_prior_toReal_mul_integral_D_m_env_prefix`
  -- and apply Tannery dominated convergence.
  let f : ℕ → EnvironmentIndex → ℝ := fun t ρ_idx =>
    (prior.weight ρ_idx).toReal *
      (∫ p : Fin t → Step,
        D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p
        ∂(prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t))
  let bound : EnvironmentIndex → ℝ := fun ρ_idx => (prior.weight ρ_idx).toReal

  have h_bound_summable : Summable bound := by
    have hsum_ne_top : (∑' ρ_idx : EnvironmentIndex, prior.weight ρ_idx) ≠ ∞ :=
      (lt_of_le_of_lt prior.tsum_le_one ENNReal.one_lt_top).ne
    simpa [bound] using ENNReal.summable_toReal (f := prior.weight) hsum_ne_top

  have h_term : ∀ ρ_idx : EnvironmentIndex, Tendsto (fun t => f t ρ_idx) atTop (nhds 0) := by
    intro ρ_idx
    have hI :=
      tendsto_integral_posteriorWeight_toReal_mul_D_m_env_prefix (O := O) (M := M) (prior := prior) (envs := envs)
        (π := π) (h_stoch := h_stoch) (ρ_idx := ρ_idx) (m := m)
    have hEq :
        (fun t =>
          ∫ p : Fin t → Step,
            (bayesianPosteriorWeight O M prior envs ρ_idx (prefixToHistory t p)).toReal *
                D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
                  ρ_idx t m p
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
          =
        (fun t => f t ρ_idx) := by
      funext t
      simpa [f] using
        (integral_posteriorWeight_toReal_mul_D_m_env_prefix (O := O) (M := M) (prior := prior) (envs := envs)
          (π := π) (h_stoch := h_stoch) (ρ_idx := ρ_idx) (t := t) (m := m))
    simpa [hEq] using hI

  have h_dom : ∀ᶠ t in atTop, ∀ ρ_idx, ‖f t ρ_idx‖ ≤ bound ρ_idx := by
    refine Filter.Eventually.of_forall ?_
    intro t ρ_idx
    have hw : 0 ≤ (prior.weight ρ_idx).toReal := ENNReal.toReal_nonneg
    have hInt_le : (∫ p : Fin t → Step,
          D_m_env (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
            ρ_idx t m p
          ∂(prefixMeasureWithPolicy (envs ρ_idx) π (h_stoch ρ_idx) t)) ≤ 1 :=
      integral_D_m_env_prefix_le_one (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
        (h_stoch := h_stoch) (ρ_idx := ρ_idx) (t := t) (m := m)
    have h_prod_nonneg : 0 ≤ f t ρ_idx :=
      mul_nonneg hw (MeasureTheory.integral_nonneg (fun p =>
        D_m_env_nonneg (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch)
          ρ_idx t m p))
    have h_le : f t ρ_idx ≤ bound ρ_idx := by
      simpa [f, bound, mul_one] using (mul_le_mul_of_nonneg_left hInt_le hw)
    have hnorm : ‖f t ρ_idx‖ = f t ρ_idx := Real.norm_of_nonneg h_prod_nonneg
    simpa [hnorm] using h_le

  have h_tsum :
      Tendsto (fun t => ∑' ρ_idx, f t ρ_idx) atTop (nhds (∑' _ : EnvironmentIndex, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence (β := EnvironmentIndex) (G := ℝ) (f := f) (g := fun _ => (0 : ℝ))
      (bound := bound) h_bound_summable h_term h_dom

  have h_series :
      (fun t =>
          ∫ p : Fin t → Step,
            F_m (O := O) (M := M) (prior := prior) (envs := envs) (π := π) (h_stoch := h_stoch) t m p
            ∂(prefixMeasureMixtureWithPolicy O M prior envs π h_stoch t))
        =
      (fun t => ∑' ρ_idx : EnvironmentIndex, f t ρ_idx) := by
    funext t
    simpa [f] using
      (integral_F_m_prefix_eq_tsum_prior_toReal_mul_integral_D_m_env_prefix (O := O) (M := M) (prior := prior)
        (envs := envs) (π := π) (h_stoch := h_stoch) (t := t) (m := m))

  have : Tendsto (fun t => ∑' ρ_idx : EnvironmentIndex, f t ρ_idx) atTop (nhds 0) := by
    simpa using h_tsum
  simpa [h_series] using this

end LeikeExpectation

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ExpectedTotalVariation
