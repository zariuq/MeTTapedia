import Mettapedia.Logic.MarkovDeFinettiHardEuler
import Mettapedia.Logic.MarkovDeFinettiHardBESTCore
import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical
import Mettapedia.Logic.MarkovDeFinettiHardCopyPerm
import Mettapedia.Logic.MarkovDeFinettiHardEulerTrails
import Mettapedia.Logic.MarkovDeFinettiHardExcursionBridge
import Mettapedia.Logic.DiaconisFreedmanFinite

/-! LLM primer:
- `MarkovState k` encodes (start : Fin k, counts : TransCounts k).
- `fiber k N eN` = trajectories of length N whose `stateOfTraj` = eN.
- The BEST theorem: #EulerTrails = #arborescences(root) × ∏_{v} (outdeg(v) - 1)!

Status: the decomposition interface is explicit.
`excursion_bound_from_decomposition` now consumes a semantic core package
(`ExcursionBiapproxPackage`) instead of a false exact WR-bridge identity.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardBEST

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiHardEuler
open Mettapedia.Logic.MarkovDeFinettiHardCopyPerm
open Mettapedia.Logic.MarkovDeFinettiHardEulerTrails
open Mettapedia.Logic.MarkovDeFinettiHardEulerTrailFiber
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHardExcursionBridge
open Mettapedia.Logic.MarkovDeFinettiHardBESTCore
open Mettapedia.Logic.EvidenceDirichlet

variable {k : ℕ}

/-! ## Excursion-count helpers -/

lemma excursionListOfTraj_length {n : ℕ} (xs : Traj k n) :
    (excursionListOfTraj (k := k) xs).length = numExcursions (k := k) xs := by
  simp [excursionListOfTraj, excursionsOfTraj, length_excursionPairs]

lemma excursionMultiset_card_eq_numExcursions {n : ℕ} (xs : Traj k n) :
    (excursionMultiset (k := k) (excursionListOfTraj (k := k) xs)).card =
      numExcursions (k := k) xs := by
  simp [excursionMultiset, excursionListOfTraj_length]

/-- Number of excursions in the first `n` transitions of a trajectory. -/
def prefixExcursionCount {n N : ℕ} (hN : n ≤ N) (xs : Traj k N) : ℕ :=
  numExcursions (k := k) (trajPrefix (k := k) hN xs)

lemma prefixExcursionCount_le_n {n N : ℕ} (hN : n ≤ N) (xs : Traj k N) :
    prefixExcursionCount (k := k) hN xs ≤ n := by
  unfold prefixExcursionCount numExcursions
  have hcard : (returnPositions (k := k) (trajPrefix (k := k) hN xs)).card ≤ n + 1 := by
    have := Finset.card_le_univ (returnPositions (k := k) (trajPrefix (k := k) hN xs))
    simpa [Fintype.card_fin] using this
  omega

/-- The excursion list of any trajectory in the fiber of `s` has length
`returnsToStart s`. -/
lemma excursionList_length_eq_returnsToStart
    {N : ℕ} (s : MarkovState k) (xs : Traj k N) (hxs : xs ∈ fiber k N s) :
    (excursionListOfTraj (k := k) xs).length = returnsToStart (k := k) s := by
  have h1 := excursionListOfTraj_length (k := k) xs
  have h2 := numExcursions_eq_returnsToStart (k := k) xs
  have h3 : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
  rw [h1, h2, h3]

/-! ## Empirical parameter step probability -/

/-- `empiricalStepProb` is nonneg. -/
lemma empiricalStepProb_nonneg' (hk : 0 < k) (c : TransCounts k) (a b : Fin k) :
    0 ≤ empiricalStepProb (k := k) hk c a b := by
  unfold empiricalStepProb
  apply div_nonneg
  · have h1 : 0 ≤ (c.counts a b : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 ≤ (DirichletParams.uniformPrior (k := k)).priorParams b := by
      simp [DirichletParams.uniformPrior, DirichletParams.uniform]
    linarith
  · have h1 : 0 ≤ (c.rowTotal a : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 < (DirichletParams.uniformPrior (k := k)).totalConcentration :=
      DirichletParams.totalConcentration_pos (k := k) (p := DirichletParams.uniformPrior) hk
    linarith

/-- `stepProb` of the empirical parameter equals the Laplace-smoothed empirical probability,
cast to NNReal. -/
lemma stepProb_empiricalParam (hk : 0 < k) (s : MarkovState k) (a b : Fin k) :
    (stepProb (k := k) (empiricalParam (k := k) hk s) a b : ℝ) =
      empiricalStepProb (k := k) hk s.counts a b := by
  unfold stepProb empiricalParam empiricalRowMeasure
  dsimp only []
  rw [MeasureTheory.ProbabilityMeasure.mk_apply]
  have hsingle :
      (empiricalRowPMF (k := k) hk s.counts a).toMeasure (Set.singleton b) =
        empiricalRowPMF (k := k) hk s.counts a b := by
    exact PMF.toMeasure_apply_singleton
      (p := empiricalRowPMF (k := k) hk s.counts a)
      (a := b)
      (h := measurableSet_singleton b)
  rw [hsingle]
  simp only [empiricalRowPMF, PMF.ofFinset_apply]
  rw [ENNReal.coe_toNNReal_eq_toReal]
  exact ENNReal.toReal_ofReal (empiricalStepProb_nonneg' hk s.counts a b)

/-- Row-normalized empirical transition probability without Laplace smoothing,
with uniform fallback on empty rows. -/
def empiricalStepProbTarget (_hk : 0 < k) (c : TransCounts k) (prev next : Fin k) : ℝ :=
  if _hrow : c.rowTotal prev = 0 then
    (1 : ℝ) / (k : ℝ)
  else
    (c.counts prev next : ℝ) / (c.rowTotal prev : ℝ)

lemma empiricalStepProbTarget_nonneg (hk : 0 < k) (c : TransCounts k) (prev next : Fin k) :
    0 ≤ empiricalStepProbTarget (k := k) hk c prev next := by
  by_cases hr : c.rowTotal prev = 0
  · simp [empiricalStepProbTarget, hr, one_div, inv_nonneg, Nat.cast_nonneg]
  · have hnum : 0 ≤ (c.counts prev next : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hden : 0 ≤ (c.rowTotal prev : ℝ) := by exact_mod_cast (Nat.zero_le _)
    simp [empiricalStepProbTarget, hr, div_nonneg hnum hden]

lemma empiricalStepProbTarget_sum (hk : 0 < k) (c : TransCounts k) (prev : Fin k) :
    (∑ j : Fin k, empiricalStepProbTarget (k := k) hk c prev j) = 1 := by
  classical
  by_cases hr : c.rowTotal prev = 0
  · have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    -- uniform fallback on empty rows
    calc
      (∑ j : Fin k, empiricalStepProbTarget (k := k) hk c prev j)
          = ∑ j : Fin k, (1 : ℝ) / (k : ℝ) := by simp [empiricalStepProbTarget, hr]
      _ = (Fintype.card (Fin k) : ℝ) * ((1 : ℝ) / (k : ℝ)) := by
            simp [Finset.sum_const, Finset.card_univ]
      _ = 1 := by
            simp [Fintype.card_fin, hk_ne]
  · have hrow :
        (c.rowTotal prev : ℝ) = ∑ j : Fin k, (c.counts prev j : ℝ) := by
          simp [TransCounts.rowTotal]
    have hne : (c.rowTotal prev : ℝ) ≠ 0 := by
      exact_mod_cast hr
    have hsum_ne : (∑ j : Fin k, (c.counts prev j : ℝ)) ≠ 0 := by
      simpa [hrow] using hne
    calc
      (∑ j : Fin k, empiricalStepProbTarget (k := k) hk c prev j)
          = ∑ j : Fin k, (c.counts prev j : ℝ) / (c.rowTotal prev : ℝ) := by
                simp [empiricalStepProbTarget, hr]
      _ = (∑ j : Fin k, (c.counts prev j : ℝ)) / (c.rowTotal prev : ℝ) := by
            simp [div_eq_mul_inv, Finset.sum_mul]
      _ = 1 := by
            simp [hrow, hsum_ne]

/-- Target PMF for a single transition row, using the unsmoothed empirical ratios. -/
def empiricalRowPMFTarget (hk : 0 < k) (c : TransCounts k) (prev : Fin k) : PMF (Fin k) :=
  PMF.ofFinset
    (fun j => ENNReal.ofReal (empiricalStepProbTarget (k := k) hk c prev j))
    (Finset.univ)
    (by
      have hsum : (∑ j : Fin k, empiricalStepProbTarget (k := k) hk c prev j) = 1 :=
        empiricalStepProbTarget_sum (k := k) hk c prev
      have hsum' :
          ENNReal.ofReal (∑ j : Fin k, empiricalStepProbTarget (k := k) hk c prev j) =
            (∑ j : Fin k, ENNReal.ofReal (empiricalStepProbTarget (k := k) hk c prev j)) := by
        simpa using
          (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
            (f := fun j => empiricalStepProbTarget (k := k) hk c prev j)
            (by intro j hj; exact empiricalStepProbTarget_nonneg (k := k) hk c prev j))
      simpa [hsum] using hsum'.symm
    )
    (by
      intro j hj
      exact (hj (Finset.mem_univ j)).elim)

/-- Target transition measure for a fixed row (unsmoothed). -/
def empiricalRowMeasureTarget (hk : 0 < k) (c : TransCounts k) (prev : Fin k) :
    MeasureTheory.ProbabilityMeasure (Fin k) :=
  ⟨(empiricalRowPMFTarget (k := k) hk c prev).toMeasure, by infer_instance⟩

/-- Unsmooth only the start row: use the target row at `start`,
and the Laplace-smoothed rows elsewhere. -/
def empiricalParamStartTarget (hk : 0 < k) (s : MarkovState k) : MarkovParam k :=
  ⟨
    ⟨MeasureTheory.Measure.dirac s.start, by infer_instance⟩,
    fun a =>
      if h : a = s.start then
        empiricalRowMeasureTarget (k := k) hk s.counts a
      else
        empiricalRowMeasure (k := k) hk s.counts a
  ⟩

lemma stepProb_empiricalParamStartTarget (hk : 0 < k) (s : MarkovState k) (a b : Fin k) :
    (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) a b : ℝ) =
      if a = s.start then
        empiricalStepProbTarget (k := k) hk s.counts a b
      else
        empiricalStepProb (k := k) hk s.counts a b := by
  by_cases h : a = s.start
  · -- target row
    unfold stepProb empiricalParamStartTarget
    dsimp only []
    have hrow :
        (if h' : a = s.start then
          empiricalRowMeasureTarget (k := k) hk s.counts a
        else
          empiricalRowMeasure (k := k) hk s.counts a) =
          empiricalRowMeasureTarget (k := k) hk s.counts a := by
      simp [h]
    rw [hrow]
    unfold empiricalRowMeasureTarget
    rw [MeasureTheory.ProbabilityMeasure.mk_apply]
    have hsingle :
        (empiricalRowPMFTarget (k := k) hk s.counts a).toMeasure (Set.singleton b) =
          empiricalRowPMFTarget (k := k) hk s.counts a b := by
      exact PMF.toMeasure_apply_singleton
        (p := empiricalRowPMFTarget (k := k) hk s.counts a)
        (a := b)
        (h := measurableSet_singleton b)
    rw [hsingle]
    simp only [empiricalRowPMFTarget, PMF.ofFinset_apply]
    rw [ENNReal.coe_toNNReal_eq_toReal]
    simpa [h] using
      (ENNReal.toReal_ofReal
        (empiricalStepProbTarget_nonneg (k := k) hk s.counts a b))
  · have hstep :
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) a b : ℝ) =
          (stepProb (k := k) (empiricalParam (k := k) hk s) a b : ℝ) := by
        unfold stepProb empiricalParamStartTarget empiricalParam
        simp [h]
    simpa [h, hstep] using
      (stepProb_empiricalParam (k := k) (hk := hk) (s := s) (a := a) (b := b))


private lemma counts_le_rowTotal (c : TransCounts k) (prev next : Fin k) :
    c.counts prev next ≤ c.rowTotal prev := by
  unfold TransCounts.rowTotal
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

/-- Per-step Laplace-vs-target transition error,
bounded by `k / (rowTotal + k)`. -/
lemma abs_empiricalStepProb_sub_target_le_k_div_rowTotalPlusK
    (hk : 0 < k) (c : TransCounts k) (prev next : Fin k) :
    |empiricalStepProb (k := k) hk c prev next -
        empiricalStepProbTarget (k := k) hk c prev next| ≤
      (k : ℝ) / ((c.rowTotal prev : ℝ) + (k : ℝ)) := by
  by_cases hr : c.rowTotal prev = 0
  · have hsum0 : (∑ a : Fin k, c.counts prev a) = 0 := by
      simpa [TransCounts.rowTotal] using hr
    have hcount0 : c.counts prev next = 0 := by
      have hzeroAll := Finset.sum_eq_zero_iff.mp hsum0
      exact hzeroAll next (by simp)
    have hemp :
        empiricalStepProb (k := k) hk c prev next = (1 : ℝ) / (k : ℝ) := by
      simp [empiricalStepProb, hr, hcount0,
        DirichletParams.uniformPrior, DirichletParams.uniform,
        DirichletParams.totalConcentration]
    calc
      |empiricalStepProb (k := k) hk c prev next -
          empiricalStepProbTarget (k := k) hk c prev next|
          = 0 := by simp [empiricalStepProbTarget, hr, hemp]
      _ ≤ (k : ℝ) / ((c.rowTotal prev : ℝ) + (k : ℝ)) := by
        have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
        have hden_nonneg : 0 ≤ (c.rowTotal prev : ℝ) + (k : ℝ) := by
          have hrow_nonneg : 0 ≤ (c.rowTotal prev : ℝ) := by
            exact_mod_cast (Nat.zero_le (c.rowTotal prev))
          linarith
        exact div_nonneg hk_nonneg hden_nonneg
  · let rN : ℕ := c.rowTotal prev
    let xN : ℕ := c.counts prev next
    have hrN_pos : 0 < rN := by
      exact Nat.pos_of_ne_zero (by simpa [rN] using hr)
    have hrN_ne : (rN : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hrN_pos)
    have hk_real_pos : 0 < (k : ℝ) := by
      exact_mod_cast hk
    have hden_pos : 0 < (rN : ℝ) + (k : ℝ) := by linarith
    have hcount_le_nat : xN ≤ rN := by
      simpa [xN, rN] using counts_le_rowTotal (c := c) (prev := prev) (next := next)
    have hx_nonneg : 0 ≤ (xN : ℝ) := by exact_mod_cast (Nat.zero_le xN)
    have hx_le : (xN : ℝ) ≤ (rN : ℝ) := by exact_mod_cast hcount_le_nat
    have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hemp :
        empiricalStepProb (k := k) hk c prev next =
          ((xN : ℝ) + 1) / ((rN : ℝ) + (k : ℝ)) := by
      simp [empiricalStepProb, rN, xN,
        DirichletParams.uniformPrior, DirichletParams.uniform,
        DirichletParams.totalConcentration]
    have htarget :
        empiricalStepProbTarget (k := k) hk c prev next =
          (xN : ℝ) / (rN : ℝ) := by
      simp [empiricalStepProbTarget, hr, rN, xN]
    have hden_ne : (rN : ℝ) + (k : ℝ) ≠ 0 := by linarith
    have hrew :
        ((xN : ℝ) + 1) / ((rN : ℝ) + (k : ℝ)) - (xN : ℝ) / (rN : ℝ) =
          ((rN : ℝ) - (k : ℝ) * (xN : ℝ)) /
            ((rN : ℝ) * ((rN : ℝ) + (k : ℝ))) := by
      field_simp [hrN_ne, hden_ne]
      ring
    have hr_nonneg : 0 ≤ (rN : ℝ) := by positivity
    have hk_ge_one_nat : 1 ≤ k := Nat.succ_le_of_lt hk
    have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_one_nat
    have hnum_bound :
        |(rN : ℝ) - (k : ℝ) * (xN : ℝ)| ≤ (k : ℝ) * (rN : ℝ) := by
      have hupper1 : (rN : ℝ) - (k : ℝ) * (xN : ℝ) ≤ (rN : ℝ) := by
        nlinarith [hk_nonneg, hx_nonneg]
      have hupper2 : (rN : ℝ) ≤ (k : ℝ) * (rN : ℝ) := by
        nlinarith [hk_ge_one, hr_nonneg]
      have hupper : (rN : ℝ) - (k : ℝ) * (xN : ℝ) ≤ (k : ℝ) * (rN : ℝ) :=
        le_trans hupper1 hupper2
      have hlower1 :
          (rN : ℝ) - (k : ℝ) * (rN : ℝ) ≤
            (rN : ℝ) - (k : ℝ) * (xN : ℝ) := by
        nlinarith [hk_nonneg, hx_le]
      have hlower2 :
          -((k : ℝ) * (rN : ℝ)) ≤ (rN : ℝ) - (k : ℝ) * (rN : ℝ) := by
        nlinarith [hr_nonneg]
      have hlower : -((k : ℝ) * (rN : ℝ)) ≤ (rN : ℝ) - (k : ℝ) * (xN : ℝ) :=
        le_trans hlower2 hlower1
      exact abs_le.mpr ⟨hlower, hupper⟩
    have hden_prod_nonneg : 0 ≤ (rN : ℝ) * ((rN : ℝ) + (k : ℝ)) := by
      positivity
    have habs_rewrite :
        |((xN : ℝ) + 1) / ((rN : ℝ) + (k : ℝ)) - (xN : ℝ) / (rN : ℝ)| =
          |(rN : ℝ) - (k : ℝ) * (xN : ℝ)| /
            ((rN : ℝ) * ((rN : ℝ) + (k : ℝ))) := by
      rw [hrew, abs_div]
      simp [abs_of_nonneg hden_prod_nonneg]
    have hfrac :
        |(rN : ℝ) - (k : ℝ) * (xN : ℝ)| /
            ((rN : ℝ) * ((rN : ℝ) + (k : ℝ))) ≤
          ((k : ℝ) * (rN : ℝ)) /
            ((rN : ℝ) * ((rN : ℝ) + (k : ℝ))) := by
      exact div_le_div_of_nonneg_right hnum_bound hden_prod_nonneg
    have hcancel :
        ((k : ℝ) * (rN : ℝ)) /
            ((rN : ℝ) * ((rN : ℝ) + (k : ℝ))) =
          (k : ℝ) / ((rN : ℝ) + (k : ℝ)) := by
      field_simp [hrN_ne]
    have hcore :
        |((xN : ℝ) + 1) / ((rN : ℝ) + (k : ℝ)) - (xN : ℝ) / (rN : ℝ)| ≤
          (k : ℝ) / ((rN : ℝ) + (k : ℝ)) := by
      calc
        |((xN : ℝ) + 1) / ((rN : ℝ) + (k : ℝ)) - (xN : ℝ) / (rN : ℝ)|
            = |(rN : ℝ) - (k : ℝ) * (xN : ℝ)| /
                ((rN : ℝ) * ((rN : ℝ) + (k : ℝ))) := habs_rewrite
        _ ≤ ((k : ℝ) * (rN : ℝ)) /
              ((rN : ℝ) * ((rN : ℝ) + (k : ℝ))) := hfrac
        _ = (k : ℝ) / ((rN : ℝ) + (k : ℝ)) := hcancel
    calc
      |empiricalStepProb (k := k) hk c prev next -
          empiricalStepProbTarget (k := k) hk c prev next|
          = |((xN : ℝ) + 1) / ((rN : ℝ) + (k : ℝ)) - (xN : ℝ) / (rN : ℝ)| := by
              simp [hemp, htarget]
      _ ≤ (k : ℝ) / ((rN : ℝ) + (k : ℝ)) := hcore
      _ = (k : ℝ) / ((c.rowTotal prev : ℝ) + (k : ℝ)) := by simp [rN]

/-- Per-step Laplace-vs-target transition error in explicit `c / L` form,
assuming `L ≤ rowTotal + k`. -/
lemma abs_empiricalStepProb_sub_target_le_k_div_L
    (hk : 0 < k) (c : TransCounts k) (prev next : Fin k)
    (L : ℕ) (hLpos : 0 < L)
    (hL : (L : ℝ) ≤ (c.rowTotal prev : ℝ) + (k : ℝ)) :
    |empiricalStepProb (k := k) hk c prev next -
        empiricalStepProbTarget (k := k) hk c prev next| ≤
      (k : ℝ) / (L : ℝ) := by
  have hbase :=
    abs_empiricalStepProb_sub_target_le_k_div_rowTotalPlusK
      (k := k) (hk := hk) (c := c) (prev := prev) (next := next)
  have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hinv : ((c.rowTotal prev : ℝ) + (k : ℝ))⁻¹ ≤ (L : ℝ)⁻¹ := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by exact_mod_cast hLpos) hL)
  have hmul :
      (k : ℝ) * (((c.rowTotal prev : ℝ) + (k : ℝ))⁻¹) ≤
        (k : ℝ) * ((L : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hinv hk_nonneg
  exact le_trans hbase (by simpa [div_eq_mul_inv] using hmul)

/-- For realizable states, the start-row total dominates the return-to-start count. -/
lemma returnsToStart_le_rowTotal_start_of_mem_stateFinset
    {N : ℕ} {s : MarkovState k} (hs : s ∈ stateFinset k N) :
    returnsToStart (k := k) s ≤ s.counts.rowTotal s.start := by
  have hbal :=
    MarkovDeFinettiHardBESTCore.flow_balance_graphOfState_of_mem_stateFinset
      (k := k) hs s.start
  have hbal' :
      s.counts.rowTotal s.start + (if s.last = s.start then 1 else 0) =
        returnsToStart (k := k) s + 1 := by
    simpa [returnsToStart,
      MarkovDeFinettiHardBESTCore.outDeg_graphOfState_eq,
      MarkovDeFinettiHardBESTCore.inDeg_graphOfState_eq,
      MarkovDeFinettiHardEuler.outdeg] using hbal
  by_cases hlast : s.last = s.start
  · have hEq : s.counts.rowTotal s.start = returnsToStart (k := k) s := by
      have : s.counts.rowTotal s.start + 1 = returnsToStart (k := k) s + 1 := by
        simpa [hlast] using hbal'
      exact Nat.succ.inj this
    simpa [hEq] using le_rfl
  · have hEq : s.counts.rowTotal s.start = returnsToStart (k := k) s + 1 := by
      simpa [hlast] using hbal'
    have hle : returnsToStart (k := k) s ≤ returnsToStart (k := k) s + 1 := Nat.le_succ _
    simpa [hEq] using hle

/-- Real-cast denominator bridge from returns-to-start to start-row total plus `k`. -/
lemma returnsToStart_toReal_le_rowTotal_start_toReal_add_k_of_mem_stateFinset
    {N : ℕ} {s : MarkovState k} (hs : s ∈ stateFinset k N) :
    (returnsToStart (k := k) s : ℝ) ≤
      (s.counts.rowTotal s.start : ℝ) + (k : ℝ) := by
  have hnat : returnsToStart (k := k) s ≤ s.counts.rowTotal s.start :=
    returnsToStart_le_rowTotal_start_of_mem_stateFinset (k := k) hs
  have hcast : (returnsToStart (k := k) s : ℝ) ≤ (s.counts.rowTotal s.start : ℝ) := by
    exact_mod_cast hnat
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.zero_le k)
  linarith

/-- Start-row specialization of the per-step Laplace-vs-target bound in `k / R` form. -/
lemma abs_empiricalStepProb_sub_target_le_k_div_returnsToStart_start
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s)
    (next : Fin k) :
    |empiricalStepProb (k := k) hk s.counts s.start next -
        empiricalStepProbTarget (k := k) hk s.counts s.start next| ≤
      (k : ℝ) / (returnsToStart (k := k) s : ℝ) := by
  have hL :
      (returnsToStart (k := k) s : ℝ) ≤
        (s.counts.rowTotal s.start : ℝ) + (k : ℝ) :=
    returnsToStart_toReal_le_rowTotal_start_toReal_add_k_of_mem_stateFinset
      (k := k) hs
  exact
    abs_empiricalStepProb_sub_target_le_k_div_L
      (k := k) (hk := hk) (c := s.counts) (prev := s.start) (next := next)
      (L := returnsToStart (k := k) s) (hLpos := hRpos) (hL := hL)



lemma abs_stepProb_empiricalParam_sub_startTarget_le_k_div_returnsToStart
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s)
    (next : Fin k) :
    |(stepProb (k := k) (empiricalParam (k := k) hk s) s.start next : ℝ) -
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) s.start next : ℝ)| ≤
      (k : ℝ) / (returnsToStart (k := k) s : ℝ) := by
  -- reduce to the empiricalStepProb vs target bound at the start row
  have h1 :
      (stepProb (k := k) (empiricalParam (k := k) hk s) s.start next : ℝ) =
        empiricalStepProb (k := k) hk s.counts s.start next := by
    simpa using (stepProb_empiricalParam (k := k) (hk := hk) (s := s) (a := s.start) (b := next))
  have h2 :
      (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) s.start next : ℝ) =
        empiricalStepProbTarget (k := k) hk s.counts s.start next := by
    simpa using
      (stepProb_empiricalParamStartTarget (k := k) (hk := hk) (s := s) (a := s.start) (b := next))
  simpa [h1, h2] using
    (abs_empiricalStepProb_sub_target_le_k_div_returnsToStart_start
      (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (next := next))

/-- Start-row L1 kernel discrepancy between `empiricalParam` and `empiricalParamStartTarget`.

This is the finite-alphabet summation of the pointwise `k / returnsToStart` bound. -/
lemma sum_abs_stepProb_empiricalParam_sub_startTarget_start_le_k_sq_div_returnsToStart
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s) :
    (∑ next : Fin k,
      |(stepProb (k := k) (empiricalParam (k := k) hk s) s.start next : ℝ) -
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) s.start next : ℝ)|) ≤
      ((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
  have hpt :
      ∀ next : Fin k,
        |(stepProb (k := k) (empiricalParam (k := k) hk s) s.start next : ℝ) -
          (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) s.start next : ℝ)| ≤
        (k : ℝ) / (returnsToStart (k := k) s : ℝ) := by
    intro next
    exact
      abs_stepProb_empiricalParam_sub_startTarget_le_k_div_returnsToStart
        (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (next := next)
  calc
    (∑ next : Fin k,
      |(stepProb (k := k) (empiricalParam (k := k) hk s) s.start next : ℝ) -
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) s.start next : ℝ)|)
        ≤ ∑ _next : Fin k, (k : ℝ) / (returnsToStart (k := k) s : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro next hnext
          exact hpt next
    _ = (k : ℝ) * ((k : ℝ) / (returnsToStart (k := k) s : ℝ)) := by
          simp [Fintype.card_fin]
    _ = ((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
          ring

/-- Outside the start row, `empiricalParamStartTarget` equals `empiricalParam`. -/
lemma sum_abs_stepProb_empiricalParam_sub_startTarget_nonstart_eq_zero
    (hk : 0 < k) {s : MarkovState k} {prev : Fin k}
    (hprev : prev ≠ s.start) :
    (∑ next : Fin k,
      |(stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) -
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ)|) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro next hnext
  have hstepEq :
      (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ) =
        empiricalStepProb (k := k) hk s.counts prev next := by
    have h :=
      stepProb_empiricalParamStartTarget (k := k) (hk := hk) (s := s) (a := prev) (b := next)
    simp [hprev, empiricalStepProb] at h
    exact h
  have hempEq :
      (stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) =
        empiricalStepProb (k := k) hk s.counts prev next := by
    simpa using
      (stepProb_empiricalParam (k := k) (hk := hk) (s := s) (a := prev) (b := next))
  have : (stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) =
      (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ) := by
    simpa [hstepEq] using hempEq
  simp [this]

/-- Uniform rowwise L1 discrepancy bound for `empiricalParam` vs `empiricalParamStartTarget`.

Only the start row contributes; non-start rows are exactly equal. -/
lemma sum_abs_stepProb_empiricalParam_sub_startTarget_row_le_k_sq_div_returnsToStart
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s)
    (prev : Fin k) :
    (∑ next : Fin k,
      |(stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) -
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ)|) ≤
      ((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
  by_cases hprev : prev = s.start
  · subst hprev
    exact
      sum_abs_stepProb_empiricalParam_sub_startTarget_start_le_k_sq_div_returnsToStart
        (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos)
  · have hzero :
      (∑ next : Fin k,
        |(stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) -
          (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ)|) = 0 :=
      sum_abs_stepProb_empiricalParam_sub_startTarget_nonstart_eq_zero
        (k := k) (hk := hk) (s := s) (prev := prev) hprev
    have hnonneg :
        0 ≤ ((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
      have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
      have hR_nonneg : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
        exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s))
      exact div_nonneg (mul_nonneg hk_nonneg hk_nonneg) hR_nonneg
    simpa [hzero] using hnonneg

/-- Lift a pointwise excursion-step bound to a product bound via
`abs_excursionsProb_diff_le_length_mul_eps`. -/
lemma abs_excursionWithReplacementProb_sub_excursionsProb_target_le_length_mul_eps
    (elist pref : ExcursionList k)
    (target : ExcursionType k → ℝ)
    (ε : ℝ)
    (hstep :
      ∀ a ∈ pref,
        |empiricalExcursionProb (k := k) elist a - target a| ≤ ε)
    (htarget_range :
      ∀ a ∈ pref,
        0 ≤ target a ∧ target a ≤ 1) :
    |excursionWithReplacementProb (k := k) elist pref -
        excursionsProb (k := k) target pref| ≤
      (pref.length : ℝ) * ε := by
  have hrange :
      ∀ a ∈ pref,
        0 ≤ empiricalExcursionProb (k := k) elist a ∧
          empiricalExcursionProb (k := k) elist a ≤ 1 ∧
          0 ≤ target a ∧ target a ≤ 1 := by
    intro a ha
    refine ⟨?_, ?_, (htarget_range a ha).1, (htarget_range a ha).2⟩
    · simpa [empiricalExcursionProb] using
        (probWeight_nonneg
          ((excursionMultiset (k := k) elist).count a)
          ((excursionMultiset (k := k) elist).card))
    · simpa [empiricalExcursionProb] using
        (probWeight_le_one
          ((excursionMultiset (k := k) elist).count a)
          ((excursionMultiset (k := k) elist).card)
          (Multiset.count_le_card _ _))
  have hprod :=
    abs_excursionsProb_diff_le_length_mul_eps
      (k := k)
      (elist := pref)
      (p := empiricalExcursionProb (k := k) elist)
      (q := target)
      (ε := ε)
      hstep
      hrange
  have hwr :
      excursionsProb (k := k) (empiricalExcursionProb (k := k) elist) pref =
        excursionWithReplacementProb (k := k) elist pref := by
    simpa using (excursionsProb_eq_wrProb (k := k) elist pref)
  calc
    |excursionWithReplacementProb (k := k) elist pref -
        excursionsProb (k := k) target pref|
        = |excursionsProb (k := k) (empiricalExcursionProb (k := k) elist) pref -
            excursionsProb (k := k) target pref| := by
              simpa [hwr]
    _ ≤ (pref.length : ℝ) * ε := hprod

/-! ## wordProbNN of empiricalParam on fiber members -/

/-- For any trajectory `xs` in `fiber(N, s)`, `wordProbNN(empiricalParam(s), xs)` depends
only on `s` (not the choice of `xs`), since `wordProbNN` is constant on fibers. -/
lemma wordProbNN_empiricalParam_const_on_fiber
    (hk : 0 < k) {N : ℕ} (s : MarkovState k) {xs ys : Traj k N}
    (hxs : xs ∈ fiber k N s) (hys : ys ∈ fiber k N s) :
    wordProbNN (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) xs) =
      wordProbNN (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) := by
  have hstate_xs : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
  have hstate_ys : stateOfTraj (k := k) ys = s := (Finset.mem_filter.1 hys).2
  exact wordProbNN_const_on_state_fiber (k := k) (empiricalParam (k := k) hk s)
    (by rw [hstate_xs, hstate_ys])

/-- `W(N, s, θ) = |fiber(N, s)| × wordProb(θ, xs₀)` for any `xs₀ ∈ fiber(N, s)`,
since `wordProb` is constant on the fiber. -/
lemma W_eq_card_mul_wordProb_of_mem_fiber
    {N : ℕ} (θ : MarkovParam k) (s : MarkovState k)
    (xs₀ : Traj k N) (hxs₀ : xs₀ ∈ fiber k N s) :
    W (k := k) N s θ =
      (fiber k N s).card *
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
  classical
  simp only [W]
  have hfib : (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s) = fiber k N s := rfl
  rw [hfib]
  have hconst : ∀ xs ∈ fiber k N s,
      wordProb (k := k) θ (trajToList (k := k) xs) =
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
    intro xs hxs
    exact wordProb_const_on_state_fiber (k := k) θ
      (by rw [(Finset.mem_filter.1 hxs).2, (Finset.mem_filter.1 hxs₀).2])
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  simp [nsmul_eq_mul]

/-! ## Pattern index set `P(n,e,s)` and decomposition identities -/

/-- Finite excursion-prefix pattern set `P(n,e,s)`.

It includes:
1. patterns coming from long-horizon prefix fibers (`prefixFiber(hN,e,s)`), and
2. all short-horizon WR patterns in `fiber(n+1,e)`.

This shared index set lets the WOR and WR decompositions range over one finite
carrier; WR then has no residual term outside `P`. -/
def excursionPatternSet
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) : Finset (ExcursionList k) :=
  ((prefixFiber (k := k) (h := hN) e s).image
    (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))) ∪
  ((fiber k (Nat.succ n) e).image
    (fun ys => excursionListOfTraj (k := k) ys))

lemma mem_excursionPatternSet_of_prefixFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    {xs : Traj k N} (hxs : xs ∈ prefixFiber (k := k) (h := hN) e s) :
    excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) ∈
      ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)) := by
  refine Finset.mem_image.2 ?_
  refine ⟨trajPrefix (k := k) hN xs, ?_, rfl⟩
  -- The prefix trajectory has state `e` by definition of `prefixFiber`.
  have hstate : prefixState (k := k) hN xs = e := (Finset.mem_filter.1 hxs).2
  have htraj : trajPrefix (k := k) hN xs ∈ trajFinset k (Nat.succ n) := by
    simp [trajFinset]
  exact Finset.mem_filter.2 ⟨htraj, by simpa [prefixState] using hstate⟩

lemma excursionPatternSet_eq_shortImage
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    excursionPatternSet (k := k) (hN := hN) e s =
      ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)) := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    rcases Finset.mem_union.1 hp with hpL | hpR
    · rcases Finset.mem_image.1 hpL with ⟨xs, hxs, rfl⟩
      exact mem_excursionPatternSet_of_prefixFiber (k := k) (hN := hN) (e := e) (s := s) hxs
    · exact hpR
  · intro hp
    exact Finset.mem_union.2 (Or.inr hp)

/-- The `p`-fiber inside `prefixFiber(hN,e,s)`. -/
def prefixPatternFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    Finset (Traj k N) :=
  (prefixFiber (k := k) (h := hN) e s).filter
    (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p)

lemma segmentSwap_mem_prefixPatternFiber_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (xs : Traj k N) (hxs : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
      prefixPatternFiber (k := k) (hN := hN) e s p := by
  have hxs_pf : xs ∈ prefixFiber (k := k) (h := hN) e s := (Finset.mem_filter.1 hxs).1
  have hmem_pf :
      segmentSwap xs a L1 L2 hL1 hL2 hcN ∈ prefixFiber (k := k) (h := hN) e s :=
    segmentSwap_mem_prefixFiber_of_prefix_before_swap
      (k := k) (h := hN) (e := e) (eN := s) (xs := xs)
      (a := a) (L1 := L1) (L2 := L2) (hna := hna)
      (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
      (ha_ret := ha_ret) (hb_ret := hb_ret) (hc_ret := hc_ret) hxs_pf
  have hpat : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
    (Finset.mem_filter.1 hxs).2
  have hprefix_eq :
      trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        trajPrefix (k := k) hN xs :=
    trajPrefix_segmentSwap_eq_of_prefix_before_swap
      (k := k) (h := hN) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      (hna := hna) (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
  refine Finset.mem_filter.2 ?_
  refine ⟨hmem_pf, ?_⟩
  simpa [hprefix_eq] using hpat

lemma card_image_segmentSwap_prefixPatternFiber_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (_hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    ((prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card =
      (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
  classical
  refine Finset.card_image_iff.mpr ?_
  intro x hx y hy hxy
  exact segmentSwap_injective (k := k) (a := a) (L1 := L1) (L2 := L2)
    (hL1 := hL1) (hL2 := hL2) (hcN := hcN) hxy

/-- Build an image-equality witness for prefix-pattern fibers from
forward/backward segment-swap membership maps. -/
lemma image_eq_segmentSwap_prefixPatternFiber_of_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (hmap :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
          prefixPatternFiber (k := k) (hN := hN) e s q)
    (hmapInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1 (by omega) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p) :
    (prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      prefixPatternFiber (k := k) (hN := hN) e s q := by
  classical
  apply Finset.Subset.antisymm
  · intro ys hys
    rcases Finset.mem_image.1 hys with ⟨xs, hxs, rfl⟩
    exact hmap xs hxs
  · intro ys hys
    refine Finset.mem_image.2 ?_
    refine ⟨segmentSwap ys a L2 L1 hL2 hL1 (by omega), hmapInv ys hys, ?_⟩
    -- involution with swapped lengths
    simpa using
      (segmentSwap_involutive (k := k) ys a L2 L1 hL2 hL1 (by omega))

/-- WOR-side mass for pattern `p`: cardinality ratio in the long-horizon fiber. -/
def worPatternMass
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
    ((fiber k N s).card : ENNReal)

/-- Pattern ratio inside the long-prefix fiber:
`|prefixPatternFiber(hN,e,s,p)| / |prefixFiber(hN,e,s)|`. -/
def prefixPatternRatio
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
    ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)

/-- WR-side mass for pattern `p`: indicator-sum over short trajectories in `fiber(n+1,e)`. -/
def wrPatternMass
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ∑ ys ∈ fiber k (Nat.succ n) e,
    if excursionListOfTraj (k := k) ys = p then
      wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys)
    else 0

/-- The short-horizon trajectories in state `e` with excursion list exactly `p`. -/
def shortPatternFiber
    (n : ℕ) (e : MarkovState k) (p : ExcursionList k) : Finset (Traj k (Nat.succ n)) :=
  (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p)

/-! ## Helper list lemmas for adjacent-excursion swaps -/

def excLen (e : ExcursionType k) : ℕ :=
  e.length - 1

def excSteps (l : ExcursionList k) : ℕ :=
  (l.map excLen).sum

lemma excLen_trajSegment_of_excursionPair
    {n : ℕ} (ys : Traj k n)
    {p : Fin (n + 1) × Fin (n + 1)}
    (hp : p ∈ excursionPairs (k := k) ys) :
    excLen (k := k) (trajSegment (k := k) ys p.1 p.2) =
      p.2.1 - p.1.1 := by
  have hp_lt : p.1 < p.2 := fst_lt_snd_of_mem_excursionPairs (k := k) ys hp
  have hp_le : p.1 ≤ p.2 := by exact (le_of_lt hp_lt)
  -- length = (p2 - p1 + 1), so length - 1 = p2 - p1
  have hlen :
      (trajSegment (k := k) ys p.1 p.2).length =
        p.2.1 - p.1.1 + 1 := by
    exact trajSegment_length (k := k) ys p.1 p.2 (by omega) (by omega) hp_le
  unfold excLen
  -- reduce with Nat arithmetic
  omega

lemma excSteps_preSeg_eq_sum_diffs
    {n : ℕ} (ys : Traj k n)
    (pre : List (Fin (n + 1) × Fin (n + 1)))
    (preSeg : ExcursionList k)
    (hpre : preSeg = pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2))
    (hmem : ∀ pr ∈ pre, pr ∈ excursionPairs (k := k) ys) :
    excSteps (k := k) preSeg =
      (pre.map (fun pr => pr.2.1 - pr.1.1)).sum := by
  classical
  subst hpre
  -- rewrite with excLen and map
  unfold excSteps
  simp only [List.map_map]
  have :
      pre.map (excLen (k := k) ∘ fun pr => trajSegment (k := k) ys pr.1 pr.2) =
        pre.map (fun pr => pr.2.1 - pr.1.1) := by
    apply List.map_congr_left
    intro pr hpr
    have hp : pr ∈ excursionPairs (k := k) ys := hmem pr hpr
    simpa [Function.comp, excLen_trajSegment_of_excursionPair (k := k) ys (p := pr) hp]
  rw [this]

-- A list-level reconstruction lemma: if l.zip l.tail decomposes as
-- pre ++ [p1, p2] ++ suf, then l = pre.map fst ++ [p1.1, p1.2, p2.2] ++ suf.map snd.
lemma list_eq_of_zip_tail_decomp
    {α : Type*} (l : List α)
    (pre suf : List (α × α)) (p1 p2 : α × α)
    (hpairs : l.zip l.tail = pre ++ [p1, p2] ++ suf) :
    l = pre.map Prod.fst ++ [p1.1, p1.2, p2.2] ++ suf.map Prod.snd := by
  revert l
  induction pre with
  | nil =>
      intro l hpairs
      simp only [List.nil_append, List.map_nil, List.cons_append] at hpairs ⊢
      -- hpairs : l.zip l.tail = p1 :: p2 :: suf
      cases l with
      | nil => simp at hpairs
      | cons a tl =>
          cases tl with
          | nil => simp at hpairs
          | cons b tl2 =>
              cases tl2 with
              | nil =>
                  simp [List.zip_cons_cons, List.tail_cons] at hpairs
              | cons c rest =>
                  simp only [List.tail_cons, List.zip_cons_cons, List.nil_append] at hpairs
                  -- hpairs : (a, b) :: (b, c) :: (c :: rest).zip rest = p1 :: p2 :: suf
                  have h1 : (a, b) = p1 := by injection hpairs
                  have h2tail : (b, c) :: (c :: rest).zip rest = p2 :: suf := by injection hpairs
                  have h2 : (b, c) = p2 := by injection h2tail
                  have hsuf : (c :: rest).zip rest = suf := by injection h2tail
                  subst h1; subst h2
                  simp only [Prod.fst, Prod.snd, List.cons.injEq, true_and]
                  -- goal : rest = suf.map Prod.snd
                  rw [← hsuf]; clear hsuf hpairs h2tail
                  induction rest generalizing c with
                  | nil => simp
                  | cons d ds ih =>
                      simp only [List.zip_cons_cons, List.map_cons, Prod.snd, List.cons.injEq,
                        true_and]
                      exact ih d
  | cons q qs ih =>
      intro l hpairs
      cases l with
      | nil => simp at hpairs
      | cons x xs =>
          cases xs with
          | nil => simp at hpairs
          | cons y ys =>
              simp only [List.tail_cons, List.zip_cons_cons, List.cons_append] at hpairs
              have hq : (x, y) = q := by injection hpairs
              have htail : (y :: ys).zip ys = qs ++ [p1, p2] ++ suf := by injection hpairs
              have hrec := ih (y :: ys) htail
              subst hq
              simp only [List.map_cons, List.cons_append]
              exact congrArg (List.cons x) hrec

-- Reconstruction lemma specialized to `returnPositionsList`.
lemma returnPositionsList_eq_of_excursionPairs_decomp
    {n : ℕ} (ys : Traj k n)
    (pre suf : List (Fin (n + 1) × Fin (n + 1)))
    (p1 p2 : Fin (n + 1) × Fin (n + 1))
    (hpairs : excursionPairs (k := k) ys = pre ++ [p1, p2] ++ suf) :
    returnPositionsList (k := k) ys =
      pre.map Prod.fst ++ [p1.1, p1.2, p2.2] ++ suf.map Prod.snd := by
  unfold excursionPairs at hpairs
  simpa [returnPositionsList] using
    (list_eq_of_zip_tail_decomp
      (l := returnPositionsList (k := k) ys)
      (pre := pre) (suf := suf) (p1 := p1) (p2 := p2) hpairs)

/-- If `l.zip l.tail = pre ++ [(x,y),(y,z)] ++ suf` and we form
`l' = pre.map Prod.fst ++ [x, w, z] ++ suf.map Prod.snd`,
then `l'.zip l'.tail = pre ++ [(x,w),(w,z)] ++ suf`. -/
private lemma zip_tail_replace_middle
    {α : Type*} (l : List α)
    (pre suf : List (α × α)) (x y z w : α)
    (hzip : l.zip l.tail = pre ++ [(x, y), (y, z)] ++ suf) :
    let l' := pre.map Prod.fst ++ [x, w, z] ++ suf.map Prod.snd
    l'.zip l'.tail = pre ++ [(x, w), (w, z)] ++ suf := by
  intro l'
  have hl := list_eq_of_zip_tail_decomp l pre suf (x, y) (y, z) hzip
  -- Extract the suffix zip property from the original hzip + hl
  have hsuf_zip : (z :: suf.map Prod.snd).zip (suf.map Prod.snd) = suf := by
    rw [hl] at hzip
    clear hl l l'
    induction pre with
    | nil =>
        simp only [List.nil_append, List.map_nil, List.tail_cons, List.zip_cons_cons,
          List.cons_append, List.cons.injEq] at hzip
        exact hzip.2.2
    | cons q qs ih_pre =>
        cases qs with
        | nil =>
            simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append,
              List.tail_cons, List.zip_cons_cons, List.cons.injEq] at hzip
            exact hzip.2.2.2
        | cons q' qs' =>
            simp only [List.map_cons, List.cons_append, List.tail_cons, List.zip_cons_cons,
              List.cons.injEq] at hzip
            exact ih_pre hzip.2
  -- Now prove the main result by induction on pre
  show l'.zip l'.tail = pre ++ [(x, w), (w, z)] ++ suf
  revert l hzip hl
  induction pre with
  | nil =>
      intro l hzip hl
      simp only [l', List.nil_append, List.map_nil, List.tail_cons, List.zip_cons_cons,
        List.cons_append, hsuf_zip]
  | cons q qs ih_pre =>
      intro l hzip hl
      rw [hl] at hzip
      show l'.zip l'.tail = (q :: qs) ++ [(x, w), (w, z)] ++ suf
      -- Case split on qs to allow zip_cons_cons to fire
      cases qs with
      | nil =>
          -- pre = [q], l = q.1 :: [x, y, z] ++ suf.map snd
          simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append,
            List.tail_cons, List.zip_cons_cons, List.cons.injEq] at hzip
          -- hzip.1 : (q.1, x) = q
          -- hzip.2.1 : (x, y) = (x, y)  (trivial)
          -- hzip.2.2.1 : (y, z) = (y, z)  (trivial)
          -- hzip.2.2.2 : (z :: suf.map snd).zip (suf.map snd) = suf
          simp only [l', List.map_cons, List.map_nil, List.nil_append, List.cons_append,
            List.tail_cons, List.zip_cons_cons, hsuf_zip, List.cons.injEq, and_true]
          exact hzip.1
      | cons q' qs' =>
          -- pre = q :: q' :: qs'
          simp only [List.map_cons, List.cons_append, List.tail_cons, List.zip_cons_cons,
            List.cons.injEq] at hzip
          obtain ⟨hq_eq, htail_zip⟩ := hzip
          -- hq_eq : (q.1, q'.1) = q
          -- htail_zip : rest about q' :: qs'
          have hl_tail := list_eq_of_zip_tail_decomp
            (q'.1 :: qs'.map Prod.fst ++ [x, y, z] ++ suf.map Prod.snd)
            (q' :: qs') suf (x, y) (y, z) htail_zip
          have ih_result := ih_pre
            (q'.1 :: qs'.map Prod.fst ++ [x, y, z] ++ suf.map Prod.snd)
            htail_zip hl_tail
          -- ih_result about (q' :: qs').map fst ++ [x,w,z] ++ suf.map snd
          simp only [l', List.map_cons, List.cons_append, List.tail_cons, List.zip_cons_cons,
            List.cons.injEq]
          exact ⟨hq_eq, ih_result⟩

/-- The crucial excursion-pairs transformation under segment swap.

If `excursionPairs xs` decomposes with middle pairs `(a,a+L1)` and `(a+L1,a+L1+L2)`,
then `excursionPairs (segmentSwap xs ...)` has middle pairs `(a,a+L2)` and `(a+L2,a+L1+L2)`,
with the same prefix and suffix. -/
lemma excursionPairs_segmentSwap_eq_swap_middle {N : ℕ} (xs : Traj k N) (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (pre suf : List (Fin (N + 1) × Fin (N + 1)))
    (hPairsOld :
      excursionPairs (k := k) xs =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0)
    (hnoret1 : ∀ (j : Fin (N + 1)), a < j.val → j.val < a + L1 → xs j ≠ xs 0)
    (hnoret2 : ∀ (j : Fin (N + 1)), a + L1 < j.val → j.val < a + L1 + L2 → xs j ≠ xs 0) :
    excursionPairs (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      pre ++
        [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
         (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
        suf := by
  classical
  let xs' := segmentSwap xs a L1 L2 hL1 hL2 hcN
  -- Step 1: Reconstruct sorted list from old excursionPairs decomposition
  have hRetOld := returnPositionsList_eq_of_excursionPairs_decomp
    (k := k) xs pre suf
    (⟨a, by omega⟩, ⟨a + L1, by omega⟩)
    (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)
    hPairsOld
  -- Step 2: The candidate new sorted list
  let l' : List (Fin (N + 1)) :=
    pre.map Prod.fst ++ [⟨a, by omega⟩, ⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩] ++
      suf.map Prod.snd
  -- Step 3: Show l' is strictly sorted
  have hSortedOld : (returnPositionsList (k := k) xs).SortedLT :=
    Finset.sortedLT_sort (returnPositions (k := k) xs)
  have hSortedNew : (returnPositionsList (k := k) xs').SortedLT :=
    Finset.sortedLT_sort (returnPositions (k := k) xs')
  have hSortedL' : l'.SortedLT := by
    rw [hRetOld] at hSortedOld
    rw [List.sortedLT_iff_pairwise] at hSortedOld ⊢
    change List.Pairwise (· < ·) (pre.map Prod.fst ++
      [⟨a, by omega⟩, ⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩] ++ suf.map Prod.snd)
    rw [List.append_assoc] at hSortedOld ⊢
    rw [List.pairwise_append] at hSortedOld ⊢
    obtain ⟨hPwPre, hPwMidSufOld, hCrossOld⟩ := hSortedOld
    -- Normalize Prod projections and list append structure
    simp only [Prod.fst, Prod.snd, List.cons_append, List.nil_append] at hPwMidSufOld hCrossOld ⊢
    refine ⟨hPwPre, ?_, ?_⟩
    · -- Pairwise (<) on ⟨a⟩ :: ⟨a+L2⟩ :: ⟨a+L1+L2⟩ :: suf.map snd
      rw [List.pairwise_cons] at hPwMidSufOld ⊢
      obtain ⟨ha_lt_all_old, hRestOld⟩ := hPwMidSufOld
      rw [List.pairwise_cons] at hRestOld ⊢
      obtain ⟨hL1_lt_all, hSufSorted⟩ := hRestOld
      constructor
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx_suf
        · exact Fin.mk_lt_mk.mpr (by omega)
        · exact ha_lt_all_old _ (.tail _ (.head _))
        · exact ha_lt_all_old x (.tail _ (.tail _ hx_suf))
      · constructor
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx_suf
          · exact Fin.mk_lt_mk.mpr (by omega)
          · rw [List.pairwise_cons] at hSufSorted
            exact lt_trans (Fin.mk_lt_mk.mpr (by omega)) (hSufSorted.1 x hx_suf)
        · exact hSufSorted
    · intro x hx y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy_suf
      · exact hCrossOld x hx _ (.head _)
      · exact lt_trans (hCrossOld x hx _ (.head _))
          (Fin.mk_lt_mk.mpr (by omega))
      · exact hCrossOld x hx _ (.tail _ (.tail _ (.head _)))
      · exact hCrossOld x hx y (.tail _ (.tail _ (.tail _ hy_suf)))
  -- Step 4: Show l' has same elements as returnPositionsList xs'
  have hRetSwap := returnPositions_segmentSwap_eq xs a L1 L2 hL1 hL2 hcN
    ha_ret hb_ret hc_ret hnoret1 hnoret2
  -- Helper: membership in returnPositions ↔ returnPositionsList
  have hMemRP : ∀ y, y ∈ returnPositions (k := k) xs ↔ y ∈ returnPositionsList (k := k) xs := by
    intro y; simp [returnPositionsList, Finset.mem_sort]
  -- Helper: decompose old returnPositionsList membership
  have hOldDecomp : ∀ y, y ∈ returnPositionsList (k := k) xs ↔
      (y ∈ pre.map Prod.fst ∨ y = ⟨a, by omega⟩ ∨ y = ⟨a + L1, by omega⟩ ∨
       y = ⟨a + L1 + L2, by omega⟩ ∨ y ∈ suf.map Prod.snd) := by
    intro y; rw [hRetOld]
    simp only [Prod.fst, Prod.snd, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
    tauto
  -- Helper: pre elements strictly less than ⟨a⟩
  have hpre_lt_a : ∀ y ∈ pre.map Prod.fst, y < (⟨a, by omega⟩ : Fin (N + 1)) := by
    have hsorted := hSortedOld
    rw [hRetOld, List.sortedLT_iff_pairwise] at hsorted
    simp only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append,
      List.pairwise_append] at hsorted
    exact fun y hy => hsorted.2.2 y hy _ (.head _)
  -- Helper: ⟨a+L1+L2⟩ < suf elements
  have hc_lt_suf : ∀ y ∈ suf.map Prod.snd,
      (⟨a + L1 + L2, by omega⟩ : Fin (N + 1)) < y := by
    have hsorted := hSortedOld
    rw [hRetOld, List.sortedLT_iff_pairwise] at hsorted
    simp only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append,
      List.pairwise_append, List.pairwise_cons] at hsorted
    exact hsorted.2.1.2.2.1
  have hMemEq : ∀ (x : Fin (N + 1)), x ∈ l' ↔ x ∈ returnPositionsList (k := k) xs' := by
    intro x
    rw [show returnPositionsList (k := k) xs' =
        (returnPositions (k := k) xs').sort (· ≤ ·) from rfl]
    rw [Finset.mem_sort, hRetSwap, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    -- Goal: x ∈ l' ↔ (x ≠ ⟨a+L1⟩ ∧ x ∈ returnPositions xs) ∨ x = ⟨a+L2⟩
    constructor
    · -- Forward: l' → (retPos xs \ {a+L1}) ∪ {a+L2}
      intro hx
      simp only [l', List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with (hx_pre | rfl | rfl | rfl) | hx_suf
      · -- x ∈ pre.map fst
        exact Or.inl ⟨(fun heq => absurd (heq ▸ hpre_lt_a x hx_pre)
            (by simp [Fin.lt_def])),
          (hMemRP x).2 ((hOldDecomp x).2 (Or.inl hx_pre))⟩
      · -- x = ⟨a⟩
        exact Or.inl ⟨(fun heq => absurd heq (by simp [Fin.ext_iff]; omega)),
          (hMemRP _).2 ((hOldDecomp _).2 (Or.inr (Or.inl rfl)))⟩
      · -- x = ⟨a+L2⟩
        exact Or.inr rfl
      · -- x = ⟨a+L1+L2⟩
        exact Or.inl ⟨(fun heq => absurd heq (by simp [Fin.ext_iff]; omega)),
          (hMemRP _).2 ((hOldDecomp _).2
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
      · -- x ∈ suf.map snd
        exact Or.inl ⟨(fun heq => absurd (heq ▸ hc_lt_suf x hx_suf)
            (by simp [Fin.lt_def])),
          (hMemRP x).2 ((hOldDecomp x).2
            (Or.inr (Or.inr (Or.inr (Or.inr hx_suf)))))⟩
    · -- Backward: (retPos xs \ {a+L1}) ∪ {a+L2} → l'
      intro hx
      simp only [l', List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
      rcases hx with ⟨hne, hx_mem⟩ | rfl
      · have hx_old := (hOldDecomp x).1 ((hMemRP x).1 hx_mem)
        rcases hx_old with hx_pre | rfl | rfl | rfl | hx_suf
        · exact Or.inl (Or.inl hx_pre)
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact absurd rfl hne
        · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
        · exact Or.inr hx_suf
      · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  -- Step 5: Conclude l' = returnPositionsList xs'
  have hL'eq : l' = returnPositionsList (k := k) xs' :=
    List.SortedLT.eq_of_mem_iff hSortedL' hSortedNew hMemEq
  -- Step 6: Compute excursionPairs xs' via zip_tail_replace_middle
  have hEPNew : excursionPairs (k := k) xs' = l'.zip l'.tail := by
    unfold excursionPairs
    rw [← hL'eq]
  rw [hEPNew]
  exact zip_tail_replace_middle (returnPositionsList (k := k) xs) pre suf
    ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ⟨a + L2, by omega⟩
    (by unfold excursionPairs at hPairsOld; exact hPairsOld)

lemma returnPositionsList_get_zero {n : ℕ} (xs : Traj k n) :
    (returnPositionsList (k := k) xs).get
      ⟨0, by
        have hmem0 : (0 : Fin (n + 1)) ∈ returnPositions (k := k) xs := by
          simp [returnPositions]
        have hcard : 0 < (returnPositions (k := k) xs).card := by
          exact Finset.card_pos.mpr ⟨0, hmem0⟩
        simpa [length_returnPositionsList] using hcard⟩
      = (0 : Fin (n + 1)) := by
  classical
  have hmem0 : (0 : Fin (n + 1)) ∈ returnPositions (k := k) xs := by
    simp [returnPositions]
  have hne : (returnPositions (k := k) xs).Nonempty := ⟨0, hmem0⟩
  have hlen : 0 < (returnPositions (k := k) xs).sort.length := by
    have hcard : 0 < (returnPositions (k := k) xs).card := by
      exact Finset.card_pos.mpr ⟨0, hmem0⟩
    simpa [Finset.length_sort] using hcard
  have hmin :
      (returnPositions (k := k) xs).min' hne = (0 : Fin (n + 1)) := by
    apply (Finset.min'_eq_iff (s := returnPositions (k := k) xs) (H := hne)
      (a := (0 : Fin (n + 1)))).2
    constructor
    · exact hmem0
    · intro b hb
      exact Fin.zero_le b
  have hsorted :
      (returnPositions (k := k) xs).sort[0] =
        (returnPositions (k := k) xs).min' hne := by
    simpa using
      (Finset.sorted_zero_eq_min' (s := returnPositions (k := k) xs) (h := hlen))
  simpa [returnPositionsList, hmin] using hsorted

lemma returnPositionsList_getElem_zero
    {n : ℕ} (xs : Traj k n) (h0 : 0 < (returnPositionsList (k := k) xs).length) :
    (returnPositionsList (k := k) xs).get ⟨0, h0⟩ = (0 : Fin (n + 1)) := by
  exact returnPositionsList_get_zero (k := k) xs

lemma sum_diffs_zip_take_fin
    {n : ℕ} :
    ∀ (l : List (Fin (n + 1))) (h0 : 0 < l.length)
      (hMono : l.Pairwise (· ≤ ·)) (m : ℕ) (hm : m < l.length),
      (((l.zip l.tail).take m).map (fun pr => pr.2.1 - pr.1.1)).sum =
        (l[m]'hm).1 - (l[0]'h0).1 := by
  intro l h0 hMono m
  induction m generalizing l with
  | zero => intro hm; simp
  | succ m ih =>
      intro hm
      cases l with
      | nil => exact absurd h0 (by simp)
      | cons a tl =>
          cases tl with
          | nil => simp at hm
          | cons b tl' =>
              have hml : m < (b :: tl').length := by simp at hm ⊢; omega
              have h0' : 0 < (b :: tl').length := by simp
              have hMono' : (b :: tl').Pairwise (· ≤ ·) := hMono.tail
              have hab : a ≤ b := by
                have := (List.pairwise_cons.mp hMono).1
                exact this b (List.mem_cons_self ..)
              have hih := ih (b :: tl') h0' hMono' hml
              simp only [List.tail_cons] at hih
              simp only [List.zip_cons_cons, List.tail_cons, List.take_succ_cons,
                List.map_cons, List.sum_cons]
              rw [hih]
              -- Need b ≤ (b :: tl')[m] for nat subtraction arithmetic
              have hb_le_m : b ≤ (b :: tl')[m]'hml := by
                have hpw := List.pairwise_cons.mp hMono'
                have hmem : (b :: tl')[m]'hml ∈ (b :: tl') := List.getElem_mem ..
                rcases List.mem_cons.mp hmem with heq | htl
                · exact le_of_eq heq.symm
                · exact hpw.1 _ htl
              simp only [List.getElem_cons_succ, List.getElem_cons_zero]
              have hab' : a.1 ≤ b.1 := hab
              have hbm : b.1 ≤ ((b :: tl')[m]'hml).1 := hb_le_m
              omega

lemma mem_left_of_mem_zip_tail
    {α : Type*} {l : List α} {p : α × α} (hp : p ∈ l.zip l.tail) : p.1 ∈ l := by
  cases l with
  | nil =>
      simp at hp
  | cons a tl =>
      cases tl with
      | nil =>
          simp at hp
      | cons b tl2 =>
          simp [List.tail] at hp
          rcases hp with hhead | htail
          · rcases hhead with ⟨rfl, rfl⟩
            simp
          · have hmem : p.1 ∈ b :: tl2 := mem_left_of_mem_zip_tail (l := b :: tl2) htail
            simpa using List.mem_cons_of_mem a hmem

lemma mem_right_of_mem_zip_tail
    {α : Type*} {l : List α} {p : α × α} (hp : p ∈ l.zip l.tail) : p.2 ∈ l := by
  cases l with
  | nil =>
      simp at hp
  | cons a tl =>
      cases tl with
      | nil =>
          simp at hp
      | cons b tl2 =>
          simp [List.tail] at hp
          rcases hp with hhead | htail
          · rcases hhead with ⟨rfl, rfl⟩
            simp
          · have hmem : p.2 ∈ b :: tl2 := mem_right_of_mem_zip_tail (l := b :: tl2) htail
            simpa using List.mem_cons_of_mem a hmem

lemma mem_returnPositions_of_mem_excursionPairs_fst
    {n : ℕ} (ys : Traj k n)
    {p : Fin (n + 1) × Fin (n + 1)} (hp : p ∈ excursionPairs (k := k) ys) :
    p.1 ∈ returnPositions (k := k) ys := by
  classical
  have hmem_list : p.1 ∈ returnPositionsList (k := k) ys := by
    have hp' : p ∈ (returnPositionsList (k := k) ys).zip
        (returnPositionsList (k := k) ys).tail := by
      simpa [excursionPairs] using hp
    exact mem_left_of_mem_zip_tail hp'
  have hmem_sort :
      p.1 ∈ (returnPositions (k := k) ys).sort (· ≤ ·) := by
    simpa [returnPositionsList] using hmem_list
  exact (Finset.mem_sort (s := returnPositions (k := k) ys) (r := (· ≤ ·))).1 hmem_sort

lemma mem_returnPositions_of_mem_excursionPairs_snd
    {n : ℕ} (ys : Traj k n)
    {p : Fin (n + 1) × Fin (n + 1)} (hp : p ∈ excursionPairs (k := k) ys) :
    p.2 ∈ returnPositions (k := k) ys := by
  classical
  have hmem_list : p.2 ∈ returnPositionsList (k := k) ys := by
    have hp' : p ∈ (returnPositionsList (k := k) ys).zip
        (returnPositionsList (k := k) ys).tail := by
      simpa [excursionPairs] using hp
    exact mem_right_of_mem_zip_tail hp'
  have hmem_sort :
      p.2 ∈ (returnPositions (k := k) ys).sort (· ≤ ·) := by
    simpa [returnPositionsList] using hmem_list
  exact (Finset.mem_sort (s := returnPositions (k := k) ys) (r := (· ≤ ·))).1 hmem_sort

lemma sum_diffs_pre_eq_fst_of_excursionPairs_decomp
    {n : ℕ} (ys : Traj k n)
    (pre suf : List (Fin (n + 1) × Fin (n + 1)))
    (p1 p2 : Fin (n + 1) × Fin (n + 1))
    (hpairs : excursionPairs (k := k) ys = pre ++ p1 :: p2 :: suf) :
    (pre.map (fun pr => pr.2.1 - pr.1.1)).sum = p1.1.1 := by
  classical
  let l : List (Fin (n + 1)) := returnPositionsList (k := k) ys
  have h0 : 0 < l.length := by
    have hmem0 : (0 : Fin (n + 1)) ∈ returnPositions (k := k) ys := by
      simp [returnPositions]
    have hcard : 0 < (returnPositions (k := k) ys).card := by
      exact Finset.card_pos.mpr ⟨0, hmem0⟩
    simpa [l, length_returnPositionsList] using hcard
  have hlen_pairs : pre.length < (excursionPairs (k := k) ys).length := by
    rw [hpairs]; simp
  have hm : pre.length < l.length := by
    have hep_len : (excursionPairs (k := k) ys).length =
        numExcursions (k := k) ys := length_excursionPairs ys
    have hne : numExcursions (k := k) ys = (returnPositions (k := k) ys).card - 1 := rfl
    have hrl : l.length = (returnPositions (k := k) ys).card := by
      simp [l, length_returnPositionsList]
    omega
  have hzip : excursionPairs (k := k) ys = l.zip l.tail := by
    simp [excursionPairs, l]
  have hlSorted : l.Pairwise (· ≤ ·) := by
    exact Finset.sort_sorted (returnPositions (k := k) ys) (· ≤ ·)
  -- pre = first pre.length elements of excursionPairs
  have hpre_eq : pre = (l.zip l.tail).take pre.length := by
    have h1 : (excursionPairs (k := k) ys).take pre.length = pre := by
      rw [hpairs]; simp [List.take_left]
    conv_rhs => rw [← hzip]
    exact h1.symm
  have hsum :
      (pre.map (fun pr => pr.2.1 - pr.1.1)).sum =
        (((l.zip l.tail).take pre.length).map (fun pr => pr.2.1 - pr.1.1)).sum := by
    conv_lhs => rw [hpre_eq]
  have hsum' := sum_diffs_zip_take_fin l h0 hlSorted pre.length hm
  -- hsum' : ... = l[pre.length].1 - l[0].1
  have hp1_getElem : (pre ++ p1 :: p2 :: suf)[pre.length]'(by simp) = p1 := by
    simp [List.getElem_append_right]
  have hp1_fst_val : p1.1.1 = (l[pre.length]'hm).1 := by
    have hzip_len : pre.length < (l.zip l.tail).length := by rw [← hzip]; exact hlen_pairs
    have htail_len : pre.length < l.tail.length := by
      simp [List.length_zip, List.length_tail] at hzip_len ⊢; omega
    -- (l.zip l.tail)[pre.length] = p1 from the decomposition
    have hzip_at_pre : (l.zip l.tail)[pre.length]'hzip_len = p1 := by
      have h1 : (excursionPairs (k := k) ys)[pre.length]'hlen_pairs =
          (l.zip l.tail)[pre.length]'hzip_len := by simp [hzip]
      rw [← h1]
      have h2 : excursionPairs (k := k) ys = pre ++ p1 :: p2 :: suf := hpairs
      simp [h2, List.getElem_append_right]
    -- Apply getElem_zip
    have hzip_expand : (l.zip l.tail)[pre.length]'hzip_len =
        (l[pre.length]'(by simp [List.length_zip] at hzip_len; omega),
         l.tail[pre.length]'htail_len) := by
      simp [List.getElem_zip]
    rw [hzip_expand] at hzip_at_pre
    exact (congrArg (fun p => p.1.1) hzip_at_pre).symm
  have hzero_val : (l[0]'h0).1 = 0 := by
    have hget0 := returnPositionsList_get_zero (k := k) ys
    have : l.get ⟨0, h0⟩ = (0 : Fin (n + 1)) := hget0
    rw [List.get_eq_getElem] at this
    simp [this]
  rw [hsum, hsum', hp1_fst_val, hzero_val]; omega




lemma map_eq_append_cons_cons_append
    {α β : Type*} (f : α → β) (l : List α)
    (preSeg sufSeg : List β) (e1 e2 : β)
    (h : l.map f = preSeg ++ [e1, e2] ++ sufSeg) :
    ∃ pre p1 p2 suf,
      l = pre ++ p1 :: p2 :: suf ∧
      preSeg = pre.map f ∧
      e1 = f p1 ∧
      e2 = f p2 ∧
      sufSeg = suf.map f := by
  revert l
  induction preSeg with
  | nil =>
      intro l h
      cases l with
      | nil =>
          simp at h
      | cons a tl =>
          cases tl with
          | nil =>
              simp at h
          | cons b tl2 =>
              -- l.map f = f a :: f b :: tl2.map f = e1 :: e2 :: sufSeg
              have h1 : f a = e1 ∧ (f b :: tl2.map f) = e2 :: sufSeg := by
                have := List.cons.inj h
                exact this
              have h2 : f b = e2 ∧ tl2.map f = sufSeg := by
                have := List.cons.inj h1.2
                exact this
              refine ⟨[], a, b, tl2, ?_, ?_, ?_, ?_, ?_⟩
              · rfl
              · simp
              · exact h1.1.symm
              · exact h2.1.symm
              · exact h2.2.symm
  | cons b preSeg ih =>
      intro l h
      cases l with
      | nil =>
          simp at h
      | cons a tl =>
          have h1 : f a = b ∧ tl.map f = preSeg ++ [e1, e2] ++ sufSeg := by
            have := List.cons.inj h
            exact this
          have htail' :
              tl.map f = preSeg ++ [e1, e2] ++ sufSeg := by
            exact h1.2
          rcases ih _ htail' with ⟨pre, p1, p2, suf, htl, hpre, he1, he2, hsuf⟩
          refine ⟨a :: pre, p1, p2, suf, ?_, ?_, ?_, ?_, ?_⟩
          · simp [htl]
          · simp [hpre, h1.1]
          · exact he1
          · exact he2
          · exact hsuf

lemma consecutive_zip_tail_snd_eq_fst
    {α : Type*} :
    ∀ (l : List α) (pre : List (α × α)) (p1 p2 : α × α) (suf : List (α × α)),
      l.zip l.tail = pre ++ p1 :: p2 :: suf → p1.2 = p2.1 := by
  intro l pre p1 p2 suf h
  induction pre generalizing l with
  | nil =>
      cases l with
      | nil =>
          simp at h
      | cons a tl =>
          cases tl with
          | nil =>
              simp at h
          | cons b tl2 =>
              have h' :
                  (a, b) :: (List.zip (b :: tl2) tl2) = p1 :: p2 :: suf := by
                simpa [List.tail] using h
              have h1 := List.cons.inj h'
              rcases h1 with ⟨hp1, htail⟩
              cases tl2 with
              | nil =>
                  -- zip (b::[]) [] = []
                  simp at htail
              | cons c tl3 =>
                  have h2 := List.cons.inj htail
                  rcases h2 with ⟨hp2, _⟩
                  -- head of zip (b::c::tl3) (c::tl3) is (b,c)
                  have hp2' : p2 = (b, c) := by
                    simpa [List.tail] using hp2.symm
                  have hp1' : p1 = (a, b) := by
                    exact hp1.symm
                  -- conclude
                  simp [hp1', hp2']
  | cons x pre ih =>
      cases l with
      | nil =>
          simp at h
      | cons a tl =>
          cases tl with
          | nil =>
              simp at h
          | cons b tl2 =>
              have h' :
                  (a, b) :: (List.zip (b :: tl2) tl2) =
                    x :: pre ++ p1 :: p2 :: suf := by
                simpa [List.tail] using h
              have h1 := List.cons.inj h'
              rcases h1 with ⟨_, htail⟩
              exact ih (b :: tl2) htail

lemma excursionPairs_decomp_of_excursionList_decomp
    {n : ℕ} (ys : Traj k n)
    (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k)
    (hlist :
      excursionListOfTraj (k := k) ys = preSeg ++ [e1, e2] ++ sufSeg) :
    ∃ (pre suf : List (Fin (n + 1) × Fin (n + 1)))
      (p1 p2 : Fin (n + 1) × Fin (n + 1)),
      excursionPairs (k := k) ys = pre ++ p1 :: p2 :: suf ∧
      preSeg = pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
      e1 = trajSegment (k := k) ys p1.1 p1.2 ∧
      e2 = trajSegment (k := k) ys p2.1 p2.2 ∧
      sufSeg = suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
      p1.2 = p2.1 := by
  -- unfold excursionListOfTraj and apply the list-map decomposition lemma
  dsimp [excursionListOfTraj, excursionsOfTraj] at hlist
  rcases map_eq_append_cons_cons_append
      (f := fun pr => trajSegment (k := k) ys pr.1 pr.2)
      (l := excursionPairs (k := k) ys)
      (preSeg := preSeg) (sufSeg := sufSeg) (e1 := e1) (e2 := e2) hlist with
    ⟨pre, p1, p2, suf, hpairs, hpre, he1, he2, hsuf⟩
  refine ⟨pre, suf, p1, p2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpairs
  · exact hpre
  · exact he1
  · exact he2
  · exact hsuf
  · -- consecutive pairs in zip share the middle element
    exact consecutive_zip_tail_snd_eq_fst
      (l := returnPositionsList (k := k) ys)
      (pre := pre) (p1 := p1) (p2 := p2) (suf := suf) (by
        -- unfold excursionPairs to see the zip
        simpa [excursionPairs] using hpairs)

/-- Short-horizon analogue of `image_eq_segmentSwap_prefixPatternFiber_of_maps`. -/
lemma image_eq_segmentSwap_shortPatternFiber_of_maps
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hmap :
      ∀ ys ∈ shortPatternFiber n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcN ∈
          shortPatternFiber n e q)
    (hmapInv :
      ∀ zs ∈ shortPatternFiber n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
          shortPatternFiber n e p) :
    (shortPatternFiber n e p).image
      (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcN) =
      shortPatternFiber n e q := by
  classical
  apply Finset.Subset.antisymm
  · intro ys hys
    rcases Finset.mem_image.1 hys with ⟨xs, hxs, rfl⟩
    exact hmap xs hxs
  · intro ys hys
    refine Finset.mem_image.2 ?_
    refine ⟨segmentSwap ys a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN), hmapInv ys hys, ?_⟩
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (segmentSwap_involutive (k := k) ys a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))

/-- Turn an ordered-list equality statement into a short-fiber forward map. -/
lemma hmapShort_of_excursionList_segmentSwap_eq
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcN ∈ fiber k (Nat.succ n) e)
    (hlist :
      ∀ ys, ys ∈ shortPatternFiber (k := k) n e p →
        excursionListOfTraj (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) = q) :
    ∀ ys ∈ shortPatternFiber (k := k) n e p,
      segmentSwap ys a L1 L2 hL1 hL2 hcN ∈ shortPatternFiber (k := k) n e q := by
  intro ys hys
  exact Finset.mem_filter.2 ⟨hmapFiber ys hys, hlist ys hys⟩

/-- Turn an ordered-list equality statement into a short-fiber inverse map. -/
lemma hmapShortInv_of_excursionList_segmentSwap_eq
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
          fiber k (Nat.succ n) e)
    (hlist :
      ∀ zs, zs ∈ shortPatternFiber (k := k) n e q →
        excursionListOfTraj (k := k)
          (segmentSwap zs a L2 L1 hL2 hL1
            (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) = p) :
    ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
        shortPatternFiber (k := k) n e p := by
  intro zs hzs
  exact Finset.mem_filter.2 ⟨hmapFiber zs hzs, hlist zs hzs⟩

/-- Build the short-pattern forward transport map from the stronger
ordered-list adjacent-swap bridge with explicit excursion-pair decomposition
data for each source trajectory. -/
lemma hmapShort_of_swap_middle_of_excursionPairs_decomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcN ∈ fiber k (Nat.succ n) e)
    (hdecomp :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) ys =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          ys ⟨a, by omega⟩ = ys 0 ∧
          ys ⟨a + L1, by omega⟩ = ys 0 ∧
          ys ⟨a + L1 + L2, by omega⟩ = ys 0 ∧
          excursionListOfTraj (k := k) ys = preSeg ++ [e1, e2] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          e1 = trajSegment (k := k) ys ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∧
          e2 = trajSegment (k := k) ys ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          q = preSeg ++ [e2, e1] ++ sufSeg) :
    ∀ ys ∈ shortPatternFiber (k := k) n e p,
      segmentSwap ys a L1 L2 hL1 hL2 hcN ∈ shortPatternFiber (k := k) n e q := by
  refine hmapShort_of_excursionList_segmentSwap_eq
    (k := k) (n := n) (e := e) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN hmapFiber ?_
  intro ys hys
  rcases hdecomp ys hys with ⟨pre, suf, preSeg, sufSeg, e1, e2,
      hPairsOld, hPairsNew, hPre, hSuf, ha_ret, hb_ret, hc_ret,
      hOld, hPreSeg, hSufSeg, hE1, hE2, hq⟩
  have hswap :
      excursionListOfTraj (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) =
        preSeg ++ [e2, e1] ++ sufSeg :=
    excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
      (k := k) (xs := ys) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcN pre suf preSeg sufSeg e1 e2
      hPairsOld hPairsNew hPre hSuf ha_ret hb_ret hc_ret
      hOld hPreSeg hSufSeg hE1 hE2
  simpa [hq] using hswap

/-- Inverse counterpart of
`hmapShort_of_swap_middle_of_excursionPairs_decomp`. -/
lemma hmapShortInv_of_swap_middle_of_excursionPairs_decomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiberInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
          fiber k (Nat.succ n) e)
    (hdecompInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) zs =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k)
            (segmentSwap zs a L2 L1 hL2 hL1
              (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap zs a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))
                  pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap zs a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))
                  pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          zs ⟨a, by omega⟩ = zs 0 ∧
          zs ⟨a + L2, by omega⟩ = zs 0 ∧
          zs ⟨a + L1 + L2, by omega⟩ = zs 0 ∧
          excursionListOfTraj (k := k) zs = preSeg ++ [e2, e1] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          e2 = trajSegment (k := k) zs ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∧
          e1 = trajSegment (k := k) zs ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          p = preSeg ++ [e1, e2] ++ sufSeg) :
    ∀ zs ∈ shortPatternFiber (k := k) n e q,
      segmentSwap zs a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
      shortPatternFiber (k := k) n e p := by
  refine hmapShortInv_of_excursionList_segmentSwap_eq
    (k := k) (n := n) (e := e) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN hmapFiberInv ?_
  intro zs hzs
  rcases hdecompInv zs hzs with ⟨pre, suf, preSeg, sufSeg, e1, e2,
      hPairsOld, hPairsNew, hPre, hSuf, ha_ret, hb2_ret, hc_ret,
      hOld, hPreSeg, hSufSeg, hE1, hE2, hp⟩
  have hPairsOld' :
      excursionPairs (k := k) zs =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L2 + L1, by omega⟩)] ++
          suf := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPairsOld
  have hPairsNew' :
      excursionPairs (k := k)
        (segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L2 + L1, by omega⟩)] ++
          suf := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPairsNew
  have hswap :
      excursionListOfTraj (k := k)
        (segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) =
        preSeg ++ [e1, e2] ++ sufSeg :=
    have hE2' :
        e1 =
          trajSegment (k := k) zs
            ⟨a + L2, by omega⟩
            ⟨a + L2 + L1, by omega⟩ := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hE2
    excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
      (k := k) (xs := zs) (a := a) (L1 := L2) (L2 := L1)
      hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)
      pre suf preSeg sufSeg e2 e1
      hPairsOld' hPairsNew' hPre hSuf ha_ret hb2_ret
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc_ret)
      hOld hPreSeg hSufSeg hE1 hE2'
  simpa [hp] using hswap

/-- Build short-pattern image equality directly from explicit decomposition
witnesses for forward and inverse adjacent swaps. -/
lemma himgShort_of_swap_middle_of_excursionPairs_decomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcN ∈ fiber k (Nat.succ n) e)
    (hdecomp :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) ys =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          ys ⟨a, by omega⟩ = ys 0 ∧
          ys ⟨a + L1, by omega⟩ = ys 0 ∧
          ys ⟨a + L1 + L2, by omega⟩ = ys 0 ∧
          excursionListOfTraj (k := k) ys = preSeg ++ [e1, e2] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
          e1 = trajSegment (k := k) ys ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∧
          e2 = trajSegment (k := k) ys ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          q = preSeg ++ [e2, e1] ++ sufSeg)
    (hmapFiberInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
          fiber k (Nat.succ n) e)
    (hdecompInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) zs =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k)
            (segmentSwap zs a L2 L1 hL2 hL1
              (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap zs a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))
                  pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap zs a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))
                  pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          zs ⟨a, by omega⟩ = zs 0 ∧
          zs ⟨a + L2, by omega⟩ = zs 0 ∧
          zs ⟨a + L1 + L2, by omega⟩ = zs 0 ∧
          excursionListOfTraj (k := k) zs = preSeg ++ [e2, e1] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
          e2 = trajSegment (k := k) zs ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∧
          e1 = trajSegment (k := k) zs ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          p = preSeg ++ [e1, e2] ++ sufSeg) :
    (shortPatternFiber (k := k) n e p).image
      (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcN) =
      shortPatternFiber (k := k) n e q := by
  apply image_eq_segmentSwap_shortPatternFiber_of_maps
    (k := k) (n := n) (e := e) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN
  · exact hmapShort_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN hmapFiber hdecomp
  · exact hmapShortInv_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN hmapFiberInv hdecompInv

/-- Build the long-prefix forward transport map from the stronger ordered-list
adjacent-swap bridge, applied to the prefixed trajectory. -/
lemma hmapPrefix_of_swap_middle_of_excursionPairs_decomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecomp :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) (trajPrefix (k := k) hN xs) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k)
            (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort)
                  pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort)
                  pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          (trajPrefix (k := k) hN xs) ⟨a, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
          (trajPrefix (k := k) hN xs) ⟨a + L1, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
          (trajPrefix (k := k) hN xs) ⟨a + L1 + L2, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
          excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = preSeg ++ [e1, e2] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          e1 = trajSegment (k := k) (trajPrefix (k := k) hN xs) ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∧
          e2 = trajSegment (k := k) (trajPrefix (k := k) hN xs) ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          q = preSeg ++ [e2, e1] ++ sufSeg) :
    ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
      segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈
        prefixPatternFiber (k := k) (hN := hN) e s q := by
  intro xs hxs
  rcases hdecomp xs hxs with ⟨pre, suf, preSeg, sufSeg, e1, e2,
      hPairsOld, hPairsNew, hPre, hSuf, ha_ret, hb_ret, hc_ret,
      hOld, hPreSeg, hSufSeg, hE1, hE2, hq⟩
  have hswapPref :
      excursionListOfTraj (k := k)
        (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort) =
        preSeg ++ [e2, e1] ++ sufSeg :=
    excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
      (k := k) (xs := trajPrefix (k := k) hN xs) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcShort
      pre suf preSeg sufSeg e1 e2
      hPairsOld hPairsNew hPre hSuf ha_ret hb_ret hc_ret
      hOld hPreSeg hSufSeg hE1 hE2
  have hprefSwap :
      trajPrefix (k := k) hN
        (segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
        segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort :=
    trajPrefix_segmentSwap_eq_segmentSwap_prefix
      (k := k) (h := hN) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcShort
  have hlist :
      excursionListOfTraj (k := k)
        (trajPrefix (k := k) hN
          (segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN))) = q := by
    simpa [hq, hprefSwap] using hswapPref
  exact Finset.mem_filter.2 ⟨hmapFiber xs hxs, hlist⟩

/-- Inverse counterpart of
`hmapPrefix_of_swap_middle_of_excursionPairs_decomp`. -/
lemma hmapPrefixInv_of_swap_middle_of_excursionPairs_decomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiberInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecompInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) (trajPrefix (k := k) hN ys) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k)
            (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
              (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
                  pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
                  pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          (trajPrefix (k := k) hN ys) ⟨a, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
          (trajPrefix (k := k) hN ys) ⟨a + L2, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
          (trajPrefix (k := k) hN ys) ⟨a + L1 + L2, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
          excursionListOfTraj (k := k) (trajPrefix (k := k) hN ys) = preSeg ++ [e2, e1] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          e2 = trajSegment (k := k) (trajPrefix (k := k) hN ys) ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∧
          e1 = trajSegment (k := k) (trajPrefix (k := k) hN ys) ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          p = preSeg ++ [e1, e2] ++ sufSeg) :
    ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
      segmentSwap ys a L2 L1 hL2 hL1
        (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN) ∈
        prefixPatternFiber (k := k) (hN := hN) e s p := by
  intro ys hys
  rcases hdecompInv ys hys with ⟨pre, suf, preSeg, sufSeg, e1, e2,
      hPairsOld, hPairsNew, hPre, hSuf, ha_ret, hb2_ret, hc_ret,
      hOld, hPreSeg, hSufSeg, hE1, hE2, hp⟩
  have hPairsOld' :
      excursionPairs (k := k) (trajPrefix (k := k) hN ys) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L2 + L1, by omega⟩)] ++
          suf := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPairsOld
  have hPairsNew' :
      excursionPairs (k := k)
        (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L2 + L1, by omega⟩)] ++
          suf := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPairsNew
  have hE2' :
      e1 =
        trajSegment (k := k) (trajPrefix (k := k) hN ys)
          ⟨a + L2, by omega⟩
          ⟨a + L2 + L1, by omega⟩ := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hE2
  have hswapPref :
      excursionListOfTraj (k := k)
        (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) =
        preSeg ++ [e1, e2] ++ sufSeg :=
    excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
      (k := k) (xs := trajPrefix (k := k) hN ys) (a := a) (L1 := L2) (L2 := L1)
      hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)
      pre suf preSeg sufSeg e2 e1
      hPairsOld' hPairsNew' hPre hSuf ha_ret hb2_ret
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc_ret)
      hOld hPreSeg hSufSeg hE1 hE2'
  have hprefSwap :
      trajPrefix (k := k) hN
        (segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN)) =
        segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) :=
    trajPrefix_segmentSwap_eq_segmentSwap_prefix
      (k := k) (h := hN) (xs := ys) (a := a) (L1 := L2) (L2 := L1) hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)
  have hlist :
      excursionListOfTraj (k := k)
        (trajPrefix (k := k) hN
          (segmentSwap ys a L2 L1 hL2 hL1
            (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN))) = p := by
    simpa [hp, hprefSwap] using hswapPref
  exact Finset.mem_filter.2 ⟨hmapFiberInv ys hys, hlist⟩

/-- Build long-prefix image equality directly from explicit decomposition
witnesses for forward and inverse adjacent swaps on prefixed trajectories. -/
lemma himgPrefix_of_swap_middle_of_excursionPairs_decomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecomp :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) (trajPrefix (k := k) hN xs) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k)
            (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort)
                  pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort)
                  pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          (trajPrefix (k := k) hN xs) ⟨a, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
          (trajPrefix (k := k) hN xs) ⟨a + L1, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
          (trajPrefix (k := k) hN xs) ⟨a + L1 + L2, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
          excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = preSeg ++ [e1, e2] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
          e1 = trajSegment (k := k) (trajPrefix (k := k) hN xs) ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∧
          e2 = trajSegment (k := k) (trajPrefix (k := k) hN xs) ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          q = preSeg ++ [e2, e1] ++ sufSeg)
    (hmapFiberInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecompInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
          (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
          excursionPairs (k := k) (trajPrefix (k := k) hN ys) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
               (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          excursionPairs (k := k)
            (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
              (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) =
            pre ++
              [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
               (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
              suf ∧
          pre.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
                  pr.1 pr.2) =
            pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          suf.map
              (fun pr =>
                trajSegment (k := k)
                  (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
                    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
                  pr.1 pr.2) =
            suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          (trajPrefix (k := k) hN ys) ⟨a, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
          (trajPrefix (k := k) hN ys) ⟨a + L2, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
          (trajPrefix (k := k) hN ys) ⟨a + L1 + L2, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
          excursionListOfTraj (k := k) (trajPrefix (k := k) hN ys) = preSeg ++ [e2, e1] ++ sufSeg ∧
          preSeg = pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          sufSeg = suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
          e2 = trajSegment (k := k) (trajPrefix (k := k) hN ys) ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∧
          e1 = trajSegment (k := k) (trajPrefix (k := k) hN ys) ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
          p = preSeg ++ [e1, e2] ++ sufSeg) :
    (prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
      prefixPatternFiber (k := k) (hN := hN) e s q := by
  apply image_eq_segmentSwap_prefixPatternFiber_of_maps
    (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 (le_trans hcShort hN)
  · exact hmapPrefix_of_swap_middle_of_excursionPairs_decomp
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hmapFiber hdecomp
  · exact hmapPrefixInv_of_swap_middle_of_excursionPairs_decomp
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hmapFiberInv hdecompInv

/-- Explicit short-fiber decomposition witness for an adjacent swap. -/
def ShortSwapMiddleDecomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n) : Prop :=
  ∀ ys ∈ shortPatternFiber (k := k) n e p,
    ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
      (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
      excursionPairs (k := k) ys =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf ∧
      excursionPairs (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf ∧
      pre.map
          (fun pr =>
            trajSegment (k := k)
              (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
        pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
      suf.map
          (fun pr =>
            trajSegment (k := k)
              (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
        suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
      ys ⟨a, by omega⟩ = ys 0 ∧
      ys ⟨a + L1, by omega⟩ = ys 0 ∧
      ys ⟨a + L1 + L2, by omega⟩ = ys 0 ∧
      excursionListOfTraj (k := k) ys = preSeg ++ [e1, e2] ++ sufSeg ∧
      preSeg = pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
      sufSeg = suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) ∧
      e1 = trajSegment (k := k) ys ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∧
      e2 = trajSegment (k := k) ys ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
      q = preSeg ++ [e2, e1] ++ sufSeg

/-- Explicit long-prefix decomposition witness for an adjacent swap. -/
def PrefixSwapMiddleDecomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) : Prop :=
  ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
    ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
      (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
      excursionPairs (k := k) (trajPrefix (k := k) hN xs) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
           (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf ∧
      excursionPairs (k := k)
        (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort) =
        pre ++
          [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
           (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
          suf ∧
      pre.map
          (fun pr =>
            trajSegment (k := k)
              (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort)
              pr.1 pr.2) =
        pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
      suf.map
          (fun pr =>
            trajSegment (k := k)
              (segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort)
              pr.1 pr.2) =
        suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
      (trajPrefix (k := k) hN xs) ⟨a, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
      (trajPrefix (k := k) hN xs) ⟨a + L1, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
      (trajPrefix (k := k) hN xs) ⟨a + L1 + L2, by omega⟩ = (trajPrefix (k := k) hN xs) 0 ∧
      excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = preSeg ++ [e1, e2] ++ sufSeg ∧
      preSeg = pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
      sufSeg = suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN xs) pr.1 pr.2) ∧
      e1 = trajSegment (k := k) (trajPrefix (k := k) hN xs) ⟨a, by omega⟩ ⟨a + L1, by omega⟩ ∧
      e2 = trajSegment (k := k) (trajPrefix (k := k) hN xs) ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
      q = preSeg ++ [e2, e1] ++ sufSeg

/-- Unpack the inverse short-swap decomposition into the explicit witness shape
expected by `hmapShortInv_of_swap_middle_of_excursionPairs_decomp`. -/
lemma shortSwapMiddleDecomp_inv_unpack
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hdecompInv : ShortSwapMiddleDecomp
      (k := k) n e q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) :
    ∀ zs ∈ shortPatternFiber (k := k) n e q,
      ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
        (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
        excursionPairs (k := k) zs =
          pre ++
            [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
             (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
            suf ∧
        excursionPairs (k := k)
          (segmentSwap zs a L2 L1 hL2 hL1
            (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) =
          pre ++
            [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
             (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
            suf ∧
        pre.map
            (fun pr =>
              trajSegment (k := k)
                (segmentSwap zs a L2 L1 hL2 hL1
                  (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))
                pr.1 pr.2) =
          pre.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
        suf.map
            (fun pr =>
              trajSegment (k := k)
                (segmentSwap zs a L2 L1 hL2 hL1
                  (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))
                pr.1 pr.2) =
          suf.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
        zs ⟨a, by omega⟩ = zs 0 ∧
        zs ⟨a + L2, by omega⟩ = zs 0 ∧
        zs ⟨a + L1 + L2, by omega⟩ = zs 0 ∧
        excursionListOfTraj (k := k) zs = preSeg ++ [e2, e1] ++ sufSeg ∧
        preSeg = pre.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
        sufSeg = suf.map (fun pr => trajSegment (k := k) zs pr.1 pr.2) ∧
        e2 = trajSegment (k := k) zs ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∧
        e1 = trajSegment (k := k) zs ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
        p = preSeg ++ [e1, e2] ++ sufSeg := by
  intro zs hzs
  simpa [ShortSwapMiddleDecomp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    hdecompInv zs hzs

/-- Unpack the inverse prefix-swap decomposition into the explicit witness shape
expected by `hmapPrefixInv_of_swap_middle_of_excursionPairs_decomp`. -/
lemma prefixSwapMiddleDecomp_inv_unpack
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompInv : PrefixSwapMiddleDecomp
      (k := k) (hN := hN) e s q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
      ∃ (pre suf : List (Fin (Nat.succ n + 1) × Fin (Nat.succ n + 1)))
        (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k),
        excursionPairs (k := k) (trajPrefix (k := k) hN ys) =
          pre ++
            [(⟨a, by omega⟩, ⟨a + L2, by omega⟩),
             (⟨a + L2, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
            suf ∧
        excursionPairs (k := k)
          (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
            (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) =
          pre ++
            [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
             (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++
            suf ∧
        pre.map
            (fun pr =>
              trajSegment (k := k)
                (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
                  (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
                pr.1 pr.2) =
          pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
        suf.map
            (fun pr =>
              trajSegment (k := k)
                (segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
                  (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
                pr.1 pr.2) =
          suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
        (trajPrefix (k := k) hN ys) ⟨a, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
        (trajPrefix (k := k) hN ys) ⟨a + L2, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
        (trajPrefix (k := k) hN ys) ⟨a + L1 + L2, by omega⟩ = (trajPrefix (k := k) hN ys) 0 ∧
        excursionListOfTraj (k := k) (trajPrefix (k := k) hN ys) = preSeg ++ [e2, e1] ++ sufSeg ∧
        preSeg = pre.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
        sufSeg = suf.map (fun pr => trajSegment (k := k) (trajPrefix (k := k) hN ys) pr.1 pr.2) ∧
        e2 = trajSegment (k := k) (trajPrefix (k := k) hN ys) ⟨a, by omega⟩ ⟨a + L2, by omega⟩ ∧
        e1 = trajSegment (k := k) (trajPrefix (k := k) hN ys) ⟨a + L2, by omega⟩ ⟨a + L1 + L2, by omega⟩ ∧
        p = preSeg ++ [e1, e2] ++ sufSeg := by
  intro ys hys
  simpa [PrefixSwapMiddleDecomp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    hdecompInv ys hys

/-- Forward short-fiber transport to `fiber` derived directly from a
`ShortSwapMiddleDecomp` witness. -/
lemma hmapShortFiber_of_shortSwapMiddleDecomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hdecomp : ShortSwapMiddleDecomp
      (k := k) n e p q a L1 L2 hL1 hL2 hcN) :
    ∀ ys ∈ shortPatternFiber (k := k) n e p,
      segmentSwap ys a L1 L2 hL1 hL2 hcN ∈ fiber k (Nat.succ n) e := by
  intro ys hys
  rcases hdecomp ys hys with ⟨_, _, _, _, _, _, _, _, _, _, ha_ret, hb_ret, hc_ret, _, _, _, _, _, _⟩
  exact segmentSwap_mem_fiber (k := k) e ys ((Finset.mem_filter.1 hys).1)
    a L1 L2 hL1 hL2 hcN ha_ret hb_ret hc_ret

/-- Inverse short-fiber transport to `fiber` derived directly from an inverse
`ShortSwapMiddleDecomp` witness. -/
lemma hmapShortFiberInv_of_shortSwapMiddleDecomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hdecompInv : ShortSwapMiddleDecomp
      (k := k) n e q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) :
    ∀ zs ∈ shortPatternFiber (k := k) n e q,
      segmentSwap zs a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
        fiber k (Nat.succ n) e := by
  have hdecompInv' :=
    shortSwapMiddleDecomp_inv_unpack
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN hdecompInv
  intro zs hzs
  rcases hdecompInv' zs hzs with ⟨_, _, _, _, _, _, _, _, _, _, ha_ret, hb_ret, hc_ret, _, _, _, _, _, _⟩
  exact segmentSwap_mem_fiber (k := k) e zs ((Finset.mem_filter.1 hzs).1)
    a L2 L1 hL2 hL1
    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)
    ha_ret hb_ret (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc_ret)

/-- A short-swap decomposition witness implies multiset equality between the
two adjacent-swap patterns (using any witness trajectory in the short fiber). -/
lemma multiset_eq_of_shortSwapMiddleDecomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hdecomp : ShortSwapMiddleDecomp
      (k := k) n e p q a L1 L2 hL1 hL2 hcN)
    {ys : Traj k (Nat.succ n)} (hys : ys ∈ shortPatternFiber (k := k) n e p) :
    Multiset.ofList q = Multiset.ofList p := by
  rcases hdecomp ys hys with
    ⟨pre, suf, preSeg, sufSeg, e1, e2, hPairsOld, hPairsNew, hPre, hSuf,
      ha_ret, hb_ret, hc_ret, hOld, hPreSeg, hSufSeg, hE1, hE2, hq⟩
  have hmult :
      excursionMultiset (k := k)
          (excursionListOfTraj (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN)) =
        excursionMultiset (k := k) (excursionListOfTraj (k := k) ys) :=
    excursionMultiset_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
      (k := k) (xs := ys) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcN pre suf preSeg sufSeg e1 e2
      hPairsOld hPairsNew hPre hSuf ha_ret hb_ret hc_ret
      hOld hPreSeg hSufSeg hE1 hE2
  have hp : excursionListOfTraj (k := k) ys = p := (Finset.mem_filter.1 hys).2
  have hq' :
      excursionListOfTraj (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) = q := by
    have hswap :
        excursionListOfTraj (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) =
          preSeg ++ [e2, e1] ++ sufSeg :=
      excursionListOfTraj_segmentSwap_eq_swap_middle_of_excursionPairs_decomp_strong
        (k := k) (xs := ys) (a := a) (L1 := L1) (L2 := L2)
        hL1 hL2 hcN pre suf preSeg sufSeg e1 e2
        hPairsOld hPairsNew hPre hSuf ha_ret hb_ret hc_ret
        hOld hPreSeg hSufSeg hE1 hE2
    simpa [hq] using hswap
  have hqmult : Multiset.ofList q = excursionMultiset (k := k)
      (excursionListOfTraj (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN)) := by
    simpa [excursionMultiset, hq']
  have hpmult : excursionMultiset (k := k) (excursionListOfTraj (k := k) ys) =
      Multiset.ofList p := by
    simpa [excursionMultiset, hp]
  calc
    Multiset.ofList q =
      excursionMultiset (k := k)
        (excursionListOfTraj (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN)) := hqmult
    _ = excursionMultiset (k := k) (excursionListOfTraj (k := k) ys) := hmult
    _ = Multiset.ofList p := hpmult

/-- Forward long-prefix transport to `prefixFiber` derived directly from a
`PrefixSwapMiddleDecomp` witness. -/
lemma hmapPrefixFiber_of_prefixSwapMiddleDecomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecomp : PrefixSwapMiddleDecomp
      (k := k) (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort) :
    ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
      segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈
        prefixFiber (k := k) (h := hN) e s := by
  intro xs hxs
  rcases hdecomp xs hxs with
    ⟨_, _, _, _, _, _, _, _, _, _, ha_ret_pref, hb_ret_pref, hc_ret_pref, _, _, _, _, _, _⟩
  have hxsPrefix : xs ∈ prefixFiber (k := k) (h := hN) e s := (Finset.mem_filter.1 hxs).1
  have hxsFiber : xs ∈ fiber k N s := (Finset.mem_filter.1 hxsPrefix).1
  have ha_ret :
      xs ⟨a, by omega⟩ = xs 0 := by
    simpa [trajPrefix] using ha_ret_pref
  have hb_ret :
      xs ⟨a + L1, by omega⟩ = xs 0 := by
    simpa [trajPrefix] using hb_ret_pref
  have hc_ret :
      xs ⟨a + L1 + L2, by omega⟩ = xs 0 := by
    simpa [trajPrefix] using hc_ret_pref
  have hmemFiber :
      segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈ fiber k N s :=
    segmentSwap_mem_fiber (k := k) s xs hxsFiber a L1 L2 hL1 hL2
      (le_trans hcShort hN) ha_ret hb_ret hc_ret
  have hprefix_swap :
      trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
        segmentSwap (trajPrefix (k := k) hN xs) a L1 L2 hL1 hL2 hcShort :=
    trajPrefix_segmentSwap_eq_segmentSwap_prefix
      (k := k) (h := hN) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcShort
  have hprefix_state_eq :
      prefixState (k := k) hN
        (segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
        prefixState (k := k) hN xs := by
    unfold prefixState
    rw [hprefix_swap]
    exact segmentSwap_stateOfTraj (k := k) (trajPrefix (k := k) hN xs) a L1 L2
      hL1 hL2 hcShort ha_ret_pref hb_ret_pref hc_ret_pref
  have hprefix_state :
      prefixState (k := k) hN
        (segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) = e := by
    exact hprefix_state_eq.trans ((Finset.mem_filter.1 hxsPrefix).2)
  exact Finset.mem_filter.2 ⟨hmemFiber, hprefix_state⟩

/-- Inverse long-prefix transport to `prefixFiber` derived directly from an
inverse `PrefixSwapMiddleDecomp` witness. -/
lemma hmapPrefixFiberInv_of_prefixSwapMiddleDecomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompInv : PrefixSwapMiddleDecomp
      (k := k) (hN := hN) e s q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
      segmentSwap ys a L2 L1 hL2 hL1
        (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN) ∈
        prefixFiber (k := k) (h := hN) e s := by
  have hdecompInv' :=
    prefixSwapMiddleDecomp_inv_unpack
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompInv
  intro ys hys
  rcases hdecompInv' ys hys with
    ⟨_, _, _, _, _, _, _, _, _, _, ha_ret_pref, hb_ret_pref, hc_ret_pref, _, _, _, _, _, _⟩
  have hysPrefix : ys ∈ prefixFiber (k := k) (h := hN) e s := (Finset.mem_filter.1 hys).1
  have hysFiber : ys ∈ fiber k N s := (Finset.mem_filter.1 hysPrefix).1
  have ha_ret :
      ys ⟨a, by omega⟩ = ys 0 := by
    simpa [trajPrefix] using ha_ret_pref
  have hb_ret :
      ys ⟨a + L2, by omega⟩ = ys 0 := by
    simpa [trajPrefix] using hb_ret_pref
  have hc_ret :
      ys ⟨a + L1 + L2, by omega⟩ = ys 0 := by
    simpa [trajPrefix] using hc_ret_pref
  have hmemFiber :
      segmentSwap ys a L2 L1 hL2 hL1
        (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN) ∈
        fiber k N s :=
    segmentSwap_mem_fiber (k := k) s ys hysFiber a L2 L1 hL2 hL1
      (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN)
      ha_ret hb_ret (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc_ret)
  have hprefix_swap :
      trajPrefix (k := k) hN
        (segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN)) =
        segmentSwap (trajPrefix (k := k) hN ys) a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) :=
    trajPrefix_segmentSwap_eq_segmentSwap_prefix
      (k := k) (h := hN) (xs := ys) (a := a) (L1 := L2) (L2 := L1)
      hL2 hL1 (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)
  have hprefix_state_eq :
      prefixState (k := k) hN
        (segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN)) =
        prefixState (k := k) hN ys := by
    unfold prefixState
    rw [hprefix_swap]
    exact segmentSwap_stateOfTraj (k := k) (trajPrefix (k := k) hN ys) a L2 L1
      hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)
      ha_ret_pref hb_ret_pref
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc_ret_pref)
  have hprefix_state :
      prefixState (k := k) hN
        (segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN)) = e := by
    exact hprefix_state_eq.trans ((Finset.mem_filter.1 hysPrefix).2)
  exact Finset.mem_filter.2 ⟨hmemFiber, hprefix_state⟩

/-- Thin wrapper: produce short-fiber image equality from `ShortSwapMiddleDecomp`. -/
lemma himgShort_of_shortSwapMiddleDecomp
    (n : ℕ) (e : MarkovState k) (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcN : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcN ∈ fiber k (Nat.succ n) e)
    (hdecomp : ShortSwapMiddleDecomp
      (k := k) n e p q a L1 L2 hL1 hL2 hcN)
    (hmapFiberInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
          fiber k (Nat.succ n) e)
    (hdecompInv : ShortSwapMiddleDecomp
      (k := k) n e q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)) :
    (shortPatternFiber (k := k) n e p).image
      (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcN) =
      shortPatternFiber (k := k) n e q := by
  have hdecompInv' :=
    shortSwapMiddleDecomp_inv_unpack
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN hdecompInv
  exact himgShort_of_swap_middle_of_excursionPairs_decomp
    (k := k) (n := n) (e := e) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcN
    hmapFiber hdecomp hmapFiberInv hdecompInv'

/-- Thin wrapper: produce long-prefix image equality from `PrefixSwapMiddleDecomp`. -/
lemma himgPrefix_of_PrefixSwapMiddleDecomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmapFiber :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecomp : PrefixSwapMiddleDecomp
      (k := k) (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (hmapFiberInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecompInv : PrefixSwapMiddleDecomp
      (k := k) (hN := hN) e s q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    (prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
      prefixPatternFiber (k := k) (hN := hN) e s q := by
  have hdecompInv' :=
    prefixSwapMiddleDecomp_inv_unpack
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompInv
  exact himgPrefix_of_swap_middle_of_excursionPairs_decomp
    (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
    hmapFiber hdecomp hmapFiberInv hdecompInv'

/-- Turn an ordered-list equality statement into a long-prefix forward map. -/
lemma hmapPrefix_of_excursionList_segmentSwap_eq
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (hmapFiber :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcN ∈ prefixFiber (k := k) (h := hN) e s)
    (hlist :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        excursionListOfTraj (k := k)
          (trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 hcN)) = q) :
    ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
      segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
        prefixPatternFiber (k := k) (hN := hN) e s q := by
  intro xs hxs
  exact Finset.mem_filter.2 ⟨hmapFiber xs hxs, hlist xs hxs⟩

/-- Turn an ordered-list equality statement into a long-prefix inverse map. -/
lemma hmapPrefixInv_of_excursionList_segmentSwap_eq
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (hmapFiber :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hlist :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        excursionListOfTraj (k := k)
          (trajPrefix (k := k) hN
            (segmentSwap ys a L2 L1 hL2 hL1
              (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))) = p) :
    ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
      segmentSwap ys a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
        prefixPatternFiber (k := k) (hN := hN) e s p := by
  intro ys hys
  exact Finset.mem_filter.2 ⟨hmapFiber ys hys, hlist ys hys⟩

/-- Concrete long-prefix transport map in the post-prefix regime (`n+1 ≤ a`):
segment swap preserves the prefix excursion list, so this maps `p` to itself. -/
lemma hmapPrefix_same_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : ∀ xs, xs ∈ prefixPatternFiber (k := k) (hN := hN) e s (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) →
      xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : ∀ xs, xs ∈ prefixPatternFiber (k := k) (hN := hN) e s (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) →
      xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : ∀ xs, xs ∈ prefixPatternFiber (k := k) (hN := hN) e s (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) →
      xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
      segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
        prefixPatternFiber (k := k) (hN := hN) e s p := by
  intro xs hxs
  have hFiber :
      segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
        prefixFiber (k := k) (h := hN) e s := by
    exact segmentSwap_mem_prefixFiber_of_prefix_before_swap
      (k := k) (h := hN) (e := e) (eN := s) (xs := xs)
      (a := a) (L1 := L1) (L2 := L2) (hna := hna)
      (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
      (ha_ret := by
        have hxs' : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s
            (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) := by
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hxs).1, rfl⟩
        exact ha_ret xs hxs')
      (hb_ret := by
        have hxs' : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s
            (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) := by
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hxs).1, rfl⟩
        exact hb_ret xs hxs')
      (hc_ret := by
        have hxs' : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s
            (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) := by
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hxs).1, rfl⟩
        exact hc_ret xs hxs')
      ((Finset.mem_filter.1 hxs).1)
  have hlist :
      excursionListOfTraj (k := k)
        (trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 hcN)) = p := by
    have hp : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
      (Finset.mem_filter.1 hxs).2
    simpa [hp] using
      excursionListOfTraj_prefix_segmentSwap_eq_of_prefix_before_swap
        (k := k) (hN := hN) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
        (hna := hna) (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
  exact Finset.mem_filter.2 ⟨hFiber, hlist⟩

/-- Inverse long-prefix transport map in the post-prefix regime (`n+1 ≤ a`):
segment swap with reversed lengths also preserves the prefix excursion list, so
this maps `p` to itself. -/
lemma hmapPrefixInv_same_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : ∀ xs, xs ∈ prefixPatternFiber (k := k) (hN := hN) e s (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) →
      xs ⟨a, by omega⟩ = xs 0)
    (hb2_ret : ∀ xs, xs ∈ prefixPatternFiber (k := k) (hN := hN) e s (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) →
      xs ⟨a + L2, by omega⟩ = xs 0)
    (hc_ret : ∀ xs, xs ∈ prefixPatternFiber (k := k) (hN := hN) e s (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) →
      xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
      segmentSwap xs a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
        prefixPatternFiber (k := k) (hN := hN) e s p := by
  intro xs hxs
  have hFiber :
      segmentSwap xs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN) ∈
        prefixFiber (k := k) (h := hN) e s := by
    exact segmentSwap_mem_prefixFiber_of_prefix_before_swap
      (k := k) (h := hN) (e := e) (eN := s) (xs := xs)
      (a := a) (L1 := L2) (L2 := L1) (hna := hna)
      (hL1 := hL2) (hL2 := hL1)
      (hcN := by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)
      (ha_ret := by
        have hxs' : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s
            (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) := by
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hxs).1, rfl⟩
        exact ha_ret xs hxs')
      (hb_ret := by
        have hxs' : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s
            (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) := by
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hxs).1, rfl⟩
        exact hb2_ret xs hxs')
      (hc_ret := by
        have hxs' : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s
            (excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs)) := by
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hxs).1, rfl⟩
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (hc_ret xs hxs'))
      ((Finset.mem_filter.1 hxs).1)
  have hlist :
      excursionListOfTraj (k := k)
        (trajPrefix (k := k) hN
          (segmentSwap xs a L2 L1 hL2 hL1
            (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN))) = p := by
    have hp : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
      (Finset.mem_filter.1 hxs).2
    simpa [hp] using
      excursionListOfTraj_prefix_segmentSwap_eq_of_prefix_before_swap
        (k := k) (hN := hN) (xs := xs) (a := a) (L1 := L2) (L2 := L1)
        (hna := hna) (hL1 := hL2) (hL2 := hL1)
        (hcN := by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcN)
  exact Finset.mem_filter.2 ⟨hFiber, hlist⟩

/-- Pattern ratio inside the short fiber:
`|shortPatternFiber(n,e,p)| / |fiber(n+1,e)|`. -/
def shortPatternRatio
    (n : ℕ) (e : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((shortPatternFiber (k := k) n e p).card : ENNReal) /
    ((fiber k (Nat.succ n) e).card : ENNReal)

lemma sum_shortPatternRatio_over_shortImage
    (n : ℕ) (e : MarkovState k) :
    ∑ p ∈ ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)),
      shortPatternRatio (k := k) n e p =
        (if (fiber k (Nat.succ n) e).card = 0 then 0 else 1) := by
  classical
  let S : Finset (ExcursionList k) :=
    (fiber k (Nat.succ n) e).image (fun ys => excursionListOfTraj (k := k) ys)
  have hcard :
      (fiber k (Nat.succ n) e).card =
        ∑ p ∈ S, (shortPatternFiber (k := k) n e p).card := by
    -- Partition the short fiber by excursion list.
    simpa [S, shortPatternFiber] using
      (Finset.card_eq_sum_card_image
        (f := fun ys : Traj k (Nat.succ n) => excursionListOfTraj (k := k) ys)
        (s := fiber k (Nat.succ n) e))
  by_cases hden : (fiber k (Nat.succ n) e).card = 0
  · have hshort0 :
      ∀ p, shortPatternRatio (k := k) n e p = 0 := by
        intro p
        have hfiber_empty : fiber k (Nat.succ n) e = ∅ := Finset.card_eq_zero.mp hden
        have hshort_empty : shortPatternFiber (k := k) n e p = ∅ := by
          unfold shortPatternFiber
          simp [hfiber_empty]
        unfold shortPatternRatio
        simp [hden, hshort_empty]
    have hsum0 :
        ∑ p ∈ S, shortPatternRatio (k := k) n e p = 0 := by
      refine Finset.sum_eq_zero ?_
      intro p hp
      simp [hshort0]
    rw [show ((fiber k (Nat.succ n) e).image
          (fun ys => excursionListOfTraj (k := k) ys)) = S by rfl]
    simp [hden, hsum0]
  · have hsum :
      ∑ p ∈ S, shortPatternRatio (k := k) n e p =
        (((fiber k (Nat.succ n) e).card : ℕ) : ENNReal) /
          ((fiber k (Nat.succ n) e).card : ENNReal) := by
      calc
        ∑ p ∈ S, shortPatternRatio (k := k) n e p
            = (((∑ p ∈ S, (shortPatternFiber (k := k) n e p).card) : ℕ) : ENNReal) /
                ((fiber k (Nat.succ n) e).card : ENNReal) := by
                  simp [shortPatternRatio, div_eq_mul_inv, Finset.sum_mul]
        _ = (((fiber k (Nat.succ n) e).card : ℕ) : ENNReal) /
              ((fiber k (Nat.succ n) e).card : ENNReal) := by
                rw [hcard]
    have hden_enn : ((fiber k (Nat.succ n) e).card : ENNReal) ≠ 0 := by
      exact_mod_cast hden
    have hden_top : ((fiber k (Nat.succ n) e).card : ENNReal) ≠ ⊤ := by simp
    have hratio1 :
        (((fiber k (Nat.succ n) e).card : ℕ) : ENNReal) /
            ((fiber k (Nat.succ n) e).card : ENNReal) = 1 := by
      exact (ENNReal.div_eq_one_iff hden_enn hden_top).2 rfl
    simp [S, hden, hsum, hratio1]

lemma shortPatternRatio_ne_top
    (n : ℕ) (e : MarkovState k) (p : ExcursionList k) :
    shortPatternRatio (k := k) n e p ≠ ⊤ := by
  by_cases hden : (fiber k (Nat.succ n) e).card = 0
  · have hfiber_empty : fiber k (Nat.succ n) e = ∅ := Finset.card_eq_zero.mp hden
    have hshort_empty : shortPatternFiber (k := k) n e p = ∅ := by
      unfold shortPatternFiber
      simp [hfiber_empty]
    unfold shortPatternRatio
    simp [hden, hshort_empty]
  · unfold shortPatternRatio
    exact ENNReal.div_ne_top (by simp) (by exact_mod_cast hden)

lemma toReal_sum_shortPatternRatio
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      shortPatternRatio (k := k) n e p).toReal =
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (shortPatternRatio (k := k) n e p).toReal := by
  exact ENNReal.toReal_sum
    (fun p hp => shortPatternRatio_ne_top (k := k) (n := n) (e := e) (p := p))

lemma sum_shortPatternRatio_toReal
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      (shortPatternRatio (k := k) n e p).toReal =
        (if (fiber k (Nat.succ n) e).card = 0 then 0 else 1) := by
  have hsum_enn :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        shortPatternRatio (k := k) n e p =
          (if (fiber k (Nat.succ n) e).card = 0 then 0 else 1) := by
    simpa [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)] using
      sum_shortPatternRatio_over_shortImage (k := k) (n := n) (e := e)
  have hsum_real := congrArg ENNReal.toReal hsum_enn
  rw [toReal_sum_shortPatternRatio (k := k) (hN := hN) (e := e) (s := s)] at hsum_real
  by_cases hden : (fiber k (Nat.succ n) e).card = 0
  · simpa [hden] using hsum_real
  · simpa [hden] using hsum_real

lemma sum_shortPatternRatio_toReal_le_one
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      (shortPatternRatio (k := k) n e p).toReal ≤ (1 : ℝ) := by
  have hsum := sum_shortPatternRatio_toReal (k := k) (hN := hN) (e := e) (s := s)
  by_cases hden : (fiber k (Nat.succ n) e).card = 0
  · simpa [hsum, hden]
  · simpa [hsum, hden]

lemma sum_prefixPatternRatio
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      prefixPatternRatio (k := k) (hN := hN) e s p =
        (if (prefixFiber (k := k) (h := hN) e s).card = 0 then 0 else 1) := by
  classical
  let P₀ : Finset (ExcursionList k) :=
    (prefixFiber (k := k) (h := hN) e s).image
      (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))
  have hcard :
      (prefixFiber (k := k) (h := hN) e s).card =
        ∑ p ∈ P₀, (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    simpa [P₀, prefixPatternFiber] using
      (Finset.card_eq_sum_card_image
        (f := fun xs : Traj k N =>
          excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))
        (s := prefixFiber (k := k) (h := hN) e s))
  have hP :
      excursionPatternSet (k := k) (hN := hN) e s =
        ((fiber k (Nat.succ n) e).image
          (fun ys => excursionListOfTraj (k := k) ys)) := by
    exact excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)
  -- Outside the long-prefix image `P₀`, numerator card is zero.
  have hsubset : P₀ ⊆ excursionPatternSet (k := k) (hN := hN) e s := by
    intro p hp
    rw [hP]
    rcases Finset.mem_image.1 hp with ⟨xs, hxs, rfl⟩
    exact mem_excursionPatternSet_of_prefixFiber (k := k) (hN := hN) (e := e) (s := s) hxs
  have hzero_out :
      ∀ p ∈ excursionPatternSet (k := k) (hN := hN) e s, p ∉ P₀ →
        (prefixPatternFiber (k := k) (hN := hN) e s p).card = 0 := by
    intro p hp hpNot
    have hempty :
        prefixPatternFiber (k := k) (hN := hN) e s p = ∅ := by
      ext xs
      constructor
      · intro hxs
        have hx : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
          (Finset.mem_filter.1 hxs).2
        have hxP0 : p ∈ P₀ := by
          refine Finset.mem_image.2 ?_
          exact ⟨xs, (Finset.mem_filter.1 hxs).1, hx⟩
        exact False.elim (hpNot hxP0)
      · intro hxs
        simp at hxs
    simp [hempty]
  have hcard_on_patternSet :
      (prefixFiber (k := k) (h := hN) e s).card =
        ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    calc
      (prefixFiber (k := k) (h := hN) e s).card
          = ∑ p ∈ P₀, (prefixPatternFiber (k := k) (hN := hN) e s p).card := hcard
      _ = ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
            exact Finset.sum_subset hsubset hzero_out
  by_cases hpf0 : (prefixFiber (k := k) (h := hN) e s).card = 0
  · have hratio0 :
      ∀ p, prefixPatternRatio (k := k) (hN := hN) e s p = 0 := by
        intro p
        have hpf_empty : prefixFiber (k := k) (h := hN) e s = ∅ := Finset.card_eq_zero.mp hpf0
        have hpat_empty : prefixPatternFiber (k := k) (hN := hN) e s p = ∅ := by
          unfold prefixPatternFiber
          simp [hpf_empty]
        unfold prefixPatternRatio
        simp [hpf0, hpat_empty]
    have hsum0 :
        ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          prefixPatternRatio (k := k) (hN := hN) e s p = 0 := by
      refine Finset.sum_eq_zero ?_
      intro p hp
      simp [hratio0]
    simp [hpf0, hsum0]
  · have hsum :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        prefixPatternRatio (k := k) (hN := hN) e s p =
          (((prefixFiber (k := k) (h := hN) e s).card : ℕ) : ENNReal) /
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) := by
      calc
        ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          prefixPatternRatio (k := k) (hN := hN) e s p
            = (((∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                (prefixPatternFiber (k := k) (hN := hN) e s p).card) : ℕ) : ENNReal) /
                ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) := by
                  simp [prefixPatternRatio, div_eq_mul_inv, Finset.sum_mul]
        _ = (((prefixFiber (k := k) (h := hN) e s).card : ℕ) : ENNReal) /
              ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) := by
                rw [hcard_on_patternSet]
    have hpf_ne_zero : ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) ≠ 0 := by
      exact_mod_cast hpf0
    have hpf_ne_top : ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) ≠ ⊤ := by simp
    have hratio1 :
        (((prefixFiber (k := k) (h := hN) e s).card : ℕ) : ENNReal) /
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) = 1 := by
      exact (ENNReal.div_eq_one_iff hpf_ne_zero hpf_ne_top).2 rfl
    simp [hpf0, hsum, hratio1]

/-- Long-prefix pattern ratio is invariant under segment-swap image cardinality
in the post-prefix regime (`n+1 ≤ a`). -/
lemma prefixPatternRatio_card_image_segmentSwap_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    (((prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card : ENNReal) /
      ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) =
    prefixPatternRatio (k := k) (hN := hN) e s p := by
  rw [card_image_segmentSwap_prefixPatternFiber_of_prefix_before_swap
      (k := k) (hN := hN) (e := e) (s := s) (p := p)
      (a := a) (L1 := L1) (L2 := L2) hna hL1 hL2 hcN]
  rfl

lemma worPatternMass_card_image_segmentSwap_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    (((prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card : ENNReal) /
      ((fiber k N s).card : ENNReal) =
    worPatternMass (k := k) (hN := hN) e s p := by
  rw [card_image_segmentSwap_prefixPatternFiber_of_prefix_before_swap
      (k := k) (hN := hN) (e := e) (s := s) (p := p)
      (a := a) (L1 := L1) (L2 := L2) hna hL1 hL2 hcN]
  rfl

/-- If segment swap sends one prefix-pattern fiber exactly onto another, then
the long-prefix pattern ratios are equal. This packages the finite-cardinality
symmetry needed for adjacent-excursion transposition arguments. -/
lemma prefixPatternRatio_eq_of_segmentSwap_image_eq
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (himg :
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      prefixPatternFiber (k := k) (hN := hN) e s q) :
    prefixPatternRatio (k := k) (hN := hN) e s p =
      prefixPatternRatio (k := k) (hN := hN) e s q := by
  have hcardImage :
      ((prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card =
      (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    refine Finset.card_image_iff.mpr ?_
    intro xs hxs ys hys hEq
    exact segmentSwap_injective (k := k) (a := a) (L1 := L1) (L2 := L2)
      (hL1 := hL1) (hL2 := hL2) (hcN := hcN) hEq
  have hcard :
      (prefixPatternFiber (k := k) (hN := hN) e s q).card =
        (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    rw [← himg, hcardImage]
  unfold prefixPatternRatio
  simp [hcard]

/-- Same as `prefixPatternRatio_eq_of_segmentSwap_image_eq`, but for WOR-side
pattern masses. -/
lemma worPatternMass_eq_of_segmentSwap_image_eq
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (himg :
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      prefixPatternFiber (k := k) (hN := hN) e s q) :
    worPatternMass (k := k) (hN := hN) e s p =
      worPatternMass (k := k) (hN := hN) e s q := by
  have hcardImage :
      ((prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card =
      (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    refine Finset.card_image_iff.mpr ?_
    intro xs hxs ys hys hEq
    exact segmentSwap_injective (k := k) (a := a) (L1 := L1) (L2 := L2)
      (hL1 := hL1) (hL2 := hL2) (hcN := hcN) hEq
  have hcard :
      (prefixPatternFiber (k := k) (hN := hN) e s q).card =
        (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    rw [← himg, hcardImage]
  unfold worPatternMass
  simp [hcard]

/-- Short-horizon analogue: if segment swap sends one short-pattern fiber onto
another, then the corresponding short-pattern ratios are equal. -/
lemma shortPatternRatio_eq_of_segmentSwap_image_eq
    (n : ℕ) (e : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ Nat.succ n)
    (himg :
      (shortPatternFiber (k := k) n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcN) =
      shortPatternFiber (k := k) n e q) :
    shortPatternRatio (k := k) n e p =
      shortPatternRatio (k := k) n e q := by
  have hcardImage :
      ((shortPatternFiber (k := k) n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcN)).card =
      (shortPatternFiber (k := k) n e p).card := by
    refine Finset.card_image_iff.mpr ?_
    intro xs hxs ys hys hEq
    exact segmentSwap_injective (k := k) (a := a) (L1 := L1) (L2 := L2)
      (hL1 := hL1) (hL2 := hL2) (hcN := hcN) hEq
  have hcard :
      (shortPatternFiber (k := k) n e q).card =
        (shortPatternFiber (k := k) n e p).card := by
    rw [← himg, hcardImage]
  unfold shortPatternRatio
  simp [hcard]

/-- Combined ratio-term invariance under synchronized short/prefix segment-swap
fiber equalities. -/
lemma abs_ratio_term_eq_of_segmentSwap_image_eq
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) (hcLong : a + L1 + L2 ≤ N)
    (himgShort :
      (shortPatternFiber (k := k) n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
      shortPatternFiber (k := k) n e q)
    (himgPrefix :
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcLong) =
      prefixPatternFiber (k := k) (hN := hN) e s q)
    (Wv Pv : ℝ) :
    |(shortPatternRatio (k := k) n e p).toReal * Wv -
      (prefixPatternRatio (k := k) (hN := hN) e s p).toReal * Pv| =
    |(shortPatternRatio (k := k) n e q).toReal * Wv -
      (prefixPatternRatio (k := k) (hN := hN) e s q).toReal * Pv| := by
  have hShort :
      shortPatternRatio (k := k) n e p =
        shortPatternRatio (k := k) n e q :=
    shortPatternRatio_eq_of_segmentSwap_image_eq
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort himgShort
  have hPrefix :
      prefixPatternRatio (k := k) (hN := hN) e s p =
        prefixPatternRatio (k := k) (hN := hN) e s q :=
    prefixPatternRatio_eq_of_segmentSwap_image_eq
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcLong himgPrefix
  simp [hShort, hPrefix]

/-- Practical wrapper: derive absolute-ratio invariance from forward/backward
segment-swap membership maps on short and long pattern fibers. -/
lemma abs_ratio_term_eq_of_segmentSwap_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) (hcLong : a + L1 + L2 ≤ N)
    (hmapShort :
      ∀ ys ∈ shortPatternFiber n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber n e q)
    (hmapShortInv :
      ∀ zs ∈ shortPatternFiber n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber n e p)
    (hmapPrefix :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcLong ∈
          prefixPatternFiber (k := k) (hN := hN) e s q)
    (hmapPrefixInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcLong) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p)
    (Wv Pv : ℝ) :
    |(shortPatternRatio (k := k) n e p).toReal * Wv -
      (prefixPatternRatio (k := k) (hN := hN) e s p).toReal * Pv| =
    |(shortPatternRatio (k := k) n e q).toReal * Wv -
      (prefixPatternRatio (k := k) (hN := hN) e s q).toReal * Pv| := by
  have himgShort :
      (shortPatternFiber n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
        shortPatternFiber n e q :=
    image_eq_segmentSwap_shortPatternFiber_of_maps
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      hmapShort hmapShortInv
  have himgPrefix :
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcLong) =
        prefixPatternFiber (k := k) (hN := hN) e s q :=
    image_eq_segmentSwap_prefixPatternFiber_of_maps
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcLong
      hmapPrefix hmapPrefixInv
  exact abs_ratio_term_eq_of_segmentSwap_image_eq
    (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hcLong
    himgShort himgPrefix Wv Pv

/-- Finite-pattern uniformity package for one adjacent segment swap.

Given forward/backward swap maps on both short and long pattern fibers, all
pattern-level observables used in the ratio decomposition are invariant under
the induced transposition `p ↔ q`. This is the reusable symmetry block for the
final orbit/cardinality averaging step in `hsumAbsRatio`. -/
theorem finite_pattern_uniformity_of_adjacent_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) (hcLong : a + L1 + L2 ≤ N)
    (hmapShort :
      ∀ ys ∈ shortPatternFiber n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber n e q)
    (hmapShortInv :
      ∀ zs ∈ shortPatternFiber n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber n e p)
    (hmapPrefix :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcLong ∈
          prefixPatternFiber (k := k) (hN := hN) e s q)
    (hmapPrefixInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcLong) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p) :
    shortPatternRatio (k := k) n e p = shortPatternRatio (k := k) n e q ∧
    prefixPatternRatio (k := k) (hN := hN) e s p =
      prefixPatternRatio (k := k) (hN := hN) e s q ∧
    worPatternMass (k := k) (hN := hN) e s p =
      worPatternMass (k := k) (hN := hN) e s q ∧
    ∀ (Wv Pv : ℝ),
      |(shortPatternRatio (k := k) n e p).toReal * Wv -
          (prefixPatternRatio (k := k) (hN := hN) e s p).toReal * Pv| =
        |(shortPatternRatio (k := k) n e q).toReal * Wv -
          (prefixPatternRatio (k := k) (hN := hN) e s q).toReal * Pv| := by
  have himgShort :
      (shortPatternFiber n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
        shortPatternFiber n e q :=
    image_eq_segmentSwap_shortPatternFiber_of_maps
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      hmapShort hmapShortInv
  have himgPrefix :
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcLong) =
        prefixPatternFiber (k := k) (hN := hN) e s q :=
    image_eq_segmentSwap_prefixPatternFiber_of_maps
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcLong
      hmapPrefix hmapPrefixInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact shortPatternRatio_eq_of_segmentSwap_image_eq
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort himgShort
  · exact prefixPatternRatio_eq_of_segmentSwap_image_eq
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcLong himgPrefix
  · exact worPatternMass_eq_of_segmentSwap_image_eq
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcLong himgPrefix
  · intro Wv Pv
    exact abs_ratio_term_eq_of_segmentSwap_image_eq
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hcLong
      himgShort himgPrefix Wv Pv

/-- Image-equality version of finite-pattern adjacent-swap uniformity.

This lightweight wrapper avoids reconstructing transport maps when image
equalities are already available. -/
lemma finite_pattern_uniformity_of_adjacent_swap_of_images
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) (hcLong : a + L1 + L2 ≤ N)
    (himgShort :
      (shortPatternFiber n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
        shortPatternFiber n e q)
    (himgPrefix :
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcLong) =
        prefixPatternFiber (k := k) (hN := hN) e s q) :
    shortPatternRatio (k := k) n e p = shortPatternRatio (k := k) n e q ∧
    prefixPatternRatio (k := k) (hN := hN) e s p =
      prefixPatternRatio (k := k) (hN := hN) e s q ∧
    worPatternMass (k := k) (hN := hN) e s p =
      worPatternMass (k := k) (hN := hN) e s q ∧
    ∀ (Wv Pv : ℝ),
      |(shortPatternRatio (k := k) n e p).toReal * Wv -
          (prefixPatternRatio (k := k) (hN := hN) e s p).toReal * Pv| =
        |(shortPatternRatio (k := k) n e q).toReal * Wv -
          (prefixPatternRatio (k := k) (hN := hN) e s q).toReal * Pv| := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact shortPatternRatio_eq_of_segmentSwap_image_eq
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort himgShort
  · exact prefixPatternRatio_eq_of_segmentSwap_image_eq
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcLong himgPrefix
  · exact worPatternMass_eq_of_segmentSwap_image_eq
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcLong himgPrefix
  · intro Wv Pv
    exact abs_ratio_term_eq_of_segmentSwap_image_eq
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hcLong
      himgShort himgPrefix Wv Pv

/-- Build both short/prefix image equalities for an adjacent transposition from
explicit decomposition witnesses and fiber-preservation maps. -/
lemma adjacent_transposition_image_eq_of_decomps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmapShortFiber :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ fiber k (Nat.succ n) e)
    (hdecompShort :
      ShortSwapMiddleDecomp n e p q a L1 L2 hL1 hL2 hcShort)
    (hmapShortFiberInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          fiber k (Nat.succ n) e)
    (hdecompShortInv :
      ShortSwapMiddleDecomp
        n e q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
    (hmapPrefixFiber :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecompPrefix :
      PrefixSwapMiddleDecomp
        (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (hmapPrefixFiberInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (le_trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) hN) ∈
          prefixFiber (k := k) (h := hN) e s)
    (hdecompPrefixInv :
      PrefixSwapMiddleDecomp
        (hN := hN) e s q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    (shortPatternFiber (k := k) n e p).image
      (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
      shortPatternFiber (k := k) n e q ∧
    (prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
      prefixPatternFiber (k := k) (hN := hN) e s q := by
  have himgShort :
      (shortPatternFiber (k := k) n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
      shortPatternFiber (k := k) n e q :=
    himgShort_of_shortSwapMiddleDecomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      hmapShortFiber hdecompShort hmapShortFiberInv hdecompShortInv
  have himgPrefix :
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
      prefixPatternFiber (k := k) (hN := hN) e s q :=
    himgPrefix_of_PrefixSwapMiddleDecomp
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      hmapPrefixFiber hdecompPrefix hmapPrefixFiberInv hdecompPrefixInv
  exact ⟨himgShort, himgPrefix⟩

/-- Automatic adjacent-transposition image equalities from decomposition
witnesses only (no separate short/prefix map hypotheses). -/
lemma adjacent_transposition_image_eq_of_decomps_auto
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompShort : ShortSwapMiddleDecomp
      (k := k) n e p q a L1 L2 hL1 hL2 hcShort)
    (hdecompShortInv : ShortSwapMiddleDecomp
      (k := k) n e q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
    (hdecompPrefix : PrefixSwapMiddleDecomp
      (k := k) (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (hdecompPrefixInv : PrefixSwapMiddleDecomp
      (k := k) (hN := hN) e s q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    (shortPatternFiber (k := k) n e p).image
      (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
      shortPatternFiber (k := k) n e q ∧
    (prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
      prefixPatternFiber (k := k) (hN := hN) e s q := by
  exact adjacent_transposition_image_eq_of_decomps
    (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
    (hmapShortFiber := hmapShortFiber_of_shortSwapMiddleDecomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShort)
    (hdecompShort := hdecompShort)
    (hmapShortFiberInv := hmapShortFiberInv_of_shortSwapMiddleDecomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShortInv)
    (hdecompShortInv := hdecompShortInv)
    (hmapPrefixFiber := hmapPrefixFiber_of_prefixSwapMiddleDecomp
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompPrefix)
    (hdecompPrefix := hdecompPrefix)
    (hmapPrefixFiberInv := hmapPrefixFiberInv_of_prefixSwapMiddleDecomp
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompPrefixInv)
    (hdecompPrefixInv := hdecompPrefixInv)

/-- Decomposition-witness wrapper for `finite_pattern_uniformity_of_adjacent_swap`.

This bridges explicit short/long adjacent-swap decomposition witnesses directly
to the finite-pattern invariance package used in the BEST-core orbit argument. -/
lemma finite_pattern_uniformity_of_adjacent_swap_of_decomps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompShort :
      ShortSwapMiddleDecomp n e p q a L1 L2 hL1 hL2 hcShort)
    (hdecompShortInv :
      ShortSwapMiddleDecomp
        n e q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
    (hdecompPrefix :
      PrefixSwapMiddleDecomp
        (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (hdecompPrefixInv :
      PrefixSwapMiddleDecomp
        (hN := hN) e s q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    shortPatternRatio (k := k) n e p = shortPatternRatio (k := k) n e q ∧
    prefixPatternRatio (k := k) (hN := hN) e s p =
      prefixPatternRatio (k := k) (hN := hN) e s q ∧
    worPatternMass (k := k) (hN := hN) e s p =
      worPatternMass (k := k) (hN := hN) e s q ∧
    ∀ (Wv Pv : ℝ),
      |(shortPatternRatio (k := k) n e p).toReal * Wv -
          (prefixPatternRatio (k := k) (hN := hN) e s p).toReal * Pv| =
        |(shortPatternRatio (k := k) n e q).toReal * Wv -
          (prefixPatternRatio (k := k) (hN := hN) e s q).toReal * Pv| := by
  have himg :
      (shortPatternFiber (k := k) n e p).image
        (fun ys => segmentSwap ys a L1 L2 hL1 hL2 hcShort) =
        shortPatternFiber (k := k) n e q ∧
      (prefixPatternFiber (k := k) (hN := hN) e s p).image
        (fun xs => segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN)) =
        prefixPatternFiber (k := k) (hN := hN) e s q :=
    adjacent_transposition_image_eq_of_decomps_auto
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      hdecompShort hdecompShortInv hdecompPrefix hdecompPrefixInv
  rcases himg with ⟨himgShort, himgPrefix⟩
  exact finite_pattern_uniformity_of_adjacent_swap_of_images
    (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
    (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort (le_trans hcShort hN)
    himgShort himgPrefix

/-- The absolute ratio-term used in `hsumAbsRatio`. -/
def ratioTerm
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p : ExcursionList k) : ℝ :=
  |(shortPatternRatio (k := k) n e p).toReal *
      (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
    (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
      (prefixCoeff (k := k) (h := hN) e s).toReal|

lemma ratioTerm_nonneg
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p : ExcursionList k) :
    0 ≤ ratioTerm (k := k) (hN := hN) (hk := hk) e s p := by
  unfold ratioTerm
  exact abs_nonneg _

lemma ratioTerm_eq_of_segmentSwap_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) (hcLong : a + L1 + L2 ≤ N)
    (hmapShort :
      ∀ ys ∈ shortPatternFiber n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber n e q)
    (hmapShortInv :
      ∀ zs ∈ shortPatternFiber n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber n e p)
    (hmapPrefix :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcLong ∈
          prefixPatternFiber (k := k) (hN := hN) e s q)
    (hmapPrefixInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcLong) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p) :
    ratioTerm (k := k) (hN := hN) (hk := hk) e s p =
      ratioTerm (k := k) (hN := hN) (hk := hk) e s q := by
  unfold ratioTerm
  simpa using
    abs_ratio_term_eq_of_segmentSwap_maps
      (k := k) (hN := hN) (e := e) (s := s)
      (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcShort hcLong
      hmapShort hmapShortInv hmapPrefix hmapPrefixInv
      (Wv := (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
      (Pv := (prefixCoeff (k := k) (h := hN) e s).toReal)

/-- `ratioTerm` invariance under an adjacent transposition from explicit
short/long decomposition witnesses. This is the direct bridge used by the
orbit-averaging step in the BEST-core proof. -/
lemma ratioTerm_eq_of_adjacent_swap_of_decomps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompShort :
      ShortSwapMiddleDecomp n e p q a L1 L2 hL1 hL2 hcShort)
    (hdecompShortInv :
      ShortSwapMiddleDecomp
        n e q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
    (hdecompPrefix :
      PrefixSwapMiddleDecomp
        (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (hdecompPrefixInv :
      PrefixSwapMiddleDecomp
        (hN := hN) e s q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    ratioTerm (k := k) (hN := hN) (hk := hk) e s p =
      ratioTerm (k := k) (hN := hN) (hk := hk) e s q := by
  rcases finite_pattern_uniformity_of_adjacent_swap_of_decomps
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      hdecompShort hdecompShortInv
      hdecompPrefix hdecompPrefixInv
      with ⟨_, _, _, hAbs⟩
  unfold ratioTerm
  simpa using hAbs
    ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
    ((prefixCoeff (k := k) (h := hN) e s).toReal)

/-- Reindex `ratioTerm` along a pattern permutation preserving the finite index
set. This is the algebraic summation step used by orbit/cardinality averaging. -/
lemma sum_ratioTerm_eq_sum_ratioTerm_comp_equiv
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (σ : ExcursionList k ≃ ExcursionList k)
    (hmem :
      ∀ p : ExcursionList k,
        p ∈ excursionPatternSet (k := k) (hN := hN) e s ↔
          σ p ∈ excursionPatternSet (k := k) (hN := hN) e s) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s p) =
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s (σ p)) := by
  classical
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hmem_symm :
      ∀ p : ExcursionList k, p ∈ P ↔ σ.symm p ∈ P := by
    intro p
    constructor
    · intro hp
      exact (hmem (σ.symm p)).2 (by simpa using hp)
    · intro hp
      simpa using (hmem (σ.symm p)).1 hp
  have hsum :=
    (Finset.sum_equiv
      (s := P) (t := P) (e := σ.symm)
      (f := fun p => ratioTerm (k := k) (hN := hN) (hk := hk) e s p)
      (g := fun p => ratioTerm (k := k) (hN := hN) (hk := hk) e s (σ p))
      (hst := hmem_symm)
      (hfg := fun p _ => by simp))
  simpa [P] using hsum

lemma sum_ratioTerm_eq_sum_ratioTerm_comp_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p q : ExcursionList k)
    (hmem :
      ∀ r : ExcursionList k,
        r ∈ excursionPatternSet (k := k) (hN := hN) e s ↔
          (Equiv.swap p q) r ∈ excursionPatternSet (k := k) (hN := hN) e s) :
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s r) =
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s ((Equiv.swap p q) r)) := by
  exact sum_ratioTerm_eq_sum_ratioTerm_comp_equiv
    (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
    (σ := Equiv.swap p q) hmem

/-- Partition the finite ratio-term sum by excursion-multiset fibers. -/
lemma sum_ratioTerm_partition_by_excursionMultiset
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s p) =
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        ratioTerm (k := k) (hN := hN) (hk := hk) e s p) := by
  classical
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hMapsTo :
      (P : Set (ExcursionList k)).MapsTo Multiset.ofList (P.image Multiset.ofList) := by
    intro p hp
    exact Finset.mem_image.2 ⟨p, hp, rfl⟩
  symm
  simpa [P] using
    (Finset.sum_fiberwise_of_maps_to
      (s := P)
      (t := P.image Multiset.ofList)
      (g := Multiset.ofList)
      hMapsTo
      (fun p => ratioTerm (k := k) (hN := hN) (hk := hk) e s p))

/-- Partition the finite absolute WR/WOR discrepancy sum by excursion-multiset
fibers. This is the finite orbit/cardinality decomposition used in the BEST core. -/
lemma sum_abs_wr_wor_patternMass_partition_by_excursionMultiset
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
  classical
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hMapsTo :
      (P : Set (ExcursionList k)).MapsTo Multiset.ofList (P.image Multiset.ofList) := by
    intro p hp
    exact Finset.mem_image.2 ⟨p, hp, rfl⟩
  symm
  simpa [P] using
    (Finset.sum_fiberwise_of_maps_to
      (s := P)
      (t := P.image Multiset.ofList)
      (g := Multiset.ofList)
      hMapsTo
          (fun p =>
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|))

/-- On a fixed multiset fiber, if the absolute WR/WOR discrepancy is constant,
the inner finite sum collapses to `card * representative`. -/
lemma sum_abs_wr_wor_on_multisetFiber_eq_card_mul_of_const
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (mset : Multiset (ExcursionType k))
    (p0 : ExcursionList k)
    (hconst :
      ∀ p,
        p ∈ excursionPatternSet (k := k) (hN := hN) e s →
          Multiset.ofList p = mset →
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal| =
            |(wrPatternMass (k := k) hk n e s p0).toReal -
              (worPatternMass (k := k) (hN := hN) e s p0).toReal|) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
    (((excursionPatternSet (k := k) (hN := hN) e s).filter
        (fun p => Multiset.ofList p = mset)).card : ℝ) *
      |(wrPatternMass (k := k) hk n e s p0).toReal -
        (worPatternMass (k := k) (hN := hN) e s p0).toReal| := by
  let P := excursionPatternSet (k := k) (hN := hN) e s
  calc
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
      Finset.sum (P.filter (fun p => Multiset.ofList p = mset))
        (fun p =>
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
            simp [P]
    _ =
      Finset.sum (P.filter (fun p => Multiset.ofList p = mset))
        (fun _ =>
          |(wrPatternMass (k := k) hk n e s p0).toReal -
            (worPatternMass (k := k) (hN := hN) e s p0).toReal|) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact hconst p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2
    _ =
      (((P.filter (fun p => Multiset.ofList p = mset)).card : ℕ) : ℝ) *
        |(wrPatternMass (k := k) hk n e s p0).toReal -
          (worPatternMass (k := k) (hN := hN) e s p0).toReal| := by
            simp
    _ =
      (((excursionPatternSet (k := k) (hN := hN) e s).filter
          (fun p => Multiset.ofList p = mset)).card : ℝ) *
        |(wrPatternMass (k := k) hk n e s p0).toReal -
          (worPatternMass (k := k) (hN := hN) e s p0).toReal| := by
            simp [P]

/-- `sum_abs_wr_wor_on_multisetFiber_eq_card_mul_of_const` with representative
obtained from `mset ∈ image Multiset.ofList`. -/
lemma sum_abs_wr_wor_on_multisetFiber_eq_card_mul_choose_of_const
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (mset : Multiset (ExcursionType k))
    (hmset :
      mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList)
    (hconst :
      ∀ p q,
        p ∈ excursionPatternSet (k := k) (hN := hN) e s →
          q ∈ excursionPatternSet (k := k) (hN := hN) e s →
            Multiset.ofList p = mset →
              Multiset.ofList q = mset →
                |(wrPatternMass (k := k) hk n e s p).toReal -
                  (worPatternMass (k := k) (hN := hN) e s p).toReal| =
                |(wrPatternMass (k := k) hk n e s q).toReal -
                  (worPatternMass (k := k) (hN := hN) e s q).toReal|) :
    ∃ p0, p0 ∈ excursionPatternSet (k := k) (hN := hN) e s ∧
      Multiset.ofList p0 = mset ∧
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
      (((excursionPatternSet (k := k) (hN := hN) e s).filter
          (fun p => Multiset.ofList p = mset)).card : ℝ) *
        |(wrPatternMass (k := k) hk n e s p0).toReal -
          (worPatternMass (k := k) (hN := hN) e s p0).toReal| := by
  rcases Finset.mem_image.1 hmset with ⟨p0, hp0P, hp0m⟩
  refine ⟨p0, hp0P, hp0m, ?_⟩
  exact sum_abs_wr_wor_on_multisetFiber_eq_card_mul_of_const
    (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
    (mset := mset) (p0 := p0)
    (fun p hp hpm => hconst p p0 hp hp0P hpm hp0m)

/-- Orbit/cardinality averaging over the multiset partition: if the absolute
WR/WOR discrepancy is fiberwise-constant on each `Multiset.ofList` class, the
double sum collapses to one representative per class. -/
lemma sum_abs_wr_wor_partition_by_excursionMultiset_eq_sum_card_mul_repr_of_const
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hconst :
      ∀ mset,
        mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList →
          ∀ p q,
            p ∈ excursionPatternSet (k := k) (hN := hN) e s →
              q ∈ excursionPatternSet (k := k) (hN := hN) e s →
                Multiset.ofList p = mset →
                  Multiset.ofList q = mset →
                    |(wrPatternMass (k := k) hk n e s p).toReal -
                      (worPatternMass (k := k) (hN := hN) e s p).toReal| =
                    |(wrPatternMass (k := k) hk n e s q).toReal -
                      (worPatternMass (k := k) (hN := hN) e s q).toReal|) :
    let P := excursionPatternSet (k := k) (hN := hN) e s
    let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
      if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
    (∑ mset ∈ P.image Multiset.ofList,
      ∑ p ∈ P with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
    (∑ mset ∈ P.image Multiset.ofList,
      (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
        |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
          (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|)) := by
  classical
  let P := excursionPatternSet (k := k) (hN := hN) e s
  let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
    if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
  refine Finset.sum_congr rfl ?_
  intro mset hmset
  have hmset' : ∃ p ∈ P, Multiset.ofList p = mset := Finset.mem_image.1 hmset
  have hrepr_def :
      repr mset =
        Classical.choose hmset' := by
    simp [repr, hmset']
  have hreprP :
      repr mset ∈ P := by
    simpa [hrepr_def] using (Classical.choose_spec hmset').1
  have hreprm :
      Multiset.ofList (repr mset) = mset := by
    simpa [hrepr_def] using (Classical.choose_spec hmset').2
  have hconst' :
      ∀ p,
        p ∈ P →
          Multiset.ofList p = mset →
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal| =
            |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
              (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal| := by
    intro p hp hpm
    exact hconst mset hmset p (repr mset) hp hreprP hpm hreprm
  calc
    (∑ p ∈ P with Multiset.ofList p = mset,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
      (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
        |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
          (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|) := by
      exact sum_abs_wr_wor_on_multisetFiber_eq_card_mul_of_const
        (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
        (mset := mset) (p0 := repr mset) hconst'
    _ = (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
        |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
          (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|) := by
      rfl

lemma sum_abs_wr_wor_partition_by_excursionMultiset_le_of_const
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (bound : ℝ)
    (hconst :
      ∀ mset,
        mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList →
          ∀ p q,
            p ∈ excursionPatternSet (k := k) (hN := hN) e s →
              q ∈ excursionPatternSet (k := k) (hN := hN) e s →
                Multiset.ofList p = mset →
                  Multiset.ofList q = mset →
                    |(wrPatternMass (k := k) hk n e s p).toReal -
                      (worPatternMass (k := k) (hN := hN) e s p).toReal| =
                    |(wrPatternMass (k := k) hk n e s q).toReal -
                      (worPatternMass (k := k) (hN := hN) e s q).toReal|)
    (hbound_repr :
      let P := excursionPatternSet (k := k) (hN := hN) e s
      let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
        if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
      (∑ mset ∈ P.image Multiset.ofList,
        (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
          |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
            (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|)) ≤ bound) :
    let P := excursionPatternSet (k := k) (hN := hN) e s
    ∑ mset ∈ P.image Multiset.ofList,
      ∑ p ∈ P with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ bound := by
  classical
  let P := excursionPatternSet (k := k) (hN := hN) e s
  let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
    if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
  have hcollapse :
      (∑ mset ∈ P.image Multiset.ofList,
        ∑ p ∈ P with Multiset.ofList p = mset,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
      (∑ mset ∈ P.image Multiset.ofList,
        (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
          |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
            (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|)) := by
    simpa [P, repr] using
      sum_abs_wr_wor_partition_by_excursionMultiset_eq_sum_card_mul_repr_of_const
        (k := k) (hN := hN) (hk := hk) (e := e) (s := s) hconst
  calc
    (∑ mset ∈ P.image Multiset.ofList,
      ∑ p ∈ P with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|)
      =
    (∑ mset ∈ P.image Multiset.ofList,
      (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
        |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
          (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|)) := hcollapse
    _ ≤ bound := by
      simpa [P, repr] using hbound_repr


lemma mem_excursionPatternSet_of_mem_shortPatternFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p : ExcursionList k) {ys : Traj k (Nat.succ n)}
    (hys : ys ∈ shortPatternFiber (k := k) n e p) :
    p ∈ excursionPatternSet (k := k) (hN := hN) e s := by
  rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)]
  exact Finset.mem_image.2 ⟨ys, (Finset.mem_filter.1 hys).1, (Finset.mem_filter.1 hys).2⟩

/-- Membership in the shared finite pattern index set is invariant under the
adjacent transposition `Equiv.swap p q` whenever we have forward/backward
segment-swap maps between the corresponding short-pattern fibers. -/
lemma mem_excursionPatternSet_swap_iff_of_shortPattern_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmap :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q)
    (hmapInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p) :
    ∀ r : ExcursionList k,
      r ∈ excursionPatternSet (k := k) (hN := hN) e s ↔
        (Equiv.swap p q) r ∈ excursionPatternSet (k := k) (hN := hN) e s := by
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hp_to_hq : p ∈ P → q ∈ P := by
    intro hpP
    have hpP' :
        p ∈ excursionPatternSet (k := k) (hN := hN) e s := by
      simpa [P] using hpP
    rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)] at hpP'
    rcases Finset.mem_image.1 hpP' with ⟨ys, hysfib, hysEq⟩
    have hys : ys ∈ shortPatternFiber (k := k) n e p := by
      exact Finset.mem_filter.2 ⟨hysfib, hysEq⟩
    have hsw : segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q :=
      hmap ys hys
    exact mem_excursionPatternSet_of_mem_shortPatternFiber
      (k := k) (hN := hN) (e := e) (s := s) q hsw
  have hq_to_hp : q ∈ P → p ∈ P := by
    intro hqP
    have hqP' :
        q ∈ excursionPatternSet (k := k) (hN := hN) e s := by
      simpa [P] using hqP
    rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)] at hqP'
    rcases Finset.mem_image.1 hqP' with ⟨zs, hzsfib, hzsEq⟩
    have hzs : zs ∈ shortPatternFiber (k := k) n e q := by
      exact Finset.mem_filter.2 ⟨hzsfib, hzsEq⟩
    have hsw : segmentSwap zs a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
        shortPatternFiber (k := k) n e p := hmapInv zs hzs
    exact mem_excursionPatternSet_of_mem_shortPatternFiber
      (k := k) (hN := hN) (e := e) (s := s) p hsw
  intro r
  by_cases hrp : r = p
  · constructor
    · intro hrP
      have hpP : p ∈ P := by simpa [hrp] using hrP
      have hqP : q ∈ P := hp_to_hq hpP
      simpa [hrp, P, Equiv.swap_apply_def] using hqP
    · intro hswapP
      have hqP : q ∈ P := by simpa [hrp, P, Equiv.swap_apply_def] using hswapP
      have hpP : p ∈ P := hq_to_hp hqP
      simpa [hrp, P] using hpP
  · by_cases hrq : r = q
    · constructor
      · intro hrP
        have hqP : q ∈ P := by simpa [hrq] using hrP
        have hpP : p ∈ P := hq_to_hp hqP
        have hswap_r : (Equiv.swap p q) r = p := by
          simpa [hrq] using (Equiv.swap_apply_right p q)
        simpa [P, hswap_r] using hpP
      · intro hswapP
        have hswap_r : (Equiv.swap p q) r = p := by
          simpa [hrq] using (Equiv.swap_apply_right p q)
        have hpP : p ∈ P := by simpa [P, hswap_r] using hswapP
        have hqP : q ∈ P := hp_to_hq hpP
        simpa [P, hrq] using hqP
    · have hfix : (Equiv.swap p q) r = r := by
        exact Equiv.swap_apply_of_ne_of_ne hrp hrq
      simpa [P, hfix]

/-- Reindexing invariance of the finite `ratioTerm` sum under an adjacent
pattern transposition, derived from short-pattern segment-swap maps. -/
lemma sum_ratioTerm_eq_sum_ratioTerm_comp_swap_of_shortPattern_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmap :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q)
    (hmapInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p) :
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s r) =
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s ((Equiv.swap p q) r)) := by
  refine sum_ratioTerm_eq_sum_ratioTerm_comp_swap
    (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (p := p) (q := q) ?_
  exact mem_excursionPatternSet_swap_iff_of_shortPattern_maps
    (k := k) (hN := hN) (e := e) (s := s)
    (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hmap hmapInv

/-- Pointwise ratio-term invariance under an adjacent pattern transposition,
assuming synchronized short/prefix segment-swap maps. -/
lemma ratioTerm_eq_ratioTerm_swap_of_adjacent_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p q r : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) (hcLong : a + L1 + L2 ≤ N)
    (hmapShort :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q)
    (hmapShortInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p)
    (hmapPrefix :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcLong ∈
          prefixPatternFiber (k := k) (hN := hN) e s q)
    (hmapPrefixInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcLong) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p) :
    ratioTerm (k := k) (hN := hN) (hk := hk) e s r =
      ratioTerm (k := k) (hN := hN) (hk := hk) e s ((Equiv.swap p q) r) := by
  by_cases hrp : r = p
  · have hpq :
      ratioTerm (k := k) (hN := hN) (hk := hk) e s p =
        ratioTerm (k := k) (hN := hN) (hk := hk) e s q :=
      ratioTerm_eq_of_segmentSwap_maps
        (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
        (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2)
        hL1 hL2 hcShort hcLong hmapShort hmapShortInv hmapPrefix hmapPrefixInv
    simpa [hrp, Equiv.swap_apply_def] using hpq
  · by_cases hrq : r = q
    · have hpq :
        ratioTerm (k := k) (hN := hN) (hk := hk) e s p =
          ratioTerm (k := k) (hN := hN) (hk := hk) e s q :=
        ratioTerm_eq_of_segmentSwap_maps
          (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
          (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2)
          hL1 hL2 hcShort hcLong hmapShort hmapShortInv hmapPrefix hmapPrefixInv
      simpa [hrq, Equiv.swap_apply_def] using hpq.symm
    · have hfix : (Equiv.swap p q) r = r := Equiv.swap_apply_of_ne_of_ne hrp hrq
      simpa [hfix]

/-- Decomposition-witness wrapper for pointwise ratio-term invariance under an
adjacent transposition on the shared finite pattern index set. -/
lemma ratioTerm_eq_ratioTerm_swap_of_adjacent_decomps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p q r : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompShort :
      ShortSwapMiddleDecomp n e p q a L1 L2 hL1 hL2 hcShort)
    (hdecompShortInv :
      ShortSwapMiddleDecomp
        n e q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
    (hdecompPrefix :
      PrefixSwapMiddleDecomp
        (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (hdecompPrefixInv :
      PrefixSwapMiddleDecomp
        (hN := hN) e s q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    ratioTerm (k := k) (hN := hN) (hk := hk) e s r =
      ratioTerm (k := k) (hN := hN) (hk := hk) e s ((Equiv.swap p q) r) := by
  have hmapShort :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q :=
    hmapShort_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapShortFiber_of_shortSwapMiddleDecomp
        (k := k) (n := n) (e := e) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShort)
      hdecompShort
  have hdecompShortInv' :=
    shortSwapMiddleDecomp_inv_unpack
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShortInv
  have hmapShortInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p :=
    hmapShortInv_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapShortFiberInv_of_shortSwapMiddleDecomp
        (k := k) (n := n) (e := e) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShortInv)
      hdecompShortInv'
  have hmapPrefix :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 (le_trans hcShort hN) ∈
          prefixPatternFiber (k := k) (hN := hN) e s q :=
    hmapPrefix_of_swap_middle_of_excursionPairs_decomp
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapPrefixFiber_of_prefixSwapMiddleDecomp
        (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompPrefix)
      hdecompPrefix
  have hdecompPrefixInv' :=
    prefixSwapMiddleDecomp_inv_unpack
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompPrefixInv
  have hmapPrefixInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using le_trans hcShort hN) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p :=
    hmapPrefixInv_of_swap_middle_of_excursionPairs_decomp
      (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapPrefixFiberInv_of_prefixSwapMiddleDecomp
        (k := k) (hN := hN) (e := e) (s := s) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompPrefixInv)
      hdecompPrefixInv'
  exact ratioTerm_eq_ratioTerm_swap_of_adjacent_maps
    (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
    (p := p) (q := q) (r := r)
    (a := a) (L1 := L1) (L2 := L2)
    hL1 hL2 hcShort (le_trans hcShort hN)
    hmapShort hmapShortInv hmapPrefix hmapPrefixInv

/-- Reindexing invariance of the finite `ratioTerm` sum under an adjacent
pattern transposition, built directly from short/prefix decomposition witnesses. -/
lemma sum_ratioTerm_eq_sum_ratioTerm_comp_swap_of_adjacent_decomps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompShort :
      ShortSwapMiddleDecomp n e p q a L1 L2 hL1 hL2 hcShort)
    (hdecompShortInv :
      ShortSwapMiddleDecomp
        n e q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
    (_hdecompPrefix :
      PrefixSwapMiddleDecomp
        (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (_hdecompPrefixInv :
      PrefixSwapMiddleDecomp
        (hN := hN) e s q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s r) =
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s ((Equiv.swap p q) r)) := by
  have hmapShort :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q :=
    hmapShort_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapShortFiber_of_shortSwapMiddleDecomp
        (k := k) (n := n) (e := e) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShort)
      hdecompShort
  have hdecompShortInv' :=
    shortSwapMiddleDecomp_inv_unpack
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShortInv
  have hmapShortInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p :=
    hmapShortInv_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapShortFiberInv_of_shortSwapMiddleDecomp
        (k := k) (n := n) (e := e) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShortInv)
      hdecompShortInv'
  have hmem :
      ∀ r : ExcursionList k,
        r ∈ excursionPatternSet (k := k) (hN := hN) e s ↔
          (Equiv.swap p q) r ∈ excursionPatternSet (k := k) (hN := hN) e s :=
    mem_excursionPatternSet_swap_iff_of_shortPattern_maps
      (k := k) (hN := hN) (e := e) (s := s)
      (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      hmapShort hmapShortInv
  exact sum_ratioTerm_eq_sum_ratioTerm_comp_swap
    (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (p := p) (q := q) hmem

lemma wrPatternMass_eq_card_mul_wordProb_of_mem_shortPatternFiber
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k)
    {ys₀ : Traj k (Nat.succ n)} (hys₀ : ys₀ ∈ shortPatternFiber (k := k) n e p) :
    wrPatternMass (k := k) hk n e s p =
      (shortPatternFiber (k := k) n e p).card *
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
  classical
  have hconst :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) =
          wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
    intro ys hys
    have hstate : stateOfTraj (k := k) ys = stateOfTraj (k := k) ys₀ := by
      have hyse : stateOfTraj (k := k) ys = e := (Finset.mem_filter.1 ((Finset.mem_filter.1 hys).1)).2
      have hys0e : stateOfTraj (k := k) ys₀ = e := (Finset.mem_filter.1 ((Finset.mem_filter.1 hys₀).1)).2
      exact hyse.trans hys0e.symm
    exact wordProb_const_on_state_fiber (k := k)
      (θ := empiricalParam (k := k) hk s) hstate
  unfold wrPatternMass shortPatternFiber
  have hsum_filter :
      ∑ ys ∈ fiber k (Nat.succ n) e,
        (if excursionListOfTraj (k := k) ys = p then
          wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) else 0) =
      ∑ ys ∈ (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p),
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) := by
    simpa using
      (Finset.sum_filter
        (s := fiber k (Nat.succ n) e)
        (p := fun ys => excursionListOfTraj (k := k) ys = p)
        (f := fun ys =>
          wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys))).symm
  rw [hsum_filter]
  have hsum_const :
      ∑ ys ∈ (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p),
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) =
      ∑ ys ∈ (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p),
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
    refine Finset.sum_congr rfl ?_
    intro ys hys
    exact hconst ys (by simpa [shortPatternFiber] using hys)
  rw [hsum_const]
  rw [Finset.sum_const]
  simp [nsmul_eq_mul, mul_comm]

lemma wrPatternMass_eq_shortRatio_mul_W
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k)
    {ys₀ : Traj k (Nat.succ n)} (hys₀ : ys₀ ∈ shortPatternFiber (k := k) n e p) :
    wrPatternMass (k := k) hk n e s p =
      shortPatternRatio (k := k) n e p *
      W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  have hysFiber : ys₀ ∈ fiber k (Nat.succ n) e := (Finset.mem_filter.1 hys₀).1
  have hwr :=
    wrPatternMass_eq_card_mul_wordProb_of_mem_shortPatternFiber
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p) hys₀
  have hW :=
    W_eq_card_mul_wordProb_of_mem_fiber
      (k := k) (N := Nat.succ n)
      (θ := empiricalParam (k := k) hk s) (s := e) ys₀ hysFiber
  have hden_ne_zero_nat : (fiber k (Nat.succ n) e).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr ⟨ys₀, hysFiber⟩
  have hden_ne_zero : ((fiber k (Nat.succ n) e).card : ENNReal) ≠ 0 := by
    exact_mod_cast hden_ne_zero_nat
  have hden_ne_top : ((fiber k (Nat.succ n) e).card : ENNReal) ≠ ⊤ := by
    simp
  have hWdiv :
      (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)) /
          ((fiber k (Nat.succ n) e).card : ENNReal) =
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
    have hcancel :
        (((fiber k (Nat.succ n) e).card : ENNReal) *
            (((fiber k (Nat.succ n) e).card : ENNReal)⁻¹)) = 1 := by
      exact ENNReal.mul_inv_cancel hden_ne_zero hden_ne_top
    calc
      (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)) /
          ((fiber k (Nat.succ n) e).card : ENNReal)
          = (((fiber k (Nat.succ n) e).card : ENNReal) *
              wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀)) *
              (((fiber k (Nat.succ n) e).card : ENNReal)⁻¹) := by
                simp [hW, div_eq_mul_inv]
      _ = wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) *
            ((((fiber k (Nat.succ n) e).card : ENNReal) *
              (((fiber k (Nat.succ n) e).card : ENNReal)⁻¹))) := by
              ac_rfl
      _ = wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
            simp [hcancel]
  calc
    wrPatternMass (k := k) hk n e s p
        = ((shortPatternFiber (k := k) n e p).card : ENNReal) *
            wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := hwr
    _ = ((shortPatternFiber (k := k) n e p).card : ENNReal) *
          ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)) /
            ((fiber k (Nat.succ n) e).card : ENNReal)) := by
          rw [hWdiv]
    _ = shortPatternRatio (k := k) n e p *
          W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
          simp [shortPatternRatio, div_eq_mul_inv]
          ac_rfl

lemma wrPatternMass_eq_shortRatio_mul_W_uncond
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) :
    wrPatternMass (k := k) hk n e s p =
      shortPatternRatio (k := k) n e p *
      W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  by_cases hcard : (shortPatternFiber (k := k) n e p).card = 0
  · have hempty : shortPatternFiber (k := k) n e p = ∅ := Finset.card_eq_zero.mp hcard
    have hwr0 : wrPatternMass (k := k) hk n e s p = 0 := by
      unfold wrPatternMass
      refine Finset.sum_eq_zero ?_
      intro ys hys
      have hyne : excursionListOfTraj (k := k) ys ≠ p := by
        intro hy
        have hmem : ys ∈ shortPatternFiber (k := k) n e p := by
          exact Finset.mem_filter.2 ⟨hys, hy⟩
        have : False := by
          simp [hempty] at hmem
        exact this.elim
      simp [hyne]
    have hnum0 : ((shortPatternFiber (k := k) n e p).card : ENNReal) = 0 := by
      exact_mod_cast hcard
    have hshort0 : shortPatternRatio (k := k) n e p = 0 := by
      unfold shortPatternRatio
      simp [hnum0]
    simp [hwr0, hshort0]
  · rcases Finset.card_ne_zero.mp hcard with ⟨ys₀, hys₀⟩
    exact wrPatternMass_eq_shortRatio_mul_W
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p) hys₀

/-- WR residual mass outside `P(n,e,s)`. -/
def wrResidualMass
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) : ENNReal :=
  ∑ ys ∈ fiber k (Nat.succ n) e,
    if excursionListOfTraj (k := k) ys ∈ excursionPatternSet (k := k) (hN := hN) e s then
      0
    else
      wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys)

lemma sum_worPatternMass_eq_prefixCoeff
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      worPatternMass (k := k) (hN := hN) e s p =
        prefixCoeff (k := k) (h := hN) e s := by
  classical
  let P₀ : Finset (ExcursionList k) :=
    (prefixFiber (k := k) (h := hN) e s).image
      (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))
  let P : Finset (ExcursionList k) := excursionPatternSet (k := k) (hN := hN) e s
  have hcard : (fiber k N s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hs
  have hcard_pf0 :
      (prefixFiber (k := k) (h := hN) e s).card =
        ∑ p ∈ P₀,
          (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    simpa [P₀, prefixPatternFiber] using
      (Finset.card_eq_sum_card_image
        (f := fun xs : Traj k N =>
          excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))
        (s := prefixFiber (k := k) (h := hN) e s))
  have hsubset : P₀ ⊆ P := by
    intro p hp
    exact Finset.mem_union.2 (Or.inl hp)
  have hzero_out :
      ∀ p ∈ P, p ∉ P₀ →
        (prefixPatternFiber (k := k) (hN := hN) e s p).card = 0 := by
    intro p hpP hpNot
    have hempty :
        prefixPatternFiber (k := k) (hN := hN) e s p = ∅ := by
      ext xs
      constructor
      · intro hxs
        have hx : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
          (Finset.mem_filter.1 hxs).2
        have hxP0 : p ∈ P₀ := by
          refine Finset.mem_image.2 ?_
          exact ⟨xs, (Finset.mem_filter.1 hxs).1, hx⟩
        exact False.elim (hpNot hxP0)
      · intro hxs
        simp at hxs
    simp [hempty]
  have hcard_pf :
      (prefixFiber (k := k) (h := hN) e s).card =
        ∑ p ∈ P, (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    calc
      (prefixFiber (k := k) (h := hN) e s).card
          = ∑ p ∈ P₀, (prefixPatternFiber (k := k) (hN := hN) e s p).card := hcard_pf0
      _ = ∑ p ∈ P, (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
          have hsum :
              ∑ p ∈ P₀, (prefixPatternFiber (k := k) (hN := hN) e s p).card =
                ∑ p ∈ P, (prefixPatternFiber (k := k) (hN := hN) e s p).card :=
            Finset.sum_subset hsubset hzero_out
          simpa using hsum
  calc
    ∑ p ∈ P,
      worPatternMass (k := k) (hN := hN) e s p
        = (((∑ p ∈ P,
              (prefixPatternFiber (k := k) (hN := hN) e s p).card) : ℕ) : ENNReal) /
            ((fiber k N s).card : ENNReal) := by
              simp [worPatternMass, div_eq_mul_inv, Finset.sum_mul]
    _ = (((prefixFiber (k := k) (h := hN) e s).card : ℕ) : ENNReal) /
          ((fiber k N s).card : ENNReal) := by
          rw [hcard_pf]
    _ = prefixCoeff (k := k) (h := hN) e s := by
          simp [prefixCoeff, hcard]

lemma worPatternMass_eq_prefixRatio_mul_prefixCoeff
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    worPatternMass (k := k) (hN := hN) e s p =
      prefixPatternRatio (k := k) (hN := hN) e s p *
      prefixCoeff (k := k) (h := hN) e s := by
  have hden_nat : (fiber k N s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hs
  have hden : ((fiber k N s).card : ENNReal) ≠ 0 := by
    exact_mod_cast hden_nat
  by_cases hpf0 : (prefixFiber (k := k) (h := hN) e s).card = 0
  · have hnum0 : ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) = 0 := by
      have hsubset :
          prefixPatternFiber (k := k) (hN := hN) e s p ⊆
            prefixFiber (k := k) (h := hN) e s := by
        intro xs hxs
        exact (Finset.mem_filter.1 hxs).1
      have hcard_le :
          (prefixPatternFiber (k := k) (hN := hN) e s p).card ≤
            (prefixFiber (k := k) (h := hN) e s).card := Finset.card_le_card hsubset
      have hcard0 : (prefixPatternFiber (k := k) (hN := hN) e s p).card = 0 := by
        omega
      exact_mod_cast hcard0
    have hpc0 : prefixCoeff (k := k) (h := hN) e s = 0 := by
      simp [prefixCoeff, hpf0]
    unfold worPatternMass
    simp [hnum0, hpc0]
  · have hpf_ne_zero : ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) ≠ 0 := by
      exact_mod_cast hpf0
    have hpf_ne_top : ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) ≠ ⊤ := by
      simp
    have hpc :
        prefixCoeff (k := k) (h := hN) e s =
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) /
            ((fiber k N s).card : ENNReal)) := by
      unfold prefixCoeff
      simp [hden_nat]
    unfold worPatternMass
    have hcancel :
        (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)) *
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) /
            ((fiber k N s).card : ENNReal)) =
        ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
          ((fiber k N s).card : ENNReal) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hmid :
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
              (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
                (((fiber k N s).card : ENNReal)⁻¹))) =
            (((fiber k N s).card : ENNReal)⁻¹) := by
        calc
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
              (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
                (((fiber k N s).card : ENNReal)⁻¹))) =
              ((((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
                  ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)) *
                (((fiber k N s).card : ENNReal)⁻¹)) := by
                  ac_rfl
          _ = (1 : ENNReal) * (((fiber k N s).card : ENNReal)⁻¹) := by
                rw [ENNReal.inv_mul_cancel hpf_ne_zero hpf_ne_top]
          _ = (((fiber k N s).card : ENNReal)⁻¹) := by simp
      calc
        (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹) *
            (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
              (((fiber k N s).card : ENNReal)⁻¹)) =
          ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
            (((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
              (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
                (((fiber k N s).card : ENNReal)⁻¹))) := by
                  ac_rfl
        _ =
          ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
            (((fiber k N s).card : ENNReal)⁻¹) := by rw [hmid]
        _ = ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
              ((fiber k N s).card : ENNReal) := by simp [div_eq_mul_inv]
    calc
      worPatternMass (k := k) (hN := hN) e s p
          = ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
              ((fiber k N s).card : ENNReal) := by rfl
      _ = (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)) *
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) /
            ((fiber k N s).card : ENNReal)) := by
            exact hcancel.symm
      _ = prefixPatternRatio (k := k) (hN := hN) e s p *
          prefixCoeff (k := k) (h := hN) e s := by
            simp [prefixPatternRatio, hpc]

lemma wrPatternMass_toReal_eq_shortRatio_toReal_mul_W_toReal
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) :
    (wrPatternMass (k := k) hk n e s p).toReal =
      (shortPatternRatio (k := k) n e p).toReal *
        (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal := by
  have hEq :
      wrPatternMass (k := k) hk n e s p =
        shortPatternRatio (k := k) n e p *
          W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) :=
    wrPatternMass_eq_shortRatio_mul_W_uncond
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p)
  calc
    (wrPatternMass (k := k) hk n e s p).toReal
        = (shortPatternRatio (k := k) n e p *
            W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal := by
            simp [hEq]
    _ = (shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal := by
          simp [ENNReal.toReal_mul]

lemma worPatternMass_toReal_eq_prefixRatio_toReal_mul_prefixCoeff_toReal
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    (worPatternMass (k := k) (hN := hN) e s p).toReal =
      (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
        (prefixCoeff (k := k) (h := hN) e s).toReal := by
  have hEq :
      worPatternMass (k := k) (hN := hN) e s p =
        prefixPatternRatio (k := k) (hN := hN) e s p *
          prefixCoeff (k := k) (h := hN) e s :=
    worPatternMass_eq_prefixRatio_mul_prefixCoeff
      (k := k) (hN := hN) (e := e) (s := s) hs p
  calc
    (worPatternMass (k := k) (hN := hN) e s p).toReal
        = (prefixPatternRatio (k := k) (hN := hN) e s p *
            prefixCoeff (k := k) (h := hN) e s).toReal := by
            simp [hEq]
    _ = (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal := by
          simp [ENNReal.toReal_mul]

/-- Canonical WR-side surrogate mass over patterns: keep the short-fiber shape,
replace the global WR scalar by an external surrogate scalar. -/
def canonicalWRSurrogateMass
    (n : ℕ) (e : MarkovState k) (wSurrogate : ℝ) (p : ExcursionList k) : ℝ :=
  (shortPatternRatio (k := k) n e p).toReal * wSurrogate

lemma abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k)
    (wSurrogate : ℝ) (p : ExcursionList k) :
    |(wrPatternMass (k := k) hk n e s p).toReal -
      canonicalWRSurrogateMass (k := k) n e wSurrogate p| =
      (shortPatternRatio (k := k) n e p).toReal *
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          wSurrogate| := by
  let a : ℝ := (shortPatternRatio (k := k) n e p).toReal
  let Wv : ℝ :=
    (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact ENNReal.toReal_nonneg
  calc
    |(wrPatternMass (k := k) hk n e s p).toReal -
      canonicalWRSurrogateMass (k := k) n e wSurrogate p|
        = |a * Wv - a * wSurrogate| := by
            simp [a, Wv, canonicalWRSurrogateMass,
              wrPatternMass_toReal_eq_shortRatio_toReal_mul_W_toReal
                (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p)]
    _ = |a * (Wv - wSurrogate)| := by ring_nf
    _ = |a| * |Wv - wSurrogate| := by rw [abs_mul]
    _ = a * |Wv - wSurrogate| := by simp [abs_of_nonneg ha_nonneg]
    _ = (shortPatternRatio (k := k) n e p).toReal *
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
            wSurrogate| := by simp [a, Wv]

lemma sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
    (hk : 0 < k) (n : ℕ) {N : ℕ} (hN : Nat.succ n ≤ N)
    (e s : MarkovState k)
    (wSurrogate εW : ℝ)
    (hWsurrogate :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        wSurrogate| ≤ εW) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        canonicalWRSurrogateMass (k := k) n e wSurrogate p| ≤ εW := by
  let P := excursionPatternSet (k := k) (hN := hN) e s
  let Δ : ℝ :=
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
      wSurrogate|
  have hrewrite :
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          canonicalWRSurrogateMass (k := k) n e wSurrogate p|) =
      (∑ p ∈ P, (shortPatternRatio (k := k) n e p).toReal) * Δ := by
    calc
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          canonicalWRSurrogateMass (k := k) n e wSurrogate p|)
          = ∑ p ∈ P,
              ((shortPatternRatio (k := k) n e p).toReal * Δ) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                simp [Δ, abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass
                  (k := k) (hk := hk) (n := n) (e := e) (s := s)
                  (wSurrogate := wSurrogate) (p := p)]
      _ = (∑ p ∈ P, (shortPatternRatio (k := k) n e p).toReal) * Δ := by
            rw [Finset.sum_mul]
  have hratio_le_one :
      (∑ p ∈ P, (shortPatternRatio (k := k) n e p).toReal) ≤ 1 := by
    simpa [P] using
      (sum_shortPatternRatio_toReal_le_one (k := k) (hN := hN) (e := e) (s := s))
  have hΔ_nonneg : 0 ≤ Δ := by
    dsimp [Δ]
    exact abs_nonneg _
  have hmul_le :
      (∑ p ∈ P, (shortPatternRatio (k := k) n e p).toReal) * Δ ≤ 1 * Δ :=
    mul_le_mul_of_nonneg_right hratio_le_one hΔ_nonneg
  have hΔ_le : Δ ≤ εW := by
    simpa [Δ] using hWsurrogate
  calc
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        canonicalWRSurrogateMass (k := k) n e wSurrogate p|)
        = (∑ p ∈ P, (shortPatternRatio (k := k) n e p).toReal) * Δ := by
            simpa [P] using hrewrite
    _ ≤ 1 * Δ := hmul_le
    _ = Δ := by ring
    _ ≤ εW := hΔ_le


/-- WR-side canonical surrogate mass bound from an excursion-level representation
error (`δrepr`) plus a per-excursion product approximation error (`ε`). -/
theorem wr_smoothing_bound_via_excursion_target
    (hk : 0 < k) (n : ℕ) {N : ℕ} (hN : Nat.succ n ≤ N)
    (e s : MarkovState k)
    (elist pref : ExcursionList k)
    (target : ExcursionType k → ℝ)
    (δrepr ε : ℝ)
    (hWrepr :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        excursionWithReplacementProb (k := k) elist pref| ≤ δrepr)
    (hstep :
      ∀ a ∈ pref, |empiricalExcursionProb (k := k) elist a - target a| ≤ ε)
    (htarget_range :
      ∀ a ∈ pref, 0 ≤ target a ∧ target a ≤ 1) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        canonicalWRSurrogateMass (k := k) n e
          (excursionsProb (k := k) target pref) p| ≤
      δrepr + (pref.length : ℝ) * ε := by
  have hwr_target :
      |excursionWithReplacementProb (k := k) elist pref -
          excursionsProb (k := k) target pref| ≤
        (pref.length : ℝ) * ε :=
    abs_excursionWithReplacementProb_sub_excursionsProb_target_le_length_mul_eps
      (k := k) (elist := elist) (pref := pref) (target := target) (ε := ε)
      hstep htarget_range
  have hWsurrogate :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          excursionsProb (k := k) target pref| ≤
        δrepr + (pref.length : ℝ) * ε := by
    have htri :=
      abs_sub_le
        ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
        (excursionWithReplacementProb (k := k) elist pref)
        (excursionsProb (k := k) target pref)
    linarith
  exact
    sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
      (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
      (wSurrogate := excursionsProb (k := k) target pref)
      (εW := δrepr + (pref.length : ℝ) * ε)
      hWsurrogate

/-- Scalar WR-side smoothing rate relative to an excursion target law, in explicit
`O(1 / returnsToStart)` form. -/
theorem wr_scalar_smoothing_rate_via_excursion_target
    (hk : 0 < k) (n : ℕ)
    (e s : MarkovState k)
    (elist pref : ExcursionList k)
    (target : ExcursionType k → ℝ)
    (Crepr Cstep : ℝ)
    (hWreprRate :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        excursionWithReplacementProb (k := k) elist pref| ≤
          Crepr / (returnsToStart (k := k) s : ℝ))
    (hstepRate :
      ∀ a ∈ pref, |empiricalExcursionProb (k := k) elist a - target a| ≤
        Cstep / (returnsToStart (k := k) s : ℝ))
    (htarget_range :
      ∀ a ∈ pref, 0 ≤ target a ∧ target a ≤ 1) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
      excursionsProb (k := k) target pref| ≤
      (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) := by
  have hwr_target :
      |excursionWithReplacementProb (k := k) elist pref -
          excursionsProb (k := k) target pref| ≤
        (pref.length : ℝ) * (Cstep / (returnsToStart (k := k) s : ℝ)) :=
    abs_excursionWithReplacementProb_sub_excursionsProb_target_le_length_mul_eps
      (k := k) (elist := elist) (pref := pref) (target := target)
      (ε := Cstep / (returnsToStart (k := k) s : ℝ))
      hstepRate htarget_range
  have hsum :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          excursionsProb (k := k) target pref| ≤
        Crepr / (returnsToStart (k := k) s : ℝ) +
          (pref.length : ℝ) * (Cstep / (returnsToStart (k := k) s : ℝ)) := by
    have htri :=
      abs_sub_le
        ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
        (excursionWithReplacementProb (k := k) elist pref)
        (excursionsProb (k := k) target pref)
    linarith
  have hsplit :
      Crepr / (returnsToStart (k := k) s : ℝ) +
          (pref.length : ℝ) * (Cstep / (returnsToStart (k := k) s : ℝ)) =
        (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) := by
    calc
      Crepr / (returnsToStart (k := k) s : ℝ) +
          (pref.length : ℝ) * (Cstep / (returnsToStart (k := k) s : ℝ))
          =
        Crepr / (returnsToStart (k := k) s : ℝ) +
          ((pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) := by ring
      _ =
        (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) := by
          rw [← add_div]
  simpa [hsplit] using hsum

/-- Pattern-mass WR smoothing rate relative to the canonical surrogate built from
an excursion target law, in explicit `O(1 / returnsToStart)` form. -/
theorem wr_pattern_smoothing_rate_via_excursion_target
    (hk : 0 < k) (n : ℕ) {N : ℕ} (hN : Nat.succ n ≤ N)
    (e s : MarkovState k)
    (elist pref : ExcursionList k)
    (target : ExcursionType k → ℝ)
    (Crepr Cstep : ℝ)
    (hWreprRate :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        excursionWithReplacementProb (k := k) elist pref| ≤
          Crepr / (returnsToStart (k := k) s : ℝ))
    (hstepRate :
      ∀ a ∈ pref, |empiricalExcursionProb (k := k) elist a - target a| ≤
        Cstep / (returnsToStart (k := k) s : ℝ))
    (htarget_range :
      ∀ a ∈ pref, 0 ≤ target a ∧ target a ≤ 1) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        canonicalWRSurrogateMass (k := k) n e
          (excursionsProb (k := k) target pref) p| ≤
      (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) := by
  have hWsurrogate :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        excursionsProb (k := k) target pref| ≤
      (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) :=
    wr_scalar_smoothing_rate_via_excursion_target
      (k := k) (hk := hk) (n := n) (e := e) (s := s)
      (elist := elist) (pref := pref) (target := target)
      (Crepr := Crepr) (Cstep := Cstep)
      hWreprRate hstepRate htarget_range
  exact
    sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
      (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
      (wSurrogate := excursionsProb (k := k) target pref)
      (εW := (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ))
      hWsurrogate
lemma abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    |(wrPatternMass (k := k) hk n e s p).toReal -
      (worPatternMass (k := k) (hN := hN) e s p).toReal| =
      |(shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal| := by
  rw [wrPatternMass_toReal_eq_shortRatio_toReal_mul_W_toReal
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p)]
  rw [worPatternMass_toReal_eq_prefixRatio_toReal_mul_prefixCoeff_toReal
      (k := k) (hN := hN) (e := e) (s := s) (hs := hs) (p := p)]

lemma sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_ratio_form
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal|) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
    (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs) (p := p)

/-- Fiberwise conversion on a fixed excursion-multiset block:
`ratioTerm` equals the absolute WR/WOR mass discrepancy term. -/
lemma sum_ratioTerm_on_excursionMultisetFiber_eq_sum_abs_wr_wor_on_excursionMultisetFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (mset : Multiset (ExcursionType k)) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
      ratioTerm (k := k) (hN := hN) (hk := hk) e s p) =
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  symm
  exact abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
    (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs) (p := p)

/-- Blockwise conversion under the multiset partition:
replace `ratioTerm` with the equivalent absolute WR/WOR discrepancy. -/
lemma sum_ratioTerm_partition_by_excursionMultiset_eq_sum_abs_wr_wor_partition_by_excursionMultiset
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        ratioTerm (k := k) (hN := hN) (hk := hk) e s p) =
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
  refine Finset.sum_congr rfl ?_
  intro mset hmset
  exact
    sum_ratioTerm_on_excursionMultisetFiber_eq_sum_abs_wr_wor_on_excursionMultisetFiber
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (hs := hs) (mset := mset)

/-- Adjacent-swap invariance of the WR/WOR absolute pattern discrepancy.

This is the concrete mass-level counterpart of `ratioTerm_eq_of_segmentSwap_maps`,
rewritten through the already-proved ratio-form identity. -/
lemma abs_wr_wor_patternMass_toReal_eq_of_segmentSwap_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n) (hcLong : a + L1 + L2 ≤ N)
    (hmapShort :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q)
    (hmapShortInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p)
    (hmapPrefix :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcLong ∈
          prefixPatternFiber (k := k) (hN := hN) e s q)
    (hmapPrefixInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcLong) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p) :
    |(wrPatternMass (k := k) hk n e s p).toReal -
      (worPatternMass (k := k) (hN := hN) e s p).toReal| =
    |(wrPatternMass (k := k) hk n e s q).toReal -
      (worPatternMass (k := k) (hN := hN) e s q).toReal| := by
  calc
    |(wrPatternMass (k := k) hk n e s p).toReal -
      (worPatternMass (k := k) (hN := hN) e s p).toReal|
        =
      |(shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal| := by
          exact abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
            (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs) (p := p)
    _ =
      |(shortPatternRatio (k := k) n e q).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s q).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal| := by
          exact abs_ratio_term_eq_of_segmentSwap_maps
            (k := k) (hN := hN) (e := e) (s := s)
            (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2)
            hL1 hL2 hcShort hcLong
            hmapShort hmapShortInv hmapPrefix hmapPrefixInv
            (Wv := (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
            (Pv := (prefixCoeff (k := k) (h := hN) e s).toReal)
    _ =
      |(wrPatternMass (k := k) hk n e s q).toReal -
        (worPatternMass (k := k) (hN := hN) e s q).toReal| := by
          symm
          exact abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
            (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs) (p := q)

/-- Decomposition-witness wrapper for pointwise adjacent-swap invariance of the
absolute WR/WOR pattern discrepancy. -/
lemma abs_wr_wor_patternMass_toReal_eq_of_adjacent_swap_of_decomps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompShort :
      ShortSwapMiddleDecomp n e p q a L1 L2 hL1 hL2 hcShort)
    (hdecompShortInv :
      ShortSwapMiddleDecomp
        n e q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort))
    (hdecompPrefix :
      PrefixSwapMiddleDecomp
        (hN := hN) e s p q a L1 L2 hL1 hL2 hcShort)
    (hdecompPrefixInv :
      PrefixSwapMiddleDecomp
        (hN := hN) e s q p a L2 L1 hL2 hL1
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    |(wrPatternMass (k := k) hk n e s p).toReal -
      (worPatternMass (k := k) (hN := hN) e s p).toReal| =
    |(wrPatternMass (k := k) hk n e s q).toReal -
      (worPatternMass (k := k) (hN := hN) e s q).toReal| := by
  have hratio :
      ratioTerm (k := k) (hN := hN) (hk := hk) e s p =
        ratioTerm (k := k) (hN := hN) (hk := hk) e s q :=
    ratioTerm_eq_of_adjacent_swap_of_decomps
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
      (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2)
      hL1 hL2 hcShort
      hdecompShort hdecompShortInv
      hdecompPrefix hdecompPrefixInv
  calc
    |(wrPatternMass (k := k) hk n e s p).toReal -
      (worPatternMass (k := k) (hN := hN) e s p).toReal|
        = ratioTerm (k := k) (hN := hN) (hk := hk) e s p := by
            simpa [ratioTerm] using
              (abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
                (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs) (p := p))
    _ = ratioTerm (k := k) (hN := hN) (hk := hk) e s q := hratio
    _ = |(wrPatternMass (k := k) hk n e s q).toReal -
          (worPatternMass (k := k) (hN := hN) e s q).toReal| := by
            simpa [ratioTerm] using
              (abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
                (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs) (p := q)).symm

/-- Reindexing invariance of the finite absolute WR/WOR discrepancy sum under an
adjacent pattern transposition. -/
lemma sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_wr_wor_patternMass_toReal_comp_swap_of_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hmapShort :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q)
    (hmapShortInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p) :
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s r).toReal -
        (worPatternMass (k := k) (hN := hN) e s r).toReal|) =
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s ((Equiv.swap p q) r)).toReal -
        (worPatternMass (k := k) (hN := hN) e s ((Equiv.swap p q) r)).toReal|) := by
  have hsum_ratio :
      (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ratioTerm (k := k) (hN := hN) (hk := hk) e s r) =
      (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ratioTerm (k := k) (hN := hN) (hk := hk) e s ((Equiv.swap p q) r)) := by
    exact sum_ratioTerm_eq_sum_ratioTerm_comp_swap_of_shortPattern_maps
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hmapShort hmapShortInv
  calc
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s r).toReal -
        (worPatternMass (k := k) (hN := hN) e s r).toReal|)
          =
      (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ratioTerm (k := k) (hN := hN) (hk := hk) e s r) := by
          simpa [ratioTerm] using
            (sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_ratio_form
              (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs)
    _ =
      (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ratioTerm (k := k) (hN := hN) (hk := hk) e s ((Equiv.swap p q) r)) := hsum_ratio
    _ =
      (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s ((Equiv.swap p q) r)).toReal -
          (worPatternMass (k := k) (hN := hN) e s ((Equiv.swap p q) r)).toReal|) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          symm
          exact abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
            (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs)
            (p := (Equiv.swap p q) r)

/-- Decomposition-witness wrapper for
`sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_wr_wor_patternMass_toReal_comp_swap_of_maps`.

This provides the swap-reindexed finite-sum equality directly from explicit
adjacent-swap decomposition witnesses on the short-pattern fibers. -/
lemma sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_wr_wor_patternMass_toReal_comp_swap_of_excursionPairs_decomp
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hcShort : a + L1 + L2 ≤ Nat.succ n)
    (hdecompShort : ShortSwapMiddleDecomp
      (k := k) n e p q a L1 L2 hL1 hL2 hcShort)
    (hdecompShortInv : ShortSwapMiddleDecomp
      (k := k) n e q p a L2 L1 hL2 hL1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort)) :
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s r).toReal -
        (worPatternMass (k := k) (hN := hN) e s r).toReal|) =
    (∑ r ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s ((Equiv.swap p q) r)).toReal -
        (worPatternMass (k := k) (hN := hN) e s ((Equiv.swap p q) r)).toReal|) := by
  have hmapShort :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        segmentSwap ys a L1 L2 hL1 hL2 hcShort ∈ shortPatternFiber (k := k) n e q :=
    hmapShort_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapShortFiber_of_shortSwapMiddleDecomp
        (k := k) (n := n) (e := e) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShort)
      hdecompShort
  have hmapShortInv :
      ∀ zs ∈ shortPatternFiber (k := k) n e q,
        segmentSwap zs a L2 L1 hL2 hL1
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcShort) ∈
          shortPatternFiber (k := k) n e p := by
    have hdecompShortInv' :=
      shortSwapMiddleDecomp_inv_unpack
        (k := k) (n := n) (e := e) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShortInv
    exact hmapShortInv_of_swap_middle_of_excursionPairs_decomp
      (k := k) (n := n) (e := e) (p := p) (q := q)
      (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
      (hmapShortFiberInv_of_shortSwapMiddleDecomp
        (k := k) (n := n) (e := e) (p := p) (q := q)
        (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort hdecompShortInv)
      hdecompShortInv'
  exact sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_wr_wor_patternMass_toReal_comp_swap_of_maps
    (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (hs := hs)
    (p := p) (q := q) (a := a) (L1 := L1) (L2 := L2) hL1 hL2 hcShort
    hmapShort hmapShortInv

lemma wrResidualMass_eq_zero
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    wrResidualMass (k := k) hk n hN e s = 0 := by
  classical
  let P : Finset (ExcursionList k) := excursionPatternSet (k := k) (hN := hN) e s
  have hmem :
      ∀ ys ∈ fiber k (Nat.succ n) e,
        excursionListOfTraj (k := k) ys ∈ P := by
    intro ys hys
    exact Finset.mem_union.2 (Or.inr <|
      Finset.mem_image.2 ⟨ys, hys, rfl⟩
    )
  unfold wrResidualMass
  refine Finset.sum_eq_zero ?_
  intro ys hys
  have hyP : excursionListOfTraj (k := k) ys ∈ excursionPatternSet (k := k) (hN := hN) e s :=
    hmem ys hys
  simp [hyP]

lemma sum_wrPatternMass_add_residual_eq_W
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        wrPatternMass (k := k) hk n e s p) +
      wrResidualMass (k := k) hk n hN e s =
      W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  classical
  let θ := empiricalParam (k := k) hk s
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hmain :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p
        =
      ∑ ys ∈ fiber k (Nat.succ n) e,
        if excursionListOfTraj (k := k) ys ∈ P then
          wordProb (k := k) θ (trajToList (k := k) ys)
        else 0 := by
    calc
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p
          =
        ∑ p ∈ P, ∑ ys ∈ fiber k (Nat.succ n) e,
          if excursionListOfTraj (k := k) ys = p then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0 := by
            simp [wrPatternMass, P, θ]
      _ =
        ∑ ys ∈ fiber k (Nat.succ n) e, ∑ p ∈ P,
          if excursionListOfTraj (k := k) ys = p then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0 := by
            rw [Finset.sum_comm]
      _ =
        ∑ ys ∈ fiber k (Nat.succ n) e,
          if excursionListOfTraj (k := k) ys ∈ P then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ys hys
            by_cases hp : excursionListOfTraj (k := k) ys ∈ P
            · have hone :
                ∑ p ∈ P,
                    (if excursionListOfTraj (k := k) ys = p then
                      wordProb (k := k) θ (trajToList (k := k) ys) else 0) =
                  wordProb (k := k) θ (trajToList (k := k) ys) := by
                rw [Finset.sum_eq_single (excursionListOfTraj (k := k) ys)]
                · simp
                · intro p hpP hpneq
                  simp [eq_comm, hpneq]
                · intro hnotin
                  exact (hnotin hp).elim
              simp [hp, hone]
            · have hzero :
                ∑ p ∈ P,
                    (if excursionListOfTraj (k := k) ys = p then
                      wordProb (k := k) θ (trajToList (k := k) ys) else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro p hpP
                have hneq : excursionListOfTraj (k := k) ys ≠ p := by
                  intro heq
                  exact hp (heq ▸ hpP)
                simp [hneq]
              simp [hp, hzero]
  calc
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        wrPatternMass (k := k) hk n e s p) +
      wrResidualMass (k := k) hk n hN e s
        =
      (∑ ys ∈ fiber k (Nat.succ n) e,
        if excursionListOfTraj (k := k) ys ∈ P then
          wordProb (k := k) θ (trajToList (k := k) ys) else 0) +
      ∑ ys ∈ fiber k (Nat.succ n) e,
        if excursionListOfTraj (k := k) ys ∈ P then 0 else
          wordProb (k := k) θ (trajToList (k := k) ys) := by
          simpa [wrResidualMass, P, θ] using congrArg (fun z => z + wrResidualMass (k := k) hk n hN e s) hmain
    _ =
      ∑ ys ∈ fiber k (Nat.succ n) e,
        ((if excursionListOfTraj (k := k) ys ∈ P then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0) +
          (if excursionListOfTraj (k := k) ys ∈ P then 0 else
            wordProb (k := k) θ (trajToList (k := k) ys))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ ys ∈ fiber k (Nat.succ n) e, wordProb (k := k) θ (trajToList (k := k) ys) := by
          refine Finset.sum_congr rfl ?_
          intro ys hys
          by_cases hp : excursionListOfTraj (k := k) ys ∈ P <;> simp [hp]
    _ = W (k := k) (Nat.succ n) e θ := by
          simp [W, fiber, Nat.succ_eq_add_one]

lemma sum_wrPatternMass_eq_W
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      wrPatternMass (k := k) hk n e s p =
        W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  have h := sum_wrPatternMass_add_residual_eq_W (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
  have hres0 := wrResidualMass_eq_zero (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
  simpa [hres0] using h

lemma sum_wrPatternMass_over_shortImage_eq_W
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    ∑ p ∈ ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)),
      wrPatternMass (k := k) hk n e s p =
        W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  simpa [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)]
    using sum_wrPatternMass_eq_W (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)

lemma sum_worPatternMass_over_shortImage_eq_prefixCoeff
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    ∑ p ∈ ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)),
      worPatternMass (k := k) (hN := hN) e s p =
        prefixCoeff (k := k) (h := hN) e s := by
  simpa [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)]
    using sum_worPatternMass_eq_prefixCoeff (k := k) (hN := hN) (e := e) (s := s) hs

lemma worPatternMass_toReal_nonneg
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    0 ≤ (worPatternMass (k := k) (hN := hN) e s p).toReal := by
  exact ENNReal.toReal_nonneg

lemma wrPatternMass_toReal_nonneg
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) :
    0 ≤ (wrPatternMass (k := k) hk n e s p).toReal := by
  exact ENNReal.toReal_nonneg

lemma abs_sum_wrPatternMass_toReal_sub_sum_worPatternMass_toReal_le
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ((wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal))| ≤
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
  simpa using
    (Finset.abs_sum_le_sum_abs
      (f := fun p =>
        (wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal)
      (s := excursionPatternSet (k := k) (hN := hN) e s))

lemma wrPatternMass_ne_top
    {n : ℕ} (hk : 0 < k) (e s : MarkovState k) (p : ExcursionList k) :
    wrPatternMass (k := k) hk n e s p ≠ ⊤ := by
  classical
  unfold wrPatternMass
  refine (ENNReal.sum_ne_top).2 ?_
  intro ys hys
  by_cases hp : excursionListOfTraj (k := k) ys = p
  · simp [hp, wordProb]
  · simp [hp]

lemma worPatternMass_ne_top
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    worPatternMass (k := k) (hN := hN) e s p ≠ ⊤ := by
  have hden_nat : (fiber k N s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hs
  have hden : ((fiber k N s).card : ENNReal) ≠ 0 := by
    exact_mod_cast hden_nat
  unfold worPatternMass
  apply ENNReal.div_ne_top
  · simp
  · exact hden

lemma toReal_sum_wrPatternMass
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      wrPatternMass (k := k) hk n e s p).toReal =
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (wrPatternMass (k := k) hk n e s p).toReal := by
  exact ENNReal.toReal_sum (fun p hp => wrPatternMass_ne_top (k := k) (hk := hk) (n := n) (e := e) (s := s) p)

lemma toReal_sum_worPatternMass
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      worPatternMass (k := k) (hN := hN) e s p).toReal =
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (worPatternMass (k := k) (hN := hN) e s p).toReal := by
  exact ENNReal.toReal_sum
    (fun p hp => worPatternMass_ne_top (k := k) (hN := hN) (e := e) (s := s) hs p)

lemma abs_toReal_sum_wr_sub_toReal_sum_wor_le_sum_abs
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        wrPatternMass (k := k) hk n e s p).toReal -
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
  rw [toReal_sum_wrPatternMass (k := k) (hk := hk) (hN := hN) (e := e) (s := s)]
  rw [toReal_sum_worPatternMass (k := k) (hN := hN) (e := e) (s := s) hs]
  calc
    |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (wrPatternMass (k := k) hk n e s p).toReal) -
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (worPatternMass (k := k) (hN := hN) e s p).toReal)| =
      |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ((wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal))| := by
      simp [Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| :=
      abs_sum_wrPatternMass_toReal_sub_sum_worPatternMass_toReal_le
        (k := k) (hk := hk) (hN := hN) (e := e) (s := s)

/-! ## BEST-side transport for WOR pattern masses

These lemmas move WOR masses from trajectory fibers to Euler-trail filters
using the already-proved copy-permutation cardinality formulas.
-/

lemma prefixPatternFiber_subset_fiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    prefixPatternFiber (k := k) (hN := hN) e s p ⊆ fiber k N s := by
  intro xs hxs
  exact prefixFiber_subset_fiber (k := k) (h := hN) (e := e) (eN := s)
    ((Finset.mem_filter.1 hxs).1)

lemma eulerTrailFinset_card_filter_prefixPatternFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (hs : s ∈ stateFinset k N) :
    ((eulerTrailFinset (graphOfState s) s.start s.last).filter
      (fun f =>
        castTraj
            (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
            (trailVertexSeq (graphOfState s) s.start f) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p)).card =
      (prefixPatternFiber (k := k) (hN := hN) e s p).card *
        ∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial := by
  have hTok : totalEdgeTokens (k := k) (graphOfState s) = N :=
    totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs
  subst hTok
  have hA :
      prefixPatternFiber (k := k) (hN := hN) e s p ⊆
        fiber k (totalEdgeTokens (k := k) (graphOfState s)) s :=
    prefixPatternFiber_subset_fiber (k := k) (hN := hN) (e := e) (s := s) (p := p)
  simpa using
    eulerTrailFinset_card_filter_trajSubset (k := k) (s := s)
      (A := prefixPatternFiber (k := k) (hN := hN) e s p) hA

lemma worPatternMass_eq_eulerTrail_ratio
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (hs : s ∈ stateFinset k N) :
    worPatternMass (k := k) (hN := hN) e s p =
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            castTraj
                (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                (trailVertexSeq (graphOfState s) s.start f) ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) /
        ((eulerTrailFinset (graphOfState s) s.start s.last).card : ENNReal) := by
  have hTok : totalEdgeTokens (k := k) (graphOfState s) = N :=
    totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs
  subst hTok
  have hcopy_ne_zero_nat :
      (∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact Nat.factorial_ne_zero (graphOfState s a b)
  have hcopy_ne_zero_enn :
      ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal) ≠ 0 := by
    exact_mod_cast hcopy_ne_zero_nat
  have hnum_mul :
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            trailVertexSeq (graphOfState s) s.start f ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) =
        ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
          ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal) := by
    have h :=
      eulerTrailFinset_card_filter_prefixPatternFiber (k := k) (hN := hN) (e := e) (s := s) (p := p) hs
    exact_mod_cast h
  have hcast_filter :
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            castTraj
                (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                (trailVertexSeq (graphOfState s) s.start f) ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) =
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            trailVertexSeq (graphOfState s) s.start f ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) := by
    simp [castTraj]
  have hden_mul :
      (((eulerTrailFinset (graphOfState s) s.start s.last).card : ℕ) : ENNReal) =
        ((fiber k (totalEdgeTokens (k := k) (graphOfState s)) s).card : ENNReal) *
          ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal) := by
    have h := eulerTrailFinset_card_eq (k := k) (s := s) hs
    exact_mod_cast h
  unfold worPatternMass
  rw [hcast_filter]
  rw [hnum_mul, hden_mul]
  set F : ENNReal := ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal)
  have hcopy_ne_top : F ≠ ⊤ := by
    dsimp [F]
    refine ENNReal.prod_ne_top ?_
    intro a ha
    refine ENNReal.prod_ne_top ?_
    intro b hb
    exact ENNReal.natCast_ne_top _
  have hcancel :
      (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) * F) /
          (((fiber k (totalEdgeTokens (k := k) (graphOfState s)) s).card : ENNReal) * F) =
        ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
          ((fiber k (totalEdgeTokens (k := k) (graphOfState s)) s).card : ENNReal) := by
    rw [mul_comm _ F, mul_comm _ F,
      ENNReal.mul_div_mul_left _ _ (by simpa [F] using hcopy_ne_zero_enn) hcopy_ne_top]
  simpa [F] using hcancel.symm

/-! ## Core reduction: correspondence identities imply the Diaconis-Freedman bound -/

/-- WOR/WR discrepancy bound for the excursion prefix induced by a fiber witness. -/
private lemma excursion_wr_wor_bound_for_witness
    (n : ℕ)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hRlarge : 4 * (Nat.succ n) * (Nat.succ n) < returnsToStart (k := k) s)
    (xs : Traj k N) (hxs : xs ∈ fiber k N s) :
    let elist : ExcursionList k := excursionListOfTraj (k := k) xs
    let m : ℕ := prefixExcursionCount (k := k) hN xs
    |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
        excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  let elist : ExcursionList k := excursionListOfTraj (k := k) xs
  let m : ℕ := prefixExcursionCount (k := k) hN xs
  have hm_le : m ≤ Nat.succ n := by
    unfold m
    simpa using
      (prefixExcursionCount_le_n (k := k) (n := Nat.succ n) (N := N) hN xs)
  have hlen_elist : elist.length = returnsToStart (k := k) s := by
    unfold elist
    exact excursionList_length_eq_returnsToStart (k := k) s xs hxs
  have hsn_sq : Nat.succ n ≤ Nat.succ n * Nat.succ n := by
    exact Nat.le_mul_of_pos_right (Nat.succ n) (Nat.succ_pos n)
  have hsq_le4 : Nat.succ n * Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := by
    calc
      Nat.succ n * Nat.succ n = 1 * (Nat.succ n * Nat.succ n) := by simp
      _ ≤ 4 * (Nat.succ n * Nat.succ n) := by
          exact Nat.mul_le_mul_right (Nat.succ n * Nat.succ n) (by decide : (1 : ℕ) ≤ 4)
  have hsn_le_quad : Nat.succ n ≤ 4 * (Nat.succ n) * (Nat.succ n) := by
    have htmp : Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := le_trans hsn_sq hsq_le4
    simpa [Nat.mul_assoc] using htmp
  have hm_len : m ≤ elist.length := by
    have hsn_le_R : Nat.succ n ≤ returnsToStart (k := k) s := by
      exact le_trans hsn_le_quad (Nat.le_of_lt hRlarge)
    exact le_trans hm_le (by simpa [hlen_elist] using hsn_le_R)
  have hR2 : 2 * m ≤ (excursionMultiset (k := k) elist).card := by
    have hm2 : 2 * m ≤ 2 * Nat.succ n := Nat.mul_le_mul_left 2 hm_le
    have hs2a : 2 * Nat.succ n ≤ 2 * (Nat.succ n * Nat.succ n) := by
      exact Nat.mul_le_mul_left 2 hsn_sq
    have hs2b : 2 * (Nat.succ n * Nat.succ n) ≤ 4 * (Nat.succ n * Nat.succ n) := by
      exact Nat.mul_le_mul_right (Nat.succ n * Nat.succ n) (by decide : (2 : ℕ) ≤ 4)
    have hs2 : 2 * Nat.succ n ≤ 4 * (Nat.succ n) * (Nat.succ n) := by
      have htmp : 2 * Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := le_trans hs2a hs2b
      simpa [Nat.mul_assoc] using htmp
    have h2R : 2 * m ≤ returnsToStart (k := k) s := by
      exact le_trans hm2 (le_trans hs2 (Nat.le_of_lt hRlarge))
    simpa [excursionMultiset, hlen_elist] using h2R
  have hworwr :
      |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
          excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
        (4 * (m : ℝ) * (m : ℝ)) / ((excursionMultiset (k := k) elist).card : ℝ) :=
    abs_excursion_wor_wr_le_take (k := k) elist m hm_len hR2
  have hworwr' :
      |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
          excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
        (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
    simpa [excursionMultiset, hlen_elist] using hworwr
  have hnum_le :
      4 * (m : ℝ) * (m : ℝ) ≤
        4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ) := by
    nlinarith [show (m : ℝ) ≤ ((Nat.succ n : ℕ) : ℝ) from (by exact_mod_cast hm_le)]
  have hRnonneg_real : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
    exact Nat.cast_nonneg _
  have hfrac_le :
      (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    exact div_le_div_of_nonneg_right hnum_le hRnonneg_real
  exact le_trans hworwr' hfrac_le

private lemma worProb_nonneg_local
    {α : Type*} [DecidableEq α]
    (ms : Multiset α) (xs : List α) :
    0 ≤ worProb ms xs := by
  induction xs generalizing ms with
  | nil =>
      simp [worProb]
  | cons a xs ih =>
      simp [worProb, ih, probWeight_nonneg, mul_nonneg]

private lemma worProb_le_one_local
    {α : Type*} [DecidableEq α]
    (ms : Multiset α) (xs : List α) :
    worProb ms xs ≤ 1 := by
  induction xs generalizing ms with
  | nil =>
      simp [worProb]
  | cons a xs ih =>
      have hstep_nonneg : 0 ≤ probWeight (ms.count a) ms.card :=
        probWeight_nonneg _ _
      have hstep_le : probWeight (ms.count a) ms.card ≤ 1 :=
        probWeight_le_one _ _ (Multiset.count_le_card _ _)
      have htail_nonneg : 0 ≤ worProb (ms.erase a) xs :=
        worProb_nonneg_local (ms := ms.erase a) (xs := xs)
      have htail_le : worProb (ms.erase a) xs ≤ 1 := ih (ms := ms.erase a)
      have hmul : probWeight (ms.count a) ms.card * worProb (ms.erase a) xs ≤ 1 := by
        nlinarith
      simpa [worProb] using hmul

private lemma prefixCoeff_wor_witness_abs_le_one
    (n : ℕ) {N : ℕ} (hN : Nat.succ n ≤ N) (e : MarkovState k) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (xs : Traj k N) :
    |(prefixCoeff (k := k) (h := hN) e s).toReal -
        excursionWithoutReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs))| ≤ 1 := by
  let elist : ExcursionList k := excursionListOfTraj (k := k) xs
  let m : ℕ := prefixExcursionCount (k := k) hN xs
  have hpc_nonneg : 0 ≤ (prefixCoeff (k := k) (h := hN) e s).toReal :=
    prefixCoeff_toReal_nonneg (k := k) (h := hN) (e := e) (eN := s)
  have hpc_le_one : (prefixCoeff (k := k) (h := hN) e s).toReal ≤ 1 :=
    prefixCoeff_toReal_le_one (k := k) (h := hN) (e := e) (eN := s) hs
  have hwor_nonneg :
      0 ≤ excursionWithoutReplacementProb (k := k) elist (elist.take m) := by
    simpa [excursionWithoutReplacementProb] using
      (worProb_nonneg_local
        (ms := excursionMultiset (k := k) elist)
        (xs := elist.take m))
  have hwor_le_one :
      excursionWithoutReplacementProb (k := k) elist (elist.take m) ≤ 1 := by
    simpa [excursionWithoutReplacementProb] using
      (worProb_le_one_local
        (ms := excursionMultiset (k := k) elist)
        (xs := elist.take m))
  exact abs_sub_le_one_of_unit_interval hpc_nonneg hpc_le_one hwor_nonneg hwor_le_one

/-- Clean semantic bridge with explicit approximation terms on WR and WOR sides. -/
private lemma excursion_bound_of_wor_wr_correspondence_biapprox
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hRlarge : 4 * (Nat.succ n) * (Nat.succ n) < returnsToStart (k := k) s)
    (xs : Traj k N) (hxs : xs ∈ fiber k N s)
    (εW εPC : ℝ)
    (hW :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        excursionWithReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs))| ≤ εW)
    (hPC :
      |(prefixCoeff (k := k) (h := hN) e s).toReal -
        excursionWithoutReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs))| ≤ εPC) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      εW + εPC +
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
  let elist : ExcursionList k := excursionListOfTraj (k := k) xs
  let m : ℕ := prefixExcursionCount (k := k) hN xs
  let W0 : ℝ := (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
  let PC0 : ℝ := (prefixCoeff (k := k) (h := hN) e s).toReal
  let WR0 : ℝ := excursionWithReplacementProb (k := k) elist (elist.take m)
  let WOR0 : ℝ := excursionWithoutReplacementProb (k := k) elist (elist.take m)
  let B : ℝ :=
    (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
      (returnsToStart (k := k) s : ℝ)
  have hwrwor : |WR0 - WOR0| ≤ B := by
    have hcore :=
      excursion_wr_wor_bound_for_witness
        (k := k) (n := n) (hN := hN) (s := s) hRlarge xs hxs
    simpa [WR0, WOR0, B, elist, m, abs_sub_comm] using hcore
  have hW0 : |W0 - WR0| ≤ εW := by
    simpa [W0, WR0, elist, m] using hW
  have hPC0 : |WOR0 - PC0| ≤ εPC := by
    simpa [WOR0, PC0, elist, m, abs_sub_comm] using hPC
  have htri1 : |W0 - PC0| ≤ |W0 - WR0| + |WR0 - PC0| :=
    abs_sub_le W0 WR0 PC0
  have htri2 : |WR0 - PC0| ≤ |WR0 - WOR0| + |WOR0 - PC0| :=
    abs_sub_le WR0 WOR0 PC0
  have haux : |WR0 - PC0| ≤ B + εPC := by
    linarith [htri2, hwrwor, hPC0]
  have hmain : |W0 - PC0| ≤ εW + εPC + B := by
    have hstep : |W0 - PC0| ≤ εW + |WR0 - PC0| := by
      linarith [htri1, hW0]
    linarith [hstep, haux]
  simpa [W0, PC0, B] using hmain

private lemma excursion_bound_of_wor_wr_correspondence_biapprox_step1
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hRlarge : 4 * (Nat.succ n) * (Nat.succ n) < returnsToStart (k := k) s)
    (xs : Traj k N) (hxs : xs ∈ fiber k N s)
    (εW : ℝ)
    (hW :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        excursionWithReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs))| ≤ εW) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      εW + 1 +
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
  have hs : s ∈ stateFinset k N := by
    have hstate : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
    have hs' : stateOfTraj (k := k) xs ∈ stateFinset k N :=
      stateOfTraj_mem_stateFinset (k := k) xs
    simpa [hstate] using hs'
  have hPC :
      |(prefixCoeff (k := k) (h := hN) e s).toReal -
        excursionWithoutReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs))| ≤ (1 : ℝ) :=
    prefixCoeff_wor_witness_abs_le_one
      (k := k) (n := n) (hN := hN) (e := e) (s := s) hs xs
  have hmain :=
    excursion_bound_of_wor_wr_correspondence_biapprox
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) hRlarge xs hxs
      (εW := εW) (εPC := 1) hW hPC
  simpa [add_assoc, add_left_comm, add_comm] using hmain

/-- If the two excursion correspondence identities are available for one fiber
witness trajectory `xs`, then the desired `O(n^2 / R)` bound follows directly
from `abs_excursion_wor_wr_le_take`. -/
private lemma excursion_bound_of_wor_wr_correspondence
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hRlarge : 4 * (Nat.succ n) * (Nat.succ n) < returnsToStart (k := k) s)
    (xs : Traj k N) (hxs : xs ∈ fiber k N s)
    (hW :
      (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal =
        excursionWithReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs)))
    (hPC :
      (prefixCoeff (k := k) (h := hN) e s).toReal =
        excursionWithoutReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs))) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  let elist : ExcursionList k := excursionListOfTraj (k := k) xs
  let m : ℕ := prefixExcursionCount (k := k) hN xs
  have hm_le : m ≤ Nat.succ n := by
    unfold m
    simpa using
      (prefixExcursionCount_le_n (k := k) (n := Nat.succ n) (N := N) hN xs)
  have hlen_elist : elist.length = returnsToStart (k := k) s := by
    unfold elist
    exact excursionList_length_eq_returnsToStart (k := k) s xs hxs
  have hsn_sq : Nat.succ n ≤ Nat.succ n * Nat.succ n := by
    exact Nat.le_mul_of_pos_right (Nat.succ n) (Nat.succ_pos n)
  have hsq_le4 : Nat.succ n * Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := by
    calc
      Nat.succ n * Nat.succ n = 1 * (Nat.succ n * Nat.succ n) := by simp
      _ ≤ 4 * (Nat.succ n * Nat.succ n) := by
          exact Nat.mul_le_mul_right (Nat.succ n * Nat.succ n) (by decide : (1 : ℕ) ≤ 4)
  have hsn_le_quad : Nat.succ n ≤ 4 * (Nat.succ n) * (Nat.succ n) := by
    have htmp : Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := le_trans hsn_sq hsq_le4
    simpa [Nat.mul_assoc] using htmp
  have hm_len : m ≤ elist.length := by
    have hsn_le_R : Nat.succ n ≤ returnsToStart (k := k) s := by
      exact le_trans hsn_le_quad (Nat.le_of_lt hRlarge)
    exact le_trans hm_le (by simpa [hlen_elist] using hsn_le_R)
  have hR2 : 2 * m ≤ (excursionMultiset (k := k) elist).card := by
    have hm2 : 2 * m ≤ 2 * Nat.succ n := Nat.mul_le_mul_left 2 hm_le
    have hs2a : 2 * Nat.succ n ≤ 2 * (Nat.succ n * Nat.succ n) := by
      exact Nat.mul_le_mul_left 2 hsn_sq
    have hs2b : 2 * (Nat.succ n * Nat.succ n) ≤ 4 * (Nat.succ n * Nat.succ n) := by
      exact Nat.mul_le_mul_right (Nat.succ n * Nat.succ n) (by decide : (2 : ℕ) ≤ 4)
    have hs2 : 2 * Nat.succ n ≤ 4 * (Nat.succ n) * (Nat.succ n) := by
      have htmp : 2 * Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := le_trans hs2a hs2b
      simpa [Nat.mul_assoc] using htmp
    have h2R : 2 * m ≤ returnsToStart (k := k) s := by
      exact le_trans hm2 (le_trans hs2 (Nat.le_of_lt hRlarge))
    simpa [excursionMultiset, hlen_elist] using h2R
  have hworwr :
      |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
          excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
        (4 * (m : ℝ) * (m : ℝ)) / ((excursionMultiset (k := k) elist).card : ℝ) :=
    abs_excursion_wor_wr_le_take (k := k) elist m hm_len hR2
  have hworwr' :
      |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
          excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
        (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
    simpa [excursionMultiset, hlen_elist] using hworwr
  have hm_real : (m : ℝ) ≤ ((Nat.succ n : ℕ) : ℝ) := by
    exact_mod_cast hm_le
  have hnum_le :
      4 * (m : ℝ) * (m : ℝ) ≤
        4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ) := by
    nlinarith
  have hRpos_nat : 0 < returnsToStart (k := k) s := by
    have : 0 < 4 * (Nat.succ n) * (Nat.succ n) := by positivity
    exact lt_trans this hRlarge
  have hRnonneg_real : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
    exact Nat.cast_nonneg _
  have hfrac_le :
      (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    exact div_le_div_of_nonneg_right hnum_le hRnonneg_real
  calc
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal|
        = |excursionWithReplacementProb (k := k) elist (elist.take m) -
            excursionWithoutReplacementProb (k := k) elist (elist.take m)| := by
          simp [hW, hPC, elist, m]
    _ = |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
            excursionWithReplacementProb (k := k) elist (elist.take m)| := by
          rw [abs_sub_comm]
    _ ≤ (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) := hworwr'
    _ ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := hfrac_le

lemma sum_abs_ratio_partition_by_excursionMultiset
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal|) =
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        |(shortPatternRatio (k := k) n e p).toReal *
            (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
            (prefixCoeff (k := k) (h := hN) e s).toReal|) := by
  simpa [ratioTerm] using
    sum_ratioTerm_partition_by_excursionMultiset
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s)

/-! ## Subgoal A: multiset-fiber constancy of |wr - wor|

The absolute discrepancy `|wrPatternMass(p) - worPatternMass(p)|` depends only
on the multiset of excursion types in `p`, not on their ordering. This is proved
by induction on `List.Perm` using the adjacent-transposition invariance machinery
(`abs_wr_wor_patternMass_toReal_eq_of_adjacent_swap_of_decomps`).

Key technique: strengthen the induction hypothesis to work with arbitrary prefixes,
so that the `cons` case of `List.Perm.rec` reduces to the IH applied to a
longer prefix. -/

/-- No-return condition from `IsConsecutivePair`: between consecutive return
positions, the trajectory does not return to start. -/
private lemma noret_of_IsConsecutivePair {N : ℕ} (xs : Traj k N)
    {a b : Fin (N + 1)}
    (h : IsConsecutivePair (returnPositions (k := k) xs) a b) :
    ∀ (j : Fin (N + 1)), a.val < j.val → j.val < b.val → xs j ≠ xs 0 := by
  intro j haj hjb hret
  rcases h with ⟨_, _, _, hgap⟩
  have hj_mem : j ∈ returnPositions (k := k) xs := by
    simp [returnPositions, Finset.mem_filter]
    exact hret
  have haj' : a < j := by exact_mod_cast haj
  have hjb' : j < b := by exact_mod_cast hjb
  exact hgap j hj_mem ⟨haj', hjb'⟩

/-- Segment preservation under `segmentSwap` when the segment starts at or beyond
the swap boundary `a + L1 + L2`, using return conditions at the boundary. -/
private lemma trajSegment_segmentSwap_outside_ge {N : ℕ} (xs : Traj k N)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (i j : Fin (N + 1)) (hij : i.val ≤ j.val)
    (hge : a + L1 + L2 ≤ i.val)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    trajSegment (k := k) (segmentSwap xs a L1 L2 hL1 hL2 hcN) i j =
      trajSegment (k := k) xs i j := by
  apply trajSegment_ext _ _ i.val j.val i.val j.val i.isLt j.isLt i.isLt j.isLt
    hij hij rfl
  intro t ht
  have ht_le : i.val + t ≤ j.val := by omega
  have hp : i.val + t < N + 1 := by omega
  have hge' : a + L1 + L2 ≤ i.val + t := by omega
  by_cases hgt : a + L1 + L2 < i.val + t
  · exact segmentSwap_eq_of_gt_range' xs a L1 L2 hL1 hL2 hcN
      (i.val + t) hp hgt
  · have hEq : i.val + t = a + L1 + L2 := by omega
    -- At the boundary, segmentSwap reads from `a + L1`, which equals the start state.
    have hbc : xs ⟨a + L1, by omega⟩ = xs ⟨a + L1 + L2, by omega⟩ := by
      exact hb_ret.trans hc_ret.symm
    -- Use the definition of segmentSwap at the boundary index.
    have hswap :
        segmentSwap xs a L1 L2 hL1 hL2 hcN ⟨i.val + t, hp⟩ =
          xs ⟨i.val + t - L2, by omega⟩ := by
      have hnot1 : ¬(i.val + t ≤ a) := by omega
      have hnot2 : ¬(i.val + t ≤ a + L2) := by omega
      have hle3 : i.val + t ≤ a + L1 + L2 := by omega
      simp [segmentSwap, hnot1, hnot2, hle3]
    -- Rewrite the RHS to the boundary value and use return equality.
    have hrew : xs ⟨i.val + t - L2, by omega⟩ = xs ⟨i.val + t, hp⟩ := by
      -- i.val + t = a + L1 + L2
      -- so i.val + t - L2 = a + L1
      have : i.val + t - L2 = a + L1 := by omega
      -- Use the return conditions to identify the two positions.
      have hbc' : xs ⟨a + L1, by omega⟩ = xs ⟨a + L1 + L2, by omega⟩ := hbc
      simpa [hEq, this] using hbc'
    simpa [hswap] using hrew

/-- The excursion pairs list satisfies a pairwise property: for any two pairs
where the first comes before the second, the snd of the first is ≤ the fst of the second.
This follows from the sorted structure of the underlying return positions list. -/
private lemma excursionPairs_pairwise_snd_le_fst {n : ℕ} (ys : Traj k n) :
    List.Pairwise (fun a b : Fin (n + 1) × Fin (n + 1) => a.2 ≤ b.1)
      (excursionPairs (k := k) ys) := by
  classical
  let l := returnPositionsList (k := k) ys
  have hs : l.SortedLT := Finset.sortedLT_sort (returnPositions (k := k) ys)
  have hzip : excursionPairs (k := k) ys = l.zip l.tail := by
    simp [excursionPairs, l]
  rw [hzip]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  -- (l.zip l.tail)[i] = (l[i], l[i+1]) and [j] = (l[j], l[j+1])
  -- Need l[i+1] ≤ l[j], which follows from i+1 ≤ j and l sorted
  have hlen_zip : (l.zip l.tail).length = l.length - 1 := by
    simp [List.length_zip, List.length_tail]
  have hli1 : i + 1 < l.length := by omega
  have hlj : j < l.length := by omega
  simp only [List.getElem_zip, List.getElem_tail]
  show l[i + 1] ≤ l[j]
  rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with h | h
  · exact le_of_eq (by congr 1)
  · exact le_of_lt ((List.SortedLT.getElem_lt_getElem_iff hs).2 h)

/-- In a sorted zip-tail decomposition `excursionPairs ys = pre ++ p1 :: p2 :: suf`,
the snd of every pre-element is `≤ p1.fst`. -/
private lemma snd_le_fst_of_mem_pre_excursionPairs {n : ℕ} (ys : Traj k n)
    {pre suf : List (Fin (n + 1) × Fin (n + 1))}
    {p1 p2 : Fin (n + 1) × Fin (n + 1)}
    (hpairs : excursionPairs (k := k) ys = pre ++ p1 :: p2 :: suf)
    {pr : Fin (n + 1) × Fin (n + 1)} (hpr : pr ∈ pre) :
    pr.2 ≤ p1.1 := by
  have hpw := excursionPairs_pairwise_snd_le_fst (k := k) ys
  rw [hpairs] at hpw
  have ⟨_, _, hcross⟩ := List.pairwise_append.mp hpw
  have hmem : p1 ∈ p1 :: p2 :: suf := List.mem_cons_self ..
  exact @hcross _ hpr _ hmem

/-- In a sorted zip-tail decomposition, `p2.snd ≤ pr.fst` for every suf-element. -/
private lemma fst_ge_snd_of_mem_suf_excursionPairs {n : ℕ} (ys : Traj k n)
    {pre suf : List (Fin (n + 1) × Fin (n + 1))}
    {p1 p2 : Fin (n + 1) × Fin (n + 1)}
    (hpairs : excursionPairs (k := k) ys = pre ++ p1 :: p2 :: suf)
    {pr : Fin (n + 1) × Fin (n + 1)} (hpr : pr ∈ suf) :
    p2.2 ≤ pr.1 := by
  have hpw := excursionPairs_pairwise_snd_le_fst (k := k) ys
  rw [hpairs] at hpw
  -- Decompose: pre ++ (p1 :: p2 :: suf) = pre ++ ([p1] ++ (p2 :: suf))
  -- First split on pre vs rest
  have hpw1 := (List.pairwise_append.mp hpw).2.1
  -- hpw1 : Pairwise R (p1 :: p2 :: suf)
  -- Now split p1 :: (p2 :: suf)
  have hpw2 := (List.pairwise_cons.mp hpw1).2
  -- hpw2 : Pairwise R (p2 :: suf)
  have hcross := (List.pairwise_cons.mp hpw2).1
  -- hcross : ∀ b ∈ suf, p2.2 ≤ b.1
  exact hcross pr hpr

/-- For a trajectory in the short-pattern fiber of `preSeg ++ [e1, e2] ++ sufSeg`,
extract the full `ShortSwapMiddleDecomp` witness data. This is the core glue
connecting pattern-level adjacent swaps to the trajectory-level decomposition. -/
private lemma shortSwapMiddleDecomp_of_patternDecomp
    (n : ℕ) (e : MarkovState k) (preSeg sufSeg : ExcursionList k)
    (e1 e2 : ExcursionType k)
    (hL1 : 0 < excLen (k := k) e1) (hL2 : 0 < excLen (k := k) e2)
    (hcN : excSteps (k := k) preSeg + excLen (k := k) e1 +
      excLen (k := k) e2 ≤ Nat.succ n) :
    ShortSwapMiddleDecomp (k := k) n e
      (preSeg ++ [e1, e2] ++ sufSeg)
      (preSeg ++ [e2, e1] ++ sufSeg)
      (excSteps (k := k) preSeg) (excLen (k := k) e1)
      (excLen (k := k) e2) hL1 hL2 hcN := by
  -- Abbreviations for readability
  set a := excSteps (k := k) preSeg with ha_def
  set L1 := excLen (k := k) e1 with hL1_def
  set L2 := excLen (k := k) e2 with hL2_def
  set p := preSeg ++ [e1, e2] ++ sufSeg with hp_def
  set q := preSeg ++ [e2, e1] ++ sufSeg with hq_def
  -- Unfold ShortSwapMiddleDecomp
  intro ys hys
  -- Extract excursionListOfTraj ys = p from membership
  have hys_filt := Finset.mem_filter.1 hys
  have hys_fib : ys ∈ fiber k (Nat.succ n) e := hys_filt.1
  have hys_pat : excursionListOfTraj (k := k) ys = p := hys_filt.2
  -- Apply excursionPairs_decomp_of_excursionList_decomp
  rcases excursionPairs_decomp_of_excursionList_decomp (k := k) ys
    preSeg sufSeg e1 e2 hys_pat with
    ⟨pre, suf, p1, p2, hpairs, hpre, he1, he2, hsuf, hp12⟩
  -- Convert cons form to append form for helper lemmas
  have hpairs_app : excursionPairs (k := k) ys = pre ++ [p1, p2] ++ suf := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]; exact hpairs
  -- Membership facts
  have hp1_mem : p1 ∈ excursionPairs (k := k) ys := by
    rw [hpairs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hp2_mem : p2 ∈ excursionPairs (k := k) ys := by
    rw [hpairs]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hpre_mem : ∀ pr ∈ pre, pr ∈ excursionPairs (k := k) ys := by
    intro pr hpr; rw [hpairs]; exact List.mem_append_left _ hpr
  have hsuf_mem : ∀ pr ∈ suf, pr ∈ excursionPairs (k := k) ys := by
    intro pr hpr; rw [hpairs]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hpr))
  -- Strict ordering
  have hp1_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys hp1_mem
  have hp2_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys hp2_mem
  -- Step 1: Identify p1.1.val = a
  have hsteps := excSteps_preSeg_eq_sum_diffs (k := k) ys pre preSeg hpre hpre_mem
  have hsum := sum_diffs_pre_eq_fst_of_excursionPairs_decomp (k := k) ys pre suf p1 p2 hpairs
  have hsteps_val : a = p1.1.1 := by omega
  -- Step 2: Identify p1.2.val - p1.1.val = L1
  have hexL1 := excLen_trajSegment_of_excursionPair (k := k) ys hp1_mem
  rw [← he1] at hexL1
  -- So p1.2.val = p1.1.val + L1 = a + L1
  have hp12_val : p1.2.1 = p2.1.1 := congrArg Fin.val hp12
  have hp1_snd_val : p1.2.1 = a + L1 := by omega
  -- Step 3: Identify p2.2.val = a + L1 + L2
  have hexL2 := excLen_trajSegment_of_excursionPair (k := k) ys hp2_mem
  rw [← he2] at hexL2
  have hp2_snd_val : p2.2.1 = a + L1 + L2 := by omega
  -- Step 4: Construct the concrete Fin-valued pair identifications
  have hp1_eq : p1 = (⟨a, by omega⟩, ⟨a + L1, by omega⟩) := by
    ext <;> simp <;> omega
  have hp2_eq : p2 = (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩) := by
    ext <;> simp <;> omega
  -- Step 5: Rewrite hpairs with concrete Fin values
  have hpairs' : excursionPairs (k := k) ys =
      pre ++ [(⟨a, by omega⟩, ⟨a + L1, by omega⟩),
              (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩)] ++ suf := by
    rw [hpairs_app]; congr 1; congr 1; simp [hp1_eq, hp2_eq]
  -- Step 6: Return conditions from returnPositions membership
  have hp1_fst_ret : ys ⟨a, by omega⟩ = ys 0 := by
    have h := mem_returnPositions_of_mem_excursionPairs_fst (k := k) ys hp1_mem
    rw [hp1_eq] at h; simp [returnPositions, Finset.mem_filter] at h; exact h
  have hp1_snd_ret : ys ⟨a + L1, by omega⟩ = ys 0 := by
    have h := mem_returnPositions_of_mem_excursionPairs_snd (k := k) ys hp1_mem
    rw [hp1_eq] at h; simp [returnPositions, Finset.mem_filter] at h; exact h
  have hp2_snd_ret : ys ⟨a + L1 + L2, by omega⟩ = ys 0 := by
    have h := mem_returnPositions_of_mem_excursionPairs_snd (k := k) ys hp2_mem
    rw [hp2_eq] at h; simp [returnPositions, Finset.mem_filter] at h; exact h
  -- Step 7: No-return conditions
  have hcp1 := IsConsecutivePair_of_mem_excursionPairs (k := k) ys
    (show (⟨a, by omega⟩, ⟨a + L1, by omega⟩) ∈ excursionPairs (k := k) ys by
      rw [← hp1_eq]; exact hp1_mem)
  have hnoret1 := noret_of_IsConsecutivePair (k := k) ys hcp1
  have hcp2 := IsConsecutivePair_of_mem_excursionPairs (k := k) ys
    (show (⟨a + L1, by omega⟩, ⟨a + L1 + L2, by omega⟩) ∈ excursionPairs (k := k) ys by
      rw [← hp2_eq]; exact hp2_mem)
  have hnoret2 := noret_of_IsConsecutivePair (k := k) ys hcp2
  -- Step 8: excursionPairs of segmentSwap
  have hpairs_swap := excursionPairs_segmentSwap_eq_swap_middle (k := k) ys a L1 L2
    hL1 hL2 hcN pre suf hpairs' hp1_fst_ret hp1_snd_ret hp2_snd_ret hnoret1 hnoret2
  -- Step 9: Pre-segment preservation
  have hpre_seg : pre.map (fun pr =>
      trajSegment (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
    pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) := by
    apply List.map_congr_left
    intro pr hpr
    have hpr_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys (hpre_mem pr hpr)
    have hpr_bound := snd_le_fst_of_mem_pre_excursionPairs (k := k) ys hpairs hpr
    rw [hp1_eq] at hpr_bound; simp at hpr_bound
    exact trajSegment_segmentSwap_outside (k := k) ys a L1 L2 hL1 hL2 hcN pr.1 pr.2
      (le_of_lt hpr_lt) (Or.inl (by omega))
  -- Step 10: Suf-segment preservation
  have hsuf_seg : suf.map (fun pr =>
      trajSegment (k := k) (segmentSwap ys a L1 L2 hL1 hL2 hcN) pr.1 pr.2) =
    suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) := by
    apply List.map_congr_left
    intro pr hpr
    have hpr_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys (hsuf_mem pr hpr)
    have hpr_bound := fst_ge_snd_of_mem_suf_excursionPairs (k := k) ys hpairs hpr
    rw [hp2_eq] at hpr_bound; simp at hpr_bound
    exact trajSegment_segmentSwap_outside_ge (k := k) ys a L1 L2 hL1 hL2 hcN pr.1 pr.2
      (le_of_lt hpr_lt) hpr_bound hp1_snd_ret hp2_snd_ret
  -- Step 11: Rewrite e1, e2, preSeg, sufSeg identifications
  have he1' : e1 = trajSegment (k := k) ys ⟨a, by omega⟩ ⟨a + L1, by omega⟩ := by
    have h1 : (⟨a, by omega⟩ : Fin _) = p1.1 := by ext; simp [hp1_eq]
    have h2 : (⟨a + L1, by omega⟩ : Fin _) = p1.2 := by ext; simp [hp1_eq]
    conv_rhs => rw [h1, h2]
    exact he1
  have he2' : e2 = trajSegment (k := k) ys ⟨a + L1, by omega⟩ ⟨a + L1 + L2, by omega⟩ := by
    have h1 : (⟨a + L1, by omega⟩ : Fin _) = p2.1 := by
      ext; simp [hp2_eq]
    have h2 : (⟨a + L1 + L2, by omega⟩ : Fin _) = p2.2 := by
      ext; simp [hp2_eq]
    conv_rhs => rw [h1, h2]
    exact he2
  have hpre' : preSeg = pre.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) := hpre
  have hsuf' : sufSeg = suf.map (fun pr => trajSegment (k := k) ys pr.1 pr.2) := hsuf
  -- Assemble all 13 conditions
  exact ⟨pre, suf, preSeg, sufSeg, e1, e2,
    hpairs', hpairs_swap, hpre_seg, hsuf_seg,
    hp1_fst_ret, hp1_snd_ret, hp2_snd_ret,
    hys_pat, hpre', hsuf', he1', he2', rfl⟩

/-- Prefix-level counterpart of `shortSwapMiddleDecomp_of_patternDecomp`. -/
private lemma prefixSwapMiddleDecomp_of_patternDecomp
    {N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (preSeg sufSeg : ExcursionList k)
    (e1 e2 : ExcursionType k)
    (hL1 : 0 < excLen (k := k) e1) (hL2 : 0 < excLen (k := k) e2)
    (hcN : excSteps (k := k) preSeg + excLen (k := k) e1 +
      excLen (k := k) e2 ≤ Nat.succ n) :
    PrefixSwapMiddleDecomp (k := k)
      (hN := hN) e s
      (preSeg ++ [e1, e2] ++ sufSeg)
      (preSeg ++ [e2, e1] ++ sufSeg)
      (excSteps (k := k) preSeg) (excLen (k := k) e1)
      (excLen (k := k) e2) hL1 hL2 hcN := by
  -- Reduce to the already-proved short-fiber version by extracting trajPrefix.
  have hshort := shortSwapMiddleDecomp_of_patternDecomp
    (k := k) n e preSeg sufSeg e1 e2 hL1 hL2 hcN
  intro xs hxs
  -- xs ∈ prefixPatternFiber means xs ∈ prefixFiber ∧ excursionListOfTraj (trajPrefix xs) = p
  have hxs_pf : xs ∈ prefixFiber (k := k) (h := hN) e s := (Finset.mem_filter.1 hxs).1
  have hxs_pat : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) =
      preSeg ++ [e1, e2] ++ sufSeg := (Finset.mem_filter.1 hxs).2
  -- Show trajPrefix hN xs ∈ shortPatternFiber n e p
  have hstate : prefixState (k := k) hN xs = e := (Finset.mem_filter.1 hxs_pf).2
  have htp_fiber : trajPrefix (k := k) hN xs ∈ fiber k (Nat.succ n) e :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [prefixState] using hstate⟩
  have htp_short : trajPrefix (k := k) hN xs ∈
      shortPatternFiber (k := k) n e (preSeg ++ [e1, e2] ++ sufSeg) :=
    Finset.mem_filter.2 ⟨htp_fiber, hxs_pat⟩
  -- Apply the short version
  exact hshort (trajPrefix (k := k) hN xs) htp_short

/-- The excursion length bound: for any pattern in the excursion pattern set,
the sum of excursion lengths of any two adjacent excursions in the list
fits within the trajectory length. -/
private lemma excSteps_add_excLen_le_of_mem_excursionPatternSet
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k)
    (hp : preSeg ++ [e1, e2] ++ sufSeg ∈ excursionPatternSet (k := k) (hN := hN) e s) :
    excSteps (k := k) preSeg + excLen (k := k) e1 +
      excLen (k := k) e2 ≤ Nat.succ n := by
  -- Extract a witness trajectory from EPS membership
  rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN)] at hp
  rcases Finset.mem_image.1 hp with ⟨ys, hys_fib, hys_pat⟩
  -- Decompose excursion pairs
  rcases excursionPairs_decomp_of_excursionList_decomp (k := k) ys
    preSeg sufSeg e1 e2 hys_pat with
    ⟨pre, suf, p1, p2, hpairs, hpre, he1, he2, _, hp12⟩
  -- Membership facts
  have hp1_mem : p1 ∈ excursionPairs (k := k) ys := by
    rw [hpairs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hp2_mem : p2 ∈ excursionPairs (k := k) ys := by
    rw [hpairs]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hpre_mem : ∀ pr ∈ pre, pr ∈ excursionPairs (k := k) ys := by
    intro pr hpr; rw [hpairs]; exact List.mem_append_left _ hpr
  -- Strict ordering
  have hp1_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys hp1_mem
  have hp2_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys hp2_mem
  -- excSteps preSeg = p1.1.val
  have hsteps := excSteps_preSeg_eq_sum_diffs (k := k) ys pre preSeg hpre hpre_mem
  have hsum := sum_diffs_pre_eq_fst_of_excursionPairs_decomp (k := k) ys pre suf p1 p2 hpairs
  have hsteps_val : excSteps (k := k) preSeg = p1.1.1 := by omega
  -- excLen values
  have hL1 := excLen_trajSegment_of_excursionPair (k := k) ys hp1_mem
  have hL2 := excLen_trajSegment_of_excursionPair (k := k) ys hp2_mem
  rw [← he1] at hL1; rw [← he2] at hL2
  -- Consecutive: p1.2 = p2.1
  have hp12_val : p1.2.1 = p2.1.1 := by exact congrArg Fin.val hp12
  -- p2.2 is a Fin (Nat.succ n + 1), so p2.2.val ≤ Nat.succ n
  have hbound : p2.2.1 ≤ Nat.succ n := Nat.lt_succ_iff.mp p2.2.2
  -- Combine: excSteps + excLen e1 + excLen e2 = p2.2.val
  omega

/-- Excursion types from actual trajectories have positive length. -/
private lemma excLen_pos_of_mem_excursionPatternSet
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k)
    (hp : preSeg ++ [e1, e2] ++ sufSeg ∈ excursionPatternSet (k := k) (hN := hN) e s) :
    0 < excLen (k := k) e1 ∧ 0 < excLen (k := k) e2 := by
  -- Extract a witness trajectory from EPS membership
  rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN)] at hp
  rcases Finset.mem_image.1 hp with ⟨ys, hys_fib, hys_pat⟩
  -- Decompose excursion pairs using the pattern decomposition
  rcases excursionPairs_decomp_of_excursionList_decomp (k := k) ys
    preSeg sufSeg e1 e2 hys_pat with
    ⟨pre, suf, p1, p2, hpairs, _, he1, he2, _, _⟩
  -- Both p1 and p2 are in excursionPairs ys
  have hp1_mem : p1 ∈ excursionPairs (k := k) ys := by
    rw [hpairs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hp2_mem : p2 ∈ excursionPairs (k := k) ys := by
    rw [hpairs]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- Strict ordering gives positive differences
  have hp1_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys hp1_mem
  have hp2_lt := fst_lt_snd_of_mem_excursionPairs (k := k) ys hp2_mem
  -- excLen = p.2.val - p.1.val for excursion pairs
  have hL1 := excLen_trajSegment_of_excursionPair (k := k) ys hp1_mem
  have hL2 := excLen_trajSegment_of_excursionPair (k := k) ys hp2_mem
  rw [← he1] at hL1; rw [← he2] at hL2
  constructor
  · omega
  · omega

private lemma worPatternMass_eq_of_list_adjacent_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (_hs : s ∈ stateFinset k N)
    (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k)
    (hp : preSeg ++ [e1, e2] ++ sufSeg ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (_hq : preSeg ++ [e2, e1] ++ sufSeg ∈ excursionPatternSet (k := k) (hN := hN) e s) :
    worPatternMass (k := k) (hN := hN) e s (preSeg ++ [e1, e2] ++ sufSeg) =
      worPatternMass (k := k) (hN := hN) e s (preSeg ++ [e2, e1] ++ sufSeg) := by
  have ⟨hL1, hL2⟩ := excLen_pos_of_mem_excursionPatternSet (k := k)
    (hN := hN) (e := e) (s := s) preSeg sufSeg e1 e2 hp
  have hcN := excSteps_add_excLen_le_of_mem_excursionPatternSet (k := k)
    (hN := hN) (e := e) (s := s) preSeg sufSeg e1 e2 hp
  have hcN_swap : excSteps (k := k) preSeg + excLen (k := k) e2 +
      excLen (k := k) e1 ≤ Nat.succ n := by omega
  have hdecompShort := shortSwapMiddleDecomp_of_patternDecomp
    (k := k) n e preSeg sufSeg e1 e2 hL1 hL2 hcN
  have hdecompShortInv := shortSwapMiddleDecomp_of_patternDecomp
    (k := k) n e preSeg sufSeg e2 e1 hL2 hL1 hcN_swap
  have hdecompPrefix := prefixSwapMiddleDecomp_of_patternDecomp
    (k := k) (hN := hN) e s preSeg sufSeg e1 e2 hL1 hL2 hcN
  have hdecompPrefixInv := prefixSwapMiddleDecomp_of_patternDecomp
    (k := k) (hN := hN) e s preSeg sufSeg e2 e1 hL2 hL1 hcN_swap
  have hunif :=
    finite_pattern_uniformity_of_adjacent_swap_of_decomps
      (k := k) (hN := hN) (e := e) (s := s)
      (p := preSeg ++ [e1, e2] ++ sufSeg)
      (q := preSeg ++ [e2, e1] ++ sufSeg)
      (a := excSteps (k := k) preSeg) (L1 := excLen (k := k) e1)
      (L2 := excLen (k := k) e2) hL1 hL2 hcN
      hdecompShort
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdecompShortInv)
      hdecompPrefix
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdecompPrefixInv)
  exact hunif.2.2.1

/-- WOR pattern mass is invariant under permutation of excursion order within
the same multiset class, for patterns in the excursion pattern set. -/
private lemma worPatternMass_eq_of_perm
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (p q : ExcursionList k)
    (hp : p ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (hq : q ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (hperm : Multiset.ofList p = Multiset.ofList q) :
    worPatternMass (k := k) (hN := hN) e s p =
      worPatternMass (k := k) (hN := hN) e s q := by
  classical
  have hperm' : List.Perm p q := by
    classical
    let _ : BEq (ExcursionType k) := instBEqOfDecidableEq
    apply (List.perm_iff_count).2
    intro a
    have hcount := congrArg (fun m => Multiset.count a m) hperm
    simpa using hcount
  have mem_of_perm :
      ∀ {l₁ l₂ : ExcursionList k}, List.Perm l₁ l₂ →
        ∀ pre, pre ++ l₁ ∈ excursionPatternSet (k := k) (hN := hN) e s →
          pre ++ l₂ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
    intro l₁ l₂ hperm''
    refine List.Perm.recOn hperm'' ?nil ?cons ?swap ?trans
    · intro pre hp'; simpa using hp'
    · intro a l₁ l₂ hperm ih pre hp'
      have hp'' : (pre ++ [a]) ++ l₁ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hp'
      have hq'' := ih (pre ++ [a]) hp''
      simpa [List.append_assoc] using hq''
    · intro a b l pre hp'
      have hp'' : pre ++ [b, a] ++ l ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hp'
      have hL := excLen_pos_of_mem_excursionPatternSet (k := k)
        (hN := hN) (e := e) (s := s) pre l b a hp''
      have hL1 : 0 < excLen (k := k) b := hL.1
      have hL2 : 0 < excLen (k := k) a := hL.2
      have hcN :=
        excSteps_add_excLen_le_of_mem_excursionPatternSet (k := k)
          (hN := hN) (e := e) (s := s) pre l b a hp''
      have hdecompShort :=
        shortSwapMiddleDecomp_of_patternDecomp (k := k) n e pre l b a hL1 hL2 hcN
      have hmapFiber :=
        hmapShortFiber_of_shortSwapMiddleDecomp
          (k := k) (n := n) (e := e) (p := pre ++ [b, a] ++ l)
          (q := pre ++ [a, b] ++ l)
          (a := excSteps (k := k) pre) (L1 := excLen (k := k) b)
          (L2 := excLen (k := k) a) hL1 hL2 hcN hdecompShort
      have hmapShort :=
        hmapShort_of_swap_middle_of_excursionPairs_decomp
          (k := k) (n := n) (e := e) (p := pre ++ [b, a] ++ l)
          (q := pre ++ [a, b] ++ l)
          (a := excSteps (k := k) pre) (L1 := excLen (k := k) b)
          (L2 := excLen (k := k) a) hL1 hL2 hcN hmapFiber hdecompShort
      have hp'img := hp''
      rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)] at hp'img
      rcases Finset.mem_image.1 hp'img with ⟨ys, hys_fib, hys_eq⟩
      have hys : ys ∈ shortPatternFiber (k := k) n e (pre ++ [b, a] ++ l) := by
        exact Finset.mem_filter.2 ⟨hys_fib, hys_eq⟩
      have hswap : segmentSwap ys (excSteps (k := k) pre) (excLen (k := k) b)
          (excLen (k := k) a) hL1 hL2 hcN ∈
          shortPatternFiber (k := k) n e (pre ++ [a, b] ++ l) :=
        hmapShort ys hys
      have hswap' :
          segmentSwap ys (excSteps (k := k) pre) (excLen (k := k) b)
            (excLen (k := k) a) hL1 hL2 hcN ∈
            shortPatternFiber (k := k) n e (pre ++ a :: b :: l) := by
        simpa [List.append_assoc] using hswap
      exact mem_excursionPatternSet_of_mem_shortPatternFiber
        (k := k) (hN := hN) (e := e) (s := s) (p := pre ++ a :: b :: l) hswap'
    · intro l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ pre hp'
      have hmid := ih₁ pre hp'
      exact ih₂ pre hmid
  have hP :
      ∀ pre,
        pre ++ p ∈ excursionPatternSet (k := k) (hN := hN) e s →
        pre ++ q ∈ excursionPatternSet (k := k) (hN := hN) e s →
          worPatternMass (k := k) (hN := hN) e s (pre ++ p) =
            worPatternMass (k := k) (hN := hN) e s (pre ++ q) := by
    refine List.Perm.recOn hperm' ?_ ?_ ?_ ?_
    · intro pre hp' hq'
      rfl
    · intro a l₁ l₂ hperm ih pre hp' hq'
      have hp'' : (pre ++ [a]) ++ l₁ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hp'
      have hq'' : (pre ++ [a]) ++ l₂ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hq'
      have h := ih (pre := pre ++ [a]) hp'' hq''
      simpa [List.append_assoc] using h
    · intro a b l pre hp' hq'
      simpa [List.append_assoc] using
        (worPatternMass_eq_of_list_adjacent_swap
          (k := k) (hN := hN) (e := e) (s := s) (_hs := hs)
          (preSeg := pre) (sufSeg := l) (e1 := b) (e2 := a)
          (by simpa [List.append_assoc] using hp')
          (by simpa [List.append_assoc] using hq'))
    · intro l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ pre hp' hq'
      have hmid := mem_of_perm h₁ (pre := pre) hp'
      have h₁' := ih₁ (pre := pre) hp' hmid
      have h₂' := ih₂ (pre := pre) hmid hq'
      exact Eq.trans h₁' h₂'
  exact hP [] (by simpa using hp) (by simpa using hq)

private lemma worPatternMass_toReal_eq_of_perm
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (p q : ExcursionList k)
    (hp : p ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (hq : q ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (hperm : Multiset.ofList p = Multiset.ofList q) :
    (worPatternMass (k := k) (hN := hN) e s p).toReal =
      (worPatternMass (k := k) (hN := hN) e s q).toReal := by
  exact congrArg ENNReal.toReal
    (worPatternMass_eq_of_perm
      (k := k) (hN := hN) (e := e) (s := s) (hs := hs)
      (p := p) (q := q) hp hq hperm)

private lemma sum_worPatternMass_on_multisetFiber_eq_card_mul_of_const
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (mset : Multiset (ExcursionType k))
    (p0 : ExcursionList k)
    (hconst :
      ∀ p,
        p ∈ excursionPatternSet (k := k) (hN := hN) e s →
          Multiset.ofList p = mset →
            (worPatternMass (k := k) (hN := hN) e s p).toReal =
              (worPatternMass (k := k) (hN := hN) e s p0).toReal) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
      (worPatternMass (k := k) (hN := hN) e s p).toReal) =
    (((excursionPatternSet (k := k) (hN := hN) e s).filter
        (fun p => Multiset.ofList p = mset)).card : ℝ) *
      (worPatternMass (k := k) (hN := hN) e s p0).toReal := by
  classical
  let P := excursionPatternSet (k := k) (hN := hN) e s
  calc
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
      (worPatternMass (k := k) (hN := hN) e s p).toReal) =
      Finset.sum (P.filter (fun p => Multiset.ofList p = mset))
        (fun p => (worPatternMass (k := k) (hN := hN) e s p).toReal) := by
          simp [P]
    _ =
      Finset.sum (P.filter (fun p => Multiset.ofList p = mset))
        (fun _ => (worPatternMass (k := k) (hN := hN) e s p0).toReal) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact hconst p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2
    _ =
      (((P.filter (fun p => Multiset.ofList p = mset)).card : ℕ) : ℝ) *
        (worPatternMass (k := k) (hN := hN) e s p0).toReal := by
          simp
    _ =
      (((excursionPatternSet (k := k) (hN := hN) e s).filter
          (fun p => Multiset.ofList p = mset)).card : ℝ) *
        (worPatternMass (k := k) (hN := hN) e s p0).toReal := by
          simp [P]

private lemma sum_worPatternMass_on_multisetFiber_eq_card_mul_choose_of_const
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (mset : Multiset (ExcursionType k))
    (hmset :
      mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList) :
    ∃ p0, p0 ∈ excursionPatternSet (k := k) (hN := hN) e s ∧
      Multiset.ofList p0 = mset ∧
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        (worPatternMass (k := k) (hN := hN) e s p).toReal) =
      (((excursionPatternSet (k := k) (hN := hN) e s).filter
          (fun p => Multiset.ofList p = mset)).card : ℝ) *
        (worPatternMass (k := k) (hN := hN) e s p0).toReal := by
  classical
  rcases Finset.mem_image.1 hmset with ⟨p0, hp0P, hp0m⟩
  refine ⟨p0, hp0P, hp0m, ?_⟩
  have hconst :
      ∀ p,
        p ∈ excursionPatternSet (k := k) (hN := hN) e s →
          Multiset.ofList p = mset →
            (worPatternMass (k := k) (hN := hN) e s p).toReal =
              (worPatternMass (k := k) (hN := hN) e s p0).toReal := by
    intro p hp hpm
    apply worPatternMass_toReal_eq_of_perm
      (k := k) (hN := hN) (e := e) (s := s) (hs := hs)
      (p := p) (q := p0) hp hp0P
    simpa [hpm, hp0m]
  exact sum_worPatternMass_on_multisetFiber_eq_card_mul_of_const
    (k := k) (hN := hN) (e := e) (s := s) (hs := hs)
    (mset := mset) (p0 := p0) hconst

private lemma abs_wr_wor_eq_of_list_adjacent_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (preSeg sufSeg : ExcursionList k) (e1 e2 : ExcursionType k)
    (hp : preSeg ++ [e1, e2] ++ sufSeg ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (hq : preSeg ++ [e2, e1] ++ sufSeg ∈ excursionPatternSet (k := k) (hN := hN) e s) :
    |(wrPatternMass (k := k) hk n e s (preSeg ++ [e1, e2] ++ sufSeg)).toReal -
      (worPatternMass (k := k) (hN := hN) e s (preSeg ++ [e1, e2] ++ sufSeg)).toReal| =
    |(wrPatternMass (k := k) hk n e s (preSeg ++ [e2, e1] ++ sufSeg)).toReal -
      (worPatternMass (k := k) (hN := hN) e s (preSeg ++ [e2, e1] ++ sufSeg)).toReal| := by
  have ⟨hL1, hL2⟩ := excLen_pos_of_mem_excursionPatternSet (k := k)
    (hN := hN) (e := e) (s := s) preSeg sufSeg e1 e2 hp
  have hcN := excSteps_add_excLen_le_of_mem_excursionPatternSet (k := k)
    (hN := hN) (e := e) (s := s) preSeg sufSeg e1 e2 hp
  have hcN_swap : excSteps (k := k) preSeg + excLen (k := k) e2 +
      excLen (k := k) e1 ≤ Nat.succ n := by omega
  have hdecompShort := shortSwapMiddleDecomp_of_patternDecomp
    (k := k) n e preSeg sufSeg e1 e2 hL1 hL2 hcN
  have hdecompShortInv := shortSwapMiddleDecomp_of_patternDecomp
    (k := k) n e preSeg sufSeg e2 e1 hL2 hL1 hcN_swap
  have hdecompPrefix := prefixSwapMiddleDecomp_of_patternDecomp
    (k := k) (hN := hN) e s preSeg sufSeg e1 e2 hL1 hL2 hcN
  have hdecompPrefixInv := prefixSwapMiddleDecomp_of_patternDecomp
    (k := k) (hN := hN) e s preSeg sufSeg e2 e1 hL2 hL1 hcN_swap
  exact abs_wr_wor_patternMass_toReal_eq_of_adjacent_swap_of_decomps
    (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (hs := hs)
    (p := preSeg ++ [e1, e2] ++ sufSeg) (q := preSeg ++ [e2, e1] ++ sufSeg)
    (a := excSteps (k := k) preSeg) (L1 := excLen (k := k) e1)
    (L2 := excLen (k := k) e2) hL1 hL2 hcN
    hdecompShort
    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdecompShortInv)
    hdecompPrefix
    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdecompPrefixInv)

/-- `|wr - wor|` is invariant under permutation of the excursion pattern list,
for patterns in the excursion pattern set.

Proved by `List.Perm.recOn` with strengthened hypothesis:
the motive is `∀ prefix, |wr(prefix ++ l₁) - wor(...)| = |wr(prefix ++ l₂) - wor(...)|`,
so that the `cons` case reduces to the IH with a longer prefix. -/
private lemma abs_wr_wor_patternMass_toReal_eq_of_perm
    {n N : ℕ} (hN : Nat.succ n ≤ N) (hk : 0 < k) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (p q : ExcursionList k)
    (hp : p ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (hq : q ∈ excursionPatternSet (k := k) (hN := hN) e s)
    (hperm : Multiset.ofList p = Multiset.ofList q) :
    |(wrPatternMass (k := k) hk n e s p).toReal -
      (worPatternMass (k := k) (hN := hN) e s p).toReal| =
    |(wrPatternMass (k := k) hk n e s q).toReal -
      (worPatternMass (k := k) (hN := hN) e s q).toReal| := by
  classical
  -- Convert multiset equality to a list permutation.
  have hperm' : List.Perm p q := by
    classical
    -- Use the `BEq` instance induced by `DecidableEq` so counts align.
    let _ : BEq (ExcursionType k) := instBEqOfDecidableEq
    apply (List.perm_iff_count).2
    intro a
    have hcount := congrArg (fun m => Multiset.count a m) hperm
    simpa using hcount
  -- Helper: membership in the shared pattern set is preserved by permutation,
  -- proved by adjacent swaps with explicit segment-swap witnesses.
  have mem_of_perm :
      ∀ {l₁ l₂ : ExcursionList k}, List.Perm l₁ l₂ →
        ∀ pre, pre ++ l₁ ∈ excursionPatternSet (k := k) (hN := hN) e s →
          pre ++ l₂ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
    intro l₁ l₂ hperm''
    refine List.Perm.recOn hperm'' ?nil ?cons ?swap ?trans
    · intro pre hp'; simpa using hp'
    · intro a l₁ l₂ hperm ih pre hp'
      have hp'' : (pre ++ [a]) ++ l₁ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hp'
      have hq'' := ih (pre ++ [a]) hp''
      simpa [List.append_assoc] using hq''
    · intro a b l pre hp'
      -- In this swap case, the permutation is `b::a::l ~ a::b::l`.
      have hp'' : pre ++ [b, a] ++ l ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hp'
      -- Build the swap witnesses from the pattern decomposition.
      have hL := excLen_pos_of_mem_excursionPatternSet (k := k)
        (hN := hN) (e := e) (s := s) pre l b a hp''
      have hL1 : 0 < excLen (k := k) b := hL.1
      have hL2 : 0 < excLen (k := k) a := hL.2
      have hcN :=
        excSteps_add_excLen_le_of_mem_excursionPatternSet (k := k)
          (hN := hN) (e := e) (s := s) pre l b a hp''
      have hdecompShort :=
        shortSwapMiddleDecomp_of_patternDecomp (k := k) n e pre l b a hL1 hL2 hcN
      have hmapFiber :=
        hmapShortFiber_of_shortSwapMiddleDecomp
          (k := k) (n := n) (e := e) (p := pre ++ [b, a] ++ l)
          (q := pre ++ [a, b] ++ l)
          (a := excSteps (k := k) pre) (L1 := excLen (k := k) b)
          (L2 := excLen (k := k) a) hL1 hL2 hcN hdecompShort
      have hmapShort :=
        hmapShort_of_swap_middle_of_excursionPairs_decomp
          (k := k) (n := n) (e := e) (p := pre ++ [b, a] ++ l)
          (q := pre ++ [a, b] ++ l)
          (a := excSteps (k := k) pre) (L1 := excLen (k := k) b)
          (L2 := excLen (k := k) a) hL1 hL2 hcN hmapFiber hdecompShort
      -- Extract a witness trajectory and apply the swap map.
      have hp'img := hp''
      rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)] at hp'img
      rcases Finset.mem_image.1 hp'img with ⟨ys, hys_fib, hys_eq⟩
      have hys : ys ∈ shortPatternFiber (k := k) n e (pre ++ [b, a] ++ l) := by
        exact Finset.mem_filter.2 ⟨hys_fib, hys_eq⟩
      have hswap : segmentSwap ys (excSteps (k := k) pre) (excLen (k := k) b)
          (excLen (k := k) a) hL1 hL2 hcN ∈
          shortPatternFiber (k := k) n e (pre ++ [a, b] ++ l) :=
        hmapShort ys hys
      have hswap' :
          segmentSwap ys (excSteps (k := k) pre) (excLen (k := k) b)
            (excLen (k := k) a) hL1 hL2 hcN ∈
            shortPatternFiber (k := k) n e (pre ++ a :: b :: l) := by
        simpa [List.append_assoc] using hswap
      exact mem_excursionPatternSet_of_mem_shortPatternFiber
        (k := k) (hN := hN) (e := e) (s := s) (p := pre ++ a :: b :: l) hswap'
    · intro l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ pre hp'
      have hmid := ih₁ pre hp'
      exact ih₂ pre hmid
  -- Prove the strengthened statement for all permutations.
  have hP :
      ∀ pre,
        pre ++ p ∈ excursionPatternSet (k := k) (hN := hN) e s →
        pre ++ q ∈ excursionPatternSet (k := k) (hN := hN) e s →
        |(wrPatternMass (k := k) hk n e s (pre ++ p)).toReal -
          (worPatternMass (k := k) (hN := hN) e s (pre ++ p)).toReal| =
        |(wrPatternMass (k := k) hk n e s (pre ++ q)).toReal -
          (worPatternMass (k := k) (hN := hN) e s (pre ++ q)).toReal| := by
    refine List.Perm.recOn hperm' ?_ ?_ ?_ ?_
    · intro pre hp' hq'
      simpa using rfl
    · intro a l₁ l₂ hperm ih pre hp' hq'
      have hp'' : (pre ++ [a]) ++ l₁ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hp'
      have hq'' : (pre ++ [a]) ++ l₂ ∈ excursionPatternSet (k := k) (hN := hN) e s := by
        simpa [List.append_assoc] using hq'
      have h := ih (pre := pre ++ [a]) hp'' hq''
      simpa [List.append_assoc] using h
    · intro a b l pre hp' hq'
      simpa [List.append_assoc] using
        (abs_wr_wor_eq_of_list_adjacent_swap
          (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (hs := hs)
          (preSeg := pre) (sufSeg := l) (e1 := b) (e2 := a)
          (by simpa [List.append_assoc] using hp')
          (by simpa [List.append_assoc] using hq'))
    · intro l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ pre hp' hq'
      have hmid := mem_of_perm h₁ (pre := pre) hp'
      have h₁' := ih₁ (pre := pre) hp' hmid
      have h₂' := ih₂ (pre := pre) hmid hq'
      exact Eq.trans h₁' h₂'
  have h := hP [] (by simpa using hp) (by simpa using hq)
  simpa using h

/-! ## Finite cardinality normalizations for pushforward terms -/





private lemma sum_if_eq_const
    {Ω Γ : Type*} [Fintype Ω] [DecidableEq Γ]
    (lift : Ω → Γ) (γ : Γ) (c : ℝ) :
    (∑ f : Ω, if lift f = γ then c else 0) =
      (Fintype.card {f : Ω // lift f = γ} : ℝ) * c := by
  classical
  calc
    (∑ f : Ω, if lift f = γ then c else 0)
        = ((Finset.univ.filter (fun f : Ω => lift f = γ)).card : ℝ) * c := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Finset.univ.filter (fun f : Ω => lift f = γ)).card * c := by simp
    _ = (Fintype.card {f : Ω // lift f = γ} : ℝ) * c := by
          simp [Fintype.card_subtype]

private lemma sum_if_eq_and_pred_const
    {Ω Γ : Type*} [Fintype Ω] [DecidableEq Γ]
    (lift : Ω → Γ) (γ : Γ) (P : Ω → Prop) [DecidablePred P] (c : ℝ) :
    (∑ f : Ω, if lift f = γ ∧ P f then c else 0) =
      (Fintype.card {f : Ω // lift f = γ ∧ P f} : ℝ) * c := by
  classical
  calc
    (∑ f : Ω, if lift f = γ ∧ P f then c else 0)
        = ((Finset.univ.filter (fun f : Ω => lift f = γ ∧ P f)).card : ℝ) * c := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Finset.univ.filter (fun f : Ω => lift f = γ ∧ P f)).card * c := by simp
    _ = (Fintype.card {f : Ω // lift f = γ ∧ P f} : ℝ) * c := by
          simp [Fintype.card_subtype]

private lemma mu0_push_eq_card
    {m R : ℕ} {Γ : Type*} [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) (γ : Γ) :
    (∑ f : Fin m → Fin R,
      if lift f = γ then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      (Fintype.card {f : Fin m → Fin R // lift f = γ} : ℝ) /
        ((R : ℝ) ^ m) := by
  calc
    (∑ f : Fin m → Fin R,
      if lift f = γ then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      (Fintype.card {f : Fin m → Fin R // lift f = γ} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
          simpa using
            (sum_if_eq_const (Ω := Fin m → Fin R) (Γ := Γ) lift γ
              ((1 : ℝ) / (R : ℝ) ^ m))
    _ =
      (Fintype.card {f : Fin m → Fin R // lift f = γ} : ℝ) /
        ((R : ℝ) ^ m) := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

private lemma muinj_push_eq_card_scaled
    {m R : ℕ} {Γ : Type*} [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) (γ : Γ) :
    (∑ f : Fin m → Fin R,
      if lift f = γ then
        (if Function.Injective f then
          (1 : ℝ) / (R : ℝ) ^ m /
            (∑ g : Fin m → Fin R,
              if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
        else 0)
      else 0) =
      (Fintype.card {f : Fin m → Fin R // lift f = γ ∧ Function.Injective f} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m /
          (∑ g : Fin m → Fin R,
            if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
  classical
  let c : ℝ :=
    (1 : ℝ) / (R : ℝ) ^ m /
      (∑ g : Fin m → Fin R,
        if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
  have hpoint :
      ∀ f : Fin m → Fin R,
        (if lift f = γ then (if Function.Injective f then c else 0) else 0) =
          (if lift f = γ ∧ Function.Injective f then c else 0) := by
    intro f
    by_cases h1 : lift f = γ <;> by_cases h2 : Function.Injective f <;> simp [h1, h2]
  calc
    (∑ f : Fin m → Fin R,
      if lift f = γ then
        (if Function.Injective f then
          (1 : ℝ) / (R : ℝ) ^ m /
            (∑ g : Fin m → Fin R,
              if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
        else 0)
      else 0)
        = ∑ f : Fin m → Fin R,
          (if lift f = γ then (if Function.Injective f then c else 0) else 0) := by
            simp [c]
    _ = ∑ f : Fin m → Fin R,
          (if lift f = γ ∧ Function.Injective f then c else 0) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact hpoint f
    _ = (Fintype.card {f : Fin m → Fin R // lift f = γ ∧ Function.Injective f} : ℝ) * c := by
          simpa using
            (sum_if_eq_and_pred_const
              (Ω := Fin m → Fin R) (Γ := Γ) lift γ
              (fun f => Function.Injective f) c)
    _ = (Fintype.card {f : Fin m → Fin R // lift f = γ ∧ Function.Injective f} : ℝ) *
          ((1 : ℝ) / (R : ℝ) ^ m /
            (∑ g : Fin m → Fin R,
              if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
          simp [c]

private lemma inj_norm_sum_eq_card_scaled
    {m R : ℕ} :
    (∑ g : Fin m → Fin R,
      if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      (Fintype.card {g : Fin m → Fin R // Function.Injective g} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
  calc
    (∑ g : Fin m → Fin R,
      if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      ((Finset.univ.filter (fun g : Fin m → Fin R => Function.Injective g)).card : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
          rw [← Finset.sum_filter]
          simp [Finset.sum_const, nsmul_eq_mul]
    _ =
      (Fintype.card {g : Fin m → Fin R // Function.Injective g} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
          simp [Fintype.card_subtype]

private lemma exists_map_with_fiber_card
    {Γ Ω : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype Ω]
    (A : Γ → Nat)
    (hA : (∑ γ : Γ, A γ) = Fintype.card Ω) :
    ∃ f : Ω → Γ, ∀ γ : Γ, Fintype.card {ω : Ω // f ω = γ} = A γ := by
  classical
  let T := Σ γ : Γ, Fin (A γ)
  have hcard : Fintype.card Ω = Fintype.card T := by
    calc
      Fintype.card Ω = ∑ γ : Γ, A γ := by simpa using hA.symm
      _ = Fintype.card T := by simp [T]
  let e : Ω ≃ T := Fintype.equivOfCardEq hcard
  refine ⟨fun ω => (e ω).1, ?_⟩
  intro γ
  have hcongr :
      Fintype.card {ω : Ω // (e ω).1 = γ} =
        Fintype.card {t : T // t.1 = γ} := by
    let g : {ω : Ω // (e ω).1 = γ} → {t : T // t.1 = γ} :=
      fun ω => ⟨e ω.1, by simpa using ω.2⟩
    have hg_bij : Function.Bijective g := by
      constructor
      · intro ω₁ ω₂ hω
        ext
        exact e.injective (Subtype.ext_iff.mp hω)
      · intro t
        refine ⟨⟨e.symm t.1, by simpa using t.2⟩, ?_⟩
        apply Subtype.ext
        simp [g]
    exact Fintype.card_congr (Equiv.ofBijective g hg_bij)
  calc
    Fintype.card {ω : Ω // (fun ω => (e ω).1) ω = γ}
      = Fintype.card {ω : Ω // (e ω).1 = γ} := by simp
    _ = Fintype.card {t : T // t.1 = γ} := hcongr
    _ = Fintype.card (Fin (A γ)) := by
          refine Fintype.card_congr ?_
          refine
            { toFun := fun t =>
                Fin.cast (by simpa [T] using congrArg A t.2) t.1.2
              invFun := fun i => ⟨⟨γ, i⟩, rfl⟩
              left_inv := ?_
              right_inv := ?_ }
          · intro t
            rcases t with ⟨⟨γ', i⟩, ht⟩
            subst ht
            simp
          · intro i
            simp
    _ = A γ := by simp

private lemma exists_lift_with_pred_counts
    {Γ Ω : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype Ω]
    (I : Ω → Prop) [DecidablePred I]
    (A B : Γ → Nat)
    (hA : (∑ γ : Γ, A γ) = Fintype.card Ω)
    (hB : (∑ γ : Γ, B γ) = Fintype.card {ω : Ω // I ω})
    (hBA : ∀ γ, B γ ≤ A γ) :
    ∃ lift : Ω → Γ,
      (∀ γ : Γ, Fintype.card {ω : Ω // lift ω = γ} = A γ) ∧
      (∀ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω} = B γ) := by
  classical
  let C : Γ → Nat := fun γ => A γ - B γ
  have hsumAB :
      (∑ γ : Γ, A γ) = (∑ γ : Γ, B γ) + (∑ γ : Γ, C γ) := by
    calc
      (∑ γ : Γ, A γ) = ∑ γ : Γ, (B γ + C γ) := by
        refine Finset.sum_congr rfl ?_
        intro γ hγ
        simp [C, Nat.add_sub_of_le (hBA γ)]
      _ = (∑ γ : Γ, B γ) + (∑ γ : Γ, C γ) := by
          simp [Finset.sum_add_distrib]
  have hC : (∑ γ : Γ, C γ) = Fintype.card {ω : Ω // ¬ I ω} := by
    have hcardSplit :
        Fintype.card Ω = Fintype.card {ω : Ω // I ω} + (∑ γ : Γ, C γ) := by
      calc
        Fintype.card Ω = ∑ γ : Γ, A γ := by simpa using hA.symm
        _ = (∑ γ : Γ, B γ) + (∑ γ : Γ, C γ) := hsumAB
        _ = Fintype.card {ω : Ω // I ω} + (∑ γ : Γ, C γ) := by simpa [hB]
    have hcompl :
        Fintype.card {ω : Ω // ¬ I ω} =
          Fintype.card Ω - Fintype.card {ω : Ω // I ω} := by
      simpa using (Fintype.card_subtype_compl I)
    omega
  obtain ⟨fInj, hfInj⟩ :=
    exists_map_with_fiber_card (Γ := Γ) (Ω := {ω : Ω // I ω}) B hB
  obtain ⟨fNon, hfNon⟩ :=
    exists_map_with_fiber_card (Γ := Γ) (Ω := {ω : Ω // ¬ I ω}) C hC
  refine ⟨(fun ω => if hω : I ω then fInj ⟨ω, hω⟩ else fNon ⟨ω, hω⟩), ?_⟩
  refine ⟨?_, ?_⟩
  · intro γ
    let lift : Ω → Γ := fun ω => if hω : I ω then fInj ⟨ω, hω⟩ else fNon ⟨ω, hω⟩
    have hsplit :
        Fintype.card {ω : Ω // lift ω = γ} =
          Fintype.card {ω : Ω // lift ω = γ ∧ I ω} +
            Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} := by
      let eSplit :
          {ω : Ω // lift ω = γ} ≃
            ({ω : Ω // lift ω = γ ∧ I ω} ⊕ {ω : Ω // lift ω = γ ∧ ¬ I ω}) :=
        { toFun := fun ω =>
            if hω : I ω.1 then
              Sum.inl ⟨ω.1, ⟨ω.2, hω⟩⟩
            else
              Sum.inr ⟨ω.1, ⟨ω.2, hω⟩⟩
          invFun := fun s =>
            match s with
            | Sum.inl ωI => ⟨ωI.1, ωI.2.1⟩
            | Sum.inr ωN => ⟨ωN.1, ωN.2.1⟩
          left_inv := by
            intro ω
            by_cases hω : I ω.1
            · simp [hω]
            · simp [hω]
          right_inv := by
            intro s
            cases s with
            | inl ωI =>
                simp [ωI.2.2]
            | inr ωN =>
                simp [ωN.2.2] }
      calc
        Fintype.card {ω : Ω // lift ω = γ}
            = Fintype.card ({ω : Ω // lift ω = γ ∧ I ω} ⊕
                {ω : Ω // lift ω = γ ∧ ¬ I ω}) := by
                  exact Fintype.card_congr eSplit
        _ = Fintype.card {ω : Ω // lift ω = γ ∧ I ω} +
              Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} := by
                simp [Fintype.card_sum]
    have hInjCard :
        Fintype.card {ω : Ω // lift ω = γ ∧ I ω} = B γ := by
      let e :
          {ω : Ω // lift ω = γ ∧ I ω} ≃
            {u : {ω : Ω // I ω} // fInj u = γ} :=
        { toFun := fun ω =>
            ⟨⟨ω.1, ω.2.2⟩, by
              simpa [lift, ω.2.2] using ω.2.1⟩
          invFun := fun u =>
            ⟨u.1.1, by
              refine ⟨?_, u.1.2⟩
              simpa [lift, u.1.2] using u.2⟩
          left_inv := by
            intro ω
            ext
            rfl
          right_inv := by
            intro u
            ext
            rfl }
      calc
        Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
            = Fintype.card {u : {ω : Ω // I ω} // fInj u = γ} := by
                exact Fintype.card_congr e
        _ = B γ := hfInj γ
    have hNonCard :
        Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} = C γ := by
      let e :
          {ω : Ω // lift ω = γ ∧ ¬ I ω} ≃
            {u : {ω : Ω // ¬ I ω} // fNon u = γ} :=
        { toFun := fun ω =>
            ⟨⟨ω.1, ω.2.2⟩, by
              simpa [lift, ω.2.2] using ω.2.1⟩
          invFun := fun u =>
            ⟨u.1.1, by
              refine ⟨?_, u.1.2⟩
              simpa [lift, u.1.2] using u.2⟩
          left_inv := by
            intro ω
            ext
            rfl
          right_inv := by
            intro u
            ext
            rfl }
      calc
        Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω}
            = Fintype.card {u : {ω : Ω // ¬ I ω} // fNon u = γ} := by
                exact Fintype.card_congr e
        _ = C γ := hfNon γ
    calc
      Fintype.card {ω : Ω // lift ω = γ}
          = Fintype.card {ω : Ω // lift ω = γ ∧ I ω} +
              Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} := hsplit
      _ = B γ + C γ := by rw [hInjCard, hNonCard]
      _ = A γ := by simp [C, Nat.add_sub_of_le (hBA γ)]
  · intro γ
    let lift : Ω → Γ := fun ω => if hω : I ω then fInj ⟨ω, hω⟩ else fNon ⟨ω, hω⟩
    let e :
        {ω : Ω // lift ω = γ ∧ I ω} ≃
          {u : {ω : Ω // I ω} // fInj u = γ} :=
      { toFun := fun ω =>
          ⟨⟨ω.1, ω.2.2⟩, by
            simpa [lift, ω.2.2] using ω.2.1⟩
        invFun := fun u =>
          ⟨u.1.1, by
            refine ⟨?_, u.1.2⟩
            simpa [lift, u.1.2] using u.2⟩
        left_inv := by
          intro ω
          ext
          rfl
        right_inv := by
          intro u
          ext
          rfl }
    calc
      Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
          = Fintype.card {u : {ω : Ω // I ω} // fInj u = γ} := by
              exact Fintype.card_congr e
      _ = B γ := hfInj γ

private lemma sum_fiber_counts_eq_card
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (lift : Ω → Γ) :
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ}) = Fintype.card Ω := by
  classical
  let T := Σ γ : Γ, {ω : Ω // lift ω = γ}
  have hcardT : Fintype.card T = ∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ} := by
    simp [T]
  let e : T ≃ Ω :=
    { toFun := fun t => t.2.1
      invFun := fun ω => ⟨lift ω, ⟨ω, rfl⟩⟩
      left_inv := by
        intro t
        rcases t with ⟨γ, ω, hω⟩
        subst hω
        rfl
      right_inv := by
        intro ω
        rfl }
  calc
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ}) = Fintype.card T := by
      symm
      exact hcardT
    _ = Fintype.card Ω := Fintype.card_congr e

private lemma sum_inj_fiber_counts_eq_card
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (I : Ω → Prop) [DecidablePred I]
    (lift : Ω → Γ) :
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω})
      = Fintype.card {ω : Ω // I ω} := by
  classical
  let T := Σ γ : Γ, {ω : Ω // lift ω = γ ∧ I ω}
  have hcardT : Fintype.card T = ∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω} := by
    simp [T]
  let e : T ≃ {ω : Ω // I ω} :=
    { toFun := fun t => ⟨t.2.1, t.2.2.2⟩
      invFun := fun ω => ⟨lift ω.1, ⟨ω.1, ⟨rfl, ω.2⟩⟩⟩
      left_inv := by
        intro t
        rcases t with ⟨γ, ω, hω, hI⟩
        subst hω
        rfl
      right_inv := by
        intro ω
        rfl }
  calc
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω}) = Fintype.card T := by
      symm
      exact hcardT
    _ = Fintype.card {ω : Ω // I ω} := Fintype.card_congr e

private lemma inj_fiber_count_le_fiber_count
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (I : Ω → Prop) [DecidablePred I]
    (lift : Ω → Γ) (γ : Γ) :
    Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
      ≤ Fintype.card {ω : Ω // lift ω = γ} := by
  exact Fintype.card_subtype_mono
    (fun ω : Ω => lift ω = γ ∧ I ω)
    (fun ω : Ω => lift ω = γ)
    (fun ω hω => hω.1)

private lemma counts_from_lift_with_pred
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (I : Ω → Prop) [DecidablePred I]
    (lift : Ω → Γ) :
    let A : Γ → Nat := fun γ => Fintype.card {ω : Ω // lift ω = γ}
    let B : Γ → Nat := fun γ => Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
    (∑ γ : Γ, A γ) = Fintype.card Ω ∧
    (∑ γ : Γ, B γ) = Fintype.card {ω : Ω // I ω} ∧
    (∀ γ : Γ, B γ ≤ A γ) := by
  intro A B
  refine ⟨?_, ?_, ?_⟩
  · simpa [A] using
      (sum_fiber_counts_eq_card (Γ := Γ) (Ω := Ω) lift)
  · simpa [B] using
      (sum_inj_fiber_counts_eq_card
        (Γ := Γ) (Ω := Ω) (I := I) lift)
  · intro γ
    simpa [A, B] using
      (inj_fiber_count_le_fiber_count
        (Γ := Γ) (Ω := Ω) (I := I) lift γ)

private lemma exists_pushforward_repr_of_counts
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (classTerm : Γ → ℝ)
    (A B : Γ → Nat)
    (hA : (∑ γ : Γ, A γ) = Fintype.card (Fin m → Fin R))
    (hB : (∑ γ : Γ, B γ) = Fintype.card {f : Fin m → Fin R // Function.Injective f})
    (hBA : ∀ γ : Γ, B γ ≤ A γ)
    (cInj : ℝ)
    (hcInj :
      (1 : ℝ) / (R : ℝ) ^ m /
        (∑ g : Fin m → Fin R,
          if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0) = cInj)
    (hreprAB : ∀ γ : Γ,
      classTerm γ =
        abs (((A γ : ℝ) / (R : ℝ) ^ m) - ((B γ : ℝ) * cInj))) :
    let Ω := Fin m → Fin R
    let μ0 : Ω → ℝ := fun _ => (1 : ℝ) / (R : ℝ) ^ m
    let μinj : Ω → ℝ := fun f =>
      if Function.Injective f then
        (1 : ℝ) / (R : ℝ) ^ m /
          (∑ g : Ω, if Function.Injective g then
            (1 : ℝ) / (R : ℝ) ^ m else 0)
      else 0
    ∃ lift : Ω → Γ,
      ∀ γ : Γ,
        classTerm γ =
          abs ((∑ f : Ω, if lift f = γ then μ0 f else 0) -
            (∑ f : Ω, if lift f = γ then μinj f else 0)) := by
  classical
  intro Ω μ0 μinj
  rcases exists_lift_with_pred_counts
      (Γ := Γ) (Ω := Ω) (I := Function.Injective)
      (A := A) (B := B) hA hB hBA with ⟨lift, hliftA, hliftB⟩
  refine ⟨lift, ?_⟩
  intro γ
  have hsum0 :
      (∑ f : Ω, if lift f = γ then μ0 f else 0) =
        (A γ : ℝ) / (R : ℝ) ^ m := by
    calc
      (∑ f : Ω, if lift f = γ then μ0 f else 0)
          = (Fintype.card {f : Ω // lift f = γ} : ℝ) /
              (R : ℝ) ^ m := by
                simpa [μ0] using
                  (mu0_push_eq_card
                    (m := m)
                    (R := R)
                    (Γ := Γ)
                    (lift := lift)
                    (γ := γ))
      _ = (A γ : ℝ) / (R : ℝ) ^ m := by
            simp [hliftA γ]
  have hsumInj :
      (∑ f : Ω, if lift f = γ then μinj f else 0) =
        (B γ : ℝ) * cInj := by
    calc
      (∑ f : Ω, if lift f = γ then μinj f else 0)
          = (Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f} : ℝ) *
              ((1 : ℝ) / (R : ℝ) ^ m /
                (∑ g : Fin m → Fin R,
                  if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
                simpa [μinj] using
                  (muinj_push_eq_card_scaled
                    (m := m)
                    (R := R)
                    (Γ := Γ)
                    (lift := lift)
                    (γ := γ))
      _ = (B γ : ℝ) *
            ((1 : ℝ) / (R : ℝ) ^ m /
              (∑ g : Fin m → Fin R,
                if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
            simp [hliftB γ]
      _ = (B γ : ℝ) * cInj := by
            rw [hcInj]
  calc
    classTerm γ =
      abs (((A γ : ℝ) / (R : ℝ) ^ m) - ((B γ : ℝ) * cInj)) := hreprAB γ
    _ =
      abs ((∑ f : Ω, if lift f = γ then μ0 f else 0) -
        (∑ f : Ω, if lift f = γ then μinj f else 0)) := by
          rw [hsum0, hsumInj]

private lemma exists_wr_push_counts
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (hΓ : Nonempty Γ) :
    let Ω := Fin m → Fin R
    let μ0 : Ω → ℝ := fun _ => (1 : ℝ) / (R : ℝ) ^ m
    ∃ lift : Ω → Γ, ∃ A : Γ → Nat,
      (∑ γ : Γ, A γ) = Fintype.card Ω ∧
      (∀ γ : Γ,
        (∑ f : Ω, if lift f = γ then μ0 f else 0) =
          (A γ : ℝ) / (R : ℝ) ^ m) := by
  classical
  intro Ω μ0
  let γ0 : Γ := Classical.choice hΓ
  let lift : Ω → Γ := fun _ => γ0
  let A : Γ → Nat := fun γ => Fintype.card {f : Ω // lift f = γ}
  refine ⟨lift, A, ?_, ?_⟩
  · simpa [A] using
      (sum_fiber_counts_eq_card (Γ := Γ) (Ω := Ω) lift)
  · intro γ
    calc
      (∑ f : Ω, if lift f = γ then μ0 f else 0) =
          (Fintype.card {f : Ω // lift f = γ} : ℝ) / (R : ℝ) ^ m := by
            simpa [μ0] using
              (mu0_push_eq_card
                (m := m) (R := R) (Γ := Γ)
                (lift := lift) (γ := γ))
      _ = (A γ : ℝ) / (R : ℝ) ^ m := by
            simp [A]

private lemma wr_class_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let A : Γ → Nat := fun γ => Fintype.card {f : Ω // lift f = γ}
    (∑ γ : Γ, A γ) = Fintype.card Ω := by
  intro Ω A
  simpa [A] using
    (sum_fiber_counts_eq_card (Γ := Γ) (Ω := Ω) lift)

private lemma wor_class_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let B : Γ → Nat := fun γ =>
      Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f}
    (∑ γ : Γ, B γ) = Fintype.card {f : Ω // Function.Injective f} := by
  intro Ω B
  simpa [B] using
    (sum_inj_fiber_counts_eq_card
      (Γ := Γ) (Ω := Ω) (I := Function.Injective) lift)

private lemma wor_le_wr_class_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let A : Γ → Nat := fun γ => Fintype.card {f : Ω // lift f = γ}
    let B : Γ → Nat := fun γ =>
      Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f}
    (∀ γ : Γ, B γ ≤ A γ) := by
  intro Ω A B γ
  simpa [A, B] using
    (inj_fiber_count_le_fiber_count
      (Γ := Γ) (Ω := Ω) (I := Function.Injective) lift γ)

private lemma wor_push_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let μinj : Ω → ℝ := fun f =>
      if Function.Injective f then
        (1 : ℝ) / (R : ℝ) ^ m /
          (∑ g : Ω, if Function.Injective g then
            (1 : ℝ) / (R : ℝ) ^ m else 0)
      else 0
    let cInj : ℝ :=
      (1 : ℝ) / (R : ℝ) ^ m /
        (∑ g : Ω, if Function.Injective g then
          (1 : ℝ) / (R : ℝ) ^ m else 0)
    let B : Γ → Nat := fun γ =>
      Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f}
    (∑ γ : Γ, B γ) = Fintype.card {f : Ω // Function.Injective f} ∧
      (∀ γ : Γ,
        (∑ f : Ω, if lift f = γ then μinj f else 0) = (B γ : ℝ) * cInj) := by
  intro Ω μinj cInj B
  refine ⟨?_, ?_⟩
  · simpa [B] using
      (sum_inj_fiber_counts_eq_card
        (Γ := Γ) (Ω := Ω) (I := Function.Injective) lift)
  · intro γ
    simpa [Ω, μinj, cInj, B] using
      (muinj_push_eq_card_scaled
        (m := m)
        (R := R)
        (Γ := Γ)
        (lift := lift)
        (γ := γ))

private lemma sum_abs_sub_biapprox_le
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (WR WOR U V : Γ → ℝ) :
    (∑ γ : Γ, |WR γ - WOR γ|) ≤
      (∑ γ : Γ, |WR γ - U γ|) +
      (∑ γ : Γ, |U γ - V γ|) +
      (∑ γ : Γ, |V γ - WOR γ|) := by
  have hpoint :
      ∀ γ : Γ,
        |WR γ - WOR γ| ≤
          |WR γ - U γ| + |U γ - V γ| + |V γ - WOR γ| := by
    intro γ
    have h1 : |WR γ - WOR γ| ≤ |WR γ - U γ| + |U γ - WOR γ| := by
      simpa using abs_sub_le (WR γ) (U γ) (WOR γ)
    have h2 : |U γ - WOR γ| ≤ |U γ - V γ| + |V γ - WOR γ| := by
      simpa using abs_sub_le (U γ) (V γ) (WOR γ)
    linarith
  have hsum :
      (∑ γ : Γ, |WR γ - WOR γ|) ≤
        ∑ γ : Γ, (|WR γ - U γ| + |U γ - V γ| + |V γ - WOR γ|) := by
    exact Finset.sum_le_sum (fun γ _ => hpoint γ)
  calc
    (∑ γ : Γ, |WR γ - WOR γ|)
        ≤ ∑ γ : Γ, (|WR γ - U γ| + |U γ - V γ| + |V γ - WOR γ|) := hsum
    _ =
      (∑ γ : Γ, |WR γ - U γ|) +
      (∑ γ : Γ, |U γ - V γ|) +
      (∑ γ : Γ, |V γ - WOR γ|) := by
        simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

private lemma sum_abs_pushforward_some_le_l1
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [DecidableEq Γ]
    (μ ν : Ω → ℝ) (lift : Ω → Option Γ) :
    (∑ γ : Γ,
      abs ((∑ f : Ω, if lift f = some γ then μ f else 0) -
        (∑ f : Ω, if lift f = some γ then ν f else 0))) ≤
      ∑ f : Ω, abs (μ f - ν f) := by
  let g : Option Γ → ℝ := fun γ' =>
    abs ((∑ f : Ω, if lift f = γ' then μ f else 0) -
      (∑ f : Ω, if lift f = γ' then ν f else 0))
  have hsum_option :
      (∑ γ' : Option Γ, g γ') = g none + ∑ γ : Γ, g (some γ) := by
    simp [g, univ_option, Finset.insertNone]
  have hsome_le :
      (∑ γ : Γ, g (some γ)) ≤ ∑ γ' : Option Γ, g γ' := by
    have hnonneg : 0 ≤ g none := by
      simp [g]
    calc
      (∑ γ : Γ, g (some γ)) ≤ g none + ∑ γ : Γ, g (some γ) := by
        exact le_add_of_nonneg_left hnonneg
      _ = ∑ γ' : Option Γ, g γ' := by
        symm
        exact hsum_option
  have hpush :
      (∑ γ' : Option Γ, g γ') ≤ ∑ f : Ω, abs (μ f - ν f) := by
    simpa [g] using
      (Mettapedia.Logic.l1_pushforward_le
        (μ := μ) (ν := ν) (f := lift))
  calc
    (∑ γ : Γ,
      abs ((∑ f : Ω, if lift f = some γ then μ f else 0) -
        (∑ f : Ω, if lift f = some γ then ν f else 0))) =
      (∑ γ : Γ, g (some γ)) := by
        simp [g]
    _ ≤ ∑ γ' : Option Γ, g γ' := hsome_le
    _ ≤ ∑ f : Ω, abs (μ f - ν f) := hpush

private lemma class_biapprox_le_pushforward_plus_errors
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [DecidableEq Γ]
    (WR WOR : Γ → ℝ)
    (lift : Ω → Option Γ)
    (μ0 μinj : Ω → ℝ)
    (εW εPC : ℝ)
    (hWR :
      (∑ γ : Γ,
        abs (WR γ - (∑ f : Ω, if lift f = some γ then μ0 f else 0))) ≤ εW)
    (hPC :
      (∑ γ : Γ,
        abs ((∑ f : Ω, if lift f = some γ then μinj f else 0) - WOR γ)) ≤ εPC) :
    (∑ γ : Γ, |WR γ - WOR γ|) ≤
      εW + εPC + (∑ f : Ω, abs (μ0 f - μinj f)) := by
  let U : Γ → ℝ := fun γ =>
    (∑ f : Ω, if lift f = some γ then μ0 f else 0)
  let V : Γ → ℝ := fun γ =>
    (∑ f : Ω, if lift f = some γ then μinj f else 0)
  have hsplit :
      (∑ γ : Γ, |WR γ - WOR γ|) ≤
        (∑ γ : Γ, |WR γ - U γ|) +
        (∑ γ : Γ, |U γ - V γ|) +
        (∑ γ : Γ, |V γ - WOR γ|) :=
    sum_abs_sub_biapprox_le (WR := WR) (WOR := WOR) (U := U) (V := V)
  have hpush :
      (∑ γ : Γ, |U γ - V γ|) ≤
        ∑ f : Ω, abs (μ0 f - μinj f) := by
    simpa [U, V] using
      (sum_abs_pushforward_some_le_l1
        (μ := μ0) (ν := μinj) (lift := lift))
  have hWR' :
      (∑ γ : Γ, |WR γ - U γ|) ≤ εW := by
    simpa [U] using hWR
  have hPC' :
      (∑ γ : Γ, |V γ - WOR γ|) ≤ εPC := by
    simpa [V, abs_sub_comm] using hPC
  linarith [hsplit, hpush, hWR', hPC']

private lemma class_collision_bound_of_alignment_package
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (WR WOR : Γ → ℝ)
    (lift : (Fin m → Fin R) → Option Γ)
    (εW εPC : ℝ)
    (hWR :
      (∑ γ : Γ,
        abs (WR γ - (∑ f : (Fin m → Fin R), if lift f = some γ then
          (1 : ℝ) / (R : ℝ) ^ m else 0))) ≤ εW)
    (hPC :
      (∑ γ : Γ,
        abs ((∑ f : (Fin m → Fin R), if lift f = some γ then
          (if Function.Injective f then
            (1 : ℝ) / (R : ℝ) ^ m /
              (∑ g : (Fin m → Fin R), if Function.Injective g then
                (1 : ℝ) / (R : ℝ) ^ m else 0)
          else 0)
          else 0) - WOR γ)) ≤ εPC)
    (hGap : εW + εPC ≤ 0)
    (hRpos : 0 < R)
    (hmR : m ≤ R) :
    (∑ γ : Γ, |WR γ - WOR γ|) ≤
      (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
  let Ω := Fin m → Fin R
  let μ0 : Ω → ℝ := fun _ =>
    (1 : ℝ) / (R : ℝ) ^ m
  let μinj : Ω → ℝ := fun f =>
    if Function.Injective f then
      (1 : ℝ) / (R : ℝ) ^ m /
        (∑ g : Ω, if Function.Injective g then
          (1 : ℝ) / (R : ℝ) ^ m else 0)
    else 0
  have hcore :
      (∑ γ : Γ, |WR γ - WOR γ|) ≤
        εW + εPC + (∑ f : Ω, abs (μ0 f - μinj f)) := by
    exact class_biapprox_le_pushforward_plus_errors
      (WR := WR) (WOR := WOR)
      (lift := lift) (μ0 := μ0) (μinj := μinj)
      (εW := εW) (εPC := εPC)
      (by simpa [Ω, μ0] using hWR)
      (by simpa [Ω, μinj] using hPC)
  have hcollision :
      (∑ f : Ω, abs (μ0 f - μinj f)) ≤
        (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
    simpa [Ω, μ0, μinj] using
      (Mettapedia.Logic.l1_iid_inj_le (R := R) (m := m) hRpos hmR)
  linarith [hcore, hcollision, hGap]

private lemma class_biapprox_le_collision_plus_errors
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (WR WOR : Γ → ℝ)
    (lift : (Fin m → Fin R) → Option Γ)
    (εW εPC : ℝ)
    (hWR :
      (∑ γ : Γ,
        abs (WR γ - (∑ f : (Fin m → Fin R), if lift f = some γ then
          (1 : ℝ) / (R : ℝ) ^ m else 0))) ≤ εW)
    (hPC :
      (∑ γ : Γ,
        abs ((∑ f : (Fin m → Fin R), if lift f = some γ then
          (if Function.Injective f then
            (1 : ℝ) / (R : ℝ) ^ m /
              (∑ g : (Fin m → Fin R), if Function.Injective g then
                (1 : ℝ) / (R : ℝ) ^ m else 0)
          else 0)
          else 0) - WOR γ)) ≤ εPC)
    (hRpos : 0 < R)
    (hmR : m ≤ R) :
    (∑ γ : Γ, |WR γ - WOR γ|) ≤
      εW + εPC + (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
  let Ω := Fin m → Fin R
  let μ0 : Ω → ℝ := fun _ =>
    (1 : ℝ) / (R : ℝ) ^ m
  let μinj : Ω → ℝ := fun f =>
    if Function.Injective f then
      (1 : ℝ) / (R : ℝ) ^ m /
        (∑ g : Ω, if Function.Injective g then
          (1 : ℝ) / (R : ℝ) ^ m else 0)
    else 0
  have hcore :
      (∑ γ : Γ, |WR γ - WOR γ|) ≤
        εW + εPC + (∑ f : Ω, abs (μ0 f - μinj f)) := by
    exact class_biapprox_le_pushforward_plus_errors
      (WR := WR) (WOR := WOR)
      (lift := lift) (μ0 := μ0) (μinj := μinj)
      (εW := εW) (εPC := εPC)
      (by simpa [Ω, μ0] using hWR)
      (by simpa [Ω, μinj] using hPC)
  have hcollision :
      (∑ f : Ω, abs (μ0 f - μinj f)) ≤
        (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
    simpa [Ω, μ0, μinj] using
      (Mettapedia.Logic.l1_iid_inj_le (R := R) (m := m) hRpos hmR)
  linarith [hcore, hcollision]

/-! ## Diaconis-Freedman core lemma

The key bound connecting `W(empiricalParam)` and `prefixCoeff` via the
excursion decomposition. This is the mathematical heart of the proof.

The proof requires the BEST theorem (or excursion ordering bijection):
1. Uniform fiber sampling → uniform excursion ordering
2. `prefixCoeff` = ∑ WOR probabilities over excursion prefix patterns
3. `W(empiricalParam)` ≈ ∑ WR probabilities (up to Laplace smoothing)
4. WOR/WR bound gives `4n²/R`
-/

/- **Diaconis-Freedman core**: for `R > 4n²`, the difference between
`W(empiricalParam s)` and `prefixCoeff` is bounded by `4n²/R`.

TODO: Prove via BEST theorem consequence (Euler trail counting / excursion
ordering bijection). The key missing pieces are:
- Fiber cardinality formula: `|fiber(N, s)| = t_s(G) × ∏_a (outdeg(a) - 1)!`
- Excursion ordering uniformity (consequence of BEST)
- Product decomposition of `wordProbNN` through excursion frequencies -/
/-! Deprecated false-form bridge

The former exact bridge statement tying representative class masses directly to
pushforward counts is known to be false on current WR semantics (see
`WRBridgeCounterexample.wr_bridge_counts_counterexample`).

The core proof now uses bi-approximation plumbing (`εW`, `εPC`) instead. -/

/-! ## Counterexample: WR bridge counts (current definitions) -/

namespace WRBridgeCounterexample

abbrev k0 : ℕ := 2
abbrev n0 : ℕ := 1
abbrev N0 : ℕ := 3

lemma hk0 : 0 < k0 := by decide
lemma hN0 : Nat.succ n0 ≤ N0 := by decide

/-- Constant short trajectory `0,0,0` (length `n0+1 = 3`). -/
def traj000 : Traj k0 (Nat.succ n0) := fun _ => 0

/-- Constant long trajectory `0,0,0,0` (length `N0+1 = 4`). -/
def traj0000 : Traj k0 N0 := fun _ => 0

/-- Evidence states for the short/long constant trajectories. -/
def e : MarkovState k0 := stateOfTraj (k := k0) traj000

def s : MarkovState k0 := stateOfTraj (k := k0) traj0000

/-- The excursion list for the short constant trajectory. -/
def p : ExcursionList k0 := excursionListOfTraj (k := k0) traj000

def mset : Multiset (ExcursionType k0) := Multiset.ofList p

def P : Finset (ExcursionList k0) :=
  excursionPatternSet (k := k0) (hN := hN0) e s

def Pset : Finset (Multiset (ExcursionType k0)) := P.image Multiset.ofList

def Γ := {mset : Multiset (ExcursionType k0) // mset ∈ Pset}

instance instDecidableEqΓ : DecidableEq Γ := by
  intro a b
  cases a with
  | mk a ha =>
      cases b with
      | mk b hb =>
          cases decEq a b with
          | isTrue h =>
              exact isTrue (by cases h; rfl)
          | isFalse h =>
              exact isFalse (by
                intro hEq
                apply h
                exact congrArg Subtype.val hEq)

lemma traj000_mem_fiber : traj000 ∈ fiber k0 (Nat.succ n0) e := by
  simp [fiber, trajFinset, e]

lemma p_mem_P : p ∈ P := by
  classical
  have hP :
      P = (fiber k0 (Nat.succ n0) e).image (fun ys => excursionListOfTraj (k := k0) ys) := by
    simpa [P] using
      (excursionPatternSet_eq_shortImage (k := k0) (hN := hN0) (e := e) (s := s))
  have htraj : traj000 ∈ fiber k0 (Nat.succ n0) e := traj000_mem_fiber
  simpa [hP] using (Finset.mem_image.2 ⟨traj000, htraj, rfl⟩)

lemma mset_mem_Pset : mset ∈ Pset := by
  classical
  exact Finset.mem_image.2 ⟨p, p_mem_P, rfl⟩

/-- The unique excursion multiset class in this tiny example. -/
def γ : Γ := ⟨mset, mset_mem_Pset⟩

abbrev mE : ℕ := returnsToStart (k := k0) e
abbrev R : ℕ := returnsToStart (k := k0) s
abbrev Ω : Type := Fin mE → Fin R

lemma traj0000_mem_fiber : traj0000 ∈ fiber k0 N0 s := by
  simp [fiber, trajFinset, s]

lemma hlen0 :
    (excursionListOfTraj (k := k0) traj0000).length = returnsToStart (k := k0) s := by
  exact excursionList_length_eq_returnsToStart (k := k0) s traj0000 traj0000_mem_fiber

/-- The draw list used in the `hwr_hwor_bridge_counts` construction. -/
def drawList : Ω → ExcursionList k0 := fun f =>
  List.ofFn (fun i : Fin mE =>
    (excursionListOfTraj (k := k0) traj0000).get
      ⟨(f i).1, by
        -- convert the `Fin R` bound using the excursion list length
        simp [hlen0]⟩)

def rawClass : Ω → Multiset (ExcursionType k0) := fun f =>
  Multiset.ofList (drawList f)

def lift0 : Ω → Option Γ := fun f =>
  if hm : rawClass f ∈ Pset then some ⟨rawClass f, hm⟩ else none

def A0 : Γ → Nat := fun γ =>
  (Finset.univ.filter (fun f : Ω => lift0 f = some γ)).card

lemma shortPatternFiber_card : (shortPatternFiber (k := k0) n0 e p).card = 1 := by
  native_decide

lemma P_filter_card : (P.filter (fun q => Multiset.ofList q = mset)).card = 1 := by
  native_decide

lemma A0_gamma : A0 γ = 9 := by
  native_decide

lemma returnsToStart_e : returnsToStart (k := k0) e = 2 := by
  native_decide

lemma returnsToStart_s : returnsToStart (k := k0) s = 3 := by
  native_decide

lemma prefixExcursionCount_traj0000 :
    prefixExcursionCount (k := k0) hN0 traj0000 = 2 := by
  native_decide

lemma short_fiber_card : (fiber k0 (Nat.succ n0) e).card = 1 := by
  native_decide

lemma empiricalStepProb_00 :
    empiricalStepProb (k := k0) hk0 s.counts 0 0 = (4 / 5 : ℝ) := by
  have hcounts00 : s.counts.counts 0 0 = 3 := by
    native_decide
  have hrow : s.counts.rowTotal 0 = 3 := by
    native_decide
  -- use the Laplace-smoothed formula
  simp [empiricalStepProb, hcounts00, hrow,
    DirichletParams.uniformPrior, DirichletParams.uniform,
    DirichletParams.totalConcentration]
  norm_num

lemma initProb_empiricalParam_local (a : Fin k0) :
    initProb (k := k0) (empiricalParam (k := k0) hk0 s) a =
      (if a = s.start then 1 else 0) := by
  classical
  by_cases h : a = s.start
  · subst h
    have hm : s.start ∈ Set.singleton s.start := Set.mem_singleton _
    simp [initProb, empiricalParam, Set.indicator, hm]
  · have hm : s.start ∉ Set.singleton a := by
        intro hs
        have : s.start = a := hs
        exact h this.symm
    simp [initProb, empiricalParam, Set.indicator, hm, h]

lemma initProb_empiricalParam_start :
    initProb (k := k0) (empiricalParam (k := k0) hk0 s) 0 = 1 := by
  have hstart : s.start = 0 := by
    simp [s, stateOfTraj, traj0000]
  simpa [hstart] using (initProb_empiricalParam_local (a := 0))

lemma stepProb_empiricalParam_00 :
    (stepProb (k := k0) (empiricalParam (k := k0) hk0 s) 0 0 : ℝ) = (4 / 5 : ℝ) := by
  simpa [empiricalStepProb_00] using
    (stepProb_empiricalParam (k := k0) (hk := hk0) (s := s) (a := 0) (b := 0))

lemma wordProb_traj000 :
    (wordProb (k := k0) (empiricalParam (k := k0) hk0 s)
      (trajToList (k := k0) traj000)).toReal = (4 / 5 : ℝ) ^ 2 := by
  have hlist : trajToList (k := k0) traj000 = [0, 0, 0] := by
    simp [trajToList, traj000]
  -- expand the recursion and evaluate the empirical step probability
  simp [wordProb, wordProbNN, wordProbAux, hlist,
    initProb_empiricalParam_start, stepProb_empiricalParam_00,
    pow_two, mul_comm]

/-- Tiny-model scalar sanity check: exact `W` value in the `k=2,n=1,N=3`
constant-trajectory example. -/
lemma W_toReal_tiny_example :
    (W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal =
      (4 / 5 : ℝ) ^ 2 := by
  have hW :=
    W_eq_card_mul_wordProb_of_mem_fiber
      (k := k0) (N := Nat.succ n0)
      (θ := empiricalParam (k := k0) hk0 s) (s := e)
      traj000 traj000_mem_fiber
  have hW' :
      (W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal =
        ((fiber k0 (Nat.succ n0) e).card : ENNReal).toReal *
          (wordProb (k := k0) (empiricalParam (k := k0) hk0 s)
            (trajToList (k := k0) traj000)).toReal := by
    simpa [ENNReal.toReal_mul] using congrArg ENNReal.toReal hW
  calc
    (W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal
        = ((fiber k0 (Nat.succ n0) e).card : ENNReal).toReal *
            (wordProb (k := k0) (empiricalParam (k := k0) hk0 s)
              (trajToList (k := k0) traj000)).toReal := hW'
    _ = (1 : ℝ) * (4 / 5 : ℝ) ^ 2 := by
          simp [short_fiber_card, wordProb_traj000]
    _ = (4 / 5 : ℝ) ^ 2 := by ring

/-- Tiny-model scalar sanity check: the WR scalar gap to surrogate `1` is
`9/25` at `R=3`, so any global `Cw / R` bound needs `Cw ≥ 27/25` for this
instance. -/
lemma W_gap_to_one_tiny_example :
    |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal - 1| =
      (9 / 25 : ℝ) := by
  rw [W_toReal_tiny_example]
  norm_num

lemma W_gap_times_R_tiny_example :
    (returnsToStart (k := k0) s : ℝ) *
      |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal - 1| =
      (27 / 25 : ℝ) := by
  rw [W_gap_to_one_tiny_example, returnsToStart_s]
  norm_num

/-- In the tiny counterexample state, the empty-prefix WR excursion surrogate is `1`. -/
lemma excursionWithReplacementProb_empty_tiny :
    excursionWithReplacementProb (k := k0)
      (excursionListOfTraj (k := k0) traj0000) ([] : ExcursionList k0) = 1 := by
  simp [excursionWithReplacementProb, wrProb]

/-- Tiny-model WR representation-rate witness with explicit constant `Crepr = 27/25`
against the empty-prefix excursion surrogate. -/
lemma tiny_wr_repr_rate_to_empty_prefix :
    |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal -
      excursionWithReplacementProb (k := k0)
        (excursionListOfTraj (k := k0) traj0000) ([] : ExcursionList k0)| ≤
      (27 / 25 : ℝ) / (returnsToStart (k := k0) s : ℝ) := by
  rw [excursionWithReplacementProb_empty_tiny, W_gap_to_one_tiny_example, returnsToStart_s]
  norm_num

/-- Sharp lower bound check: for the empty-prefix surrogate in this tiny state,
any bound of the form `|W - surrogate| ≤ Cw / R` forces `Cw ≥ 27/25`. -/
lemma tiny_Cw_lower_bound_for_empty_prefix
    {Cw : ℝ}
    (hbound :
      |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal -
          excursionWithReplacementProb (k := k0)
            (excursionListOfTraj (k := k0) traj0000) ([] : ExcursionList k0)| ≤
        Cw / (returnsToStart (k := k0) s : ℝ)) :
    (27 / 25 : ℝ) ≤ Cw := by
  rw [excursionWithReplacementProb_empty_tiny, W_gap_to_one_tiny_example, returnsToStart_s] at hbound
  have hmult : (27 / 25 : ℝ) ≤ Cw := by
    have : (9 / 25 : ℝ) ≤ Cw / 3 := by simpa using hbound
    nlinarith
  exact hmult

/-- Two-layer constructive witness (statewise, fixed tiny instance):
choose `pref = []`, `target = empiricalExcursionProb`, `Crepr = 27/25`, `Cstep = 0`. -/
lemma tiny_excursion_target_statewise_witness :
    ∃ elist pref : ExcursionList k0,
      ∃ target : ExcursionType k0 → ℝ,
        ∃ Crepr Cstep : ℝ,
          |(W (k := k0) (Nat.succ n0) e (empiricalParam (k := k0) hk0 s)).toReal -
            excursionWithReplacementProb (k := k0) elist pref| ≤
              Crepr / (returnsToStart (k := k0) s : ℝ) ∧
          (∀ a ∈ pref,
            |empiricalExcursionProb (k := k0) elist a - target a| ≤
              Cstep / (returnsToStart (k := k0) s : ℝ)) ∧
          (∀ a ∈ pref, 0 ≤ target a ∧ target a ≤ 1) ∧
          Crepr + (pref.length : ℝ) * Cstep ≤ (27 / 25 : ℝ) := by
  refine ⟨excursionListOfTraj (k := k0) traj0000, [], ?_, (27 / 25 : ℝ), 0, ?_, ?_, ?_, ?_⟩
  · exact empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000)
  · simpa using tiny_wr_repr_rate_to_empty_prefix
  · intro a ha
    cases ha
  · intro a ha
    cases ha
  · norm_num

/-- Nontrivial WR-side pattern-mass smoothing bound in the tiny instance,
derived from `wr_pattern_smoothing_rate_via_excursion_target`. -/
lemma tiny_wr_pattern_smoothing_rate :
    ∑ p' ∈ excursionPatternSet (k := k0) (hN := hN0) e s,
      |(wrPatternMass (k := k0) hk0 n0 e s p').toReal -
        canonicalWRSurrogateMass (k := k0) n0 e
          (excursionsProb (k := k0)
            (empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000))
            ([] : ExcursionList k0)) p'| ≤
      (27 / 25 : ℝ) / (returnsToStart (k := k0) s : ℝ) := by
  have hstepRate :
      ∀ a ∈ ([] : ExcursionList k0),
        |empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000) a -
          empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000) a| ≤
          (0 : ℝ) / (returnsToStart (k := k0) s : ℝ) := by
    intro a ha
    cases ha
  have htarget_range :
      ∀ a ∈ ([] : ExcursionList k0),
        0 ≤ empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000) a ∧
          empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000) a ≤ 1 := by
    intro a ha
    cases ha
  simpa using
    wr_pattern_smoothing_rate_via_excursion_target
      (k := k0) (hk := hk0) (n := n0) (hN := hN0) (e := e) (s := s)
      (elist := excursionListOfTraj (k := k0) traj0000)
      (pref := ([] : ExcursionList k0))
      (target := empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000))
      (Crepr := (27 / 25 : ℝ)) (Cstep := 0)
      tiny_wr_repr_rate_to_empty_prefix hstepRate htarget_range

lemma tiny_wr_pattern_smoothing_rate_numeric :
    ∑ p' ∈ excursionPatternSet (k := k0) (hN := hN0) e s,
      |(wrPatternMass (k := k0) hk0 n0 e s p').toReal -
        canonicalWRSurrogateMass (k := k0) n0 e
          (excursionsProb (k := k0)
            (empiricalExcursionProb (k := k0) (excursionListOfTraj (k := k0) traj0000))
            ([] : ExcursionList k0)) p'| ≤
      (9 / 25 : ℝ) := by
  have hdiv :
      (27 / 25 : ℝ) / (returnsToStart (k := k0) s : ℝ) = (9 / 25 : ℝ) := by
    rw [returnsToStart_s]
    norm_num
  have h := tiny_wr_pattern_smoothing_rate
  rw [hdiv] at h
  exact h

/--
Counterexample to the WR half of `hwr_hwor_bridge_counts` at
`k=2, n=1, N=3` (constant trajectories).
-/
theorem wr_bridge_counts_counterexample :
    (((P.filter (fun q => Multiset.ofList q = mset)).card : ℝ) *
        (wrPatternMass (k := k0) hk0 n0 e s p).toReal) ≠
      (A0 γ : ℝ) / (returnsToStart (k := k0) s : ℝ) ^ mE := by
  classical
  have hys0 : traj000 ∈ shortPatternFiber (k := k0) n0 e p := by
    simp [shortPatternFiber, fiber, trajFinset, e, p]
  have hwr :
      wrPatternMass (k := k0) hk0 n0 e s p =
        wordProb (k := k0) (empiricalParam (k := k0) hk0 s) (trajToList (k := k0) traj000) := by
    have hwr' :=
      wrPatternMass_eq_card_mul_wordProb_of_mem_shortPatternFiber
        (k := k0) (hk := hk0) (n := n0) (e := e) (s := s) (p := p) hys0
    simpa [shortPatternFiber_card] using hwr'
  have hLHS :
      (((P.filter (fun q => Multiset.ofList q = mset)).card : ℝ) *
          (wrPatternMass (k := k0) hk0 n0 e s p).toReal) = (4 / 5 : ℝ) ^ 2 := by
    simp [P_filter_card, hwr, wordProb_traj000]
  have hRHS :
      (A0 γ : ℝ) / (returnsToStart (k := k0) s : ℝ) ^ mE = 1 := by
    simp [A0_gamma, returnsToStart_s, returnsToStart_e, mE]
    norm_num
  have hneq : (4 / 5 : ℝ) ^ 2 ≠ (1 : ℝ) := by
    norm_num
  exact (by simpa [hLHS, hRHS] using hneq)

end WRBridgeCounterexample

/--
Explicit core package for the excursion decomposition bound.

`εW` and `εPC` are the WR-side and WOR-side class-alignment residuals.
The package states that their sum is nonpositive and that the classwise WR/WOR
mass discrepancy is controlled by the collision term plus `εW + εPC`.
-/
def ExcursionBiapproxPackage
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k) : Prop :=
  ∃ εW εPC : ℝ,
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
      εW + εPC +
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ)
    ∧ εW + εPC ≤ 0

/-- Build the core biapproximation package from a bound on representative multiset fibers.

This reduces the full `ExcursionBiapproxPackage` to a single explicit bound on the
collapsed multiset partition. The constancy on each multiset fiber is discharged by
`abs_wr_wor_patternMass_toReal_eq_of_perm`. -/
lemma excursionBiapproxPackage_of_repr_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (bound : ℝ)
    (hbound_repr :
      let P := excursionPatternSet (k := k) (hN := hN) e s
      let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
        if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
      (∑ mset ∈ P.image Multiset.ofList,
        (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
          |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
            (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|)) ≤ bound)
    (hbound_le_collision :
      bound ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ)) :
    ExcursionBiapproxPackage (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s) := by
  classical
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hconst :
      ∀ mset,
        mset ∈ P.image Multiset.ofList →
          ∀ p q,
            p ∈ P → q ∈ P →
              Multiset.ofList p = mset →
                Multiset.ofList q = mset →
                  |(wrPatternMass (k := k) hk n e s p).toReal -
                    (worPatternMass (k := k) (hN := hN) e s p).toReal| =
                  |(wrPatternMass (k := k) hk n e s q).toReal -
                    (worPatternMass (k := k) (hN := hN) e s q).toReal| := by
    intro mset hmset p q hp hq hpm hpq
    apply abs_wr_wor_patternMass_toReal_eq_of_perm
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s) (hs := hs)
      (p := p) (q := q) hp hq
    simpa [hpm, hpq]
  have hsum_bound :
      (∑ mset ∈ P.image Multiset.ofList,
        ∑ p ∈ P with Multiset.ofList p = mset,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤ bound := by
    simpa [P] using
      (sum_abs_wr_wor_partition_by_excursionMultiset_le_of_const
        (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
        (bound := bound) hconst hbound_repr)
  refine ⟨0, 0, ?_, by simp⟩
  have hcollision :
      bound ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := hbound_le_collision
  have hsum_collision :
      (∑ mset ∈ P.image Multiset.ofList,
        ∑ p ∈ P with Multiset.ofList p = mset,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|)
        ≤ 0 + 0 +
          (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
            (returnsToStart (k := k) s : ℝ) := by
    linarith [hsum_bound, hcollision]
  simpa [P] using hsum_collision

private lemma excursion_wor_wr_core_from_semantic_package
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (εW εPC : ℝ)
    (hsum_biapprox :
      (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
        ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
        εW + εPC +
          (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
            (returnsToStart (k := k) s : ℝ))
    (hsemantic_gap : εW + εPC ≤ 0) :
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  linarith [hsum_biapprox, hsemantic_gap]


private lemma excursion_wor_wr_core
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hcore : ExcursionBiapproxPackage (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  rcases hcore with ⟨εW, εPC, hsum_biapprox, hsemantic_gap⟩
  have hpart :=
    sum_ratioTerm_partition_by_excursionMultiset
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
  have hsumRatio :
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(shortPatternRatio (k := k) n e p).toReal *
            (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
            (prefixCoeff (k := k) (h := hN) e s).toReal|) =
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ratioTerm (k := k) (hN := hN) (hk := hk) e s p := by
    simp [ratioTerm]
  rw [hsumRatio, hpart]
  rw [sum_ratioTerm_partition_by_excursionMultiset_eq_sum_abs_wr_wor_partition_by_excursionMultiset
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s) hs]
  exact
    excursion_wor_wr_core_from_semantic_package
      (k := k) (hN := hN) (hk := hk)
      (n := n) (e := e) (s := s)
      (εW := εW) (εPC := εPC)
      (hsum_biapprox := hsum_biapprox)
      (hsemantic_gap := hsemantic_gap)

/-- Concrete WR-side smoothing rate for the canonical surrogate mass. -/
theorem wr_smoothing_rate_canonicalWRSurrogate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (wSurrogate Cw : ℝ)
    (hWclose :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ)) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        canonicalWRSurrogateMass (k := k) n e wSurrogate p| ≤
      Cw / (returnsToStart (k := k) s : ℝ) := by
  exact
    sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
      (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
      (wSurrogate := wSurrogate)
      (εW := Cw / (returnsToStart (k := k) s : ℝ))
      hWclose


/-- Concrete exact choice for the scalar WR surrogate:
set `wSurrogate = W(...).toReal`, yielding zero WR residual mass. -/
theorem wr_smoothing_rate_canonicalWRSurrogate_exact
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        canonicalWRSurrogateMass (k := k) n e
          ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal) p| ≤
      0 := by
  have hWclose :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal| ≤
      (0 : ℝ) / (returnsToStart (k := k) s : ℝ) := by
    simp
  simpa using
    wr_smoothing_rate_canonicalWRSurrogate
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s)
      (wSurrogate := (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
      (Cw := 0) hWclose

/-- Concrete WOR-side transport rate from the canonical WR surrogate:
WR-smoothing residual plus the DF collision term. -/
theorem wor_transport_rate_canonicalWRSurrogate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hcore : ExcursionBiapproxPackage (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s))
    (wSurrogate Cw : ℝ)
    (hWclose :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ)) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
        (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
      (Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hwr_canonical :
      ∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          canonicalWRSurrogateMass (k := k) n e wSurrogate p| ≤
        Cw / (returnsToStart (k := k) s : ℝ) := by
    simpa [P] using
      wr_smoothing_rate_canonicalWRSurrogate
        (k := k) (hk := hk) (n := n) (e := e)
        (hN := hN) (s := s) (wSurrogate := wSurrogate) (Cw := Cw) hWclose
  have hwr_wor :
      ∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    have hratio :=
      excursion_wor_wr_core (k := k) (hk := hk) (n := n) (e := e)
        (hN := hN) (s := s) hs hcore
    simpa [P,
      sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_ratio_form
        (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs] using hratio
  have htriangle :
      (∑ p ∈ P,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| : ℝ) ≤
      (∑ p ∈ P,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (wrPatternMass (k := k) hk n e s p).toReal| : ℝ) +
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| : ℝ) := by
    let f : ExcursionList k → ℝ := fun p =>
      |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|
    let g : ExcursionList k → ℝ := fun p =>
      |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
        (wrPatternMass (k := k) hk n e s p).toReal| +
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|
    have hfg : ∀ p ∈ P, f p ≤ g p := by
      intro p hp
      dsimp [f, g]
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (abs_sub_le
          (canonicalWRSurrogateMass (k := k) n e wSurrogate p)
          ((wrPatternMass (k := k) hk n e s p).toReal)
          ((worPatternMass (k := k) (hN := hN) e s p).toReal))
    have hsum_le : (∑ p ∈ P, f p) ≤ ∑ p ∈ P, g p :=
      Finset.sum_le_sum hfg
    calc
      (∑ p ∈ P,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| : ℝ) = ∑ p ∈ P, f p := by
            simp [f]
      _ ≤ ∑ p ∈ P, g p := hsum_le
      _ =
        (∑ p ∈ P,
          |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
            (wrPatternMass (k := k) hk n e s p).toReal| : ℝ) +
        (∑ p ∈ P,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal| : ℝ) := by
              simp [g, Finset.sum_add_distrib]
  have hcanon_wr_eq :
      (∑ p ∈ P,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (wrPatternMass (k := k) hk n e s p).toReal|) =
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          canonicalWRSurrogateMass (k := k) n e wSurrogate p|) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact abs_sub_comm _ _
  have hcanon_wr :
      (∑ p ∈ P,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (wrPatternMass (k := k) hk n e s p).toReal|) ≤
      Cw / (returnsToStart (k := k) s : ℝ) := by
    calc
      (∑ p ∈ P,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (wrPatternMass (k := k) hk n e s p).toReal|)
          =
        (∑ p ∈ P,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            canonicalWRSurrogateMass (k := k) n e wSurrogate p|) := hcanon_wr_eq
      _ ≤ Cw / (returnsToStart (k := k) s : ℝ) := hwr_canonical
  have hsum :
      (∑ p ∈ P,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
      Cw / (returnsToStart (k := k) s : ℝ) +
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    exact le_trans htriangle (add_le_add hcanon_wr hwr_wor)
  have hsplit :
      Cw / (returnsToStart (k := k) s : ℝ) +
          (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
            (returnsToStart (k := k) s : ℝ) =
        (Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    ring
  calc
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|
        = ∑ p ∈ P,
            |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
              (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
                simp [P]
    _ ≤ Cw / (returnsToStart (k := k) s : ℝ) +
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := hsum
    _ = (Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := hsplit


/-- Exact-surrogate specialization of `wor_transport_rate_canonicalWRSurrogate`:
freeze `wSurrogate` to the actual WR scalar `W(...).toReal`, so the WR residual is zero
and only the collision term remains. -/
theorem wor_transport_rate_canonicalWRSurrogate_exact
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hcore : ExcursionBiapproxPackage (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |canonicalWRSurrogateMass (k := k) n e
          ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal) p -
        (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  have hWclose :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal| ≤
      (0 : ℝ) / (returnsToStart (k := k) s : ℝ) := by
    simp
  simpa using
    wor_transport_rate_canonicalWRSurrogate
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) (hs := hs) (hcore := hcore)
      (wSurrogate := (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
      (Cw := 0) hWclose

private lemma excursion_bound_from_pattern_abs_sum
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (B : ℝ)
    (hsumAbs :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ B) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ B := by
  have hWdecomp :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p =
        W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) :=
    sum_wrPatternMass_eq_W (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
  have hPCdecomp :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        worPatternMass (k := k) (hN := hN) e s p =
          prefixCoeff (k := k) (h := hN) e s :=
    sum_worPatternMass_eq_prefixCoeff (k := k) (hN := hN) (e := e) (s := s) hs
  have hrepr :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal| =
      |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p).toReal
        - (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            worPatternMass (k := k) (hN := hN) e s p).toReal| := by
    rw [← hWdecomp, ← hPCdecomp]
  rw [hrepr]
  exact le_trans
    (abs_toReal_sum_wr_sub_toReal_sum_wor_le_sum_abs
      (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs)
    hsumAbs

/-- Decomposition bound through an explicit surrogate law with separate WR/WOR errors. -/
theorem excursion_bound_from_decomposition_biapprox
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (q : ExcursionList k → ℝ) (εW εPC : ℝ)
    (hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      εW + εPC := by
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have htriangle :
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p|) +
      (∑ p ∈ P,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
    have hpoint :
        ∀ p : ExcursionList k,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
          |(wrPatternMass (k := k) hk n e s p).toReal - q p| +
            |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
      intro p
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (abs_sub_le
          ((wrPatternMass (k := k) hk n e s p).toReal)
          (q p)
          ((worPatternMass (k := k) (hN := hN) e s p).toReal))
    calc
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
          ∑ p ∈ P,
            (|(wrPatternMass (k := k) hk n e s p).toReal - q p| +
              |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
                refine Finset.sum_le_sum ?_
                intro p hp
                exact hpoint p
      _ =
        (∑ p ∈ P,
          |(wrPatternMass (k := k) hk n e s p).toReal - q p|) +
        (∑ p ∈ P,
          |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
            simp [Finset.sum_add_distrib]
  have hsumAbs :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εW + εPC := by
    calc
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| =
          ∑ p ∈ P,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
                simp [P]
      _ ≤
        (∑ p ∈ P,
          |(wrPatternMass (k := k) hk n e s p).toReal - q p|) +
        (∑ p ∈ P,
          |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal|) := htriangle
      _ ≤ εW + εPC := by
        exact add_le_add (by simpa [P] using hwr_q) (by simpa [P] using hq_wor)
  have hfinal :=
    excursion_bound_from_pattern_abs_sum
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN)
      (s := s) (hs := hs) (B := εW + εPC) hsumAbs
  simpa using hfinal

theorem excursion_bound_from_canonical_wr_surrogate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (wSurrogate εW εPC : ℝ)
    (hWsurrogate :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        wSurrogate| ≤ εW)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      εW + εPC := by
  exact
    excursion_bound_from_decomposition_biapprox
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) (hs := hs)
      (q := canonicalWRSurrogateMass (k := k) n e wSurrogate)
      (εW := εW) (εPC := εPC)
      (sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
        (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
        (wSurrogate := wSurrogate) (εW := εW) (hWsurrogate := hWsurrogate))
      hq_wor

/-- Adjusted decomposition bound through an explicit surrogate class law. -/
theorem excursion_bound_from_decomposition_adjusted
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (q : ExcursionList k → ℝ) (ε : ℝ)
    (hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ ε)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
          (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
            (returnsToStart (k := k) s : ℝ)) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      ε + (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  let C : ℝ :=
    (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
      (returnsToStart (k := k) s : ℝ)
  exact
    excursion_bound_from_decomposition_biapprox
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) (hs := hs)
      (q := q) (εW := ε) (εPC := C) hwr_q (by simpa [C] using hq_wor)

/-- Pattern-level WR/WOR discrepancy bound obtained from a surrogate pattern law `q`. -/
lemma sum_abs_wr_wor_patternMass_toReal_le_of_surrogate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (q : ExcursionList k → ℝ) (εW εPC : ℝ)
    (hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εW + εPC := by
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hpoint :
      ∀ p : ExcursionList k,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| +
          |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
    intro p
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (abs_sub_le
        ((wrPatternMass (k := k) hk n e s p).toReal)
        (q p)
        ((worPatternMass (k := k) (hN := hN) e s p).toReal))
  calc
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|
        = ∑ p ∈ P,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
              simp [P]
    _ ≤
      ∑ p ∈ P,
        (|(wrPatternMass (k := k) hk n e s p).toReal - q p| +
          |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact hpoint p
    _ =
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p|) +
      (∑ p ∈ P,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
          simp [Finset.sum_add_distrib]
    _ ≤ εW + εPC := by
      exact add_le_add (by simpa [P] using hwr_q) (by simpa [P] using hq_wor)

/-- Convert a pattern-level bi-approximation + nonpositive gap into the class-level
`ExcursionBiapproxPackage` used by the hard-direction pipeline. -/
lemma excursionBiapproxPackage_of_pattern_surrogate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (q : ExcursionList k → ℝ) (εW εPC : ℝ)
    (hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC)
    (hgap : εW + εPC ≤ 0) :
    ExcursionBiapproxPackage (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s) := by
  refine ⟨εW, εPC, ?_, hgap⟩
  have hsum_pattern :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εW + εPC :=
    sum_abs_wr_wor_patternMass_toReal_le_of_surrogate
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (q := q) (εW := εW) (εPC := εPC) hwr_q hq_wor
  have hpart :
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
      (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
        ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) :=
    sum_abs_wr_wor_patternMass_partition_by_excursionMultiset
      (k := k) (hN := hN) (hk := hk) (e := e) (s := s)
  have hcollision_nonneg :
      0 ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    have hnum_nonneg :
        0 ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by positivity
    have hden_nonneg : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
      exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s))
    exact div_nonneg hnum_nonneg hden_nonneg
  calc
    (∑ mset ∈ (excursionPatternSet (k := k) (hN := hN) e s).image Multiset.ofList,
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s with Multiset.ofList p = mset,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
            simpa using hpart.symm
    _ ≤ εW + εPC := hsum_pattern
    _ ≤ εW + εPC +
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
            linarith

theorem excursion_bound_from_decomposition
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hcore : ExcursionBiapproxPackage (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  classical
  have hWdecomp :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p =
        W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) :=
    sum_wrPatternMass_eq_W (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
  have hPCdecomp :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        worPatternMass (k := k) (hN := hN) e s p =
          prefixCoeff (k := k) (h := hN) e s :=
    sum_worPatternMass_eq_prefixCoeff (k := k) (hN := hN) (e := e) (s := s) hs
  have hrepr :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal| =
      |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p).toReal
        - (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            worPatternMass (k := k) (hN := hN) e s p).toReal| := by
    rw [← hWdecomp, ← hPCdecomp]
  have hsumAbsRatio :=
    excursion_wor_wr_core (k := k) hk n e hN s hs hcore
  have hsumAbs :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    simpa [sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_ratio_form
      (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs] using hsumAbsRatio
  exact excursion_bound_from_pattern_abs_sum
    (k := k) hk n e hN s hs
    (B := (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
      (returnsToStart (k := k) s : ℝ))
    hsumAbs

end MarkovDeFinettiHardBEST

end Mettapedia.Logic
