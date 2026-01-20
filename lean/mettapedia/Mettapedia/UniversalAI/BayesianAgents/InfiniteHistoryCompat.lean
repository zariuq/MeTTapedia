import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mettapedia.UniversalAI.BayesianAgents.Core
import Mettapedia.UniversalAI.InfiniteHistory

/-!
# BayesianAgents ↔ InfiniteHistory compatibility

This file lifts the Core history-based model to the infinite-history
measure-theoretic core, keeping the finite action/percept setting.
-/

namespace Mettapedia.UniversalAI.BayesianAgents.Core

open scoped BigOperators
open scoped ENNReal
open Finset
open Preorder

namespace InfiniteHistoryCompat

universe u

variable {Action : Type u} {Percept : Type u}
  [Fintype Action] [Fintype Percept]

local instance : MeasurableSpace Action := ⊤
local instance : MeasurableSpace Percept := ⊤

local notation "Step" => (Action × Percept)
abbrev StepFamilyT (Action : Type u) (Percept : Type u) : ℕ → Type u :=
  Mettapedia.UniversalAI.InfiniteHistory.StepFamily (Action := Action) (Percept := Percept)
abbrev PrefixT (Action : Type u) (Percept : Type u) (n : ℕ) : Type u :=
  Mettapedia.UniversalAI.InfiniteHistory.Prefix (Action := Action) (Percept := Percept) n
abbrev TrajectoryT (Action : Type u) (Percept : Type u) : Type u :=
  Mettapedia.UniversalAI.InfiniteHistory.Trajectory (Action := Action) (Percept := Percept)
local notation "StepFamily" => StepFamilyT Action Percept
local notation "Prefix" n => PrefixT Action Percept n
local notation "Trajectory" => TrajectoryT Action Percept

local instance : MeasurableSpace Step := by
  infer_instance

local instance (n : ℕ) : MeasurableSpace (StepFamily n) := by
  infer_instance

local instance (n : ℕ) : MeasurableSpace (Prefix n) := by
  infer_instance

local instance : MeasurableSpace Trajectory := by
  infer_instance

instance : Fintype Step := by
  infer_instance

instance : MeasurableSingletonClass Step := by
  infer_instance

instance (n : ℕ) : Fintype (Prefix n) := by
  infer_instance

instance (n : ℕ) : MeasurableSingletonClass (Prefix n) := by
  infer_instance

/-- Convert a prefix into a Core `History` by flattening step pairs. -/
def prefixToHistory (n : ℕ) (x : Prefix n) : History Action Percept :=
  (List.finRange (n + 1)).flatMap fun i =>
    let s : Step := x ⟨i.val, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩
    [HistElem.act s.1, HistElem.per s.2]

/-- Extend a prefix by one step. -/
def prefixExtend (a : ℕ) (pref : Prefix a) (s : Step) : Prefix (a + 1) :=
  _root_.IicProdIoc (X := StepFamily) a (a + 1)
    (pref, (MeasurableEquiv.piSingleton (X := StepFamily) a s))

omit [Fintype Action] [Fintype Percept] in
theorem prefixExtend_apply_last (a : ℕ) (pref : Prefix a) (s : Step) :
    prefixExtend (Action := Action) (Percept := Percept) a pref s
        ⟨a + 1, mem_Iic.2 (le_rfl)⟩ = s := by
  have hnot : ¬ (a + 1 ≤ a) := Nat.not_succ_le_self a
  simp [prefixExtend, _root_.IicProdIoc_def, hnot, MeasurableEquiv.piSingleton]

omit [Fintype Action] [Fintype Percept] in
theorem prefixExtend_frestrictLe (a : ℕ) (pref : Prefix a) (s : Step) :
    frestrictLe₂ (π := StepFamily) (a := a) (b := a + 1) (Nat.le_succ a)
        (prefixExtend (Action := Action) (Percept := Percept) a pref s) = pref := by
  have h :=
    congrArg
      (fun f => f (pref, (MeasurableEquiv.piSingleton (X := StepFamily) a s)))
      (frestrictLe₂_comp_IicProdIoc (X := StepFamily) (a := a) (b := a + 1)
        (hab := Nat.le_succ a))
  simpa [prefixExtend] using h

theorem measurable_prefixExtend (a : ℕ) (pref : Prefix a) :
    Measurable fun s : Step =>
      prefixExtend (Action := Action) (Percept := Percept) a pref s := by
  have h_pi :
      Measurable fun s : Step =>
        (MeasurableEquiv.piSingleton (X := StepFamily) a s) := by
    simpa using (MeasurableEquiv.piSingleton (X := StepFamily) a).measurable
  -- `measurable_of_finite` keeps the compat layer simple and avoids instance mismatches
  -- from the `Prefix` abbreviations.
  simpa using
    (measurable_of_finite
      (f := fun s : Step =>
        prefixExtend (Action := Action) (Percept := Percept) a pref s))

omit [Fintype Action] [Fintype Percept] in
theorem prefixToHistory_succ (a : ℕ) (x : Prefix (a + 1)) :
    prefixToHistory (Action := Action) (Percept := Percept) (a + 1) x =
      prefixToHistory (Action := Action) (Percept := Percept) a
          (frestrictLe₂ (π := StepFamily) (a := a) (b := a + 1) (Nat.le_succ a) x) ++
        [HistElem.act (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).1,
          HistElem.per (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2] := by
  classical
  let f : Fin (a + 2) → List (HistElem Action Percept) := fun i =>
    let s : Step := x ⟨i.val, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩
    [HistElem.act s.1, HistElem.per s.2]
  have h_range :
      List.finRange (a + 2) =
        (List.finRange (a + 1)).map Fin.castSucc ++ [Fin.last (a + 1)] := by
    have h_ofFn :
        List.ofFn (fun i : Fin (a + 2) => i) =
          (List.ofFn fun i : Fin (a + 1) => Fin.castSucc i).concat (Fin.last (a + 1)) := by
      simpa using (List.ofFn_succ' (f := fun i : Fin (a + 2) => i))
    have h_cast :
        List.ofFn (fun i : Fin (a + 1) => Fin.castSucc i) =
          (List.finRange (a + 1)).map Fin.castSucc := by
      simpa using (List.ofFn_eq_map (f := fun i : Fin (a + 1) => Fin.castSucc i))
    calc
      List.finRange (a + 2) = List.ofFn (fun i : Fin (a + 2) => i) := by
        simpa using (List.ofFn_id (a + 2)).symm
      _ = (List.ofFn fun i : Fin (a + 1) => Fin.castSucc i).concat (Fin.last (a + 1)) := h_ofFn
      _ = ((List.finRange (a + 1)).map Fin.castSucc).concat (Fin.last (a + 1)) := by
        simpa using congrArg (fun l => l.concat (Fin.last (a + 1))) h_cast
      _ = (List.finRange (a + 1)).map Fin.castSucc ++ [Fin.last (a + 1)] := by
        simp [List.concat_eq_append]
  have h_flat :
      (List.finRange (a + 2)).flatMap f =
        (List.finRange (a + 1)).flatMap (fun i => f (Fin.castSucc i)) ++
          f (Fin.last (a + 1)) := by
    simp [h_range, List.flatMap_append, List.flatMap_map]
  have h_prefix :
      (List.finRange (a + 1)).flatMap (fun i => f (Fin.castSucc i)) =
        prefixToHistory (Action := Action) (Percept := Percept) a
          (frestrictLe₂ (π := StepFamily) (a := a) (b := a + 1) (Nat.le_succ a) x) := by
    simp [prefixToHistory, f, frestrictLe₂_apply]
  have h_last :
      f (Fin.last (a + 1)) =
        [HistElem.act (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).1,
          HistElem.per (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2] := by
    simp [f]
  calc
    prefixToHistory (Action := Action) (Percept := Percept) (a + 1) x =
        (List.finRange (a + 2)).flatMap f := by
          simp [prefixToHistory, f]
    _ =
        (List.finRange (a + 1)).flatMap (fun i => f (Fin.castSucc i)) ++
          f (Fin.last (a + 1)) := h_flat
    _ =
        prefixToHistory (Action := Action) (Percept := Percept) a
            (frestrictLe₂ (π := StepFamily) (a := a) (b := a + 1) (Nat.le_succ a) x) ++
          [HistElem.act (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).1,
            HistElem.per (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2] := by
          simp [h_prefix, h_last]

omit [Fintype Action] [Fintype Percept] in
theorem prefixToHistory_extend (a : ℕ) (pref : Prefix a) (s : Step) :
    prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
        (prefixExtend (Action := Action) (Percept := Percept) a pref s) =
      prefixToHistory (Action := Action) (Percept := Percept) a pref ++
        [HistElem.act s.1, HistElem.per s.2] := by
  have h_succ :=
    prefixToHistory_succ (Action := Action) (Percept := Percept) (a := a)
      (x := prefixExtend (Action := Action) (Percept := Percept) a pref s)
  have h_restrict :
      frestrictLe₂ (π := StepFamily) (a := a) (b := a + 1) (Nat.le_succ a)
          (prefixExtend (Action := Action) (Percept := Percept) a pref s) = pref :=
    prefixExtend_frestrictLe (Action := Action) (Percept := Percept) (a := a) (pref := pref)
      (s := s)
  have h_last :
      (prefixExtend (Action := Action) (Percept := Percept) a pref s)
          ⟨a + 1, mem_Iic.2 (le_rfl)⟩ = s :=
    prefixExtend_apply_last (Action := Action) (Percept := Percept) (a := a) (pref := pref) (s := s)
  simpa [h_restrict, h_last] using h_succ

omit [Fintype Action] [Fintype Percept] in
theorem percepts_actper_pairs (pairs : List (Action × Percept)) :
    History.percepts (Action := Action) (Percept := Percept)
        (pairs.flatMap (fun ⟨act, per⟩ => [HistElem.act act, HistElem.per per])) =
      pairs.map Prod.snd := by
  induction pairs with
  | nil =>
      simp [History.percepts]
  | cons p rest ih =>
      cases p with
      | mk act per =>
          simp [History.percepts, ih]

omit [Fintype Action] [Fintype Percept] in
theorem cycles_actper_pairs (pairs : List (Action × Percept)) :
    History.cycles (Action := Action) (Percept := Percept)
        (pairs.flatMap (fun ⟨act, per⟩ => [HistElem.act act, HistElem.per per])) =
      pairs.length := by
  simp [History.cycles, percepts_actper_pairs]

omit [Fintype Action] [Fintype Percept] in
/-- Helper: histories built from action/percept pairs are well-formed. -/
theorem wellFormed_actper_pairs (pairs : List (Action × Percept)) :
    let h := pairs.flatMap (fun ⟨act, per⟩ => [HistElem.act act, HistElem.per per])
    History.wellFormed (Action := Action) (Percept := Percept) h := by
  induction pairs with
  | nil =>
      simp [History.wellFormed]
  | cons p rest ih =>
      simp [History.wellFormed, ih]

omit [Fintype Action] [Fintype Percept] in
theorem prefixToHistory_wellFormed (n : ℕ) (x : Prefix n) :
    History.wellFormed (Action := Action) (Percept := Percept) (prefixToHistory n x) := by
  let pairs : List (Action × Percept) :=
    (List.finRange (n + 1)).map fun i =>
      let s := x ⟨i.val, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩
      (s.1, s.2)
  have h_pairs :
      History.wellFormed (Action := Action) (Percept := Percept)
        (pairs.flatMap (fun ⟨act, per⟩ => [HistElem.act act, HistElem.per per])) :=
    wellFormed_actper_pairs (Action := Action) (Percept := Percept) pairs
  simpa [prefixToHistory, pairs, List.flatMap_map] using h_pairs

omit [Fintype Action] [Fintype Percept] in
theorem cycles_prefixToHistory (n : ℕ) (x : Prefix n) :
    History.cycles (Action := Action) (Percept := Percept) (prefixToHistory n x) = n + 1 := by
  let pairs : List (Action × Percept) :=
    (List.finRange (n + 1)).map fun i =>
      let s := x ⟨i.val, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩
      (s.1, s.2)
  have h_pairs :
      History.cycles (Action := Action) (Percept := Percept)
          (pairs.flatMap (fun ⟨act, per⟩ => [HistElem.act act, HistElem.per per])) =
        pairs.length :=
    cycles_actper_pairs (Action := Action) (Percept := Percept) pairs
  have h_len : pairs.length = n + 1 := by
    simp [pairs]
  simpa [prefixToHistory, pairs, List.flatMap_map, h_len] using h_pairs

/-- History of the first `t` steps of a trajectory (0 steps yields empty history). -/
def trajectoryToHistorySteps : ℕ → Trajectory → History Action Percept
  | 0, _ => []
  | t + 1, traj => prefixToHistory t (frestrictLe (π := StepFamily) t traj)

omit [Fintype Action] [Fintype Percept] in
theorem trajectoryToHistorySteps_zero (traj : Trajectory) :
    trajectoryToHistorySteps (Action := Action) (Percept := Percept) 0 traj = [] := rfl

omit [Fintype Action] [Fintype Percept] in
theorem trajectoryToHistorySteps_succ (t : ℕ) (traj : Trajectory) :
    trajectoryToHistorySteps (Action := Action) (Percept := Percept) (t + 1) traj =
      prefixToHistory t (frestrictLe (π := StepFamily) t traj) := rfl

omit [Fintype Action] [Fintype Percept] in
theorem cycles_trajectoryToHistorySteps (t : ℕ) (traj : Trajectory) :
    History.cycles (Action := Action) (Percept := Percept)
        (trajectoryToHistorySteps (Action := Action) (Percept := Percept) t traj) = t := by
  cases t with
  | zero =>
      simp [trajectoryToHistorySteps, History.cycles, History.percepts]
  | succ n =>
      simpa [trajectoryToHistorySteps] using
        (cycles_prefixToHistory (Action := Action) (Percept := Percept) n
          (frestrictLe (π := StepFamily) n traj))

/-- Cylinder set at time `t`: trajectories whose first `t` steps yield history `h`. -/
def cylinderSetAt (t : ℕ) (h : History Action Percept) : Set Trajectory :=
  {traj | trajectoryToHistorySteps (Action := Action) (Percept := Percept) t traj = h}

/-- Cylinder set for a history uses its number of cycles as the time index. -/
def cylinderSet (h : History Action Percept) : Set Trajectory :=
  cylinderSetAt (Action := Action) (Percept := Percept) (History.cycles h) h

omit [Fintype Action] [Fintype Percept] in
theorem cylinderSetAt_succ (t : ℕ) (h : History Action Percept) :
    cylinderSetAt (Action := Action) (Percept := Percept) (t + 1) h =
      (frestrictLe (π := StepFamily) t) ⁻¹' {p | prefixToHistory t p = h} := by
  ext traj
  simp [cylinderSetAt, trajectoryToHistorySteps]

omit [Fintype Action] [Fintype Percept] in
/-- Helper: append a single action to an act/per history. -/
theorem wellFormed_actper_prefix_act (pairs : List (Action × Percept)) (a : Action) :
    let h := pairs.flatMap (fun ⟨act, per⟩ => [HistElem.act act, HistElem.per per])
    History.wellFormed (Action := Action) (Percept := Percept) (h ++ [HistElem.act a]) := by
  induction pairs with
  | nil =>
      simp [History.wellFormed]
  | cons p rest ih =>
      simp [History.wellFormed, List.flatMap_cons, ih]

omit [Fintype Action] [Fintype Percept] in
theorem prefixToHistory_append_act_wellFormed (n : ℕ) (x : Prefix n) (a : Action) :
    History.wellFormed (Action := Action) (Percept := Percept)
      (prefixToHistory n x ++ [HistElem.act a]) := by
  let pairs : List (Action × Percept) :=
    (List.finRange (n + 1)).map fun i =>
      let s := x ⟨i.val, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩
      (s.1, s.2)
  have h_pairs :
      History.wellFormed (Action := Action) (Percept := Percept)
        (pairs.flatMap (fun ⟨act, per⟩ => [HistElem.act act, HistElem.per per]) ++
          [HistElem.act a]) :=
    wellFormed_actper_prefix_act (Action := Action) (Percept := Percept) pairs a
  simpa [prefixToHistory, pairs, List.flatMap_map] using h_pairs

/-- Stochasticity: percept distribution sums to 1 on well-formed histories. -/
def isStochastic (μ : Environment Action Percept) : Prop :=
  ∀ h, History.wellFormed (Action := Action) (Percept := Percept) h →
    (∑ x : Percept, μ.prob h x) = 1

/-- Policy-driven transition measure on steps given a prefix. -/
noncomputable def transitionMeasureWithPolicy
    (μ : Environment Action Percept) (π : Agent Action Percept) (n : ℕ) (x : Prefix n) :
    MeasureTheory.Measure Step :=
  MeasureTheory.Measure.sum fun s : Step =>
    (π.policy (prefixToHistory n x) s.1 *
        μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2) •
      MeasureTheory.Measure.dirac s

/-- Policy-driven transition kernel. -/
noncomputable def transitionKernelWithPolicy
    (μ : Environment Action Percept) (π : Agent Action Percept) (n : ℕ) :
    ProbabilityTheory.Kernel (Prefix n) (StepFamily (n + 1)) where
  toFun := transitionMeasureWithPolicy μ π n
  measurable' := by
    exact measurable_of_finite _

/-- The policy-driven transition kernel is a Markov kernel under stochasticity. -/
theorem transitionKernelWithPolicy_isMarkov
    (μ : Environment Action Percept) (π : Agent Action Percept) (n : ℕ)
    (h_stoch : isStochastic μ) :
    ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n) := by
  constructor
  intro x
  constructor
  show transitionMeasureWithPolicy μ π n x Set.univ = 1
  simp only [transitionMeasureWithPolicy]
  rw [MeasureTheory.Measure.sum_apply_of_countable, tsum_fintype]

  have h_simp : ∀ s : Step,
      ((π.policy (prefixToHistory n x) s.1 *
            μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2) •
          MeasureTheory.Measure.dirac s) Set.univ =
        π.policy (prefixToHistory n x) s.1 *
          μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2 := by
    intro s
    simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
    rw [MeasureTheory.Measure.dirac_apply' s MeasurableSet.univ]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  simp only [h_simp]

  -- Split sum over actions and percepts.
  rw [Fintype.sum_prod_type]

  have h_factor : ∀ a : Action,
      ∑ p : Percept,
          π.policy (prefixToHistory n x) a *
            μ.prob (prefixToHistory n x ++ [HistElem.act a]) p =
        π.policy (prefixToHistory n x) a *
          ∑ p : Percept, μ.prob (prefixToHistory n x ++ [HistElem.act a]) p := by
    intro a
    rw [Finset.mul_sum]
  simp only [h_factor]

  have h_inner_eq_one : ∀ a : Action,
      ∑ p : Percept, μ.prob (prefixToHistory n x ++ [HistElem.act a]) p = 1 := by
    intro a
    have h_wf := prefixToHistory_append_act_wellFormed (n := n) (x := x) a
    have h_stoch_app := h_stoch (prefixToHistory n x ++ [HistElem.act a]) h_wf
    simpa [tsum_fintype] using h_stoch_app
  simp only [h_inner_eq_one, mul_one]

  have h_wf : History.wellFormed (Action := Action) (Percept := Percept) (prefixToHistory n x) :=
    prefixToHistory_wellFormed (n := n) (x := x)
  simpa [tsum_fintype] using (π.policy_sum_one (prefixToHistory n x) h_wf)

/-- Initial step measure from empty history. -/
noncomputable def initialStepMeasureWithPolicy
    (μ : Environment Action Percept) (π : Agent Action Percept) :
    MeasureTheory.Measure Step :=
  MeasureTheory.Measure.sum fun s : Step =>
    (π.policy ([] : History Action Percept) s.1 *
        μ.prob [HistElem.act s.1] s.2) •
      MeasureTheory.Measure.dirac s

/-- The initial step measure is a probability measure under stochasticity. -/
theorem initialStepMeasureWithPolicy_isProbability
    (μ : Environment Action Percept) (π : Agent Action Percept) (h_stoch : isStochastic μ) :
    MeasureTheory.IsProbabilityMeasure (initialStepMeasureWithPolicy μ π) := by
  constructor
  simp only [initialStepMeasureWithPolicy]
  rw [MeasureTheory.Measure.sum_apply_of_countable, tsum_fintype]

  have h_simp : ∀ s : Step,
      ((π.policy ([] : History Action Percept) s.1 *
            μ.prob [HistElem.act s.1] s.2) • MeasureTheory.Measure.dirac s) Set.univ =
        π.policy ([] : History Action Percept) s.1 * μ.prob [HistElem.act s.1] s.2 := by
    intro s
    simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
    rw [MeasureTheory.Measure.dirac_apply' s MeasurableSet.univ]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  simp only [h_simp]

  rw [Fintype.sum_prod_type]

  have h_factor : ∀ a : Action,
      ∑ p : Percept,
          π.policy ([] : History Action Percept) a * μ.prob [HistElem.act a] p =
        π.policy ([] : History Action Percept) a * ∑ p : Percept, μ.prob [HistElem.act a] p := by
    intro a
    rw [Finset.mul_sum]
  simp only [h_factor]

  have h_inner_eq_one : ∀ a : Action, ∑ p : Percept, μ.prob [HistElem.act a] p = 1 := by
    intro a
    have h_wf : History.wellFormed (Action := Action) (Percept := Percept)
        ([HistElem.act a] : History Action Percept) := by
      rfl
    have h_stoch_app := h_stoch [HistElem.act a] h_wf
    simpa [tsum_fintype] using h_stoch_app
  simp only [h_inner_eq_one, mul_one]

  have h_wf : History.wellFormed (Action := Action) (Percept := Percept)
      ([] : History Action Percept) := by
    rfl
  simpa [tsum_fintype] using (π.policy_sum_one ([] : History Action Percept) h_wf)

theorem integral_transitionMeasureWithPolicy
    (μ : Environment Action Percept) (π : Agent Action Percept) (n : ℕ) (x : Prefix n)
    {g : Step → ℝ} (hg : MeasureTheory.Integrable g (transitionMeasureWithPolicy μ π n x)) :
    ∫ s, g s ∂ transitionMeasureWithPolicy μ π n x =
      ∑ s : Step,
        (π.policy (prefixToHistory n x) s.1 *
            μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2).toReal * g s := by
  classical
  have h_sum :
      ∫ s, g s ∂ transitionMeasureWithPolicy μ π n x =
        ∑' s : Step,
          ∫ s', g s' ∂
            ((π.policy (prefixToHistory n x) s.1 *
                  μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2) •
              MeasureTheory.Measure.dirac s) := by
    simpa [transitionMeasureWithPolicy] using
      (MeasureTheory.integral_sum_measure (μ := fun s : Step =>
        (π.policy (prefixToHistory n x) s.1 *
              μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2) •
          MeasureTheory.Measure.dirac s) (f := g) hg)
  have h_dirac :
      ∀ s : Step,
        ∫ s', g s' ∂
          ((π.policy (prefixToHistory n x) s.1 *
                μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2) •
            MeasureTheory.Measure.dirac s) =
          (π.policy (prefixToHistory n x) s.1 *
              μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2).toReal * g s := by
    intro s
    simp [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
  calc
    ∫ s, g s ∂ transitionMeasureWithPolicy μ π n x =
        ∑' s : Step,
          ∫ s', g s' ∂
            ((π.policy (prefixToHistory n x) s.1 *
                  μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2) •
              MeasureTheory.Measure.dirac s) := h_sum
    _ =
        ∑' s : Step,
          (π.policy (prefixToHistory n x) s.1 *
              μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2).toReal * g s := by
        simp [h_dirac]
    _ = ∑ s : Step,
          (π.policy (prefixToHistory n x) s.1 *
              μ.prob (prefixToHistory n x ++ [HistElem.act s.1]) s.2).toReal * g s := by
        simp [tsum_fintype]


/-- Convert between a single step and the `Iic 0` prefix space. -/
def stepToIic0 : Step ≃ (Prefix 0) where
  toFun s := fun _ => s
  invFun f := f ⟨0, mem_Iic.2 (le_rfl)⟩
  left_inv _ := rfl
  right_inv f := by
    funext ⟨i, hi⟩
    have hi0 : i = 0 := Nat.le_zero.mp (mem_Iic.1 hi)
    subst hi0
    rfl

theorem stepToIic0_measurable :
    Measurable (stepToIic0 (Action := Action) (Percept := Percept)) := by
  simpa using
    (measurable_of_finite
      (f := (stepToIic0 (Action := Action) (Percept := Percept))))

/-- Initial measure on `Iic 0` from the policy-driven initial step. -/
noncomputable def initialMeasureIic0WithPolicy
    (μ : Environment Action Percept) (π : Agent Action Percept) :
    MeasureTheory.Measure (Prefix 0) :=
  (initialStepMeasureWithPolicy μ π).map stepToIic0

instance initialMeasureIic0WithPolicy_isProbability
    (μ : Environment Action Percept) (π : Agent Action Percept) (h_stoch : isStochastic μ) :
    MeasureTheory.IsProbabilityMeasure (initialMeasureIic0WithPolicy μ π) := by
  haveI : MeasureTheory.IsProbabilityMeasure (initialStepMeasureWithPolicy μ π) :=
    initialStepMeasureWithPolicy_isProbability μ π h_stoch
  constructor
  simp only [initialMeasureIic0WithPolicy]
  rw [MeasureTheory.Measure.map_apply
    (stepToIic0_measurable (Action := Action) (Percept := Percept)) MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact MeasureTheory.measure_univ

/-- Environment measure on trajectories induced by policy `π`. -/
noncomputable def environmentMeasureWithPolicy
    (μ : Environment Action Percept) (π : Agent Action Percept) (h_stoch : isStochastic μ) :
    MeasureTheory.Measure Trajectory :=
  have hκ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n) :=
    fun n => transitionKernelWithPolicy_isMarkov μ π n h_stoch
  let _ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n) := hκ
  Mettapedia.UniversalAI.InfiniteHistory.trajMeasureOf (X := StepFamily)
    (κ := transitionKernelWithPolicy μ π) 0 (initialMeasureIic0WithPolicy μ π)

theorem environmentMeasureWithPolicy_isProbability
    (μ : Environment Action Percept) (π : Agent Action Percept) (h_stoch : isStochastic μ) :
    MeasureTheory.IsProbabilityMeasure (environmentMeasureWithPolicy μ π h_stoch) := by
  haveI : MeasureTheory.IsProbabilityMeasure (initialMeasureIic0WithPolicy μ π) :=
    initialMeasureIic0WithPolicy_isProbability μ π h_stoch
  haveI : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n) :=
    fun n => transitionKernelWithPolicy_isMarkov μ π n h_stoch
  simpa [environmentMeasureWithPolicy] using
    (Mettapedia.UniversalAI.InfiniteHistory.trajMeasureOf_isProbability
      (X := StepFamily) (κ := transitionKernelWithPolicy μ π) 0
      (initialMeasureIic0WithPolicy μ π))

open MeasureTheory ProbabilityTheory

/-- Base case: the policy-driven trajectory measure at step 0 matches the initial step mass. -/
theorem environmentMeasureWithPolicy_step0_singleton
    (μ : Environment Action Percept) (π : Agent Action Percept) (h_stoch : isStochastic μ)
    (s : Step) :
    environmentMeasureWithPolicy μ π h_stoch {traj | traj 0 = s} =
      π.policy [] s.1 * μ.prob [HistElem.act s.1] s.2 := by
  classical
  have h_set :
      ({traj : Trajectory | traj 0 = s} : Set Trajectory) =
        (frestrictLe (π := StepFamily) 0) ⁻¹' ({stepToIic0 s} : Set (Prefix 0)) := by
    ext traj
    constructor
    · intro h0
      have h_eq : frestrictLe (π := StepFamily) 0 traj = stepToIic0 s := by
        funext i
        rcases i with ⟨i, hi⟩
        have hi0 : i = 0 := Nat.le_zero.mp (mem_Iic.1 hi)
        subst hi0
        simpa [frestrictLe_apply, stepToIic0, h0]
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using h_eq
    · intro hmem
      have h_eq : frestrictLe (π := StepFamily) 0 traj = stepToIic0 s := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hmem
      have h_at0 := congrArg (fun f => f ⟨0, mem_Iic.2 (le_rfl)⟩) h_eq
      simpa [frestrictLe_apply, stepToIic0] using h_at0

  have h_map :
      (environmentMeasureWithPolicy μ π h_stoch).map (frestrictLe (π := StepFamily) 0) =
        initialMeasureIic0WithPolicy μ π := by
    haveI : ∀ n, IsMarkovKernel (transitionKernelWithPolicy μ π n) :=
      fun n => transitionKernelWithPolicy_isMarkov μ π n h_stoch
    have hf : Measurable (frestrictLe (π := StepFamily) 0) :=
      measurable_frestrictLe (X := StepFamily) 0
    simp [environmentMeasureWithPolicy]
    rw [MeasureTheory.Measure.map_comp (μ := initialMeasureIic0WithPolicy μ π)
      (κ := @Kernel.traj StepFamily (fun _ => inferInstance) (transitionKernelWithPolicy μ π)
        (fun n => transitionKernelWithPolicy_isMarkov μ π n h_stoch) 0) hf]
    rw [Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
    simp

  have hs_iic0 : MeasurableSet ({stepToIic0 s} : Set (Prefix 0)) := by
    simp
  have hf0 : Measurable (frestrictLe (π := StepFamily) 0) :=
    measurable_frestrictLe (X := StepFamily) 0

  calc
    environmentMeasureWithPolicy μ π h_stoch {traj | traj 0 = s}
        = environmentMeasureWithPolicy μ π h_stoch ((frestrictLe (π := StepFamily) 0) ⁻¹'
            ({stepToIic0 s} : Set (Prefix 0))) := by
              simp [h_set]
    _ = (environmentMeasureWithPolicy μ π h_stoch).map (frestrictLe (π := StepFamily) 0)
          ({stepToIic0 s} : Set (Prefix 0)) := by
            simpa using
              (MeasureTheory.Measure.map_apply (μ := environmentMeasureWithPolicy μ π h_stoch) hf0
                hs_iic0).symm
    _ = initialMeasureIic0WithPolicy μ π ({stepToIic0 s} : Set (Prefix 0)) := by
          simp [h_map]
    _ = initialStepMeasureWithPolicy μ π {s} := by
          have hs_step : MeasurableSet ({stepToIic0 s} : Set (Prefix 0)) := by simp
          have h_pre :
              stepToIic0 ⁻¹' ({stepToIic0 s} : Set (Prefix 0)) = ({s} : Set Step) := by
            ext s'
            simp
          simp [initialMeasureIic0WithPolicy,
            MeasureTheory.Measure.map_apply stepToIic0_measurable hs_step, h_pre]
    _ = π.policy [] s.1 * μ.prob [HistElem.act s.1] s.2 := by
          have hs : MeasurableSet ({s} : Set Step) := by simp
          classical
          simp [initialStepMeasureWithPolicy, hs, Set.indicator, Finset.mem_univ]

/-- Map the trajectory measure to prefixes of length `n`. -/
theorem environmentMeasureWithPolicy_map_frestrictLe
    (μ : Environment Action Percept) (π : Agent Action Percept) (h_stoch : isStochastic μ)
    (n : ℕ) :
    (environmentMeasureWithPolicy μ π h_stoch).map (frestrictLe (π := StepFamily) n) =
      MeasureTheory.Measure.bind (initialMeasureIic0WithPolicy μ π)
        (Kernel.partialTraj (transitionKernelWithPolicy μ π) 0 n) := by
  haveI : ∀ k, IsMarkovKernel (transitionKernelWithPolicy μ π k) :=
    fun k => transitionKernelWithPolicy_isMarkov μ π k h_stoch
  have hf : Measurable (frestrictLe (π := StepFamily) n) :=
    measurable_frestrictLe (X := StepFamily) n
  simp [environmentMeasureWithPolicy]
  rw [MeasureTheory.Measure.map_comp (μ := initialMeasureIic0WithPolicy μ π)
    (κ := @Kernel.traj StepFamily (fun _ => inferInstance) (transitionKernelWithPolicy μ π)
      (fun k => transitionKernelWithPolicy_isMarkov μ π k h_stoch) 0) hf]
  simp [Kernel.traj_map_frestrictLe]

theorem environmentMeasureWithPolicy_cylinderSetAt_succ
    (μ : Environment Action Percept) (π : Agent Action Percept) (h_stoch : isStochastic μ)
    (t : ℕ) (h : History Action Percept) :
    environmentMeasureWithPolicy μ π h_stoch (cylinderSetAt (Action := Action) (Percept := Percept) (t + 1) h) =
      MeasureTheory.Measure.bind (initialMeasureIic0WithPolicy μ π)
        (Kernel.partialTraj (transitionKernelWithPolicy μ π) 0 t)
          {p | prefixToHistory t p = h} := by
  have hf : Measurable (frestrictLe (π := StepFamily) t) :=
    measurable_frestrictLe (X := StepFamily) t
  have hs_finite :
      ({p | prefixToHistory t p = h} : Set (Prefix t)).Finite :=
    (Set.finite_univ : (Set.univ : Set (Prefix t)).Finite).subset
      (by intro p hp; exact Set.mem_univ p)
  have hs : MeasurableSet ({p | prefixToHistory t p = h} : Set (Prefix t)) :=
    hs_finite.measurableSet
  calc
    environmentMeasureWithPolicy μ π h_stoch (cylinderSetAt (Action := Action) (Percept := Percept) (t + 1) h)
        = environmentMeasureWithPolicy μ π h_stoch ((frestrictLe (π := StepFamily) t) ⁻¹'
            ({p | prefixToHistory t p = h} : Set (Prefix t))) := by
              simp [cylinderSetAt_succ (Action := Action) (Percept := Percept) (t := t) (h := h)]
    _ = (environmentMeasureWithPolicy μ π h_stoch).map (frestrictLe (π := StepFamily) t)
          ({p | prefixToHistory t p = h} : Set (Prefix t)) := by
            simpa using
              (MeasureTheory.Measure.map_apply (μ := environmentMeasureWithPolicy μ π h_stoch) hf
                hs).symm
    _ = MeasureTheory.Measure.bind (initialMeasureIic0WithPolicy μ π)
          (Kernel.partialTraj (transitionKernelWithPolicy μ π) 0 t)
          ({p | prefixToHistory t p = h} : Set (Prefix t)) := by
            simp [environmentMeasureWithPolicy_map_frestrictLe (μ := μ) (π := π)
              (h_stoch := h_stoch) (n := t)]

section FiniteHorizonUtility

variable [PerceptReward Percept]

def trajShift (k : ℕ) (traj : Trajectory) : Trajectory :=
  fun n => traj (k + n)

def trajTail (traj : Trajectory) : Trajectory :=
  trajShift (Action := Action) (Percept := Percept) 1 traj

omit [Fintype Action] [Fintype Percept] [PerceptReward Percept] in
theorem measurable_trajShift (k : ℕ) :
    Measurable (trajShift (Action := Action) (Percept := Percept) k) := by
  refine measurable_pi_iff.mpr ?_
  intro n
  simpa [trajShift] using (measurable_pi_apply (a := k + n))

omit [Fintype Action] [Fintype Percept] [PerceptReward Percept] in
theorem measurable_trajTail :
    Measurable (trajTail (Action := Action) (Percept := Percept)) := by
  simpa [trajTail] using
    (measurable_trajShift (Action := Action) (Percept := Percept) (k := 1))

omit [Fintype Action] [Fintype Percept] in
theorem measurable_reward_at (k : ℕ) :
    Measurable fun traj : Trajectory => PerceptReward.reward (traj k).2 := by
  have h_reward : Measurable (fun p : Percept => PerceptReward.reward p) := by
    simpa using
      (measurable_from_top (β := ℝ) (f := fun p : Percept => PerceptReward.reward p))
  have h_eval : Measurable fun traj : Trajectory => (traj k).2 := by
    simpa using (measurable_snd.comp (measurable_pi_apply (a := k)))
  exact h_reward.comp h_eval

omit [Fintype Action] [Fintype Percept] in
theorem measurable_reward_prefix (a : ℕ) :
    Measurable fun z : PrefixT Action Percept (a + 1) =>
      PerceptReward.reward (z ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2 := by
  have h_reward : Measurable (fun p : Percept => PerceptReward.reward p) := by
    simpa using
      (measurable_from_top (β := ℝ) (f := fun p : Percept => PerceptReward.reward p))
  have h_eval :
      Measurable fun z : PrefixT Action Percept (a + 1) =>
        (z ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2 := by
    have h_step :
        Measurable fun z : PrefixT Action Percept (a + 1) =>
          z ⟨a + 1, mem_Iic.2 (le_rfl)⟩ := by
      simpa using
        (measurable_pi_apply
          (a := (⟨a + 1, mem_Iic.2 (le_rfl)⟩ : Finset.Iic (a + 1))))
    exact measurable_snd.comp h_step
  exact h_reward.comp h_eval

omit [Fintype Action] [Fintype Percept] [PerceptReward Percept] in
theorem trajTail_shift (k : ℕ) (traj : Trajectory) :
    trajTail (Action := Action) (Percept := Percept) (trajShift (Action := Action) (Percept := Percept) k traj) =
      trajShift (Action := Action) (Percept := Percept) (k + 1) traj := by
  funext n
  have h : k + (1 + n) = k + 1 + n := by
    simp [Nat.add_assoc]
  have h' : traj (k + (1 + n)) = traj (k + 1 + n) := congrArg traj h
  simp [trajTail, trajShift, h']

omit [Fintype Action] [Fintype Percept] [PerceptReward Percept] in
theorem trajShift_succ (k : ℕ) (traj : Trajectory) :
    trajShift (Action := Action) (Percept := Percept) 1
        (trajShift (Action := Action) (Percept := Percept) k traj) =
      trajShift (Action := Action) (Percept := Percept) (k + 1) traj := by
  funext n
  have h : k + (1 + n) = k + 1 + n := by
    simp [Nat.add_assoc]
  have h' : traj (k + (1 + n)) = traj (k + 1 + n) := congrArg traj h
  simp [trajShift, h']

omit [Fintype Action] [Fintype Percept] [PerceptReward Percept] in
theorem trajShift_zero (traj : Trajectory) :
    trajShift (Action := Action) (Percept := Percept) 0 traj = traj := by
  funext n
  exact congrArg traj (Nat.zero_add n)

noncomputable def discountedRewardSum (γ : DiscountFactor) : ℕ → Trajectory → ℝ
  | 0, _ => 0
  | t + 1, traj =>
      PerceptReward.reward (traj 0).2 + γ.val * discountedRewardSum γ t (trajTail traj)

noncomputable def discountedRewardSumFrom (γ : DiscountFactor) (k : ℕ) (t : ℕ)
    (traj : Trajectory) : ℝ :=
  discountedRewardSum (Action := Action) (Percept := Percept) γ t
    (trajShift (Action := Action) (Percept := Percept) k traj)

omit [Fintype Action] [Fintype Percept] in
theorem measurable_discountedRewardSum (γ : DiscountFactor) (t : ℕ) :
    Measurable (discountedRewardSum (Action := Action) (Percept := Percept) γ t) := by
  induction t with
  | zero =>
      simp [discountedRewardSum]
  | succ t ih =>
      have h_reward : Measurable fun traj : Trajectory => PerceptReward.reward (traj 0).2 := by
        simpa using (measurable_reward_at (Action := Action) (Percept := Percept) (k := 0))
      have h_tail :
          Measurable fun traj : Trajectory =>
            discountedRewardSum (Action := Action) (Percept := Percept) γ t (trajTail traj) := by
        exact ih.comp (measurable_trajTail (Action := Action) (Percept := Percept))
      have h_mul :
          Measurable fun traj : Trajectory =>
            γ.val * discountedRewardSum (Action := Action) (Percept := Percept) γ t (trajTail traj) := by
        simpa using (measurable_const.mul h_tail)
      simpa [discountedRewardSum] using h_reward.add h_mul

omit [Fintype Action] [Fintype Percept] in
theorem measurable_discountedRewardSumFrom (γ : DiscountFactor) (k t : ℕ) :
    Measurable (discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t) := by
  simpa [discountedRewardSumFrom] using
    (measurable_discountedRewardSum (Action := Action) (Percept := Percept) γ t).comp
      (measurable_trajShift (Action := Action) (Percept := Percept) (k := k))

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSumFrom_zero (γ : DiscountFactor) (k : ℕ) (traj : Trajectory) :
    discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k 0 traj = 0 := by
  simp [discountedRewardSumFrom, discountedRewardSum]

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSum_zero (γ : DiscountFactor) (traj : Trajectory) :
    discountedRewardSum (Action := Action) (Percept := Percept) γ 0 traj = 0 := rfl

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSum_succ (γ : DiscountFactor) (t : ℕ) (traj : Trajectory) :
    discountedRewardSum (Action := Action) (Percept := Percept) γ (t + 1) traj =
      PerceptReward.reward (traj 0).2 +
        γ.val * discountedRewardSum (Action := Action) (Percept := Percept) γ t (trajTail traj) := rfl

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSumFrom_succ (γ : DiscountFactor) (k t : ℕ) (traj : Trajectory) :
    discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k (t + 1) traj =
      PerceptReward.reward (traj (k)).2 +
        γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj := by
  simp [discountedRewardSumFrom, discountedRewardSum, trajTail_shift, trajShift]

omit [Fintype Action] [Fintype Percept] in
theorem summable_geometric_discount (γ : DiscountFactor) (h_lt : γ.val < 1) :
    Summable (fun n : ℕ => |γ.val ^ n|) := by
  have h := summable_geometric_of_lt_one γ.nonneg h_lt
  simpa [abs_of_nonneg (pow_nonneg γ.nonneg _)] using h

omit [Fintype Action] [Fintype Percept] in
theorem discountedUtilityTrunc_succ_head
    (γ : DiscountFactor) (t : ℕ) (traj : Trajectory) :
    Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
        (Action := Action) (Percept := Percept)
        (fun s : Step => PerceptReward.reward s.2)
        (fun n => γ.val ^ n) (t + 1) traj =
      PerceptReward.reward (traj 0).2 +
        γ.val *
          Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
            (Action := Action) (Percept := Percept)
            (fun s : Step => PerceptReward.reward s.2)
            (fun n => γ.val ^ n) t (trajTail traj) := by
  have h_tail :
      (Finset.range t).sum
          (fun n => (γ.val ^ (n + 1)) * PerceptReward.reward (traj (n + 1)).2) =
        γ.val * (Finset.range t).sum
          (fun n => (γ.val ^ n) * PerceptReward.reward (trajTail traj n).2) := by
    calc
      (Finset.range t).sum
          (fun n => (γ.val ^ (n + 1)) * PerceptReward.reward (traj (n + 1)).2)
          =
        (Finset.range t).sum
          (fun n => γ.val * ((γ.val ^ n) * PerceptReward.reward (traj (n + 1)).2)) := by
          simp [pow_succ, mul_assoc, mul_comm]
      _ = γ.val * (Finset.range t).sum
          (fun n => (γ.val ^ n) * PerceptReward.reward (traj (n + 1)).2) := by
          symm
          simp [Finset.mul_sum]
      _ = γ.val * (Finset.range t).sum
          (fun n => (γ.val ^ n) * PerceptReward.reward (trajTail traj n).2) := by
          have h_traj :
              (fun n => (γ.val ^ n) * PerceptReward.reward (traj (n + 1)).2) =
                (fun n => (γ.val ^ n) * PerceptReward.reward (trajTail traj n).2) := by
            funext n
            have h_tail : trajTail traj n = traj (n + 1) := by
              dsimp [trajTail, trajShift]
              exact congrArg traj (Nat.add_comm 1 n)
            rw [h_tail]
          simp [h_traj]
  have h_head :
      PerceptReward.reward (traj 0).2 +
          γ.val *
            (Finset.range t).sum
              (fun n => (γ.val ^ n) * PerceptReward.reward (trajTail traj n).2) =
        γ.val *
            (Finset.range t).sum
              (fun n => (γ.val ^ n) * PerceptReward.reward (trajTail traj n).2) +
          PerceptReward.reward (traj 0).2 := by
    simp [add_comm]
  simp [Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc, Finset.sum_range_succ',
    h_tail, h_head]

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSumFrom_eq_discountedUtilityTrunc
    (γ : DiscountFactor) (k t : ℕ) (traj : Trajectory) :
    discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t traj =
      Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
        (Action := Action) (Percept := Percept)
        (fun s : Step => PerceptReward.reward s.2)
        (fun n => γ.val ^ n) t (trajShift k traj) := by
  induction t generalizing k with
  | zero =>
      simp [discountedRewardSumFrom, discountedRewardSum,
        Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc_zero]
  | succ t ih =>
      have h_tail :
          Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
              (Action := Action) (Percept := Percept)
              (fun s : Step => PerceptReward.reward s.2)
              (fun n => γ.val ^ n) t (trajTail (trajShift k traj)) =
            Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
              (Action := Action) (Percept := Percept)
              (fun s : Step => PerceptReward.reward s.2)
              (fun n => γ.val ^ n) t (trajShift (k + 1) traj) := by
        simp [trajTail_shift]
      calc
        discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k (t + 1) traj
            =
          PerceptReward.reward (traj k).2 +
            γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj := by
              simpa using
                (discountedRewardSumFrom_succ (Action := Action) (Percept := Percept)
                  (γ := γ) (k := k) (t := t) (traj := traj))
        _ =
          PerceptReward.reward ((trajShift k traj) 0).2 +
            γ.val *
              Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
                (Action := Action) (Percept := Percept)
                (fun s : Step => PerceptReward.reward s.2)
                (fun n => γ.val ^ n) t (trajShift (k + 1) traj) := by
              simp [trajShift, ih (k + 1)]
        _ =
          Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
            (Action := Action) (Percept := Percept)
            (fun s : Step => PerceptReward.reward s.2)
            (fun n => γ.val ^ n) (t + 1) (trajShift k traj) := by
              have h :=
                discountedUtilityTrunc_succ_head (Action := Action) (Percept := Percept)
                  (γ := γ) (t := t) (traj := trajShift k traj)
              simpa [h_tail] using h.symm

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSum_eq_discountedUtilityTrunc
    (γ : DiscountFactor) (t : ℕ) (traj : Trajectory) :
    discountedRewardSum (Action := Action) (Percept := Percept) γ t traj =
      Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
        (Action := Action) (Percept := Percept)
        (fun s : Step => PerceptReward.reward s.2)
        (fun n => γ.val ^ n) t traj := by
  have h :=
    discountedRewardSumFrom_eq_discountedUtilityTrunc
      (Action := Action) (Percept := Percept) (γ := γ) (k := 0) (t := t) (traj := traj)
  simpa [discountedRewardSumFrom,
    trajShift_zero (Action := Action) (Percept := Percept)] using h

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSumFrom_nonneg (γ : DiscountFactor) (k t : ℕ) (traj : Trajectory) :
    0 ≤ discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t traj := by
  induction t generalizing k with
  | zero =>
      simp [discountedRewardSumFrom, discountedRewardSum]
  | succ t ih =>
      have h_reward : 0 ≤ PerceptReward.reward (traj k).2 := PerceptReward.nonneg _
      have h_gamma : 0 ≤ γ.val := γ.nonneg
      have h_tail : 0 ≤ discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj :=
        ih (k + 1)
      have h_mul : 0 ≤ γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj :=
        mul_nonneg h_gamma h_tail
      simpa [discountedRewardSumFrom_succ] using add_nonneg h_reward h_mul

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSumFrom_le (γ : DiscountFactor) (k t : ℕ) (traj : Trajectory) :
    discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t traj ≤ (t : ℝ) := by
  induction t generalizing k with
  | zero =>
      simp [discountedRewardSumFrom, discountedRewardSum]
  | succ t ih =>
      have h_reward : PerceptReward.reward (traj k).2 ≤ 1 := PerceptReward.le_one _
      have h_gamma : γ.val ≤ 1 := γ.le_one
      have h_nonneg :
          0 ≤ discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj := by
        simpa using
          (discountedRewardSumFrom_nonneg (Action := Action) (Percept := Percept) γ (k + 1) t traj)
      have h_mul :
          γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj ≤
            (t : ℝ) := by
        have h_le_tail :
            discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj ≤ (t : ℝ) :=
          ih (k + 1)
        have h1 :
            γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj ≤
              1 * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj := by
          exact mul_le_mul_of_nonneg_right h_gamma h_nonneg
        have h2 :
            1 * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj ≤
              1 * (t : ℝ) := by
          exact mul_le_mul_of_nonneg_left h_le_tail (by exact (show 0 ≤ (1 : ℝ) from zero_le_one))
        simpa [one_mul] using h1.trans h2
      have h_sum :
          PerceptReward.reward (traj k).2 +
              γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj ≤
            1 + (t : ℝ) := by
        exact add_le_add h_reward h_mul
      have h_sum' :
          PerceptReward.reward (traj k).2 +
              γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (k + 1) t traj ≤
            (t + 1 : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using h_sum
      simpa [discountedRewardSumFrom_succ, Nat.cast_add, Nat.cast_one] using h_sum'

omit [Fintype Action] [Fintype Percept] in
theorem discountedRewardSumFrom_norm_le (γ : DiscountFactor) (k t : ℕ) (traj : Trajectory) :
    ‖discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t traj‖ ≤ (t : ℝ) := by
  have h_nonneg :
      0 ≤ discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t traj := by
    simpa using
      (discountedRewardSumFrom_nonneg (Action := Action) (Percept := Percept) γ k t traj)
  have h_le :
      discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t traj ≤ (t : ℝ) :=
    discountedRewardSumFrom_le (Action := Action) (Percept := Percept) γ k t traj
  simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_le

theorem discountedRewardSumFrom_integrable
    (μ : Environment Action Percept) (π : Agent Action Percept)
    (a k t : ℕ) (pref : Prefix a)
    [hκ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n)]
    (γ : DiscountFactor) :
    MeasureTheory.Integrable
      (discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t)
      ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
        (κ := transitionKernelWithPolicy μ π) a) pref) := by
  have h_meas :
      Measurable (discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t) :=
    measurable_discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t
  have h_bound :
      ∀ᵐ traj ∂((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
        (κ := transitionKernelWithPolicy μ π) a) pref),
        ‖discountedRewardSumFrom (Action := Action) (Percept := Percept) γ k t traj‖ ≤ (t : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro traj
    exact discountedRewardSumFrom_norm_le (Action := Action) (Percept := Percept) γ k t traj
  haveI :
      MeasureTheory.IsFiniteMeasure
        ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) a) pref) := by
    refine ⟨?_⟩
    simp [ENNReal.one_lt_top]
  exact MeasureTheory.Integrable.of_bound (h_meas.aestronglyMeasurable) (t : ℝ) h_bound

omit [Fintype Action] [Fintype Percept] in
theorem reward_from_prefix (a : ℕ) (traj : Trajectory) :
    PerceptReward.reward (traj (a + 1)).2 =
      PerceptReward.reward
        ((frestrictLe (π := StepFamily) (a + 1) traj) ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2 := by
  simp [frestrictLe_apply]

noncomputable def valueFromMeasure
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) (t : ℕ) : ℝ :=
  Mettapedia.UniversalAI.InfiniteHistory.value (Action := Action) (Percept := Percept)
    (environmentMeasureWithPolicy μ π h_stoch)
    (discountedRewardSum (Action := Action) (Percept := Percept) γ t)

noncomputable def valueFromMeasureInf
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) : ℝ :=
  Mettapedia.UniversalAI.InfiniteHistory.value (Action := Action) (Percept := Percept)
    (environmentMeasureWithPolicy μ π h_stoch)
    (Mettapedia.UniversalAI.InfiniteHistory.discountedUtility
      (Action := Action) (Percept := Percept)
      (fun s : Step => PerceptReward.reward s.2)
      (fun n => γ.val ^ n))

omit [Fintype Action] [Fintype Percept] in
theorem measurable_reward_step :
    Measurable fun s : Step => PerceptReward.reward s.2 := by
  have h_reward : Measurable (fun p : Percept => PerceptReward.reward p) := by
    simpa using
      (measurable_from_top (β := ℝ) (f := fun p : Percept => PerceptReward.reward p))
  exact h_reward.comp measurable_snd

omit [Fintype Action] [Fintype Percept] in
theorem reward_step_abs_le_one (s : Step) :
    |PerceptReward.reward s.2| ≤ (1 : ℝ) := by
  have h_nonneg : 0 ≤ PerceptReward.reward s.2 := PerceptReward.nonneg _
  have h_le : PerceptReward.reward s.2 ≤ 1 := PerceptReward.le_one _
  simpa [abs_of_nonneg h_nonneg] using h_le

noncomputable def valueFromPrefix
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) (a t : ℕ) (pref : Prefix a) : ℝ :=
  let _ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n) :=
    fun n => transitionKernelWithPolicy_isMarkov μ π n h_stoch
  MeasureTheory.integral
    ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
        (κ := transitionKernelWithPolicy μ π) a) pref)
    (discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 1) t)

theorem valueFromPrefix_eq_discountedUtilityTrunc
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) (a t : ℕ) (pref : Prefix a)
    [hκ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n)] :
    valueFromPrefix (Action := Action) (Percept := Percept) μ π γ h_stoch a t pref =
      ∫ traj,
        Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
          (Action := Action) (Percept := Percept)
          (fun s : Step => PerceptReward.reward s.2)
          (fun n => γ.val ^ n) t (trajShift (Action := Action) (Percept := Percept) (a + 1) traj) ∂
        (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) a) pref := by
  dsimp [valueFromPrefix]
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro traj
  simp [discountedRewardSumFrom_eq_discountedUtilityTrunc]

theorem valueFromMeasure_eq_discountedUtilityTrunc
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) (t : ℕ) :
    valueFromMeasure (Action := Action) (Percept := Percept) μ π γ h_stoch t =
      ∫ traj,
        Mettapedia.UniversalAI.InfiniteHistory.discountedUtilityTrunc
          (Action := Action) (Percept := Percept)
          (fun s : Step => PerceptReward.reward s.2)
          (fun n => γ.val ^ n) t traj ∂
        environmentMeasureWithPolicy μ π h_stoch := by
  simp [valueFromMeasure, Mettapedia.UniversalAI.InfiniteHistory.value]
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro traj
  simp [discountedRewardSum_eq_discountedUtilityTrunc]

theorem tendsto_valueFromMeasure
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) (h_lt : γ.val < 1) :
    Filter.Tendsto
        (fun t => valueFromMeasure (Action := Action) (Percept := Percept) μ π γ h_stoch t)
        Filter.atTop
        (nhds (valueFromMeasureInf (Action := Action) (Percept := Percept) μ π γ h_stoch)) := by
  haveI : MeasureTheory.IsProbabilityMeasure (environmentMeasureWithPolicy μ π h_stoch) :=
    environmentMeasureWithPolicy_isProbability μ π h_stoch
  haveI : MeasureTheory.IsFiniteMeasure (environmentMeasureWithPolicy μ π h_stoch) :=
    by infer_instance
  have h_tendsto :=
    Mettapedia.UniversalAI.InfiniteHistory.tendsto_integral_discountedUtilityTrunc
      (Action := Action) (Percept := Percept)
      (reward := fun s : Step => PerceptReward.reward s.2)
      (w := fun n => γ.val ^ n) (R := 1)
      (h_reward := measurable_reward_step (Action := Action) (Percept := Percept))
      (h_reward_bound := reward_step_abs_le_one (Action := Action) (Percept := Percept))
      (h_R_nonneg := by simp)
      (hw := summable_geometric_discount γ h_lt)
      (μ := environmentMeasureWithPolicy μ π h_stoch)
  simpa [valueFromMeasure_eq_discountedUtilityTrunc, valueFromMeasureInf,
    Mettapedia.UniversalAI.InfiniteHistory.value] using h_tendsto

omit [PerceptReward Percept] in
theorem integral_trajKernelOf_succ
    (μ : Environment Action Percept) (π : Agent Action Percept)
    (a : ℕ) (pref : Prefix a)
    [hκ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n)]
    {f : Trajectory → ℝ}
    (hf : MeasureTheory.Integrable f
      ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
        (κ := transitionKernelWithPolicy μ π) a) pref)) :
    ∫ x, f x ∂
        (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) a) pref =
      ∫ x, ∫ y, f y ∂
        (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) (a + 1)) x
        ∂ (ProbabilityTheory.Kernel.partialTraj (transitionKernelWithPolicy μ π) a (a + 1) pref) := by
  have hf' :
      MeasureTheory.Integrable f
        (ProbabilityTheory.Kernel.traj (κ := transitionKernelWithPolicy μ π) a pref) := by
    simpa [Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf_eq] using hf
  have h :=
    (ProbabilityTheory.Kernel.integral_traj_partialTraj
      (κ := transitionKernelWithPolicy μ π) (a := a) (b := a + 1) (x₀ := pref)
      (hab := Nat.le_succ a) (f := f) hf')
  simpa [Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf_eq] using h.symm

omit [PerceptReward Percept] in
theorem trajKernelOf_map_frestrictLe_self
    (μ : Environment Action Percept) (π : Agent Action Percept) (a : ℕ) (pref : Prefix a)
    [hκ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n)] :
    (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
        (κ := transitionKernelWithPolicy μ π) a pref).map
      (frestrictLe (π := StepFamily) a) = MeasureTheory.Measure.dirac pref := by
  have h_map :=
    (ProbabilityTheory.Kernel.traj_map_frestrictLe_apply
      (κ := transitionKernelWithPolicy μ π) (a := a) (b := a) pref)
  have h_map' :
      (ProbabilityTheory.Kernel.traj (κ := transitionKernelWithPolicy μ π) a pref).map
        (frestrictLe (π := StepFamily) a) =
        ProbabilityTheory.Kernel.id pref := by
    simpa [ProbabilityTheory.Kernel.partialTraj_self] using h_map
  simpa [Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf_eq,
    ProbabilityTheory.Kernel.id_apply] using h_map'

omit [PerceptReward Percept] in
theorem integral_comp_frestrictLe_trajKernelOf_eq
    (μ : Environment Action Percept) (π : Agent Action Percept)
    (a : ℕ) (pref : PrefixT Action Percept a)
    [hκ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n)]
    {g : PrefixT Action Percept a → ℝ} (hg : Measurable g) :
    ∫ y, g (frestrictLe (π := StepFamily) a y) ∂
        (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) a) pref =
      g pref := by
  have h_map :
      MeasureTheory.Measure.map (frestrictLe (π := StepFamily) a)
          ((ProbabilityTheory.Kernel.traj (κ := transitionKernelWithPolicy μ π) a) pref) =
        MeasureTheory.Measure.dirac pref := by
    simpa [Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf_eq] using
      (trajKernelOf_map_frestrictLe_self (μ := μ) (π := π) (a := a) (pref := pref))
  have h_phi :
      AEMeasurable (frestrictLe (π := StepFamily) a)
        ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) a) pref) :=
    (measurable_frestrictLe (X := StepFamily) a).aemeasurable
  calc
    ∫ y, g (frestrictLe (π := StepFamily) a y) ∂
        (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) a) pref
        = ∫ z, g z ∂ MeasureTheory.Measure.map
            (frestrictLe (π := StepFamily) a)
            ((ProbabilityTheory.Kernel.traj (κ := transitionKernelWithPolicy μ π) a) pref) := by
          symm
          simpa [Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf_eq] using
            (MeasureTheory.integral_map h_phi (hg.aestronglyMeasurable))
    _ = ∫ z, g z ∂ MeasureTheory.Measure.dirac pref := by
          simp [h_map]
    _ = g pref := by
          simp

theorem integral_reward_trajKernelOf
    (μ : Environment Action Percept) (π : Agent Action Percept)
    (a : ℕ) (pref : PrefixT Action Percept (a + 1))
    [hκ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n)] :
    ∫ y, PerceptReward.reward (y (a + 1)).2 ∂
        (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) (a + 1)) pref =
      PerceptReward.reward (pref ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2 := by
  let g : PrefixT Action Percept (a + 1) → ℝ := fun z =>
    PerceptReward.reward (z ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2
  have h_g_meas : Measurable g := by
    simpa [g] using
      (measurable_reward_prefix (Action := Action) (Percept := Percept) (a := a))
  calc
    ∫ y, PerceptReward.reward (y (a + 1)).2 ∂
        (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) (a + 1)) pref
        = ∫ y, g (frestrictLe (π := StepFamily) (a + 1) y) ∂
            (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
              (κ := transitionKernelWithPolicy μ π) (a + 1)) pref := by
          refine MeasureTheory.integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro y
          simp [g, reward_from_prefix (Action := Action) (Percept := Percept) (a := a) (traj := y)]
    _ = g pref := by
          simpa using
            (integral_comp_frestrictLe_trajKernelOf_eq (μ := μ) (π := π)
              (a := a + 1) (pref := pref) (g := g) h_g_meas)
    _ = PerceptReward.reward (pref ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2 := by
          simp [g]

theorem valueFromPrefix_succ
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) (a t : ℕ) (pref : Prefix a) :
    valueFromPrefix (Action := Action) (Percept := Percept) μ π γ h_stoch a (t + 1) pref =
      ∫ x,
          (PerceptReward.reward (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2 +
              γ.val * valueFromPrefix (Action := Action) (Percept := Percept) μ π γ h_stoch (a + 1) t x)
        ∂ ProbabilityTheory.Kernel.partialTraj (transitionKernelWithPolicy μ π) a (a + 1) pref := by
  let _ : ∀ n, ProbabilityTheory.IsMarkovKernel (transitionKernelWithPolicy μ π n) :=
    fun n => transitionKernelWithPolicy_isMarkov μ π n h_stoch
  have h_integrable :
      MeasureTheory.Integrable
        (discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 1) (t + 1))
        ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) a) pref) :=
    discountedRewardSumFrom_integrable (Action := Action) (Percept := Percept)
      μ π a (a + 1) (t + 1) pref γ
  have h_step :=
    integral_trajKernelOf_succ (Action := Action) (Percept := Percept)
      (μ := μ) (π := π) (a := a) (pref := pref)
      (f := discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 1) (t + 1))
      h_integrable
  have h_step' :
      valueFromPrefix (Action := Action) (Percept := Percept) μ π γ h_stoch a (t + 1) pref =
        ∫ x, ∫ y,
            discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 1) (t + 1) y ∂
              (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
                (κ := transitionKernelWithPolicy μ π) (a + 1)) x
          ∂ ProbabilityTheory.Kernel.partialTraj (transitionKernelWithPolicy μ π) a (a + 1) pref := by
    simpa [valueFromPrefix] using h_step
  refine h_step'.trans ?_
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have h_reward_integrable :
      MeasureTheory.Integrable
        (fun y : Trajectory => PerceptReward.reward (y (a + 1)).2)
        ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) (a + 1)) x) := by
    have h_meas :
        Measurable fun y : Trajectory => PerceptReward.reward (y (a + 1)).2 :=
      measurable_reward_at (Action := Action) (Percept := Percept) (k := a + 1)
    have h_bound :
        ∀ᵐ y ∂((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) (a + 1)) x),
          ‖PerceptReward.reward (y (a + 1)).2‖ ≤ (1 : ℝ) := by
      refine Filter.Eventually.of_forall ?_
      intro y
      have h_nonneg : 0 ≤ PerceptReward.reward (y (a + 1)).2 := PerceptReward.nonneg _
      have h_le : PerceptReward.reward (y (a + 1)).2 ≤ 1 := PerceptReward.le_one _
      simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_le
    haveI :
        MeasureTheory.IsFiniteMeasure
          ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
            (κ := transitionKernelWithPolicy μ π) (a + 1)) x) := by
      refine ⟨?_⟩
      simp [ENNReal.one_lt_top]
    exact MeasureTheory.Integrable.of_bound (h_meas.aestronglyMeasurable) 1 h_bound
  have h_tail_integrable :
      MeasureTheory.Integrable
        (discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 2) t)
        ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) (a + 1)) x) :=
    discountedRewardSumFrom_integrable (Action := Action) (Percept := Percept)
      μ π (a + 1) (a + 2) t x γ
  have h_tail_integrable' :
      MeasureTheory.Integrable
        (fun y : Trajectory =>
          γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 2) t y)
        ((Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
          (κ := transitionKernelWithPolicy μ π) (a + 1)) x) :=
    h_tail_integrable.const_mul γ.val
  calc
    ∫ y,
        discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 1) (t + 1) y ∂
          (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
            (κ := transitionKernelWithPolicy μ π) (a + 1)) x
        =
        ∫ y,
            (PerceptReward.reward (y (a + 1)).2 +
              γ.val * discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 2) t y) ∂
              (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
                (κ := transitionKernelWithPolicy μ π) (a + 1)) x := by
          refine MeasureTheory.integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro y
          simp [discountedRewardSumFrom_succ]
    _ =
        (∫ y, PerceptReward.reward (y (a + 1)).2 ∂
          (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
            (κ := transitionKernelWithPolicy μ π) (a + 1)) x) +
        γ.val * ∫ y,
          discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 2) t y ∂
            (Mettapedia.UniversalAI.InfiniteHistory.trajKernelOf (X := StepFamily)
              (κ := transitionKernelWithPolicy μ π) (a + 1)) x := by
          have h_add := MeasureTheory.integral_add h_reward_integrable h_tail_integrable'
          -- pull out the scalar
          simpa [MeasureTheory.integral_const_mul, add_comm, add_left_comm, add_assoc] using h_add
    _ =
        PerceptReward.reward (x ⟨a + 1, mem_Iic.2 (le_rfl)⟩).2 +
          γ.val * valueFromPrefix (Action := Action) (Percept := Percept) μ π γ h_stoch (a + 1) t x := by
          have h_reward :=
            integral_reward_trajKernelOf (Action := Action) (Percept := Percept)
              (μ := μ) (π := π) (a := a) (pref := x)
          simpa [valueFromPrefix, h_reward]

theorem valueFromMeasure_zero
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) :
    valueFromMeasure (Action := Action) (Percept := Percept) μ π γ h_stoch 0 = 0 := by
  simp [valueFromMeasure, discountedRewardSum, Mettapedia.UniversalAI.InfiniteHistory.value]

theorem valueFromPrefix_zero
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (h_stoch : isStochastic μ) (a : ℕ) (pref : Prefix a) :
    valueFromPrefix (Action := Action) (Percept := Percept) μ π γ h_stoch a 0 pref = 0 := by
  have h0 :
      discountedRewardSumFrom (Action := Action) (Percept := Percept) γ (a + 1) 0 =
        fun _ => (0 : ℝ) := by
    funext traj
    simp [discountedRewardSumFrom_zero]
  simp [valueFromPrefix, h0]

theorem coreValue_succ_step_sum
    (μ : Environment Action Percept) (π : Agent Action Percept) (γ : DiscountFactor)
    (a t : ℕ) (pref : Prefix a) :
    value μ π γ (prefixToHistory (Action := Action) (Percept := Percept) a pref) (2 * (t + 1)) =
      ∑ s : Step,
        (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) s.1 *
            μ.prob (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
              [HistElem.act s.1]) s.2).toReal *
          (PerceptReward.reward s.2 +
            γ.val *
              value μ π γ
                (prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
                  (prefixExtend (Action := Action) (Percept := Percept) a pref s))
                (2 * t)) := by
  have h_wf :
      History.wellFormed (Action := Action) (Percept := Percept)
        (prefixToHistory (Action := Action) (Percept := Percept) a pref) :=
    prefixToHistory_wellFormed (Action := Action) (Percept := Percept) a pref
  have h_horizon : 2 * (t + 1) = 2 * t + 2 := by
    simp [Nat.mul_succ]
  calc
    value μ π γ (prefixToHistory (Action := Action) (Percept := Percept) a pref) (2 * (t + 1))
        =
        value μ π γ (prefixToHistory (Action := Action) (Percept := Percept) a pref) (2 * t + 2) := by
          simp [h_horizon]
    _ =
        ∑ a' : Action,
          (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
            qValue μ π γ (prefixToHistory (Action := Action) (Percept := Percept) a pref) a'
              (2 * t + 1) := by
          simp [value_succ, h_wf]
    _ =
        ∑ a' : Action,
          (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
            ∑ p : Percept,
              (μ.prob
                    (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                        [HistElem.act a']) p).toReal *
                (PerceptReward.reward p +
                  γ.val *
                    value μ π γ
                      (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                          [HistElem.act a', HistElem.per p])
                      (2 * t)) := by
          refine Finset.sum_congr rfl ?_
          intro a' _ha'
          have h_wf_act :
              History.wellFormed (Action := Action) (Percept := Percept)
                (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                    [HistElem.act a']) :=
            prefixToHistory_append_act_wellFormed (Action := Action) (Percept := Percept) a pref a'
          simp [qValue_succ, h_wf_act]
    _ =
        ∑ s : Step,
          (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) s.1 *
              μ.prob (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                [HistElem.act s.1]) s.2).toReal *
            (PerceptReward.reward s.2 +
              γ.val *
                value μ π γ
                  (prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
                    (prefixExtend (Action := Action) (Percept := Percept) a pref s))
                  (2 * t)) := by
          classical
          -- Reindex the action/percept sum as a sum over steps.
          have h_rewrite :
              ∑ a' : Action,
                (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                  ∑ p : Percept,
                    (μ.prob
                          (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                              [HistElem.act a']) p).toReal *
                      (PerceptReward.reward p +
                        γ.val *
                          value μ π γ
                            (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                                [HistElem.act a', HistElem.per p])
                            (2 * t)) =
                ∑ a' : Action, ∑ p : Percept,
                  (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                    (μ.prob
                          (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                              [HistElem.act a']) p).toReal *
                      (PerceptReward.reward p +
                        γ.val *
                          value μ π γ
                            (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                                [HistElem.act a', HistElem.per p])
                            (2 * t)) := by
                refine Finset.sum_congr rfl ?_
                intro a' _ha'
                simp [Finset.mul_sum, mul_assoc]
          have h_extend :
              ∑ a' : Action, ∑ p : Percept,
                  (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                    (μ.prob
                          (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                              [HistElem.act a']) p).toReal *
                      (PerceptReward.reward p +
                        γ.val *
                          value μ π γ
                            (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                                [HistElem.act a', HistElem.per p])
                            (2 * t)) =
                ∑ a' : Action, ∑ p : Percept,
                  (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                    (μ.prob
                          (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                              [HistElem.act a']) p).toReal *
                      (PerceptReward.reward p +
                        γ.val *
                          value μ π γ
                            (prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
                              (prefixExtend (Action := Action) (Percept := Percept) a pref (a', p)))
                            (2 * t)) := by
                simp [prefixToHistory_extend]
          -- rewrite to a sum over steps, using the prefix extension lemma
          have h_step :
              ∑ s : Step,
                  (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) s.1 *
                      μ.prob (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                        [HistElem.act s.1]) s.2).toReal *
                    (PerceptReward.reward s.2 +
                      γ.val *
                        value μ π γ
                          (prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
                            (prefixExtend (Action := Action) (Percept := Percept) a pref s))
                          (2 * t)) =
                ∑ a' : Action, ∑ p : Percept,
                  (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                    (μ.prob
                          (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                              [HistElem.act a']) p).toReal *
                      (PerceptReward.reward p +
                        γ.val *
                          value μ π γ
                            (prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
                              (prefixExtend (Action := Action) (Percept := Percept) a pref (a', p)))
                            (2 * t)) := by
                simp [Fintype.sum_prod_type]
          calc
            ∑ a' : Action,
                (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                  ∑ p : Percept,
                    (μ.prob
                          (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                              [HistElem.act a']) p).toReal *
                      (PerceptReward.reward p +
                        γ.val *
                          value μ π γ
                            (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                                [HistElem.act a', HistElem.per p])
                            (2 * t))
                = ∑ a' : Action, ∑ p : Percept,
                    (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                      (μ.prob
                            (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                                [HistElem.act a']) p).toReal *
                        (PerceptReward.reward p +
                          γ.val *
                            value μ π γ
                              (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                                  [HistElem.act a', HistElem.per p])
                              (2 * t)) := h_rewrite
            _ = ∑ a' : Action, ∑ p : Percept,
                  (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) a').toReal *
                    (μ.prob
                          (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                              [HistElem.act a']) p).toReal *
                      (PerceptReward.reward p +
                        γ.val *
                          value μ π γ
                            (prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
                              (prefixExtend (Action := Action) (Percept := Percept) a pref (a', p)))
                            (2 * t)) := h_extend
            _ = ∑ s : Step,
                  (π.policy (prefixToHistory (Action := Action) (Percept := Percept) a pref) s.1 *
                      μ.prob (prefixToHistory (Action := Action) (Percept := Percept) a pref ++
                        [HistElem.act s.1]) s.2).toReal *
                    (PerceptReward.reward s.2 +
                      γ.val *
                        value μ π γ
                          (prefixToHistory (Action := Action) (Percept := Percept) (a + 1)
                            (prefixExtend (Action := Action) (Percept := Percept) a pref s))
                          (2 * t)) := h_step.symm

end FiniteHorizonUtility

end InfiniteHistoryCompat

end Mettapedia.UniversalAI.BayesianAgents.Core
