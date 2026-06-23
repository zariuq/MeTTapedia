import Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal
import Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
import Mettapedia.UniversalAI.TimeBoundedAIXI.Core

/-!
# Controlled Finite HMM Planning Examples

This file gives small finite-horizon `value`/`qValue` examples for the
controlled-HMM environment bridge.

Positive example:
* a chosen action can deterministically steer the next observation and thus the
  immediate reward.

Negative example:
* these examples only exercise one-step control and a tiny deterministic model;
  they are not a full POMDP planning theory.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovPlanningExamples

open Mettapedia.Logic.ControlledFiniteHiddenMarkovModel
open Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal
open Mettapedia.UniversalAI.BayesianAgents.Core
open Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge

open scoped ENNReal

/-- Tiny local Dirac helper for finite planning examples. -/
private def diracPM {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) : MeasureTheory.ProbabilityMeasure α :=
  ⟨MeasureTheory.Measure.dirac a, MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

@[simp] theorem diracPM_apply_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α]
    (a b : α) :
    diracPM a ({b} : Set α) = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h
    simp [diracPM]
  · simp [diracPM, h]

@[simp] theorem singleton_indicator_one_toNNReal
    {α : Type*} [DecidableEq α] (a b : α) :
    (((Set.singleton a).indicator (1 : α → ENNReal)) b).toNNReal = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h
    have hb : b ∈ Set.singleton b := Set.mem_singleton b
    have hind : (((Set.singleton b).indicator (1 : α → ENNReal)) b) = 1 := by
      rw [Set.indicator_of_mem hb]
      simp
    simp [hind]
  · have hb : b ∉ Set.singleton a := by
        intro hb
        exact h (Set.mem_singleton_iff.mp hb)
    have hind : (((Set.singleton a).indicator (1 : α → ENNReal)) b) = 0 := by
      rw [Set.indicator_of_notMem hb]
    simp [h, hind]

/-- Reward the percept `1` and give reward `0` to percept `0`. -/
instance : PerceptReward (Fin 2) where
  reward := fun y => if y = 1 then 1 else 0
  reward_nonneg := by
    intro y
    by_cases hy : y = 1 <;> simp [hy]
  reward_le_one := by
    intro y
    by_cases hy : y = 1 <;> simp [hy]

/-- Undiscounted finite-horizon examples. -/
noncomputable def gammaOne : DiscountFactor := ⟨1, by simp, by simp⟩

/-- Action `0` steers to latent state `0`, action `1` steers to latent state
`1`, and each latent state emits its matching observation deterministically. -/
noncomputable def controlledSwitchHMM : ControlledFiniteHMMParam (Fin 2) 2 2 where
  init := diracPM 0
  trans := fun a _ =>
    if a = 0 then diracPM 0 else diracPM 1
  emission := fun
    | 0 => diracPM 0
    | 1 => diracPM 1

noncomputable def controlledSwitchEnv : Environment (Fin 2) (Fin 2) :=
  toEnvironment controlledSwitchHMM

noncomputable def chooseOneAgent : Agent (Fin 2) (Fin 2) :=
  Mettapedia.UniversalAI.TimeBoundedAIXI.Core.deterministicAgent (fun _ => (1 : Fin 2))

@[simp] theorem controlledSwitchEnv_prob_act0_obs0 :
    controlledSwitchEnv.prob [HistElem.act 0] 0 = 1 := by
  calc
    controlledSwitchEnv.prob [HistElem.act 0] 0
      = observationMassGivenAction controlledSwitchHMM (filteringMass controlledSwitchHMM []) 0 0 := by
          simpa [controlledSwitchEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := controlledSwitchHMM) (zs := []) (a := 0) (y := 0))
    _ = 1 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
          simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem controlledSwitchEnv_prob_act0_obs1 :
    controlledSwitchEnv.prob [HistElem.act 0] 1 = 0 := by
  calc
    controlledSwitchEnv.prob [HistElem.act 0] 1
      = observationMassGivenAction controlledSwitchHMM (filteringMass controlledSwitchHMM []) 0 1 := by
          simpa [controlledSwitchEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := controlledSwitchHMM) (zs := []) (a := 0) (y := 1))
    _ = 0 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
          simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem controlledSwitchEnv_prob_act1_obs0 :
    controlledSwitchEnv.prob [HistElem.act 1] 0 = 0 := by
  calc
    controlledSwitchEnv.prob [HistElem.act 1] 0
      = observationMassGivenAction controlledSwitchHMM (filteringMass controlledSwitchHMM []) 1 0 := by
          simpa [controlledSwitchEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := controlledSwitchHMM) (zs := []) (a := 1) (y := 0))
    _ = 0 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
          simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem controlledSwitchEnv_prob_act1_obs1 :
    controlledSwitchEnv.prob [HistElem.act 1] 1 = 1 := by
  calc
    controlledSwitchEnv.prob [HistElem.act 1] 1
      = observationMassGivenAction controlledSwitchHMM (filteringMass controlledSwitchHMM []) 1 1 := by
          simpa [controlledSwitchEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := controlledSwitchHMM) (zs := []) (a := 1) (y := 1))
    _ = 1 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
          simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM]

/-- Positive example: action `1` has immediate `qValue = 1` because it
deterministically yields the rewarding percept. -/
theorem controlledSwitch_qValue_act1 :
    qValue controlledSwitchEnv chooseOneAgent gammaOne [] 1 1 = 1 := by
  rw [qValue_succ]
  simp [History.wellFormed, gammaOne, chooseOneAgent, value_zero]
  change (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) = 1
  simp

/-- Negative example: action `0` has immediate `qValue = 0` because it
deterministically yields the non-rewarding percept. -/
theorem controlledSwitch_qValue_act0 :
    qValue controlledSwitchEnv chooseOneAgent gammaOne [] 0 1 = 0 := by
  rw [qValue_succ]
  simp [History.wellFormed, gammaOne, chooseOneAgent, value_zero]
  change (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) = 0
  simp

/-- Positive example: the policy-independent optimal Q-value also assigns value
`1` to action `1` at the empty history. -/
theorem controlledSwitch_optimalQValue_act1 :
    optimalQValue controlledSwitchEnv gammaOne [] 1 1 = 1 := by
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, optimalValue_zero]
  change (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) = 1
  simp

/-- Negative example: the policy-independent optimal Q-value assigns value `0`
to action `0` at the empty history. -/
theorem controlledSwitch_optimalQValue_act0 :
    optimalQValue controlledSwitchEnv gammaOne [] 0 1 = 0 := by
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, optimalValue_zero]
  change (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) = 0
  simp

/-- The chosen action `1` is already optimal for the one-step problem. -/
theorem controlledSwitch_qValue_eq_optimalQValue_act1 :
    qValue controlledSwitchEnv chooseOneAgent gammaOne [] 1 1 =
      optimalQValue controlledSwitchEnv gammaOne [] 1 1 := by
  rw [controlledSwitch_qValue_act1, controlledSwitch_optimalQValue_act1]

/-- At horizon `2`, the optimal value at the empty history is `1`: the first
rewarding step can be secured, and the remaining horizon contributes `0`
because `optimalQValue _ _ _ _ 0 = 0`. -/
theorem controlledSwitch_optimalValue_two :
    optimalValue controlledSwitchEnv gammaOne [] 2 = 1 := by
  rw [optimalValue_succ]
  simp [History.wellFormed]
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [controlledSwitch_optimalQValue_act0, controlledSwitch_optimalQValue_act1]
  · simp

/-- The deterministic policy choosing action `1` is therefore optimal at horizon
`2` on the empty history. -/
theorem controlledSwitch_value_two_eq_optimalValue :
    value controlledSwitchEnv chooseOneAgent gammaOne [] 2 =
      optimalValue controlledSwitchEnv gammaOne [] 2 := by
  rw [controlledSwitch_optimalValue_two]
  have hwf : History.wellFormed (Action := Fin 2) (Percept := Fin 2) [] := by
    simp [History.wellFormed]
  calc
    value controlledSwitchEnv chooseOneAgent gammaOne [] 2
      = qValue controlledSwitchEnv chooseOneAgent gammaOne [] 1 1 := by
          simpa [chooseOneAgent] using
            (Mettapedia.UniversalAI.TimeBoundedAIXI.Core.value_deterministicAgent_succ
              (μ := controlledSwitchEnv) (γ := gammaOne) (act := fun _ => (1 : Fin 2))
              (h := ([] : History (Fin 2) (Fin 2))) (n := 1) hwf)
    _ = 1 := controlledSwitch_qValue_act1

/-- The maximizing action chosen by `optimalAction` is the rewarding action `1`
for the one-step problem. -/
theorem controlledSwitch_optimalAction_one :
    optimalAction controlledSwitchEnv gammaOne [] 1 = 1 := by
  by_contra hne
  let oa : Fin 2 := optimalAction controlledSwitchEnv gammaOne [] 1
  have hoa : oa = optimalAction controlledSwitchEnv gammaOne [] 1 := rfl
  have hone : oa ≠ 1 := by
    simpa [hoa] using hne
  have hzero : oa = 0 := by
    rcases Fin.eq_zero_or_eq_succ oa with h0 | ⟨j, hj⟩
    · exact h0
    · fin_cases j
      exact False.elim (hone (by simpa using hj))
  have hmax :=
    optimalAction_achieves_max
      (μ := controlledSwitchEnv) (γ := gammaOne) (h := ([] : History (Fin 2) (Fin 2)))
      (horizon := 1) (a := (1 : Fin 2))
  rw [← hoa, hzero, controlledSwitch_optimalQValue_act1, controlledSwitch_optimalQValue_act0] at hmax
  linarith

@[simp] theorem controlledSwitch_oneStepQValue_after11_act0 :
    oneStepQValue controlledSwitchHMM [(1, 1)] 0 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := Set.mem_singleton (0 : Fin 2)
  have h01 : (0 : Fin 2) ∉ Set.singleton (1 : Fin 2) := by
    intro h
    have h' : (0 : Fin 2) = (1 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    intro h
    have h' : (1 : Fin 2) = (0 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h11 : (1 : Fin 2) ∈ Set.singleton (1 : Fin 2) := Set.mem_singleton (1 : Fin 2)
  simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM, filteringMassAux,
    Set.indicator, PerceptReward.reward, h00, h01, h10, h11]

@[simp] theorem controlledSwitch_oneStepQValue_after11_act1 :
    oneStepQValue controlledSwitchHMM [(1, 1)] 1 = 1 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := Set.mem_singleton (0 : Fin 2)
  have h01 : (0 : Fin 2) ∉ Set.singleton (1 : Fin 2) := by
    intro h
    have h' : (0 : Fin 2) = (1 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    intro h
    have h' : (1 : Fin 2) = (0 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h11 : (1 : Fin 2) ∈ Set.singleton (1 : Fin 2) := Set.mem_singleton (1 : Fin 2)
  simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM, filteringMassAux,
    Set.indicator, PerceptReward.reward, h00, h01, h10, h11]

@[simp] theorem controlledSwitch_oneStepQValue_after00_act0 :
    oneStepQValue controlledSwitchHMM [(0, 0)] 0 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := Set.mem_singleton (0 : Fin 2)
  have h01 : (0 : Fin 2) ∉ Set.singleton (1 : Fin 2) := by
    intro h
    have h' : (0 : Fin 2) = (1 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    intro h
    have h' : (1 : Fin 2) = (0 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h11 : (1 : Fin 2) ∈ Set.singleton (1 : Fin 2) := Set.mem_singleton (1 : Fin 2)
  simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM, filteringMassAux,
    Set.indicator, PerceptReward.reward, h00, h01, h10, h11]

@[simp] theorem controlledSwitch_oneStepQValue_after00_act1 :
    oneStepQValue controlledSwitchHMM [(0, 0)] 1 = 1 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := Set.mem_singleton (0 : Fin 2)
  have h01 : (0 : Fin 2) ∉ Set.singleton (1 : Fin 2) := by
    intro h
    have h' : (0 : Fin 2) = (1 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    intro h
    have h' : (1 : Fin 2) = (0 : Fin 2) := Set.mem_singleton_iff.mp h
    norm_num at h'
  have h11 : (1 : Fin 2) ∈ Set.singleton (1 : Fin 2) := Set.mem_singleton (1 : Fin 2)
  simp [controlledSwitchHMM, stepProb, emissionProb, initProb, diracPM, filteringMassAux,
    Set.indicator, PerceptReward.reward, h00, h01, h10, h11]

@[simp] theorem controlledSwitch_oneStepOptimalValue_after11 :
    oneStepOptimalValue controlledSwitchHMM [(1, 1)] = 1 := by
  unfold oneStepOptimalValue
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [controlledSwitch_oneStepQValue_after11_act0, controlledSwitch_oneStepQValue_after11_act1]
  · simp

@[simp] theorem controlledSwitch_oneStepOptimalValue_after00 :
    oneStepOptimalValue controlledSwitchHMM [(0, 0)] = 1 := by
  unfold oneStepOptimalValue
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [controlledSwitch_oneStepQValue_after00_act0, controlledSwitch_oneStepQValue_after00_act1]
  · simp

theorem controlledSwitch_qValue_after11_act1 :
    qValue controlledSwitchEnv chooseOneAgent gammaOne (historyOfCycles [(1, 1)]) 1 1 = 1 := by
  simpa [controlledSwitchEnv] using
    (qValue_historyOfCycles_one_eq_oneStepQValue
      (θ := controlledSwitchHMM) (π := chooseOneAgent) (γ := gammaOne) (zs := [(1, 1)]) (a := 1))

theorem controlledSwitch_value_after11_two :
    value controlledSwitchEnv chooseOneAgent gammaOne (historyOfCycles [(1, 1)]) 2 = 1 := by
  have hwf :
      History.wellFormed (Action := Fin 2) (Percept := Fin 2)
        (historyOfCycles [(1, 1)]) = true := by
    simp [historyOfCycles, History.wellFormed]
  calc
    value controlledSwitchEnv chooseOneAgent gammaOne (historyOfCycles [(1, 1)]) 2
      = qValue controlledSwitchEnv chooseOneAgent gammaOne (historyOfCycles [(1, 1)]) 1 1 := by
          simpa [chooseOneAgent] using
            (Mettapedia.UniversalAI.TimeBoundedAIXI.Core.value_deterministicAgent_succ
              (μ := controlledSwitchEnv) (γ := gammaOne) (act := fun _ => (1 : Fin 2))
              (h := historyOfCycles [(1, 1)]) (n := 1) hwf)
    _ = 1 := controlledSwitch_qValue_after11_act1

theorem controlledSwitch_optimalValue_after11_two :
    optimalValue controlledSwitchEnv gammaOne (historyOfCycles [(1, 1)]) 2 = 1 := by
  simpa [controlledSwitchEnv] using
    (optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
      (θ := controlledSwitchHMM) (γ := gammaOne) (zs := [(1, 1)]))

theorem controlledSwitch_optimalValue_after00_two :
    optimalValue controlledSwitchEnv gammaOne (historyOfCycles [(0, 0)]) 2 = 1 := by
  simpa [controlledSwitchEnv] using
    (optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
      (θ := controlledSwitchHMM) (γ := gammaOne) (zs := [(0, 0)]))

/-- A richer horizon example: with horizon `3` from the Q-node, action `1`
collects two deterministic rewards. -/
theorem controlledSwitch_qValue_act1_three :
    qValue controlledSwitchEnv chooseOneAgent gammaOne [] 1 3 = 2 := by
  have htail :
      value controlledSwitchEnv chooseOneAgent gammaOne [HistElem.act 1, HistElem.per 1] 2 = 1 := by
    simpa [historyOfCycles, gammaOne] using controlledSwitch_value_after11_two
  rw [qValue_succ]
  simp [History.wellFormed, gammaOne, controlledSwitchEnv_prob_act1_obs0,
    controlledSwitchEnv_prob_act1_obs1]
  change PerceptReward.reward 1 +
      value controlledSwitchEnv chooseOneAgent gammaOne [HistElem.act 1, HistElem.per 1] 2 = 2
  rw [htail]
  norm_num [PerceptReward.reward]

/-- The policy-independent optimal Q-value agrees on the same two-step reward
total for action `1`. -/
theorem controlledSwitch_optimalQValue_act1_three :
    optimalQValue controlledSwitchEnv gammaOne [] 1 3 = 2 := by
  have htail :
      optimalValue controlledSwitchEnv gammaOne [HistElem.act 1, HistElem.per 1] 2 = 1 := by
    simpa [historyOfCycles, gammaOne] using controlledSwitch_optimalValue_after11_two
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, controlledSwitchEnv_prob_act1_obs0,
    controlledSwitchEnv_prob_act1_obs1]
  change PerceptReward.reward 1 +
      optimalValue controlledSwitchEnv gammaOne [HistElem.act 1, HistElem.per 1] 2 = 2
  rw [htail]
  norm_num [PerceptReward.reward]

/-- Even the initially non-rewarding action `0` still has horizon-`3`
policy-independent value `1`, because the next step can switch to action `1`. -/
theorem controlledSwitch_optimalQValue_act0_three :
    optimalQValue controlledSwitchEnv gammaOne [] 0 3 = 1 := by
  have htail :
      optimalValue controlledSwitchEnv gammaOne [HistElem.act 0, HistElem.per 0] 2 = 1 := by
    simpa [historyOfCycles, gammaOne] using controlledSwitch_optimalValue_after00_two
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, controlledSwitchEnv_prob_act0_obs0,
    controlledSwitchEnv_prob_act0_obs1]
  change PerceptReward.reward 0 +
      optimalValue controlledSwitchEnv gammaOne [HistElem.act 0, HistElem.per 0] 2 = 1
  rw [htail]
  norm_num [PerceptReward.reward]

/-- At horizon `4`, the optimal value at the empty history is `2`. -/
theorem controlledSwitch_optimalValue_four :
    optimalValue controlledSwitchEnv gammaOne [] 4 = 2 := by
  rw [optimalValue_succ]
  simp [History.wellFormed]
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [controlledSwitch_optimalQValue_act0_three, controlledSwitch_optimalQValue_act1_three]
  · simp

/-- The deterministic policy choosing action `1` remains optimal at horizon `4`
on the empty history. -/
theorem controlledSwitch_value_four_eq_optimalValue :
    value controlledSwitchEnv chooseOneAgent gammaOne [] 4 =
      optimalValue controlledSwitchEnv gammaOne [] 4 := by
  rw [controlledSwitch_optimalValue_four]
  have hwf : History.wellFormed (Action := Fin 2) (Percept := Fin 2) [] := by
    simp [History.wellFormed]
  calc
    value controlledSwitchEnv chooseOneAgent gammaOne [] 4
      = qValue controlledSwitchEnv chooseOneAgent gammaOne [] 1 3 := by
          simpa [chooseOneAgent] using
            (Mettapedia.UniversalAI.TimeBoundedAIXI.Core.value_deterministicAgent_succ
              (μ := controlledSwitchEnv) (γ := gammaOne) (act := fun _ => (1 : Fin 2))
              (h := ([] : History (Fin 2) (Fin 2))) (n := 3) hwf)
    _ = 2 := controlledSwitch_qValue_act1_three

/-! ## Ambiguous controlled family with widened decision interval -/

/-- High-value model: action `1` can sustain rewarding observations, so the
horizon-`4` optimal value is `2`. The extra latent state `2` is inert and only
serves to match the family cardinality. -/
noncomputable def ambiguousHighHMM : ControlledFiniteHMMParam (Fin 2) 3 2 where
  init := diracPM 0
  trans := fun a _ => if a = 0 then diracPM 0 else diracPM 1
  emission := fun
    | 0 => diracPM 0
    | 1 => diracPM 1
    | 2 => diracPM 0

noncomputable def ambiguousHighEnv : Environment (Fin 2) (Fin 2) :=
  toEnvironment ambiguousHighHMM

/-- Low-value model: action `0` gives a single rewarding pulse and then drops
into a dead latent state with only observation `0`. -/
noncomputable def ambiguousLowHMM : ControlledFiniteHMMParam (Fin 2) 3 2 where
  init := diracPM 0
  trans := fun a x =>
    match x with
    | 0 => if a = 0 then diracPM 1 else diracPM 2
    | 1 => diracPM 2
    | 2 => diracPM 2
  emission := fun
    | 0 => diracPM 0
    | 1 => diracPM 1
    | 2 => diracPM 0

noncomputable def ambiguousLowEnv : Environment (Fin 2) (Fin 2) :=
  toEnvironment ambiguousLowHMM

noncomputable def ambiguousControlledFamily : Fin 2 → ControlledFiniteHMMParam (Fin 2) 3 2
  | 0 => ambiguousHighHMM
  | 1 => ambiguousLowHMM

@[simp] theorem ambiguousHighEnv_prob_act0_obs0 :
    ambiguousHighEnv.prob [HistElem.act 0] 0 = 1 := by
  calc
    ambiguousHighEnv.prob [HistElem.act 0] 0
      = observationMassGivenAction ambiguousHighHMM (filteringMass ambiguousHighHMM []) 0 0 := by
          simpa [ambiguousHighEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousHighHMM) (zs := []) (a := 0) (y := 0))
    _ = 1 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousHighEnv_prob_act0_obs1 :
    ambiguousHighEnv.prob [HistElem.act 0] 1 = 0 := by
  calc
    ambiguousHighEnv.prob [HistElem.act 0] 1
      = observationMassGivenAction ambiguousHighHMM (filteringMass ambiguousHighHMM []) 0 1 := by
          simpa [ambiguousHighEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousHighHMM) (zs := []) (a := 0) (y := 1))
    _ = 0 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousHighEnv_prob_act1_obs0 :
    ambiguousHighEnv.prob [HistElem.act 1] 0 = 0 := by
  calc
    ambiguousHighEnv.prob [HistElem.act 1] 0
      = observationMassGivenAction ambiguousHighHMM (filteringMass ambiguousHighHMM []) 1 0 := by
          simpa [ambiguousHighEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousHighHMM) (zs := []) (a := 1) (y := 0))
    _ = 0 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousHighEnv_prob_act1_obs1 :
    ambiguousHighEnv.prob [HistElem.act 1] 1 = 1 := by
  calc
    ambiguousHighEnv.prob [HistElem.act 1] 1
      = observationMassGivenAction ambiguousHighHMM (filteringMass ambiguousHighHMM []) 1 1 := by
          simpa [ambiguousHighEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousHighHMM) (zs := []) (a := 1) (y := 1))
    _ = 1 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousLowEnv_prob_act0_obs0 :
    ambiguousLowEnv.prob [HistElem.act 0] 0 = 0 := by
  calc
    ambiguousLowEnv.prob [HistElem.act 0] 0
      = observationMassGivenAction ambiguousLowHMM (filteringMass ambiguousLowHMM []) 0 0 := by
          simpa [ambiguousLowEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousLowHMM) (zs := []) (a := 0) (y := 0))
    _ = 0 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousLowEnv_prob_act0_obs1 :
    ambiguousLowEnv.prob [HistElem.act 0] 1 = 1 := by
  calc
    ambiguousLowEnv.prob [HistElem.act 0] 1
      = observationMassGivenAction ambiguousLowHMM (filteringMass ambiguousLowHMM []) 0 1 := by
          simpa [ambiguousLowEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousLowHMM) (zs := []) (a := 0) (y := 1))
    _ = 1 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousLowEnv_prob_act1_obs0 :
    ambiguousLowEnv.prob [HistElem.act 1] 0 = 1 := by
  calc
    ambiguousLowEnv.prob [HistElem.act 1] 0
      = observationMassGivenAction ambiguousLowHMM (filteringMass ambiguousLowHMM []) 1 0 := by
          simpa [ambiguousLowEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousLowHMM) (zs := []) (a := 1) (y := 0))
    _ = 1 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousLowEnv_prob_act1_obs1 :
    ambiguousLowEnv.prob [HistElem.act 1] 1 = 0 := by
  calc
    ambiguousLowEnv.prob [HistElem.act 1] 1
      = observationMassGivenAction ambiguousLowHMM (filteringMass ambiguousLowHMM []) 1 1 := by
          simpa [ambiguousLowEnv, toEnvironment, historyOfCycles] using
            (environmentProb_historyOfCycles_append_act (θ := ambiguousLowHMM) (zs := []) (a := 1) (y := 1))
    _ = 0 := by
          unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
            filteringStepMass predictiveLatentMass
          repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
          simp [ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM]

@[simp] theorem ambiguousHigh_oneStepQValue_after11_act0 :
    oneStepQValue ambiguousHighHMM [(1, 1)] 0 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM, PerceptReward.reward]

@[simp] theorem ambiguousHigh_oneStepQValue_after11_act1 :
    oneStepQValue ambiguousHighHMM [(1, 1)] 1 = 1 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [filteringMassAux, ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM,
    PerceptReward.reward]
  rw [Fin.sum_univ_three]
  simp

@[simp] theorem ambiguousHigh_oneStepQValue_after00_act0 :
    oneStepQValue ambiguousHighHMM [(0, 0)] 0 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM, PerceptReward.reward]

@[simp] theorem ambiguousHigh_oneStepQValue_after00_act1 :
    oneStepQValue ambiguousHighHMM [(0, 0)] 1 = 1 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [filteringMassAux, ambiguousHighHMM, stepProb, emissionProb, initProb, diracPM,
    PerceptReward.reward]
  rw [Fin.sum_univ_three]
  simp

@[simp] theorem ambiguousHigh_oneStepOptimalValue_after11 :
    oneStepOptimalValue ambiguousHighHMM [(1, 1)] = 1 := by
  unfold oneStepOptimalValue
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [ambiguousHigh_oneStepQValue_after11_act0, ambiguousHigh_oneStepQValue_after11_act1]
  · simp

@[simp] theorem ambiguousHigh_oneStepOptimalValue_after00 :
    oneStepOptimalValue ambiguousHighHMM [(0, 0)] = 1 := by
  unfold oneStepOptimalValue
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [ambiguousHigh_oneStepQValue_after00_act0, ambiguousHigh_oneStepQValue_after00_act1]
  · simp

theorem ambiguousHigh_optimalValue_after11_two :
    optimalValue ambiguousHighEnv gammaOne (historyOfCycles [(1, 1)]) 2 = 1 := by
  simpa [ambiguousHighEnv] using
    (optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
      (θ := ambiguousHighHMM) (γ := gammaOne) (zs := [(1, 1)]))

theorem ambiguousHigh_optimalValue_after00_two :
    optimalValue ambiguousHighEnv gammaOne (historyOfCycles [(0, 0)]) 2 = 1 := by
  simpa [ambiguousHighEnv] using
    (optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
      (θ := ambiguousHighHMM) (γ := gammaOne) (zs := [(0, 0)]))

theorem ambiguousHigh_optimalQValue_act1_three :
    optimalQValue ambiguousHighEnv gammaOne [] 1 3 = 2 := by
  have htail :
      optimalValue ambiguousHighEnv gammaOne [HistElem.act 1, HistElem.per 1] 2 = 1 := by
    simpa [historyOfCycles, gammaOne] using ambiguousHigh_optimalValue_after11_two
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, ambiguousHighEnv_prob_act1_obs0, ambiguousHighEnv_prob_act1_obs1]
  change PerceptReward.reward (1 : Fin 2) +
      optimalValue ambiguousHighEnv gammaOne [HistElem.act 1, HistElem.per 1] 2 = 2
  rw [htail]
  norm_num [PerceptReward.reward]

theorem ambiguousHigh_optimalQValue_act0_three :
    optimalQValue ambiguousHighEnv gammaOne [] 0 3 = 1 := by
  have htail :
      optimalValue ambiguousHighEnv gammaOne [HistElem.act 0, HistElem.per 0] 2 = 1 := by
    simpa [historyOfCycles, gammaOne] using ambiguousHigh_optimalValue_after00_two
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, ambiguousHighEnv_prob_act0_obs0, ambiguousHighEnv_prob_act0_obs1]
  change PerceptReward.reward (0 : Fin 2) +
      optimalValue ambiguousHighEnv gammaOne [HistElem.act 0, HistElem.per 0] 2 = 1
  rw [htail]
  norm_num [PerceptReward.reward]

theorem ambiguousHigh_optimalValue_four :
    optimalValue ambiguousHighEnv gammaOne [] 4 = 2 := by
  rw [optimalValue_succ]
  simp [History.wellFormed]
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [ambiguousHigh_optimalQValue_act0_three, ambiguousHigh_optimalQValue_act1_three]
  · simp

theorem ambiguousHigh_optimalAction_three :
    optimalAction ambiguousHighEnv gammaOne [] 3 = 1 := by
  by_contra hne
  let oa : Fin 2 := optimalAction ambiguousHighEnv gammaOne [] 3
  have hoa : oa = optimalAction ambiguousHighEnv gammaOne [] 3 := rfl
  have hone : oa ≠ 1 := by
    simpa [hoa] using hne
  have hzero : oa = 0 := by
    rcases Fin.eq_zero_or_eq_succ oa with h0 | ⟨j, hj⟩
    · exact h0
    · fin_cases j
      exact False.elim (hone (by simpa using hj))
  have hmax :=
    optimalAction_achieves_max
      (μ := ambiguousHighEnv) (γ := gammaOne) (h := ([] : History (Fin 2) (Fin 2)))
      (horizon := 3) (a := (1 : Fin 2))
  rw [← hoa, hzero, ambiguousHigh_optimalQValue_act1_three,
    ambiguousHigh_optimalQValue_act0_three] at hmax
  linarith

@[simp] theorem ambiguousLow_oneStepQValue_after01_act0 :
    oneStepQValue ambiguousLowHMM [(0, 1)] 0 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [filteringMassAux, ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM,
    PerceptReward.reward]

@[simp] theorem ambiguousLow_oneStepQValue_after01_act1 :
    oneStepQValue ambiguousLowHMM [(0, 1)] 1 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM, PerceptReward.reward]

@[simp] theorem ambiguousLow_oneStepQValue_after10_act0 :
    oneStepQValue ambiguousLowHMM [(1, 0)] 0 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [filteringMassAux, ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM,
    PerceptReward.reward]
  have hind :
      ((Set.singleton (0 : Fin 3)).indicator (1 : Fin 3 → ENNReal) (2 : Fin 3)) = 0 := by
    have h20 : (2 : Fin 3) ∉ ({(0 : Fin 3)} : Set (Fin 3)) := by
      decide
    change (((Set.singleton (0 : Fin 3)).indicator (1 : Fin 3 → ENNReal) (2 : Fin 3)) = (0 : ENNReal))
    simpa using
      (Set.indicator_of_notMem
        (s := Set.singleton (0 : Fin 3))
        (f := (1 : Fin 3 → ENNReal))
        h20)
  rw [Fin.sum_univ_three]
  simp [hind]

@[simp] theorem ambiguousLow_oneStepQValue_after10_act1 :
    oneStepQValue ambiguousLowHMM [(1, 0)] 1 = 0 := by
  unfold oneStepQValue observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  repeat' (first | rw [Fin.sum_univ_two] | rw [Fin.sum_univ_three])
  simp [ambiguousLowHMM, stepProb, emissionProb, initProb, diracPM, PerceptReward.reward]

@[simp] theorem ambiguousLow_oneStepOptimalValue_after01 :
    oneStepOptimalValue ambiguousLowHMM [(0, 1)] = 0 := by
  unfold oneStepOptimalValue
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [ambiguousLow_oneStepQValue_after01_act0, ambiguousLow_oneStepQValue_after01_act1]
  · simp

@[simp] theorem ambiguousLow_oneStepOptimalValue_after10 :
    oneStepOptimalValue ambiguousLowHMM [(1, 0)] = 0 := by
  unfold oneStepOptimalValue
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [ambiguousLow_oneStepQValue_after10_act0, ambiguousLow_oneStepQValue_after10_act1]
  · simp

theorem ambiguousLow_optimalValue_after01_two :
    optimalValue ambiguousLowEnv gammaOne (historyOfCycles [(0, 1)]) 2 = 0 := by
  simpa [ambiguousLowEnv] using
    (optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
      (θ := ambiguousLowHMM) (γ := gammaOne) (zs := [(0, 1)]))

theorem ambiguousLow_optimalValue_after10_two :
    optimalValue ambiguousLowEnv gammaOne (historyOfCycles [(1, 0)]) 2 = 0 := by
  simpa [ambiguousLowEnv] using
    (optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
      (θ := ambiguousLowHMM) (γ := gammaOne) (zs := [(1, 0)]))

theorem ambiguousLow_optimalQValue_act0_three :
    optimalQValue ambiguousLowEnv gammaOne [] 0 3 = 1 := by
  have htail :
      optimalValue ambiguousLowEnv gammaOne [HistElem.act 0, HistElem.per 1] 2 = 0 := by
    simpa [historyOfCycles, gammaOne] using ambiguousLow_optimalValue_after01_two
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, ambiguousLowEnv_prob_act0_obs0, ambiguousLowEnv_prob_act0_obs1]
  change PerceptReward.reward (1 : Fin 2) +
      optimalValue ambiguousLowEnv gammaOne [HistElem.act 0, HistElem.per 1] 2 = 1
  rw [htail]
  norm_num [PerceptReward.reward]

theorem ambiguousLow_optimalQValue_act1_three :
    optimalQValue ambiguousLowEnv gammaOne [] 1 3 = 0 := by
  have htail :
      optimalValue ambiguousLowEnv gammaOne [HistElem.act 1, HistElem.per 0] 2 = 0 := by
    simpa [historyOfCycles, gammaOne] using ambiguousLow_optimalValue_after10_two
  rw [optimalQValue_succ]
  simp [History.wellFormed, gammaOne, ambiguousLowEnv_prob_act1_obs0, ambiguousLowEnv_prob_act1_obs1]
  change PerceptReward.reward (0 : Fin 2) +
      optimalValue ambiguousLowEnv gammaOne [HistElem.act 1, HistElem.per 0] 2 = 0
  rw [htail]
  norm_num [PerceptReward.reward]

theorem ambiguousLow_optimalValue_four :
    optimalValue ambiguousLowEnv gammaOne [] 4 = 1 := by
  rw [optimalValue_succ]
  simp [History.wellFormed]
  have huniv : (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) := by
    ext a
    fin_cases a <;> simp
  rw [huniv, Finset.fold_insert, Finset.fold_singleton]
  · simp [ambiguousLow_optimalQValue_act0_three, ambiguousLow_optimalQValue_act1_three]
  · simp

theorem ambiguousLow_optimalAction_three :
    optimalAction ambiguousLowEnv gammaOne [] 3 = 0 := by
  by_contra hne
  let oa : Fin 2 := optimalAction ambiguousLowEnv gammaOne [] 3
  have hoa : oa = optimalAction ambiguousLowEnv gammaOne [] 3 := rfl
  have hnotZero : oa ≠ 0 := by
    simpa [hoa] using hne
  have hone : oa = 1 := by
    rcases Fin.eq_zero_or_eq_succ oa with h0 | ⟨j, hj⟩
    · exact False.elim (hnotZero h0)
    · fin_cases j
      simpa using hj
  have hmax :=
    optimalAction_achieves_max
      (μ := ambiguousLowEnv) (γ := gammaOne) (h := ([] : History (Fin 2) (Fin 2)))
      (horizon := 3) (a := (0 : Fin 2))
  rw [← hoa, hone, ambiguousLow_optimalQValue_act0_three,
    ambiguousLow_optimalQValue_act1_three] at hmax
  linarith

theorem ambiguousControlledFamily_recursiveOptimalInterval_nontrivial :
    lowerRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 <
      upperRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 := by
  have hhigh :=
    optimalValue_historyOfCycles_mem_recursiveEnvelope
      (Θ := ambiguousControlledFamily) (γ := gammaOne)
      4 ([] : List (CycleObservation (Fin 2) 2)) (0 : Fin 2)
  have hlow :=
    optimalValue_historyOfCycles_mem_recursiveEnvelope
      (Θ := ambiguousControlledFamily) (γ := gammaOne)
      4 ([] : List (CycleObservation (Fin 2) 2)) (1 : Fin 2)
  have hupper :
      2 ≤ upperRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 := by
    have hhigh_eq :
        optimalValue (toEnvironment (ambiguousControlledFamily 0)) gammaOne
            (historyOfCycles ([] : List (CycleObservation (Fin 2) 2))) 4 = 2 := by
      simpa [ambiguousControlledFamily, ambiguousHighEnv, historyOfCycles, toEnvironment] using
        ambiguousHigh_optimalValue_four
    have hupper' := hhigh.2
    rw [hhigh_eq] at hupper'
    exact hupper'
  have hlower :
      lowerRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 ≤ 1 := by
    have hlow_eq :
        optimalValue (toEnvironment (ambiguousControlledFamily 1)) gammaOne
            (historyOfCycles ([] : List (CycleObservation (Fin 2) 2))) 4 = 1 := by
      simpa [ambiguousControlledFamily, ambiguousLowEnv, historyOfCycles, toEnvironment] using
        ambiguousLow_optimalValue_four
    have hlower' := hlow.1
    rw [hlow_eq] at hlower'
    exact hlower'
  linarith

theorem ambiguousControlledFamily_no_unique_optimalAction_three :
    ¬ ∃ a : Fin 2, ∀ i : Fin 2,
      optimalAction (toEnvironment (ambiguousControlledFamily i)) gammaOne [] 3 = a := by
  intro h
  rcases h with ⟨a, ha⟩
  have hhigh : optimalAction ambiguousHighEnv gammaOne [] 3 = a := by
    simpa [ambiguousControlledFamily, ambiguousHighEnv] using ha (0 : Fin 2)
  have hlow : optimalAction ambiguousLowEnv gammaOne [] 3 = a := by
    simpa [ambiguousControlledFamily, ambiguousLowEnv] using ha (1 : Fin 2)
  rw [ambiguousHigh_optimalAction_three] at hhigh
  rw [ambiguousLow_optimalAction_three] at hlow
  have : (1 : Fin 2) = 0 := hhigh.trans hlow.symm
  norm_num at this

theorem ambiguousControlledFamily_optimalValue_mem_interval_and_no_uniqueAction :
    (∀ i : Fin 2,
        lowerRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 ≤
            optimalValue (toEnvironment (ambiguousControlledFamily i)) gammaOne [] 4 ∧
          optimalValue (toEnvironment (ambiguousControlledFamily i)) gammaOne [] 4 ≤
            upperRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4) ∧
      lowerRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 <
        upperRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 ∧
      ¬ ∃ a : Fin 2, ∀ i : Fin 2,
        optimalAction (toEnvironment (ambiguousControlledFamily i)) gammaOne [] 3 = a := by
  constructor
  · intro i
    simpa [historyOfCycles] using
      (optimalValue_historyOfCycles_mem_recursiveEnvelope
        (Θ := ambiguousControlledFamily) (γ := gammaOne)
        4 ([] : List (CycleObservation (Fin 2) 2)) i)
  · constructor
    · exact ambiguousControlledFamily_recursiveOptimalInterval_nontrivial
    · exact ambiguousControlledFamily_no_unique_optimalAction_three

/-- The deterministic policy choosing action `1` therefore has two-step value
`1` at the empty history. -/
example :
    value controlledSwitchEnv chooseOneAgent gammaOne [] 2 = 1 := by
  have hwf : History.wellFormed (Action := Fin 2) (Percept := Fin 2) [] := by
    simp [History.wellFormed]
  calc
    value controlledSwitchEnv chooseOneAgent gammaOne [] 2
      = qValue controlledSwitchEnv chooseOneAgent gammaOne [] 1 1 := by
          simpa [chooseOneAgent] using
            (Mettapedia.UniversalAI.TimeBoundedAIXI.Core.value_deterministicAgent_succ
              (μ := controlledSwitchEnv) (γ := gammaOne) (act := fun _ => (1 : Fin 2))
              (h := ([] : History (Fin 2) (Fin 2))) (n := 1) hwf)
    _ = 1 := controlledSwitch_qValue_act1

end Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovPlanningExamples
