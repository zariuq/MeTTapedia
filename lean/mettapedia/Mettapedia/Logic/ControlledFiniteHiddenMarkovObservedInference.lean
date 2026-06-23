import Mettapedia.Logic.ControlledFiniteHiddenMarkovModel
import Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge

/-!
# Observed-Only Inference for Controlled Finite Hidden Markov Models

This file gives the first honest observed-only inference layer for
action-conditioned finite HMMs.

Positive example:
* controlled filtering and smoothing masses are normalized exactly.

Negative example:
* this file does not yet add rewards, optimal control, or credal ambiguity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.ControlledFiniteHiddenMarkovObservedInference

open Mettapedia.Logic.ControlledFiniteHiddenMarkovModel
open Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
open scoped BigOperators ENNReal NNReal

universe uA

variable {Action : Type uA} {latent obs : ℕ}

/-- Total observed mass of a completed action-observation trace. -/
def observedCycleProb
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) : ℝ≥0∞ :=
  ∑ x : Fin latent, filteringMass θ zs x

@[simp] theorem observedCycleProb_nil
    (θ : ControlledFiniteHMMParam Action latent obs) :
    observedCycleProb θ [] = 1 := by
  simp [observedCycleProb, filteringMass, filteringMassAux, initialLatentMass, initProb_sum_enn]

theorem observedCycleProb_le_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    observedCycleProb θ zs ≤ 1 := filteringMass_sum_le_one θ zs

theorem observedCycleProb_ne_top
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    observedCycleProb θ zs ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (observedCycleProb_le_one θ zs)

/-- Backward continuation mass from a current latent state along a future
action-observation trace. -/
def backwardMessage
    (θ : ControlledFiniteHMMParam Action latent obs) :
    Fin latent → List (CycleObservation Action obs) → ℝ≥0∞
  | _, [] => 1
  | x, (a, y) :: zs =>
      ∑ x' : Fin latent,
        (stepProb θ a x x' : ℝ≥0∞) *
          (emissionProb θ x' y : ℝ≥0∞) *
            backwardMessage θ x' zs

@[simp] theorem backwardMessage_nil
    (θ : ControlledFiniteHMMParam Action latent obs) (x : Fin latent) :
    backwardMessage θ x [] = 1 := rfl

@[simp] theorem backwardMessage_cons
    (θ : ControlledFiniteHMMParam Action latent obs)
    (x : Fin latent) (a : Action) (y : Fin obs)
    (zs : List (CycleObservation Action obs)) :
    backwardMessage θ x ((a, y) :: zs) =
      ∑ x' : Fin latent,
        (stepProb θ a x x' : ℝ≥0∞) *
          (emissionProb θ x' y : ℝ≥0∞) *
            backwardMessage θ x' zs := rfl

/-- Generic forward/backward factorization from an arbitrary initial latent
mass. -/
theorem filteringMassAux_sum_eq_sum_mul_backward
    (θ : ControlledFiniteHMMParam Action latent obs) :
    ∀ (m : LatentMass latent) (zs : List (CycleObservation Action obs)),
      ∑ x : Fin latent, filteringMassAux θ m zs x =
        ∑ x : Fin latent, m x * backwardMessage θ x zs
  | m, [] => by
      simp [filteringMassAux, backwardMessage]
  | m, (a, y) :: zs => by
      rw [filteringMassAux]
      rw [filteringMassAux_sum_eq_sum_mul_backward θ (filteringStepMass θ m a y) zs]
      unfold filteringStepMass predictiveLatentMass
      calc
        ∑ x' : Fin latent,
            (∑ x : Fin latent, m x * (stepProb θ a x x' : ℝ≥0∞)) *
              (emissionProb θ x' y : ℝ≥0∞) *
                backwardMessage θ x' zs
          =
            ∑ x' : Fin latent,
              ∑ x : Fin latent,
                (m x * (stepProb θ a x x' : ℝ≥0∞)) *
                  ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs) := by
                    refine Finset.sum_congr rfl ?_
                    intro x' hx'
                    calc
                      (∑ x : Fin latent, m x * (stepProb θ a x x' : ℝ≥0∞)) *
                          (emissionProb θ x' y : ℝ≥0∞) *
                            backwardMessage θ x' zs
                        =
                          (∑ x : Fin latent, m x * (stepProb θ a x x' : ℝ≥0∞)) *
                            ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs) := by
                              ac_rfl
                      _ =
                          ∑ x : Fin latent,
                            (m x * (stepProb θ a x x' : ℝ≥0∞)) *
                              ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs) := by
                                rw [Finset.sum_mul]
        _ =
            ∑ x : Fin latent,
              ∑ x' : Fin latent,
                (m x * (stepProb θ a x x' : ℝ≥0∞)) *
                  ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs) := by
                    rw [Finset.sum_comm]
        _ =
            ∑ x : Fin latent,
              m x *
                ∑ x' : Fin latent,
                  (stepProb θ a x x' : ℝ≥0∞) *
                    ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs) := by
                      refine Finset.sum_congr rfl ?_
                      intro x hx
                      calc
                        ∑ x' : Fin latent,
                            (m x * (stepProb θ a x x' : ℝ≥0∞)) *
                              ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs)
                          =
                            ∑ x' : Fin latent,
                              m x *
                                ((stepProb θ a x x' : ℝ≥0∞) *
                                  ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs)) := by
                                    refine Finset.sum_congr rfl ?_
                                    intro x' hx'
                                    ac_rfl
                        _ =
                            m x *
                              ∑ x' : Fin latent,
                                (stepProb θ a x x' : ℝ≥0∞) *
                                  ((emissionProb θ x' y : ℝ≥0∞) * backwardMessage θ x' zs) := by
                                    rw [Finset.mul_sum]
        _ =
            ∑ x : Fin latent, m x * backwardMessage θ x ((a, y) :: zs) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [backwardMessage_cons]
              refine congrArg (fun t => m x * t) ?_
              refine Finset.sum_congr rfl ?_
              intro x' hx'
              ac_rfl

theorem observedCycleProb_eq_sum_init_mul_backward
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    observedCycleProb θ zs =
      ∑ x : Fin latent, initialLatentMass θ x * backwardMessage θ x zs := by
  simpa [observedCycleProb, filteringMass]
    using filteringMassAux_sum_eq_sum_mul_backward θ (initialLatentMass θ) zs

theorem observedCycleProb_append
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs ws : List (CycleObservation Action obs)) :
    observedCycleProb θ (zs ++ ws) =
      ∑ x : Fin latent, filteringMass θ zs x * backwardMessage θ x ws := by
  unfold observedCycleProb
  rw [filteringMass_append]
  exact filteringMassAux_sum_eq_sum_mul_backward θ (filteringMass θ zs) ws

theorem observedCycleProb_append_singleton
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    observedCycleProb θ (zs ++ [(a, y)]) =
      observationMassGivenAction θ (filteringMass θ zs) a y := by
  unfold observedCycleProb observationMassGivenAction
  rw [filteringMass_append_singleton]

/-- Normalized filtering posterior mass after a completed controlled trace. -/
def filteringPosteriorMass
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (x : Fin latent) : ℝ≥0∞ :=
  filteringMass θ zs x / observedCycleProb θ zs

theorem filteringPosteriorMass_sum_eq_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (hobs : observedCycleProb θ zs ≠ 0) :
    ∑ x : Fin latent, filteringPosteriorMass θ zs x = 1 := by
  have htop : observedCycleProb θ zs ≠ ⊤ := observedCycleProb_ne_top θ zs
  unfold filteringPosteriorMass
  calc
    ∑ x : Fin latent, filteringMass θ zs x / observedCycleProb θ zs
      = ∑ x : Fin latent, filteringMass θ zs x * (observedCycleProb θ zs)⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑ x : Fin latent, filteringMass θ zs x) * (observedCycleProb θ zs)⁻¹ := by
          rw [Finset.sum_mul]
    _ = observedCycleProb θ zs * (observedCycleProb θ zs)⁻¹ := by
          rw [observedCycleProb]
    _ = 1 := ENNReal.mul_inv_cancel hobs htop

theorem filteringPosteriorMass_le_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (x : Fin latent) (hobs : observedCycleProb θ zs ≠ 0) :
    filteringPosteriorMass θ zs x ≤ 1 := by
  calc
    filteringPosteriorMass θ zs x ≤ ∑ x' : Fin latent, filteringPosteriorMass θ zs x' := by
      exact Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ x)
    _ = 1 := filteringPosteriorMass_sum_eq_one θ zs hobs

/-- Unnormalized smoothing mass at a split point. -/
def smoothingMass
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs ws : List (CycleObservation Action obs))
    (x : Fin latent) : ℝ≥0∞ :=
  filteringMass θ zs x * backwardMessage θ x ws

theorem smoothingMass_sum_eq_observedCycleProb_append
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs ws : List (CycleObservation Action obs)) :
    ∑ x : Fin latent, smoothingMass θ zs ws x =
      observedCycleProb θ (zs ++ ws) := by
  simpa [smoothingMass] using (observedCycleProb_append θ zs ws).symm

/-- Normalized smoothing posterior mass at a split point. -/
def smoothingPosteriorMass
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs ws : List (CycleObservation Action obs))
    (x : Fin latent) : ℝ≥0∞ :=
  smoothingMass θ zs ws x / observedCycleProb θ (zs ++ ws)

theorem smoothingPosteriorMass_sum_eq_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs ws : List (CycleObservation Action obs))
    (hobs : observedCycleProb θ (zs ++ ws) ≠ 0) :
    ∑ x : Fin latent, smoothingPosteriorMass θ zs ws x = 1 := by
  have htop : observedCycleProb θ (zs ++ ws) ≠ ⊤ := observedCycleProb_ne_top θ (zs ++ ws)
  unfold smoothingPosteriorMass
  calc
    ∑ x : Fin latent, smoothingMass θ zs ws x / observedCycleProb θ (zs ++ ws)
      = ∑ x : Fin latent, smoothingMass θ zs ws x * (observedCycleProb θ (zs ++ ws))⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑ x : Fin latent, smoothingMass θ zs ws x) *
          (observedCycleProb θ (zs ++ ws))⁻¹ := by
            rw [Finset.sum_mul]
    _ = observedCycleProb θ (zs ++ ws) * (observedCycleProb θ (zs ++ ws))⁻¹ := by
            rw [smoothingMass_sum_eq_observedCycleProb_append]
    _ = 1 := ENNReal.mul_inv_cancel hobs htop

/-- Filtering mass viewed directly on BayesianAgents histories. -/
def historyFilteringMass
    (θ : ControlledFiniteHMMParam Action latent obs)
    (h : Mettapedia.UniversalAI.BayesianAgents.Core.History Action (Fin obs)) :
    LatentMass latent :=
  filteringMass θ (completedCycles h)

/-- Total observed mass on a history with completed cycles. -/
def observedHistoryProb
    (θ : ControlledFiniteHMMParam Action latent obs)
    (h : Mettapedia.UniversalAI.BayesianAgents.Core.History Action (Fin obs)) : ℝ≥0∞ :=
  observedCycleProb θ (completedCycles h)

theorem historyFilteringMass_historyOfCycles_append_act_per
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    historyFilteringMass θ
        (historyOfCycles zs ++
          [Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.act a,
           Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.per y]) =
      filteringStepMass θ (filteringMass θ zs) a y := by
  simpa [historyFilteringMass] using
    filteringMass_completedCycles_historyOfCycles_append_act_per θ zs a y

theorem observedHistoryProb_historyOfCycles_append_act_per
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    observedHistoryProb θ
        (historyOfCycles zs ++
          [Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.act a,
           Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.per y]) =
      environmentProb θ
        (historyOfCycles zs ++
          [Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.act a]) y := by
  calc
    observedHistoryProb θ
        (historyOfCycles zs ++
          [Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.act a,
           Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.per y])
      = observedCycleProb θ (zs ++ [(a, y)]) := by
          simp [observedHistoryProb]
    _ = observationMassGivenAction θ (filteringMass θ zs) a y := by
          exact observedCycleProb_append_singleton θ zs a y
    _ =
        environmentProb θ
          (historyOfCycles zs ++
            [Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.act a]) y := by
              symm
              exact environmentProb_historyOfCycles_append_act θ zs a y

section Examples

/-- Positive example: filtering posterior masses normalize on any completed
trace with nonzero observed mass. -/
example
    (θ : ControlledFiniteHMMParam Action 2 2)
    (zs : List (CycleObservation Action 2))
    (hobs : observedCycleProb θ zs ≠ 0) :
    ∑ x : Fin 2, filteringPosteriorMass θ zs x = 1 :=
  filteringPosteriorMass_sum_eq_one θ zs hobs

/-- Negative example: observed history probability after appending a completed
cycle is not equal to the old observed history probability in general; it is the
pending-action predictive mass for the new observation. -/
example
    (θ : ControlledFiniteHMMParam Action 2 2)
    (zs : List (CycleObservation Action 2))
    (a : Action) (y : Fin 2) :
    observedHistoryProb θ
        (historyOfCycles zs ++
          [Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.act a,
           Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.per y]) =
      environmentProb θ
        (historyOfCycles zs ++
          [Mettapedia.UniversalAI.BayesianAgents.Core.HistElem.act a]) y :=
  observedHistoryProb_historyOfCycles_append_act_per θ zs a y

end Examples

end Mettapedia.Logic.ControlledFiniteHiddenMarkovObservedInference
