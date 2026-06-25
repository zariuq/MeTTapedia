import Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel
import Mettapedia.UniversalAI.BayesianAgents.Core

/-!
# Controlled Finite HMM Bridge to BayesianAgents Environments

This file packages a controlled finite HMM as a history-conditional
environment in the `BayesianAgents.Core` sense.

We treat the environment state as latent, actions as externally supplied, and
percepts as emitted observations.

Positive example:
* a history ending in an action gets a next-percept distribution derived from
  the controlled latent belief state.

Negative example:
* this file does not yet include rewards, optimal control, or a credal
  observed-only WM layer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge

open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel
open Mettapedia.UniversalAI.BayesianAgents.Core
open scoped BigOperators ENNReal

universe uA

variable {Action : Type uA} {latent obs : ℕ}

/-- Turn a completed action-observation trace into an alternating history. -/
def historyOfCycles :
    List (CycleObservation Action obs) → History Action (Fin obs)
  | [] => []
  | (a, y) :: zs => HistElem.act a :: HistElem.per y :: historyOfCycles zs

/-- Extract the completed action-observation cycles from a history. -/
def completedCycles :
    History Action (Fin obs) → List (CycleObservation Action obs)
  | [] => []
  | [HistElem.act _] => []
  | HistElem.act a :: HistElem.per y :: rest => (a, y) :: completedCycles rest
  | _ => []

/-- The pending action at the tip of a well-formed history, if present. -/
def pendingAction? : History Action (Fin obs) → Option Action
  | [] => none
  | [HistElem.act a] => some a
  | HistElem.act _ :: HistElem.per _ :: rest => pendingAction? rest
  | _ => none

@[simp] theorem completedCycles_historyOfCycles
    (zs : List (CycleObservation Action obs)) :
    completedCycles (historyOfCycles zs) = zs := by
  induction zs with
  | nil =>
      simp [historyOfCycles, completedCycles]
  | cons z zs ih =>
      cases z with
      | mk a y =>
          simp [historyOfCycles, completedCycles, ih]

@[simp] theorem completedCycles_historyOfCycles_append_act
    (zs : List (CycleObservation Action obs)) (a : Action) :
    completedCycles (historyOfCycles zs ++ [HistElem.act a]) = zs := by
  induction zs with
  | nil =>
      simp [historyOfCycles, completedCycles]
  | cons z zs ih =>
      cases z with
      | mk a' y =>
          simp [historyOfCycles, completedCycles, ih]

@[simp] theorem completedCycles_historyOfCycles_append_act_per
    (zs : List (CycleObservation Action obs)) (a : Action) (y : Fin obs) :
    completedCycles (historyOfCycles zs ++ [HistElem.act a, HistElem.per y]) =
      zs ++ [(a, y)] := by
  induction zs with
  | nil =>
      simp [historyOfCycles, completedCycles]
  | cons z zs ih =>
      cases z with
      | mk a' y' =>
          simp [historyOfCycles, completedCycles, ih]

@[simp] theorem pendingAction?_historyOfCycles
    (zs : List (CycleObservation Action obs)) :
    pendingAction? (historyOfCycles zs) = none := by
  induction zs with
  | nil =>
      simp [historyOfCycles, pendingAction?]
  | cons z zs ih =>
      cases z with
      | mk a y =>
          simp [historyOfCycles, pendingAction?, ih]

@[simp] theorem pendingAction?_historyOfCycles_append_act
    (zs : List (CycleObservation Action obs)) (a : Action) :
    pendingAction? (historyOfCycles zs ++ [HistElem.act a]) = some a := by
  induction zs with
  | nil =>
      simp [historyOfCycles, pendingAction?]
  | cons z zs ih =>
      cases z with
      | mk a' y =>
          simp [historyOfCycles, pendingAction?, ih]

/-- Next-observation mass induced by a controlled HMM from a history. -/
def environmentProb
    (θ : ControlledFiniteHMMParam Action latent obs)
    (h : History Action (Fin obs)) (y : Fin obs) : ℝ≥0∞ :=
  match pendingAction? h with
  | none => 0
  | some a =>
      observationMassGivenAction θ
        (filteringMass θ (completedCycles h)) a y

theorem environmentProb_sum_le_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (h : History Action (Fin obs)) :
    ∑ y : Fin obs, environmentProb θ h y ≤ 1 := by
  unfold environmentProb
  cases hpend : pendingAction? h with
  | none =>
      simp
  | some a =>
      calc
        ∑ y : Fin obs,
            observationMassGivenAction θ (filteringMass θ (completedCycles h)) a y
          = ∑ x : Fin latent, filteringMass θ (completedCycles h) x := by
              exact observationMassGivenAction_sum_eq θ (filteringMass θ (completedCycles h)) a
      _ ≤ 1 := filteringMass_sum_le_one θ (completedCycles h)

theorem environmentProb_historyOfCycles_append_act
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    environmentProb θ (historyOfCycles zs ++ [HistElem.act a]) y =
      observationMassGivenAction θ (filteringMass θ zs) a y := by
  simp [environmentProb]

theorem filteringMass_completedCycles_historyOfCycles_append_act_per
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    filteringMass θ
        (completedCycles (historyOfCycles zs ++ [HistElem.act a, HistElem.per y])) =
      filteringStepMass θ (filteringMass θ zs) a y := by
  rw [completedCycles_historyOfCycles_append_act_per, filteringMass_append_singleton]

/-- Controlled finite HMM as a `BayesianAgents.Core.Environment`. -/
noncomputable def toEnvironment
    (θ : ControlledFiniteHMMParam Action latent obs) :
    Environment Action (Fin obs) where
  prob := environmentProb θ
  prob_le_one := by
    intro h _hw
    exact environmentProb_sum_le_one θ h

section Examples

/-- Positive example: a history with no pending action has zero next-percept
mass. -/
example (θ : ControlledFiniteHMMParam Action 2 2) :
    environmentProb θ ([] : History Action (Fin 2)) 0 = 0 := by
  simp [environmentProb, pendingAction?]

/-- Negative example: the bridge does not force malformed histories to carry
any meaningful next-percept law. -/
example (θ : ControlledFiniteHMMParam Action 2 2) (y : Fin 2) :
    environmentProb θ ([HistElem.per y] : History Action (Fin 2)) y = 0 := by
  simp [environmentProb, pendingAction?]

end Examples

end Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
