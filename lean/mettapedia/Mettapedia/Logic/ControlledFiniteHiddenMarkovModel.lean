import Mathlib.Data.ENNReal.BigOperators
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.MarkovDeFinettiMomentProblem
import Mettapedia.ProbabilityTheory.FiniteMeasureSupport

/-!
# Controlled Finite Hidden Markov Models

This file extends the finite-state finite-emission HMM surface with an action
alphabet.

We work at the cycle level:

* a latent prior,
* an action-conditioned latent transition kernel,
* a finite emission kernel,
* cycle-level predictive and filtering masses.

Positive example:
* action-conditioned next-observation probabilities are defined from a latent
  belief state plus the chosen action.

Negative example:
* this file does not yet include value functions, rewards, or the full POMDP
  planning bridge.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.ControlledFiniteHiddenMarkovModel

open Mettapedia.Logic
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.ProbabilityTheory.FiniteMeasureSupport
open scoped BigOperators ENNReal NNReal
open MeasureTheory

universe uA

variable {Action : Type uA} {latent obs : ℕ}

/-- Finite hidden Markov model with action-conditioned latent transitions. -/
structure ControlledFiniteHMMParam (Action : Type uA) (latent obs : ℕ) where
  init : ProbabilityMeasure (Fin latent)
  trans : Action → Fin latent → ProbabilityMeasure (Fin latent)
  emission : Fin latent → ProbabilityMeasure (Fin obs)

/-- One completed action-observation cycle. -/
abbrev CycleObservation (Action : Type uA) (obs : ℕ) := Action × Fin obs

/-- Initial latent-state probability. -/
def initProb (θ : ControlledFiniteHMMParam Action latent obs) (x : Fin latent) : ℝ≥0 :=
  θ.init (Set.singleton x)

/-- Action-conditioned latent transition probability. -/
def stepProb
    (θ : ControlledFiniteHMMParam Action latent obs)
    (a : Action) (x x' : Fin latent) : ℝ≥0 :=
  θ.trans a x (Set.singleton x')

/-- Emission probability. -/
def emissionProb
    (θ : ControlledFiniteHMMParam Action latent obs)
    (x : Fin latent) (y : Fin obs) : ℝ≥0 :=
  θ.emission x (Set.singleton y)

theorem initProb_sum_enn (θ : ControlledFiniteHMMParam Action latent obs) :
    ∑ x : Fin latent, (initProb θ x : ℝ≥0∞) = 1 := by
  have h := probabilityMeasure_sum_singletons_enn θ.init
  rw [show (∑ x : Fin latent, (initProb θ x : ℝ≥0∞)) =
      ∑ x : Fin latent, ((θ.init : Measure (Fin latent)) ({x} : Set (Fin latent))) from by
        congr 1
        funext x
        exact probabilityMeasure_coe_singleton θ.init x]
  exact h

theorem stepProb_sum_enn
    (θ : ControlledFiniteHMMParam Action latent obs)
    (a : Action) (x : Fin latent) :
    ∑ x' : Fin latent, (stepProb θ a x x' : ℝ≥0∞) = 1 := by
  have h := probabilityMeasure_sum_singletons_enn (θ.trans a x)
  rw [show (∑ x' : Fin latent, (stepProb θ a x x' : ℝ≥0∞)) =
      ∑ x' : Fin latent, (((θ.trans a x : ProbabilityMeasure (Fin latent)) :
        Measure (Fin latent)) ({x'} : Set (Fin latent))) from by
        congr 1
        funext x'
        exact probabilityMeasure_coe_singleton (θ.trans a x) x']
  exact h

theorem emissionProb_sum_enn
    (θ : ControlledFiniteHMMParam Action latent obs)
    (x : Fin latent) :
    ∑ y : Fin obs, (emissionProb θ x y : ℝ≥0∞) = 1 := by
  have h := probabilityMeasure_sum_singletons_enn (θ.emission x)
  rw [show (∑ y : Fin obs, (emissionProb θ x y : ℝ≥0∞)) =
      ∑ y : Fin obs, (((θ.emission x : ProbabilityMeasure (Fin obs)) :
        Measure (Fin obs)) ({y} : Set (Fin obs))) from by
        congr 1
        funext y
        exact probabilityMeasure_coe_singleton (θ.emission x) y]
  exact h

/-- A latent mass function before applying the next action-observation cycle. -/
abbrev LatentMass (latent : ℕ) := Fin latent → ℝ≥0∞

/-- The initial latent mass. -/
def initialLatentMass (θ : ControlledFiniteHMMParam Action latent obs) : LatentMass latent :=
  fun x => (initProb θ x : ℝ≥0∞)

/-- Predictive latent mass after taking action `a` and before seeing the next
observation. -/
def predictiveLatentMass
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) (a : Action) : LatentMass latent :=
  fun x' => ∑ x : Fin latent, m x * (stepProb θ a x x' : ℝ≥0∞)

/-- Filtering mass after taking action `a` and then seeing observation `y`. -/
def filteringStepMass
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) (a : Action) (y : Fin obs) : LatentMass latent :=
  fun x => predictiveLatentMass θ m a x * (emissionProb θ x y : ℝ≥0∞)

/-- Predictive mass of seeing observation `y` after action `a` from latent mass
`m`. -/
def observationMassGivenAction
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) (a : Action) (y : Fin obs) : ℝ≥0∞ :=
  ∑ x : Fin latent, filteringStepMass θ m a y x

/-- Auxiliary left-to-right filtering fold over completed cycles. -/
def filteringMassAux
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) :
    List (CycleObservation Action obs) → LatentMass latent
  | [] => m
  | (a, y) :: zs => filteringMassAux θ (filteringStepMass θ m a y) zs

/-- Filtering mass after a completed action-observation trace. -/
def filteringMass
    (θ : ControlledFiniteHMMParam Action latent obs) :
    List (CycleObservation Action obs) → LatentMass latent :=
  filteringMassAux θ (initialLatentMass θ)

theorem predictiveLatentMass_sum_eq
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) (a : Action) :
    ∑ x' : Fin latent, predictiveLatentMass θ m a x' =
      ∑ x : Fin latent, m x := by
  unfold predictiveLatentMass
  calc
    ∑ x' : Fin latent, ∑ x : Fin latent, m x * (stepProb θ a x x' : ℝ≥0∞)
      = ∑ x : Fin latent, ∑ x' : Fin latent, m x * (stepProb θ a x x' : ℝ≥0∞) := by
          rw [Finset.sum_comm]
    _ = ∑ x : Fin latent, m x * ∑ x' : Fin latent, (stepProb θ a x x' : ℝ≥0∞) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.mul_sum]
    _ = ∑ x : Fin latent, m x * 1 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [stepProb_sum_enn]
    _ = ∑ x : Fin latent, m x := by
          simp

theorem observationMassGivenAction_sum_eq
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) (a : Action) :
    ∑ y : Fin obs, observationMassGivenAction θ m a y =
      ∑ x : Fin latent, m x := by
  unfold observationMassGivenAction filteringStepMass
  calc
    ∑ y : Fin obs, ∑ x : Fin latent,
        predictiveLatentMass θ m a x * (emissionProb θ x y : ℝ≥0∞)
      = ∑ x : Fin latent, ∑ y : Fin obs,
          predictiveLatentMass θ m a x * (emissionProb θ x y : ℝ≥0∞) := by
            rw [Finset.sum_comm]
    _ = ∑ x : Fin latent,
          predictiveLatentMass θ m a x * ∑ y : Fin obs, (emissionProb θ x y : ℝ≥0∞) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [Finset.mul_sum]
    _ = ∑ x : Fin latent, predictiveLatentMass θ m a x * 1 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [emissionProb_sum_enn]
    _ = ∑ x : Fin latent, predictiveLatentMass θ m a x := by
            simp
    _ = ∑ x : Fin latent, m x := predictiveLatentMass_sum_eq θ m a

theorem filteringStepMass_sum_eq_observationMass
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) (a : Action) (y : Fin obs) :
    ∑ x : Fin latent, filteringStepMass θ m a y x =
      observationMassGivenAction θ m a y := rfl

theorem filteringStepMass_sum_le_total
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent) (a : Action) (y : Fin obs) :
    ∑ x : Fin latent, filteringStepMass θ m a y x ≤
      ∑ x : Fin latent, m x := by
  rw [filteringStepMass_sum_eq_observationMass]
  calc
    observationMassGivenAction θ m a y
      ≤ ∑ y' : Fin obs, observationMassGivenAction θ m a y' := by
          exact Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ y)
    _ = ∑ x : Fin latent, m x := observationMassGivenAction_sum_eq θ m a

theorem filteringMassAux_sum_le
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent)
    (hm : ∑ x : Fin latent, m x ≤ 1) :
    ∀ zs : List (CycleObservation Action obs),
      ∑ x : Fin latent, filteringMassAux θ m zs x ≤ 1
  | [] => hm
  | (a, y) :: zs => by
      have hstep :
          ∑ x : Fin latent, filteringStepMass θ m a y x ≤ 1 :=
        (filteringStepMass_sum_le_total θ m a y).trans hm
      simpa [filteringMassAux] using filteringMassAux_sum_le θ (filteringStepMass θ m a y) hstep zs

theorem filteringMass_sum_le_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    ∑ x : Fin latent, filteringMass θ zs x ≤ 1 := by
  apply filteringMassAux_sum_le
  simpa [initialLatentMass] using (le_of_eq (initProb_sum_enn θ))

theorem filteringMassAux_append
    (θ : ControlledFiniteHMMParam Action latent obs)
    (m : LatentMass latent)
    (zs ws : List (CycleObservation Action obs)) :
    filteringMassAux θ m (zs ++ ws) =
      filteringMassAux θ (filteringMassAux θ m zs) ws := by
  induction zs generalizing m with
  | nil =>
      simp [filteringMassAux]
  | cons z zs ih =>
      cases z with
      | mk a y =>
          simpa [filteringMassAux] using
            ih (m := filteringStepMass θ m a y)

theorem filteringMass_append
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs ws : List (CycleObservation Action obs)) :
    filteringMass θ (zs ++ ws) =
      filteringMassAux θ (filteringMass θ zs) ws := by
  simpa [filteringMass] using
    filteringMassAux_append θ (initialLatentMass θ) zs ws

theorem filteringMass_append_singleton
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    filteringMass θ (zs ++ [(a, y)]) =
      filteringStepMass θ (filteringMass θ zs) a y := by
  ext x
  have h :=
    congrArg (fun m : LatentMass latent => m x)
      (filteringMass_append θ zs [(a, y)])
  simpa [filteringMassAux, filteringStepMass] using h

section Examples

open scoped BigOperators

/-- Positive example: the one-step observation masses after any action sum to
the current latent mass total. -/
example (θ : ControlledFiniteHMMParam Action 2 2)
    (m : LatentMass 2) (a : Action) :
    ∑ y : Fin 2, observationMassGivenAction θ m a y = ∑ x : Fin 2, m x :=
  observationMassGivenAction_sum_eq θ m a

/-- Negative example: after conditioning on one specific observation, the
latent mass need not sum to `1`; it only stays bounded by the previous total. -/
example (θ : ControlledFiniteHMMParam Action 2 2)
    (m : LatentMass 2) (a : Action) (y : Fin 2) :
    ∑ x : Fin 2, filteringStepMass θ m a y x ≤ ∑ x : Fin 2, m x :=
  filteringStepMass_sum_le_total θ m a y

end Examples

end Mettapedia.Logic.ControlledFiniteHiddenMarkovModel
