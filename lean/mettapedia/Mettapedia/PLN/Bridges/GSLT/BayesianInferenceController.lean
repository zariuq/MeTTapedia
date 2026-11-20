import Mettapedia.PLN.Bridges.GSLT.InferenceControl
import Mettapedia.ProbabilityTheory.BayesianInference.ExperimentDecision

/-!
# Bayesian control of certified search

A finite latent model predicts outcomes and costs of actual search actions.
An observation changes the model by Bayes' rule; a zero-likelihood observation
is retained as an anomaly. The resulting PLN guidance schedules existing work
by predicted net reward. Forecast weights are not observation-count confidence.
The branching authority still determines successors and certificate emissions.
Soundness holds for every update; liveness additionally requires fairness.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController

open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.PLN.Bridges.GSLT.InferenceControl

/-- Search procedures may attach these roles to their own action type. -/
inductive ActionRole where
  | selectPremises | expandClause | probeNeighborhood | invokeATP | compileQuery | stop
  deriving DecidableEq, Repr

structure Model (Θ Action Outcome : Type*) [Fintype Θ] [Fintype Outcome] where
  likelihood : Action → Θ → Prob Outcome
  reward : Outcome → ℝ
  reward_nonneg : ∀ outcome, 0 ≤ reward outcome
  cost : Action → Outcome → ℝ
  cost_nonneg : ∀ action outcome, 0 ≤ cost action outcome

variable {Θ Action Outcome Node Answer : Type*} [Fintype Θ] [Fintype Outcome]

namespace Model

def expectedReward (model : Model Θ Action Outcome) (prior : Prob Θ) (action : Action) : ℝ :=
  ∑ state, ∑ outcome, prior.1 state * (model.likelihood action state).1 outcome * model.reward outcome

def expectedCost (model : Model Θ Action Outcome) (prior : Prob Θ) (action : Action) : ℝ :=
  ∑ state, ∑ outcome, prior.1 state * (model.likelihood action state).1 outcome * model.cost action outcome

def value (model : Model Θ Action Outcome) (prior : Prob Θ) (action : Action) : ℝ :=
  model.expectedReward prior action - model.expectedCost prior action

theorem expectedReward_nonneg (model : Model Θ Action Outcome) (prior : Prob Θ) (action : Action) :
    0 ≤ model.expectedReward prior action := by
  apply Finset.sum_nonneg
  intro state _
  apply Finset.sum_nonneg
  intro outcome _
  exact mul_nonneg (mul_nonneg (prior.2.1 state)
    ((model.likelihood action state).2.1 outcome)) (model.reward_nonneg outcome)

/-- A model over search outcomes is a distribution over utility and actual
cost together, so an observation can change both forecasts. -/
def update? (model : Model Θ Action Outcome) (prior : Prob Θ)
    (action : Action) (outcome : Outcome) : Option (Prob Θ) :=
  if possible : 0 < evidence prior (fun state => (model.likelihood action state).1 outcome) then
    some (posterior prior _ (fun state => (model.likelihood action state).2.1 outcome) possible)
  else none

theorem update?_apply (model : Model Θ Action Outcome) (prior : Prob Θ)
    (action : Action) (outcome : Outcome)
    (possible : 0 < evidence prior (fun state => (model.likelihood action state).1 outcome)) :
    model.update? prior action outcome =
      some (posterior prior _ (fun state => (model.likelihood action state).2.1 outcome) possible) := by
  rw [update?, dif_pos possible]

def guidance (model : Model Θ Action Outcome) (actionOf : Node → Action) :
    Guidance (Prob Θ) Node ℝ ℝ where
  scorer := ⟨fun prior node => ⟨ENNReal.ofReal (model.expectedReward prior (actionOf node)), 0⟩⟩
  estimate prior node := model.expectedCost prior (actionOf node)
  rank forecast cost := forecast.pos.toReal - cost
  prefer := (· ≥ ·)

theorem guidance_priority (model : Model Θ Action Outcome) (actionOf : Node → Action)
    (prior : Prob Θ) (node : Node) :
    (model.guidance actionOf).priorityAt prior node = model.value prior (actionOf node) := by
  simp only [Guidance.priorityAt, Guidance.evidenceAt, Guidance.estimateAt, guidance, value]
  rw [ENNReal.toReal_ofReal (model.expectedReward_nonneg prior (actionOf node))]

end Model

structure Memory (Θ Action Outcome : Type*) [Fintype Θ] where
  belief : Prob Θ
  observations : List (Action × Outcome)
  anomalies : List (Action × Outcome)

def learn (model : Model Θ Action Outcome) (memory : Memory Θ Action Outcome)
    (action : Action) (outcome : Outcome) : Memory Θ Action Outcome :=
  match model.update? memory.belief action outcome with
  | some belief => ⟨belief, (action, outcome) :: memory.observations, memory.anomalies⟩
  | none => ⟨memory.belief, (action, outcome) :: memory.observations, (action, outcome) :: memory.anomalies⟩

theorem learn_records_outcome (model : Model Θ Action Outcome) (memory : Memory Θ Action Outcome)
    (action : Action) (outcome : Outcome) :
    (learn model memory action outcome).observations = (action, outcome) :: memory.observations := by
  unfold learn
  split <;> rfl

theorem impossible_outcome_retained (model : Model Θ Action Outcome) (memory : Memory Θ Action Outcome)
    (action : Action) (outcome : Outcome) (unexpected : model.update? memory.belief action outcome = none) :
    (learn model memory action outcome).belief = memory.belief ∧
      (learn model memory action outcome).anomalies = (action, outcome) :: memory.anomalies := by
  simp [learn, unexpected]

/-- Forecasts and update likelihoods are conditional on the retained history.
`Action` can additionally carry the goal and complete search context; neither
history nor repeated attempt identity is silently replaced by independence. -/
def contextualController (modelAt : List (Action × Outcome) → Model Θ Action Outcome)
    (initial : Memory Θ Action Outcome)
    (actionOf : Node → Action) (observe : Node → Option Answer → List Node → Outcome) :
    Controller Node Answer (Memory Θ Action Outcome) where
  initialMemory := initial
  scheduler memory := ((modelAt memory.observations).guidance actionOf).scheduler memory.belief
  advance memory node answer children :=
    learn (modelAt memory.observations) memory (actionOf node) (observe node answer children)

/-- A stationary conditional-outcome model is a useful specialization. Actual
applications owe the asserted conditional likelihood law; soundness of proof
checking below does not require the forecast to be statistically correct. -/
def controller (model : Model Θ Action Outcome) (initial : Memory Θ Action Outcome)
    (actionOf : Node → Action) (observe : Node → Option Answer → List Node → Outcome) :
    Controller Node Answer (Memory Θ Action Outcome) :=
  contextualController (fun _ => model) initial actionOf observe

theorem contextual_run_sound (modelAt : List (Action × Outcome) → Model Θ Action Outcome)
    (initial : Memory Θ Action Outcome)
    (actionOf : Node → Action) (observe : Node → Option Answer → List Node → Outcome)
    (system : BranchingSystem Node Answer) (roots : List Node) (work : Nat) :
    (Snapshot.run system (contextualController modelAt initial actionOf observe) work
      (Snapshot.initial (contextualController modelAt initial actionOf observe) roots)).search.Sound system roots :=
  Snapshot.sound_run system _ (initial_sound system roots) work

theorem run_sound (model : Model Θ Action Outcome) (initial : Memory Θ Action Outcome)
    (actionOf : Node → Action) (observe : Node → Option Answer → List Node → Outcome)
    (system : BranchingSystem Node Answer) (roots : List Node) (work : Nat) :
    (Snapshot.run system (controller model initial actionOf observe) work
      (Snapshot.initial (controller model initial actionOf observe) roots)).search.Sound system roots :=
  Snapshot.sound_run system _ (initial_sound system roots) work

/-- Each actual emitted certificate satisfies any invariant already enforced
by the proof authority, independently of learned model accuracy. -/
theorem emitted_valid (model : Model Θ Action Outcome) (initial : Memory Θ Action Outcome)
    (actionOf : Node → Action) (observe : Node → Option Answer → List Node → Outcome)
    (system : BranchingSystem Node Answer) (roots : List Node) (work : Nat)
    (valid : Answer → Prop) (authority : ∀ node answer, system.emit node = some answer → valid answer)
    (event : Emission Node Answer)
    (emitted : event ∈ (Snapshot.run system (controller model initial actionOf observe) work
      (Snapshot.initial (controller model initial actionOf observe) roots)).search.events) :
    valid event.value := by
  have sound := run_sound model initial actionOf observe system roots work
  exact authority event.origin event.value (sound.2 event emitted).2

/-- Explicit fairness upgrades sound guidance to eventual discovery. A score
alone gives no fairness theorem on an infinite frontier. -/
theorem fair_complete (model : Model Θ Action Outcome) (initial : Memory Θ Action Outcome)
    (actionOf : Node → Action) (observe : Node → Option Answer → List Node → Outcome)
    (system : BranchingSystem Node Answer) (roots : List Node)
    (fair : Snapshot.FairFrom system (controller model initial actionOf observe) roots)
    {node : Node} {answer : Answer} (generated : Generated system roots node)
    (emits : system.emit node = some answer) :
    ∃ work, (⟨node, answer⟩ : Emission Node Answer) ∈
      (Snapshot.run system (controller model initial actionOf observe) work
        (Snapshot.initial (controller model initial actionOf observe) roots)).search.events :=
  Snapshot.fair_emits_reachable system _ roots fair generated emits

/-- Selection is constructed by optimization on the supplied finite action
set, not supplied as an assumed optimal policy. -/
def bestAction [Fintype Action] [Nonempty Action]
    (model : Model Θ Action Outcome) (prior : Prob Θ) : Action :=
  Classical.choose (Finset.exists_max_image Finset.univ (model.value prior)
    (Finset.univ_nonempty : (Finset.univ : Finset Action).Nonempty))

theorem bestAction_optimal [Fintype Action] [Nonempty Action]
    (model : Model Θ Action Outcome) (prior : Prob Θ) (alternative : Action) :
    model.value prior alternative ≤ model.value prior (bestAction model prior) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (model.value prior)
    (Finset.univ_nonempty : (Finset.univ : Finset Action).Nonempty))).2 alternative (Finset.mem_univ _)

end Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController
