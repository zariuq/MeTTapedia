import Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController

/-! # Learning search-action preferences and paying for useful computation -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController.Controls

open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.DecisionValueOfInformation

/-- The latent bit determines which of two concrete procedures succeeds.
The true action invokes an ATP; false probes the proof neighborhood. -/
def model : Model Bool Bool Bool where
  likelihood action state := Prob.dirac (state == action)
  reward result := if result then 1 else 0
  reward_nonneg result := by cases result <;> norm_num
  cost action _ := if action then 1 / 10 else 1 / 5
  cost_nonneg action _ := by cases action <;> norm_num

def prior : Prob Bool :=
  ⟨fun state => if state then 1 / 4 else 3 / 4,
    (by intro state; cases state <;> norm_num), by norm_num [Fintype.sum_bool]⟩

theorem initial_values : model.value prior true = 3 / 20 ∧ model.value prior false = 11 / 20 := by
  norm_num [Model.value, Model.expectedReward, Model.expectedCost, model, prior,
    Prob.dirac, Fintype.sum_bool]

theorem observation_possible : evidence prior (fun state => (model.likelihood true state).1 true) = 1 / 4 := by
  norm_num [evidence, prior, model, Prob.dirac, Fintype.sum_bool]

def initial : Memory Bool Bool Bool := ⟨prior, [], []⟩
def learned : Memory Bool Bool Bool := learn model initial true true

theorem learned_belief (state : Bool) : learned.belief.1 state = if state then 1 else 0 := by
  have possible : 0 < evidence prior (fun state => (model.likelihood true state).1 true) := by
    rw [observation_possible]; norm_num
  simp only [learned, learn, initial, Model.update?_apply model prior true true possible]
  cases state <;> norm_num [posterior_apply, evidence, prior, model, Prob.dirac, Fintype.sum_bool]

theorem learned_values : model.value learned.belief true = 9 / 10 ∧
    model.value learned.belief false = -(1 / 5) := by
  norm_num [Model.value, Model.expectedReward, Model.expectedCost, model, Fintype.sum_bool,
    learned_belief, Prob.dirac]

/-- Actual Bayesian learning changes both the success and action-cost
tradeoff without changing which steps count as proof steps. -/
theorem learning_reverses_preference :
    model.value prior true < model.value prior false ∧
      model.value learned.belief false < model.value learned.belief true := by
  rw [initial_values.1, initial_values.2, learned_values.1, learned_values.2]
  constructor <;> norm_num

/-- Here the outcome reports which cost category the computation incurred.
Bayesian learning therefore changes its predicted resource distribution. -/
def costModel : Model Bool Bool Bool where
  likelihood := model.likelihood
  reward _ := 1
  reward_nonneg _ := by norm_num
  cost _ outcome := if outcome then 1 / 5 else 4 / 5
  cost_nonneg _ outcome := by cases outcome <;> norm_num

def costLearned : Memory Bool Bool Bool := learn costModel initial true true

theorem learned_cost_belief (state : Bool) : costLearned.belief.1 state = if state then 1 else 0 := by
  have same : costLearned = learned := rfl
  rw [same]
  exact learned_belief state

theorem cost_prediction_learns :
    costModel.expectedCost prior true = 13 / 20 ∧
      costModel.expectedCost costLearned.belief true = 1 / 5 := by
  norm_num [Model.expectedCost, costModel, model, prior, Prob.dirac,
    Fintype.sum_bool, learned_cost_belief]

theorem learned_best_is_ATP : bestAction model learned.belief = true := by
  have optimal := bestAction_optimal model learned.belief true
  cases selected : bestAction model learned.belief with
  | false => rw [selected, learned_values.1, learned_values.2] at optimal; norm_num at optimal
  | true => rfl

/-- A perfect diagnostic chooses the working proof procedure, saving an
expected failed attempt; its positive cost is paid in the same objective. -/
def wrongProcedure (state action : Fin 2) : ℝ := if state = action then 0 else 1

theorem useful_diagnostic_net_value :
    netDecisionValue (decisionExperiment binaryUniform Prob.dirac wrongProcedure)
      0 id (1 / 4) = 1 / 4 := by
  norm_num [netDecisionValue, grossDecisionValue, staticRisk, signalRisk, decisionExperiment,
    joint_apply, binaryUniform, binaryDist, wrongProcedure, Prob.dirac, Fin.sum_univ_two]

/-- A separate diagnostic revealing an irrelevant bit has greater gross
information than doing nothing, and strictly negative task value at cost one. -/
theorem information_can_choose_irrelevant_expense :
    0 < expectedInformationGain binaryUniform Prob.dirac ∧
      netDecisionValue (decisionExperiment binaryUniform Prob.dirac
        (fun _ (_ : Unit) => 0)) () (fun _ => ()) 1 < 0 :=
  positive_information_negative_task_value

def independentBits : Prob (Bool × Bool) :=
  ⟨fun _ => 1 / 4, (fun _ => by norm_num), by
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

def nuisanceKernel (state : Bool × Bool) : Prob Bool := Prob.dirac state.2
def taskLoss (state : Bool × Bool) (action : Bool) : ℝ := if state.1 = action then 0 else 1

theorem nuisance_information : expectedInformationGain independentBits nuisanceKernel = Real.log 2 := by
  norm_num [expectedInformationGain, conditionalMass, observationLaw, Prob.bind,
    joint_apply, evidence, independentBits, nuisanceKernel, Prob.dirac,
    Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem nuisance_does_not_help_task (policy : Bool → Bool) :
    signalRisk (decisionExperiment independentBits nuisanceKernel taskLoss) policy = 1 / 2 := by
  cases yes : policy true <;> cases no : policy false <;>
    norm_num [signalRisk, decisionExperiment, joint_apply, independentBits,
      nuisanceKernel, taskLoss, Prob.dirac, Fintype.sum_prod_type, Fintype.sum_bool, yes, no]

theorem nuisance_is_costly (policy : Bool → Bool) :
    netDecisionValue (decisionExperiment independentBits nuisanceKernel taskLoss)
      false policy 1 = -1 := by
  rw [netDecisionValue, grossDecisionValue, nuisance_does_not_help_task,
    staticRisk_eq_prior_risk]
  norm_num [independentBits, taskLoss, Fintype.sum_prod_type, Fintype.sum_bool]

/-- On the choice between this experiment and doing no computation, strictly
maximizing information chooses an expense with no benefit to a nonconstant
task. Every policy after the experiment still incurs risk 1/2. -/
theorem information_ranking_reverses_task_value :
    0 < expectedInformationGain independentBits nuisanceKernel ∧
      ∀ policy : Bool → Bool,
        netDecisionValue (decisionExperiment independentBits nuisanceKernel taskLoss)
          false policy 1 < 0 := by
  constructor
  · rw [nuisance_information]; exact Real.log_pos (by norm_num)
  · intro policy; rw [nuisance_is_costly]; norm_num

#print axioms learning_reverses_preference
#print axioms learned_best_is_ATP
#print axioms useful_diagnostic_net_value

end Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController.Controls
