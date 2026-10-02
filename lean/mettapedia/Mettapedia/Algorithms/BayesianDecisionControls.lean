import Mettapedia.Algorithms.FiniteBayesianDecision
import Mettapedia.Algorithms.ResumableLogChoice
import Mettapedia.Algorithms.CompleteConstraintChoice
import Mettapedia.Algorithms.ConstrainedBayesianDecision

/-! # Positive and negative raw planning certificates -/

namespace Mettapedia.Algorithms.BayesianDecisionControls

open Mettapedia.Cybernetics.ApproximateAdequacy
open FiniteBayesianDecision

def posteriorMass (s : Bool) : ℚ := if s then 3 / 4 else 1 / 4

def reward (s : Bool) : ℚ := if s then 1 else 0

def model (action : Bool) (_ : Bool) (next : Bool × Bool) : ℚ :=
  if next = (action, action) then 1 else 0

def world (action : Fin 2) (_ : Bool) (next : Bool × Unit) : ℚ :=
  if next = (decide (action = 1), ()) then 1 else 0

def successorTable (action : Bool) (x : Bool × Bool) (y : Bool × Unit) : ℚ :=
  if x = (action, action) ∧ y = (action, ()) then 1 else 0

/-- The controllers have different action and observation types. -/
def certificate : Instance Bool Bool Bool Unit Bool (Fin 2) Bool 1 where
  prior _ := 1 / 2
  likelihood s := if s then 3 else 1
  posterior := posteriorMass
  trial := posteriorMass
  worldPrior := posteriorMass
  model := model
  world := world
  modelReward := reward
  worldReward := reward
  metric s t := if s = t then 0 else 1
  modelPolicy c := (c, fun _ => PUnit.unit)
  worldPolicy c := ((if c then 1 else 0), fun _ => PUnit.unit)
  initial s t := if s = t then posteriorMass s else 0
  execution c _ _ := (successorTable c, fun _ _ => PUnit.unit)
  magnitude := 1
  terms := 0
  predictionError _ := 0
  inferenceError _ := 0
  numericalError _ := 0
  computed := reward
  uniformError := 0
  slack := 0
  candidates := [false, true]
  admissible _ := true
  selected := true

theorem heterogeneous_execution_accepted : certificate.check = true := by decide +kernel

/-- The real-world guarantee is obtained from the general acceptance theorem. -/
theorem heterogeneous_world_optimal :
    (certificate.worldScore false : ℝ) - (certificate.worldScore true : ℝ) ≤ 0 := by
  simpa only [certificate, Rat.cast_zero, mul_zero, add_zero] using
    (certificate.regret heterogeneous_execution_accepted false (by decide +kernel)).2

theorem wrong_posterior_refused :
    ({ certificate with posterior := fun _ => 1 / 2 }).check = false := by decide +kernel

theorem wrong_initial_marginals_refused :
    ({ certificate with initial := fun _ _ => 0 }).check = false := by decide +kernel

theorem wrong_successor_marginals_refused :
    ({ certificate with execution := fun _ _ _ => (fun _ _ => 0, fun _ _ => PUnit.unit) }).check =
      false := by decide +kernel

theorem unsupported_trial_refused :
    FiniteKLCertificate.check (fun s : Bool => if s then 1 else 0)
      (fun s => if s then 0 else 1) 1 2 1 = false := by decide +kernel

/-- A genuinely approximate posterior can receive a nonzero error certificate. -/
theorem nonzero_variational_error_accepted :
    FiniteKLCertificate.check (fun _ : Bool => 1 / 2) posteriorMass 1 1 1 = true := by decide +kernel

theorem unjustified_exact_inference_refused :
    FiniteKLCertificate.check (fun _ : Bool => 1 / 2) posteriorMass 1 0 1 = false := by decide +kernel

theorem inadmissible_refused :
    ({ certificate with admissible := fun c => !c }).check = false := by decide +kernel

theorem wrong_ordering_refused :
    ({ certificate with selected := false }).check = false := by decide +kernel

theorem understated_numerical_error_refused :
    ({ certificate with computed := fun _ => 0 }).check = false := by decide +kernel

def logWeight (c _ : Bool) : ℚ := if c then 1 else 0
def logArgument (_ _ : Bool) : ℚ := 2

theorem logarithmic_budget_retains_pending :
    (ResumableLogChoice.resume [false, true] logWeight logArgument true 1 0
      ⟨[], [false, true]⟩).map (·.pending) = some [false, true] := by decide +kernel

theorem logarithmic_comparison_completes :
    (ResumableLogChoice.resume [false, true] logWeight logArgument true 1 2
      ⟨[], [false, true]⟩).map (·.pending) = some [] := by decide +kernel

theorem forged_logarithmic_receipt_refused :
    ResumableLogChoice.resume [false, true] logWeight logArgument false 1 2
      ⟨[false, true], []⟩ = none := by decide +kernel

theorem identical_logarithmic_scores_stay_pending :
    (ResumableLogChoice.resume [false, true] (fun _ _ : Bool => 1) logArgument true 3 2
      ⟨[], [false, true]⟩).map (·.pending) = some [false, true] := by decide +kernel

theorem retained_logarithmic_prefix_completes :
    (ResumableLogChoice.resume [false, true] logWeight logArgument true 2 1
      ⟨[false], [true]⟩).map (·.pending) = some [] := by decide +kernel

theorem signed_logarithmic_weights_accepted :
    (ResumableLogChoice.resume [false, true] (fun c _ : Bool => if c then 0 else -1)
      logArgument true 1 2 ⟨[], [false, true]⟩).map (·.pending) = some [] := by decide +kernel

open Mettapedia.Algorithms.WellFoundedServices

def repairs : Problem Bool Bool where
  vars := [false, true]
  dom _ := [false, true]
  constraints := [⟨[false, true], fun ds => decide (ds ≠ [false, false])⟩]

def repairChoice (assignment : Assignment Bool Bool) : Bool :=
  decide (assignment.lookup false = some true)

def repairCertificate : Instance Bool Bool Bool Unit Bool (Fin 2) (Assignment Bool Bool) 1 where
  prior := certificate.prior
  likelihood := certificate.likelihood
  posterior := certificate.posterior
  trial := certificate.trial
  worldPrior := certificate.worldPrior
  model := certificate.model
  world := certificate.world
  modelReward := certificate.modelReward
  worldReward := certificate.worldReward
  metric := certificate.metric
  modelPolicy a := certificate.modelPolicy (repairChoice a)
  worldPolicy a := certificate.worldPolicy (repairChoice a)
  initial := certificate.initial
  execution a := certificate.execution (repairChoice a)
  magnitude := certificate.magnitude
  terms := certificate.terms
  predictionError _ := 0
  inferenceError _ := 0
  numericalError _ := 0
  computed a := reward (repairChoice a)
  uniformError := 0
  slack := 0
  candidates := [[(false, true), (true, false)]]
  admissible _ := true
  selected := [(false, true), (true, false)]

theorem complete_repair_space_accepted :
    ConstrainedBayesianDecision.check repairs repairCertificate = true := by decide +kernel

theorem invalid_repair_refused :
    ConstrainedBayesianDecision.check repairs
      { repairCertificate with selected := [(false, false), (true, false)] } = false := by
  decide +kernel

theorem all_repairs_world_regret (alternative : Assignment Bool Bool)
    (solution : repairs.Solution alternative) :
    repairs.Solution repairCertificate.selected ∧
      (repairCertificate.worldScore alternative : ℝ) -
        (repairCertificate.worldScore repairCertificate.selected : ℝ) ≤ 0 := by
  have wellFormed : repairs.WellFormed := by
    constructor
    · decide +kernel
    · intro _ _ v _
      cases v <;> decide +kernel
  have supported : ∀ first second, CompleteConstraintChoice.Agrees repairs first second →
      repairCertificate.worldPolicy first = repairCertificate.worldPolicy second := by
    intro first second same
    have lookup := same false (by decide +kernel)
    simp only [repairCertificate, repairChoice, lookup]
  simpa only [repairCertificate, Rat.cast_zero, mul_zero, add_zero] using
    ConstrainedBayesianDecision.regret_all_solutions repairs wellFormed repairCertificate
      supported complete_repair_space_accepted alternative solution

end Mettapedia.Algorithms.BayesianDecisionControls
