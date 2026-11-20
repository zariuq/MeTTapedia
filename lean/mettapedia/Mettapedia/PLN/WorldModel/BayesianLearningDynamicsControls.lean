import Mettapedia.PLN.WorldModel.BayesianLearningDynamics
import Mettapedia.ProbabilityTheory.Distributions.BetaBernoulli

/-!
# Exact resumption and failures of prediction-only memory

Bernoulli histories reduce to a sufficient pair of counts. Keeping only the
current predictive mean loses information: the empty history and one success
plus one failure predict the same next outcome but update differently. Kernel
drift and numerical projection have concrete nonzero errors. Delayed parameter
deployment leaves assimilation and retained evidence separately observable.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.BayesianLearningDynamics.Controls

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory
open Mettapedia.ProbabilityTheory.BayesianInference

namespace BernoulliMemory

def counts (observations : List Bool) : ℕ × ℕ :=
  (observations.count true, observations.count false)

/-- The actual ordered Bernoulli likelihood before normalization. -/
def likelihood (observations : List Bool) (parameter : ℝ) : ℝ :=
  (observations.map fun observation => if observation then parameter else 1 - parameter).prod

theorem likelihood_eq_counts (observations : List Bool) (parameter : ℝ) :
    likelihood observations parameter =
      parameter ^ (counts observations).1 * (1 - parameter) ^ (counts observations).2 := by
  induction observations with
  | nil => simp [likelihood, counts]
  | cons observation rest ih =>
      have ih' := ih
      simp only [likelihood, counts] at ih'
      cases observation <;>
        simp [likelihood, counts, pow_succ, ih', mul_assoc, mul_left_comm, mul_comm]

/-- A sufficient count checkpoint preserves every future likelihood factor,
including after an arbitrarily long suspension. -/
theorem resume_likelihood (first second future : List Bool)
    (sameCounts : counts first = counts second) (parameter : ℝ) :
    likelihood (first ++ future) parameter = likelihood (second ++ future) parameter := by
  simp only [likelihood, List.map_append, List.prod_append]
  change likelihood first parameter * likelihood future parameter =
    likelihood second parameter * likelihood future parameter
  rw [likelihood_eq_counts first, likelihood_eq_counts second, sameCounts]

def batch (prior : BetaBernoulliPrior) (observations : List Bool) : BetaBernoulliPrior where
  α := prior.α + (counts observations).1
  β := prior.β + (counts observations).2
  α_pos := add_pos_of_pos_of_nonneg prior.α_pos (Nat.cast_nonneg _)
  β_pos := add_pos_of_pos_of_nonneg prior.β_pos (Nat.cast_nonneg _)

theorem beta_ext {first second : BetaBernoulliPrior}
    (alpha : first.α = second.α) (beta : first.β = second.β) : first = second := by
  cases first
  cases second
  simp_all

/-- The existing conjugate update and the sufficient-statistic batch agree in
both parameters, not just in the current posterior-mean readout. -/
theorem online_eq_batch (prior : BetaBernoulliPrior) (observations : List Bool) :
    observations.foldl BetaBernoulliPrior.posterior prior = batch prior observations := by
  induction observations generalizing prior with
  | nil => apply beta_ext <;> simp [batch, counts]
  | cons observation rest ih =>
      rw [List.foldl_cons, ih]
      apply beta_ext <;>
        cases observation <;>
        simp [batch, counts, BetaBernoulliPrior.posterior] <;> ring

theorem resume_posterior (prior : BetaBernoulliPrior) (past future : List Bool) :
    (past ++ future).foldl BetaBernoulliPrior.posterior prior =
      future.foldl BetaBernoulliPrior.posterior (batch prior past) := by
  rw [List.foldl_append]
  rw [online_eq_batch prior past]

def uniform : BetaBernoulliPrior := ⟨1, 1, by norm_num, by norm_num⟩

/-- Equal current predictions need not be sufficient for the next update. -/
theorem equal_prediction_different_updates :
    (batch uniform []).mean = (batch uniform [true, false]).mean ∧
      ((batch uniform []).posterior true).mean = 2 / 3 ∧
      ((batch uniform [true, false]).posterior true).mean = 3 / 5 ∧
      ((batch uniform []).posterior true).mean ≠
        ((batch uniform [true, false]).posterior true).mean := by
  norm_num [batch, uniform, counts, BetaBernoulliPrior.mean, BetaBernoulliPrior.posterior]

/-- The lost concentration has an exact predictive cost after one new datum. -/
theorem prediction_only_resume_error :
    |((batch uniform []).posterior true).mean -
      ((batch uniform [true, false]).posterior true).mean| = 1 / 15 := by
  norm_num [batch, uniform, counts, BetaBernoulliPrior.mean, BetaBernoulliPrior.posterior]

end BernoulliMemory

noncomputable def fair : Prob Bool :=
  ⟨fun _ => 1 / 2, (by intro state; norm_num), by simp⟩

noncomputable def report : PositiveLikelihood Bool :=
  ⟨fun state => if state then 3 / 4 else 1 / 4, by intro state; cases state <;> norm_num⟩

theorem report_posterior : (report.update fair).1 true = 3 / 4 := by
  norm_num [PositiveLikelihood.update, posterior_apply, evidence, fair, report, Fintype.sum_bool]

theorem two_report_posterior : (report.update (report.update fair)).1 true = 9 / 10 := by
  norm_num [PositiveLikelihood.update, posterior_apply, evidence, fair, report, Fintype.sum_bool]

/-- A point projection discards posterior uncertainty and has nonzero error. -/
theorem numerical_projection_error :
    l1Distance (report.update fair) (Prob.dirac true) = 1 / 2 := by
  norm_num [l1Distance, PositiveLikelihood.update, posterior_apply, evidence, fair, report,
    Prob.dirac, Fintype.sum_bool]

noncomputable def stationary (state : Bool) : Prob Bool := Prob.dirac state
noncomputable def drifting (state : Bool) : Prob Bool := Prob.dirac (!state)

/-- A model that omits a deterministic environmental flip is maximally wrong
in finite ℓ¹ distance, even with an uninformative observation. -/
theorem omitted_drift_error :
    l1Distance
      ((PositiveLikelihood.unit (S := Bool)).update (bind (Prob.dirac false) drifting))
      ((PositiveLikelihood.unit (S := Bool)).update (bind (Prob.dirac false) stationary)) = 2 := by
  norm_num [stationary, drifting, l1Distance, Prob.dirac]

theorem drift_row_bound (state : Bool) :
    l1Distance (drifting state) (stationary state) ≤ 2 := by
  cases state <;> norm_num [drifting, stationary, l1Distance, Prob.dirac, Fintype.sum_bool]

/-- The general propagation theorem applies to the concrete drift model. -/
theorem drift_certificate :
    l1Distance (bind (Prob.dirac false) drifting) (bind (Prob.dirac false) stationary) ≤
      l1Distance (Prob.dirac false) (Prob.dirac false) + 2 :=
  prediction_l1_bound _ _ drifting stationary 2 drift_row_bound

namespace SufficientMemory

/-- The visible state may be toggled; an unobserved persistent tag is
retained in the fine model but absent from all emissions. -/
noncomputable def fine : FilteringModel (Bool × Bool) Bool where
  transition action state := Prob.dirac (if action then (!state.1, state.2) else state)
  emission _ := ⟨fun state => report.value state.1, fun state => report.positive state.1⟩

noncomputable def coarse : FilteringModel Bool Bool where
  transition action state := Prob.dirac (if action then !state else state)
  emission _ := report

theorem transition (action : Bool) (state : Bool × Bool) :
    coarsen (fine.transition action state) Prod.fst = coarse.transition action state.1 := by
  cases action <;> simp [fine, coarse, coarsen_dirac]

/-- All future controlled predictions and observations can resume from the
visible-state distribution without retaining the irrelevant tag. -/
theorem exact_resume (first second : Prob (Bool × Bool))
    (same : coarsen first Prod.fst = coarsen second Prod.fst) (future : List Bool) :
    coarsen (fine.run future first) Prod.fst = coarsen (fine.run future second) Prod.fst :=
  FilteringModel.resume_from_sufficient Prod.fst fine coarse transition
    (fun _ _ => rfl) first second same future

/-- A concrete pair of distinct fine checkpoints has the same complete
future observable behavior. -/
theorem hidden_tag_resume (future : List Bool) :
    coarsen (fine.run future (Prob.dirac (false, false))) Prod.fst =
      coarsen (fine.run future (Prob.dirac (false, true))) Prod.fst :=
  exact_resume _ _ (by rw [coarsen_dirac, coarsen_dirac]) future

end SufficientMemory

open Mettapedia.MachineLearning.ContinualLearning.RealTimeContinualSchedule

/-- Two arrivals can be assimilated although only one parameter update fits
the same work schedule. Parameter cadence is not observation multiplicity. -/
theorem slower_deployment_full_evidence :
    completedUpdates twoRatio 2 = 1 ∧
      (PositiveLikelihood.online fair [report, report]).1 true = 9 / 10 := by
  constructor
  · decide
  · exact two_report_posterior

open Mettapedia.GSLT.Core.BranchingTemporal (Scheduler)
open Mettapedia.GSLT.Core.InferenceControl (Controller Snapshot)

noncomputable def initial : CoupledState Bool Unit ℝ Unit Unit Unit Unit where
  environment := ()
  arrived := []
  assimilated := []
  waiting := []
  posterior := fair
  approximation := fair
  deployed := 1 / 2
  inference := Snapshot.initial (Controller.fixed Scheduler.breadthFirst) []
  deploymentVersion := 0

noncomputable def assimilated :=
  (initial.arrive () ()).assimilate () [] report id

noncomputable def deployed :=
  assimilated.deploy (fun posterior _ => posterior.1 true)

/-- Assimilation updates the posterior while deployed parameters remain old;
deployment then catches up without counting the observation a second time. -/
theorem arrival_assimilation_deployment :
    assimilated.posterior.1 true = 3 / 4 ∧
      assimilated.deployed = 1 / 2 ∧
      deployed.deployed = 3 / 4 ∧
      deployed.posterior.1 true = 3 / 4 ∧
      deployed.assimilated = [()] ∧
      deployed.waiting = [] := by
  exact ⟨report_posterior, rfl, report_posterior, report_posterior, rfl, rfl⟩

#print axioms PositiveLikelihood.scheduled_batches_exact
#print axioms posterior_l1_bound
#print axioms filtering_l1_bound
#print axioms FilteringModel.resume_from_sufficient
#print axioms BernoulliMemory.online_eq_batch
#print axioms BernoulliMemory.equal_prediction_different_updates
#print axioms omitted_drift_error
#print axioms SufficientMemory.hidden_tag_resume
#print axioms scheduled_staleness_bound
#print axioms CoupledState.Transition.preserves_ledger
#print axioms CoupledState.predict_error
#print axioms CoupledState.assimilate_error
#print axioms CoupledState.resume_sound
#print axioms arrival_assimilation_deployment

end Mettapedia.PLN.WorldModel.BayesianLearningDynamics.Controls
