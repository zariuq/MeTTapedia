import Mettapedia.ProbabilityTheory.BayesianInference.Variational

/-!
# Generalized EM for finite latent models

The observed likelihood is obtained by summing out the latent state.
With an exact E-step, any increase in expected complete-data log
likelihood increases the data likelihood, subject to the stated support
conditions. The difference includes a posterior KL term.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianInference.ExpectationMaximization

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open scoped BigOperators

variable {S O I : Type*} [Fintype S] [Fintype O]

structure Model (S O : Type*) [Fintype S] [Fintype O] where
  prior : Prob S
  channel : S → Prob O

namespace Model

def likelihood (model : Model S O) (y : O) (s : S) : ℝ := (model.channel s).1 y

theorem likelihood_nonneg (model : Model S O) (y : O) (s : S) :
    0 ≤ model.likelihood y s := (model.channel s).2.1 y

noncomputable def observationMass (model : Model S O) (y : O) : ℝ :=
  evidence model.prior (model.likelihood y)

theorem observationMass_eq (model : Model S O) (y : O) :
    model.observationMass y = (observationLaw model.prior model.channel).1 y := rfl

noncomputable def eStep (model : Model S O) (y : O) (supported : 0 < model.observationMass y) :
    Prob S :=
  posterior model.prior (model.likelihood y) (model.likelihood_nonneg y) supported

/-- Expected complete-data log probability for one observation. -/
noncomputable def completeScore (model : Model S O) (y : O) (q : Prob S) : ℝ :=
  ∑ s, q.1 s * Real.log (model.prior.1 s * model.likelihood y s)

private theorem score_plus_freeEnergy (model : Model S O) (y : O) (q : Prob S) :
    model.completeScore y q + variationalFreeEnergy model.prior (model.likelihood y) q =
      ∑ s, q.1 s * Real.log (q.1 s) := by
  unfold completeScore variationalFreeEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem log_gain_eq_complete_gain_add_kl (old new : Model S O) (y : O)
    (oldPossible : 0 < old.observationMass y) (newPossible : 0 < new.observationMass y)
    (support : SupportedBy (old.eStep y oldPossible)
      (fun s => new.prior.1 s * new.likelihood y s)) :
    Real.log (new.observationMass y) - Real.log (old.observationMass y) =
      new.completeScore y (old.eStep y oldPossible) - old.completeScore y (old.eStep y oldPossible) +
        klSum (old.eStep y oldPossible).1 (new.eStep y newPossible).1 := by
  let q := old.eStep y oldPossible
  have previous := old.score_plus_freeEnergy y q
  have current := new.score_plus_freeEnergy y q
  have oldBound : variationalFreeEnergy old.prior (old.likelihood y) q =
      -Real.log (old.observationMass y) :=
    variationalFreeEnergy_posterior old.prior (old.likelihood y) _ oldPossible
  have newBound : variationalFreeEnergy new.prior (new.likelihood y) q =
      klSum q.1 (new.eStep y newPossible).1 - Real.log (new.observationMass y) :=
    variationalFreeEnergy_eq new.prior q _ _ newPossible support
  rw [oldBound] at previous
  rw [newBound] at current
  linarith

theorem complete_gain_le_log_gain (old new : Model S O) (y : O)
    (oldPossible : 0 < old.observationMass y) (newPossible : 0 < new.observationMass y)
    (support : SupportedBy (old.eStep y oldPossible)
      (fun s => new.prior.1 s * new.likelihood y s)) :
    new.completeScore y (old.eStep y oldPossible) - old.completeScore y (old.eStep y oldPossible) ≤
      Real.log (new.observationMass y) - Real.log (old.observationMass y) := by
  let p := old.eStep y oldPossible
  let q := new.eStep y newPossible
  have bound : 0 ≤ klSum p.1 q.1 :=
    klSumOn_nonneg Finset.univ p.1 q.1
      (fun s _ => p.2.1 s) (fun s _ => q.2.1 s)
      (fun s _ => supportedBy_posterior new.prior p _ _ newPossible support s)
      (by rw [p.2.2, q.2.2])
  rw [old.log_gain_eq_complete_gain_add_kl new y oldPossible newPossible support]
  exact le_add_of_nonneg_right bound

variable [Fintype I]

noncomputable def logLikelihood (model : Model S O) (data : I → O) : ℝ :=
  ∑ i, Real.log (model.observationMass (data i))

noncomputable def qScore (model : Model S O) (data : I → O) (latent : I → Prob S) : ℝ :=
  ∑ i, model.completeScore (data i) (latent i)

/-- A generalized M-step need only improve the batch Q score. -/
theorem generalized_step (old new : Model S O) (data : I → O)
    (oldPossible : ∀ i, 0 < old.observationMass (data i))
    (newPossible : ∀ i, 0 < new.observationMass (data i))
    (support : ∀ i, SupportedBy (old.eStep (data i) (oldPossible i))
      (fun s => new.prior.1 s * new.likelihood (data i) s))
    (improves : old.qScore data (fun i => old.eStep (data i) (oldPossible i)) ≤
      new.qScore data (fun i => old.eStep (data i) (oldPossible i))) :
    old.logLikelihood data ≤ new.logLikelihood data := by
  have gap := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    old.complete_gain_le_log_gain new (data i) (oldPossible i) (newPossible i) (support i))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at gap
  unfold qScore at improves
  unfold logLikelihood
  linarith

end Model
end Mettapedia.ProbabilityTheory.BayesianInference.ExpectationMaximization
