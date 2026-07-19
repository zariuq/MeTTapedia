import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianOperator
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianChain

/-!
# Kalman correspondence for one workspace correction

The scalar Kalman measurement update has the workspace shape
`prior + gate * (proposal - prior)`.  This is a one-step Bayesian correction,
not a claim that repeatedly assimilating the same observation has the same
posterior as its fixed point.  Separately, the operator-level linear-Gaussian
energy equilibrium is transported from the predictive-coding spine and is
exactly its posterior mean.

The one-step and gain-risk algebra below are new workspace adapters.  The
posterior-mean equilibrium theorem is a direct lift of
`LinearGaussianOperatorModel.equilibrium_iff_eq_posteriorMean`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Set
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Scalar one-step workspace adapter -/

/-- The one-slot, one-operator observation update.  Its proposal is the old
state plus the observation innovation, so proposal minus old state is exactly
`observation - observationGain * oldState`. -/
noncomputable def scalarKalmanWorkspaceFamily
    (observation observationGain priorPrecision observationPrecision : ℝ) :
    GatedOperatorFamily (Fin 1) (Fin 1) ℝ ℝ ℝ where
  read := fun _ workspace => workspace 0
  transform := fun _ prior => prior
  gate := fun _ _ _ _ =>
    scalarKalmanGain observationGain priorPrecision observationPrecision
  write := fun _ workspace _ _ =>
    workspace 0 + (observation - observationGain * workspace 0)

/-- One scalar workspace correction is exactly the sealed scalar Kalman update.
No recurrence or repeated-observation claim is made. -/
theorem scalarKalmanWorkspaceStep_eq_update
    (observation observationGain priorPrecision observationPrecision : ℝ)
    (workspace : Workspace (Fin 1) ℝ) :
    (scalarKalmanWorkspaceFamily observation observationGain
      priorPrecision observationPrecision).step workspace 0 =
        scalarKalmanUpdate (workspace 0) observation observationGain
          priorPrecision observationPrecision := by
  simp [scalarKalmanWorkspaceFamily, GatedOperatorFamily.step,
    GatedOperatorFamily.operatorAverageScale, GatedOperatorFamily.gateAt,
    GatedOperatorFamily.contentAt, GatedOperatorFamily.latent,
    scalarKalmanUpdate]

/-- With unit observation gain and positive precisions, the Kalman gain is a
genuine workspace gate in `[0,1]`. -/
theorem scalarKalmanGain_unit_mem_Icc
    (priorPrecision observationPrecision : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision) :
    scalarKalmanGain 1 priorPrecision observationPrecision ∈ Icc (0 : ℝ) 1 := by
  have hsum : 0 < priorPrecision + observationPrecision := by linarith
  constructor
  · simp only [scalarKalmanGain, one_pow, mul_one]
    exact div_nonneg hobservation.le hsum.le
  · simp only [scalarKalmanGain, one_pow, mul_one]
    exact (div_le_one hsum).2 (by linarith)

/-- The unit-observation Kalman adapter satisfies the structural unit-interval
gate premise of `Dynamics`. -/
theorem scalarKalmanWorkspaceFamily_unit_gates
    (observation priorPrecision observationPrecision : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision)
    (workspace : Workspace (Fin 1) ℝ) :
    GatedOperatorFamily.GatesUnitInterval
      (scalarKalmanWorkspaceFamily observation 1 priorPrecision observationPrecision)
      workspace := by
  intro operator slot
  fin_cases operator
  fin_cases slot
  simpa [scalarKalmanWorkspaceFamily, GatedOperatorFamily.gateAt,
    GatedOperatorFamily.latent] using
      scalarKalmanGain_unit_mem_Icc priorPrecision observationPrecision
        hprior hobservation

/-! ## Gain optimality -/

/-- Mean-squared estimation risk for a scalar correction gain.  The prior and
observation precisions are positive and the corresponding variances are their
reciprocals. -/
noncomputable def scalarGainRisk
    (observationGain priorPrecision observationPrecision gate : ℝ) : ℝ :=
  (1 - gate * observationGain) ^ 2 / priorPrecision +
    gate ^ 2 / observationPrecision

/-- Exact excess-risk square around the Kalman gain. -/
theorem scalarGainRisk_sub_kalman_eq_square
    (observationGain priorPrecision observationPrecision gate : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision) :
    scalarGainRisk observationGain priorPrecision observationPrecision gate -
        scalarGainRisk observationGain priorPrecision observationPrecision
          (scalarKalmanGain observationGain priorPrecision observationPrecision) =
      ((priorPrecision + observationPrecision * observationGain ^ 2) /
          (priorPrecision * observationPrecision)) *
        (gate - scalarKalmanGain observationGain priorPrecision
          observationPrecision) ^ 2 := by
  have hden : 0 < priorPrecision +
      observationPrecision * observationGain ^ 2 := by
    positivity
  unfold scalarGainRisk scalarKalmanGain
  field_simp [ne_of_gt hprior, ne_of_gt hobservation, ne_of_gt hden]
  ring

/-- Gate-optimality crown: for positive precisions, the scalar Kalman gain is
the unique global minimizer of the one-step estimation risk. -/
theorem scalarKalmanGain_uniqueMinimizer
    (observationGain priorPrecision observationPrecision : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision) :
    (∀ gate,
      scalarGainRisk observationGain priorPrecision observationPrecision
          (scalarKalmanGain observationGain priorPrecision observationPrecision) ≤
        scalarGainRisk observationGain priorPrecision observationPrecision gate) ∧
    (∀ gate,
      scalarGainRisk observationGain priorPrecision observationPrecision gate =
          scalarGainRisk observationGain priorPrecision observationPrecision
            (scalarKalmanGain observationGain priorPrecision observationPrecision) ↔
        gate = scalarKalmanGain observationGain priorPrecision
          observationPrecision) := by
  have hcoefficient : 0 <
      (priorPrecision + observationPrecision * observationGain ^ 2) /
        (priorPrecision * observationPrecision) := by
    positivity
  constructor
  · intro gate
    have hsquare := scalarGainRisk_sub_kalman_eq_square
      observationGain priorPrecision observationPrecision gate hprior hobservation
    rw [sub_eq_iff_eq_add] at hsquare
    rw [hsquare]
    exact le_add_of_nonneg_left
      (mul_nonneg hcoefficient.le (sq_nonneg _))
  · intro gate
    constructor
    · intro heq
      have hsquare := scalarGainRisk_sub_kalman_eq_square
        observationGain priorPrecision observationPrecision gate hprior hobservation
      rw [heq, sub_self] at hsquare
      have hgateSquare :
          (gate - scalarKalmanGain observationGain priorPrecision
            observationPrecision) ^ 2 = 0 := by
        exact (mul_eq_zero.mp hsquare.symm).resolve_left hcoefficient.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hgateSquare)
    · rintro rfl
      rfl

/-! ## Transported operator-level posterior equilibrium -/

/-- A linear-Gaussian workspace state uses the sealed operator model's
Euclidean latent coordinate space. -/
abbrev LinearGaussianWorkspaceState (Latent : Type*) [Fintype Latent] :=
  LinearGaussianOperatorSpace Latent

/-- Posterior-equilibrium crown: the energy equilibrium of a linear-Gaussian
workspace state is exactly the conditional posterior mean.  This directly
instantiates the sealed operator theorem and does not identify it with the
fixed point of repeated assimilation of one observation. -/
theorem linearGaussianWorkspace_equilibrium_iff_eq_posteriorMean
    {Latent Residual : Type*}
    [Fintype Latent] [DecidableEq Latent]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Latent Residual)
    (workspace : LinearGaussianWorkspaceState Latent) :
    model.Equilibrium workspace ↔ workspace = model.posteriorMean :=
  model.equilibrium_iff_eq_posteriorMean workspace

/-! ## Positive and negative fixtures -/

/-- Equal precisions give the midpoint correction in one workspace step. -/
theorem equalPrecision_workspaceKalman_positiveExample :
    (scalarKalmanWorkspaceFamily 2 1 1 1).step (fun _ => 1) 0 = 3 / 2 := by
  rw [scalarKalmanWorkspaceStep_eq_update]
  norm_num [scalarKalmanUpdate, scalarKalmanGain]

/-- Reusing the same fixed gain on the same observation is not the original
one-observation posterior: the second step moves from `3/2` to `7/4`. -/
theorem repeatedObservation_not_samePosterior_negativeExample :
    (scalarKalmanWorkspaceFamily 2 1 1 1).step
        ((scalarKalmanWorkspaceFamily 2 1 1 1).step (fun _ => 1)) 0 ≠ 3 / 2 := by
  norm_num [scalarKalmanWorkspaceFamily, GatedOperatorFamily.step,
    GatedOperatorFamily.operatorAverageScale, GatedOperatorFamily.gateAt,
    GatedOperatorFamily.contentAt, GatedOperatorFamily.latent,
    scalarKalmanGain]

#print axioms scalarKalmanWorkspaceStep_eq_update
#print axioms scalarKalmanGain_uniqueMinimizer
#print axioms linearGaussianWorkspace_equilibrium_iff_eq_posteriorMean
#print axioms equalPrecision_workspaceKalman_positiveExample
#print axioms repeatedObservation_not_samePosterior_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
