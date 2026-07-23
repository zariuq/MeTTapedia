import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefState
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.MatrixBelief
import Mettapedia.PLN.Bridges.PredictiveCoding.EvidenceRegisterBridge

/-!
# Statistical and penalty precision

Statistical precision belongs to a declared observation model.  Penalty
precision weights an algorithmic residual.  They produce the same scalar or
matrix equilibrium only when an explicit calibration premise identifies their
weights.  The separate types below prevent observation reliability, residual
penalties, signed errors, dual adjoints, natural parameters, and nonnegative
evidence counts from being exchanged merely because all can occur in a local
message.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PrecisionSemantics

open Set
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

noncomputable section

/-! ## Typed precision vocabulary -/

/-- Positive inverse variance supplied by a statistical observation model. -/
structure StatisticalPrecision where
  weight : ℝ
  weight_pos : 0 < weight

/-- Positive coefficient assigned to an algorithmic residual penalty. -/
structure PenaltyPrecision where
  weight : ℝ
  weight_pos : 0 < weight

/-- Calibration is an explicit equality between the two differently typed
precision weights. -/
def Calibrated (statistical : StatisticalPrecision)
    (penalty : PenaltyPrecision) : Prop :=
  statistical.weight = penalty.weight

/-- Signed Gaussian natural parameter. -/
structure NaturalParameter where
  value : ℝ

/-- Signed prediction residual with an explicitly chosen orientation. -/
structure PredictionError where
  value : ℝ

/-- Signed multiplier or adjoint associated with a constraint. -/
structure DualAdjoint where
  value : ℝ

/-- Nonnegative support count; dependence and provenance remain separate
obligations on a collection of counts. -/
structure EvidenceCount where
  value : ℝ
  value_nonneg : 0 ≤ value

/-- A tagged local-message language that keeps the six semantic roles
disjoint. -/
inductive LocalMessage where
  | statisticalPrecision (precision : StatisticalPrecision)
  | penaltyPrecision (precision : PenaltyPrecision)
  | naturalParameter (parameter : NaturalParameter)
  | predictionError (error : PredictionError)
  | dualAdjoint (adjoint : DualAdjoint)
  | evidenceCount (count : EvidenceCount)

/-- Statistical and penalty precision remain distinct messages even when
their underlying real weights coincide. -/
theorem statisticalPrecision_ne_penaltyPrecision
    (statistical : StatisticalPrecision) (penalty : PenaltyPrecision) :
    LocalMessage.statisticalPrecision statistical ≠
      LocalMessage.penaltyPrecision penalty := by
  simp

/-- Evidence counts cannot encode a negative signed message. -/
theorem no_negative_evidenceCount :
    ¬ ∃ count : EvidenceCount, count.value = -1 := by
  rintro ⟨count, hcount⟩
  linarith [count.value_nonneg]

/-! ## Scalar coincidence and converse -/

/-- Posterior mean under a declared independent Gaussian observation. -/
def statisticalPosteriorMean
    (priorMean observation : ℝ) (prior : StatisticalPrecision)
    (observationReliability : StatisticalPrecision) : ℝ :=
  gaussianFusion priorMean observation prior.weight observationReliability.weight

/-- Equilibrium selected by a scalar quadratic residual penalty. -/
def penaltyEquilibrium
    (priorMean observation : ℝ) (prior : StatisticalPrecision)
    (penalty : PenaltyPrecision) : ℝ :=
  gaussianFusion priorMean observation prior.weight penalty.weight

/-- The penalty equilibrium minimizes the corresponding two-residual
quadratic energy. -/
theorem penaltyEquilibrium_isMinOn
    (priorMean observation : ℝ) (prior : StatisticalPrecision)
    (penalty : PenaltyPrecision) :
    IsMinOn
      (twoSourceGaussianEnergy priorMean observation
        prior.weight penalty.weight) univ
      (penaltyEquilibrium priorMean observation prior penalty) := by
  exact gaussianFusion_isMinOn_twoSourceGaussianEnergy
    priorMean observation prior.weight penalty.weight
      prior.weight_pos penalty.weight_pos

/-- Matching the residual penalty to the observation reliability makes the
PC equilibrium equal the statistical posterior mean. -/
theorem penaltyEquilibrium_eq_statisticalPosterior_of_calibrated
    (priorMean observation : ℝ) (prior : StatisticalPrecision)
    (statistical : StatisticalPrecision) (penalty : PenaltyPrecision)
    (hcalibrated : Calibrated statistical penalty) :
    penaltyEquilibrium priorMean observation prior penalty =
      statisticalPosteriorMean priorMean observation prior statistical := by
  change statistical.weight = penalty.weight at hcalibrated
  simp only [penaltyEquilibrium, statisticalPosteriorMean]
  rw [← hcalibrated]

/-- Converse calibration theorem: for a fixed positive prior, equality of the
two affine fusion maps for every observation forces the penalty weight to be
the declared statistical precision. -/
theorem penaltyEquilibrium_eq_forall_iff_calibrated
    (priorMean : ℝ) (prior statistical : StatisticalPrecision)
    (penalty : PenaltyPrecision) :
    (∀ observation,
      penaltyEquilibrium priorMean observation prior penalty =
        statisticalPosteriorMean priorMean observation prior statistical) ↔
      Calibrated statistical penalty := by
  constructor
  · intro hmaps
    have h := hmaps (priorMean + 1)
    have hpenaltySum : prior.weight + penalty.weight ≠ 0 :=
      ne_of_gt (add_pos prior.weight_pos penalty.weight_pos)
    have hstatisticalSum : prior.weight + statistical.weight ≠ 0 :=
      ne_of_gt (add_pos prior.weight_pos statistical.weight_pos)
    simp only [penaltyEquilibrium, statisticalPosteriorMean, gaussianFusion] at h
    field_simp [hpenaltySum, hstatisticalSum] at h
    unfold Calibrated
    nlinarith [prior.weight_pos]
  · intro hcalibrated observation
    exact penaltyEquilibrium_eq_statisticalPosterior_of_calibrated
      priorMean observation prior statistical penalty hcalibrated

/-! ## Matrix coincidence by covariance matching -/

/-- Replace only the residual penalty operator of an existing affine
linear-Gaussian model.  This keeps the real operator geometry and offset while
making the algorithmic penalty choice explicit. -/
def operatorModelWithResidualPenalty
    {Latent Residual : Type*}
    [Fintype Latent] [DecidableEq Latent]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Latent Residual)
    (penalty : Matrix Residual Residual ℝ) (hpenalty : penalty.PosDef) :
    LinearGaussianOperatorModel Latent Residual where
  residualMatrix := model.residualMatrix
  residualPrecision := penalty
  residualOffset := model.residualOffset
  residualMatrix_injective := model.residualMatrix_injective
  residualPrecision_posDef := hpenalty

/-- Matrix Gaussian coincidence: when the algorithmic residual penalty is
the inverse-covariance precision of the statistical model, its quadratic
equilibrium is exactly that model's conditional posterior mean. -/
theorem matrixPenaltyEquilibrium_iff_eq_statisticalPosterior
    {Latent Residual : Type*}
    [Fintype Latent] [DecidableEq Latent]
    [Fintype Residual] [DecidableEq Residual]
    (statisticalModel : LinearGaussianOperatorModel Latent Residual)
    (penalty : Matrix Residual Residual ℝ) (hpenalty : penalty.PosDef)
    (hcalibrated : penalty = statisticalModel.residualPrecision)
    (state : LinearGaussianOperatorSpace Latent) :
    (operatorModelWithResidualPenalty statisticalModel penalty hpenalty).Equilibrium state ↔
      state = ∫ posteriorState, posteriorState ∂statisticalModel.posterior := by
  subst penalty
  simpa [operatorModelWithResidualPenalty] using
    statisticalModel.equilibrium_iff_eq_conditionalPosteriorMean state

/-! ## Executable positive and negative boundaries -/

/-- Unit statistical precision. -/
def unitStatisticalPrecision : StatisticalPrecision :=
  ⟨1, by norm_num⟩

/-- Statistical precision four. -/
def fourStatisticalPrecision : StatisticalPrecision :=
  ⟨4, by norm_num⟩

/-- Penalty precision four. -/
def fourPenaltyPrecision : PenaltyPrecision :=
  ⟨4, by norm_num⟩

/-- Statistical precision one hundredth. -/
def hundredthStatisticalPrecision : StatisticalPrecision :=
  ⟨1 / 100, by norm_num⟩

/-- Penalty precision one hundred. -/
def hundredPenaltyPrecision : PenaltyPrecision :=
  ⟨100, by norm_num⟩

/-- Penalty precision one. -/
def unitPenaltyPrecision : PenaltyPrecision :=
  ⟨1, by norm_num⟩

/-- Penalty precision two. -/
def twoPenaltyPrecision : PenaltyPrecision :=
  ⟨2, by norm_num⟩

/-- The matched rational fixture produces `17/25` in both semantic charts. -/
theorem matchedPrecision_positiveExample :
    statisticalPosteriorMean (1 / 5) (4 / 5)
        unitStatisticalPrecision fourStatisticalPrecision = 17 / 25 ∧
      penaltyEquilibrium (1 / 5) (4 / 5)
        unitStatisticalPrecision fourPenaltyPrecision = 17 / 25 := by
  norm_num [statisticalPosteriorMean, penaltyEquilibrium, gaussianFusion,
    unitStatisticalPrecision, fourStatisticalPrecision, fourPenaltyPrecision]

/-- A statistically weak observation and an algorithmically strong penalty
select `1/101` and `100/101`, respectively.  Reusing the residual expression
does not calibrate the penalty. -/
theorem miscalibratedPrecision_negativeExample :
    statisticalPosteriorMean 0 1 unitStatisticalPrecision
        hundredthStatisticalPrecision = 1 / 101 ∧
      penaltyEquilibrium 0 1 unitStatisticalPrecision
        hundredPenaltyPrecision = 100 / 101 ∧
      statisticalPosteriorMean 0 1 unitStatisticalPrecision
          hundredthStatisticalPrecision ≠
        penaltyEquilibrium 0 1 unitStatisticalPrecision
          hundredPenaltyPrecision := by
  norm_num [statisticalPosteriorMean, penaltyEquilibrium, gaussianFusion,
    unitStatisticalPrecision, hundredthStatisticalPrecision,
    hundredPenaltyPrecision]

/-- Treating one dependent unit packet as two independent penalty terms moves
the equilibrium from `1/2` to `2/3`.  The correct dependence-aware target
retains the single-packet value. -/
theorem dependentDuplicate_changesPenalty_negativeExample :
    statisticalPosteriorMean 0 1 unitStatisticalPrecision
        unitStatisticalPrecision = 1 / 2 ∧
      penaltyEquilibrium 0 1 unitStatisticalPrecision
        twoPenaltyPrecision = 2 / 3 ∧
      statisticalPosteriorMean 0 1 unitStatisticalPrecision
          unitStatisticalPrecision ≠
        penaltyEquilibrium 0 1 unitStatisticalPrecision
          twoPenaltyPrecision := by
  norm_num [statisticalPosteriorMean, penaltyEquilibrium, gaussianFusion,
    unitStatisticalPrecision, twoPenaltyPrecision]

/-- Concrete signed-message boundary from the conformance fixture: reversing
the residual reverses the penalty force, while neither force nor the natural
parameter equals the positive precision. -/
theorem signedMessageRoles_negativeExample :
    (2 : ℝ) * (4 / 5 - 1 / 5) = 6 / 5 ∧
      (2 : ℝ) * (1 / 5 - 4 / 5) = -6 / 5 ∧
      (2 : ℝ) * (1 / 5) = 2 / 5 ∧
      (2 : ℝ) ≠ 6 / 5 ∧
      (2 : ℝ) ≠ 2 / 5 := by
  norm_num

#print axioms statisticalPrecision_ne_penaltyPrecision
#print axioms no_negative_evidenceCount
#print axioms penaltyEquilibrium_isMinOn
#print axioms penaltyEquilibrium_eq_statisticalPosterior_of_calibrated
#print axioms penaltyEquilibrium_eq_forall_iff_calibrated
#print axioms matrixPenaltyEquilibrium_iff_eq_statisticalPosterior
#print axioms matchedPrecision_positiveExample
#print axioms miscalibratedPrecision_negativeExample
#print axioms dependentDuplicate_changesPenalty_negativeExample
#print axioms signedMessageRoles_negativeExample

end

end PrecisionSemantics

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
