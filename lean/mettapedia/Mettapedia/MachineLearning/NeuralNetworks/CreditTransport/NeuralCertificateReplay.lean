import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OptimizerTransport
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ErrorCoordinateResidualSemantics

/-!
# Formal boundary for fixed-checkpoint neural certificate replay

A replay can reconstruct the raw local credit, the direction actually
subtracted by a uniform-rate optimizer, their transport distance, and the
final energy-gradient/precision scalar identity for prospective latent and
deep error-coordinate settling.  Those measured equalities do not establish
uniform contraction, readout sensitivity, a negative-curvature budget below
precision, or that a longer finite-depth credit is the exact equilibrium
credit.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace NeuralCertificateReplay

open scoped InnerProductSpace
open OptimizerTransport
open NonlinearResolvent
open ProspectiveResidualSemantics
open ErrorCoordinateResidualSemantics

variable {Credit : Type*}
  [NormedAddCommGroup Credit] [InnerProductSpace ℝ Credit]

/-- One fixed-depth neural replay row after resolving tensor hashes back to
their mathematical values. -/
structure ReplayRow (Credit : Type*) where
  depth : ℕ
  rawCredit : Credit
  transportedDirection : Credit
  parameterDisplacement : Credit
  uniformLearningRate : ℝ
  rawCreditNorm : ℝ
  transportedDirectionNorm : ℝ
  optimizerTransportError : ℝ
  finiteReferenceCredit : Credit
  finiteReferenceGap : ℝ

/-- Every optimizer-derived scalar field and the sign convention of the
parameter displacement are reconstructible from the resolved tensors. -/
structure OptimizerReconstructible (row : ReplayRow Credit) : Prop where
  learningRate_pos : 0 < row.uniformLearningRate
  rawCreditNorm_eq : row.rawCreditNorm = ‖row.rawCredit‖
  transportedDirectionNorm_eq :
    row.transportedDirectionNorm = ‖row.transportedDirection‖
  optimizerTransportError_eq :
    row.optimizerTransportError =
      ‖row.transportedDirection - row.rawCredit‖
  parameterDisplacement_eq :
    row.parameterDisplacement =
      -(row.uniformLearningRate) • row.transportedDirection
  finiteReferenceGap_eq :
    row.finiteReferenceGap =
      ‖row.rawCredit - row.finiteReferenceCredit‖

/-- Reconstruction of the emitted distance supplies exactly the optimizer
transport premise used by the credit calculus. -/
theorem OptimizerReconstructible.hasOptimizerTransportError
    {row : ReplayRow Credit}
    (reconstructible : OptimizerReconstructible row) :
    HasOptimizerTransportError row.rawCredit row.transportedDirection
      row.optimizerTransportError := by
  rw [HasOptimizerTransportError,
    ← reconstructible.optimizerTransportError_eq]

/-- A replay row becomes an optimizer-aware alignment certificate only after
an independent raw-to-exact credit error bound is supplied. -/
theorem OptimizerReconstructible.positiveAlignment
    {row : ReplayRow Credit} {exactCredit : Credit} {rawError : ℝ}
    (reconstructible : OptimizerReconstructible row)
    (rawBound : ‖row.rawCredit - exactCredit‖ ≤ rawError)
    (relative :
      rawError + row.optimizerTransportError <
        row.transportedDirectionNorm) :
    0 < ⟪exactCredit, row.transportedDirection⟫_ℝ := by
  apply transportedCredit_positiveAlignment exactCredit row.rawCredit
    row.transportedDirection rawError row.optimizerTransportError rawBound
    reconstructible.hasOptimizerTransportError
  simpa [reconstructible.transportedDirectionNorm_eq] using relative

/-- Scalar fields recomputed at a final accepted latent or error-coordinate
state.  The vector equations are owned by `ProspectiveResidualSemantics` and
`ErrorCoordinateResidualSemantics`; this structure records their common norm
identity. -/
structure EnergyGradientResidualFields where
  precision : ℝ
  finalEnergyGradientNorm : ℝ
  finalEquationResidualNorm : ℝ

/-- A replayed equation-residual scalar is the final energy-gradient norm
divided by positive precision. -/
structure EnergyGradientResidualReconstructible
    (fields : EnergyGradientResidualFields) : Prop where
  precision_pos : 0 < fields.precision
  residual_eq :
    fields.finalEquationResidualNorm =
      fields.finalEnergyGradientNorm / fields.precision

theorem EnergyGradientResidualReconstructible.residual_zero_iff_gradient_zero
    {fields : EnergyGradientResidualFields}
    (reconstructible : EnergyGradientResidualReconstructible fields) :
    fields.finalEquationResidualNorm = 0 ↔
      fields.finalEnergyGradientNorm = 0 := by
  rw [reconstructible.residual_eq, div_eq_zero_iff]
  simp [ne_of_gt reconstructible.precision_pos]

/-- A replayed deep-ePC gradient field becomes an equilibrium-distance
certificate only after its vector norm is reconstructed and the declared task
gradient is `rho`-hypomonotone with `rho` strictly below precision. -/
theorem EnergyGradientResidualReconstructible.errorCoordinateDistanceBound
    {fields : EnergyGradientResidualFields}
    (reconstructible : EnergyGradientResidualReconstructible fields)
    (rho : ℝ) (taskGradient : Credit → Credit) (error : Credit)
    {exactResolver : Credit → Credit}
    (hdominates : rho < fields.precision)
    (htask : HypomonotoneMap rho taskGradient)
    (gradientNorm_eq :
      fields.finalEnergyGradientNorm =
        ‖errorCoordinateEnergyGradient
          fields.precision taskGradient error‖)
    (resolventEquation : IsUnitResolventMapOf
      (prospectiveImplicitOperator
        fields.precision taskGradient) exactResolver) :
    ‖error - exactResolver 0‖ ≤
      fields.finalEnergyGradientNorm / (fields.precision - rho) := by
  rw [gradientNorm_eq]
  exact distance_exactErrorState_le_finalGradient_div_curvatureGap
      fields.precision rho taskGradient error
      (ne_of_gt reconstructible.precision_pos) hdominates htask
      resolventEquation

/-! ## Positive and negative fixtures -/

noncomputable def positiveReplayRow : ReplayRow ℝ where
  depth := 4
  rawCredit := 2
  transportedDirection := 3
  parameterDisplacement := -(3 / 10)
  uniformLearningRate := 1 / 10
  rawCreditNorm := 2
  transportedDirectionNorm := 3
  optimizerTransportError := 1
  finiteReferenceCredit := 5 / 2
  finiteReferenceGap := 1 / 2

theorem positiveReplayRow_reconstructible :
    OptimizerReconstructible positiveReplayRow := by
  constructor <;>
    norm_num [positiveReplayRow, Real.norm_eq_abs]

theorem positiveReplayRow_alignment_with_raw_bound :
    0 < ⟪(2 : ℝ), positiveReplayRow.transportedDirection⟫_ℝ := by
  apply positiveReplayRow_reconstructible.positiveAlignment (rawError := 0)
  · norm_num [positiveReplayRow, Real.norm_eq_abs]
  · norm_num [positiveReplayRow]

noncomputable def positiveEnergyGradientResidual :
    EnergyGradientResidualFields where
  precision := 4
  finalEnergyGradientNorm := 2
  finalEquationResidualNorm := 1 / 2

theorem positiveEnergyGradientResidual_reconstructible :
    EnergyGradientResidualReconstructible positiveEnergyGradientResidual := by
  constructor <;> norm_num [positiveEnergyGradientResidual]

/-- Exact agreement with a longer finite-depth reference says nothing about
the unknown exact equilibrium credit without an independent error theorem. -/
theorem zeroFiniteReferenceGap_does_not_identify_exactCredit :
    let raw : ℝ := 1
    let finiteReference : ℝ := 1
    let exactCredit : ℝ := -1
    ‖raw - finiteReference‖ = 0 ∧ ‖raw - exactCredit‖ = 2 := by
  norm_num [Real.norm_eq_abs]

/-- A reported gradient norm does not become a resolver residual merely by
copying the same scalar into the residual field when precision is not one. -/
theorem copiedGradientNorm_not_equationResidual :
    ¬ EnergyGradientResidualReconstructible
      { precision := 4
        finalEnergyGradientNorm := 2
        finalEquationResidualNorm := 2 } := by
  intro claimed
  have residual_eq := claimed.residual_eq
  norm_num at residual_eq

#print axioms OptimizerReconstructible.hasOptimizerTransportError
#print axioms OptimizerReconstructible.positiveAlignment
#print axioms EnergyGradientResidualReconstructible.residual_zero_iff_gradient_zero
#print axioms EnergyGradientResidualReconstructible.errorCoordinateDistanceBound
#print axioms positiveReplayRow_reconstructible
#print axioms positiveReplayRow_alignment_with_raw_bound
#print axioms positiveEnergyGradientResidual_reconstructible
#print axioms zeroFiniteReferenceGap_does_not_identify_exactCredit
#print axioms copiedGradientNorm_not_equationResidual

end NeuralCertificateReplay

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
