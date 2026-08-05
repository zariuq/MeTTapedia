import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Cadence
import Mettapedia.MachineLearning.ContinualLearning.EvidenceLedger
import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.InterferenceGram
import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.PCPlasticity

/-!
# Two-timescale adaptation: consolidation laws

This file proves three boundaries for repeated consolidations:

* a consolidated evidence contribution must be removed from the carried fast
  ledger or it is counted exactly twice;
* linear centered consolidation operators commute exactly when their task
  curvatures commute, for a nonzero update rate; and
* matched target progress protects prior capability only on the same residual
  branch (H5), with the reflected endpoint as a checked failure case.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

/-! ## T4: consolidation without double counting -/

/-- Scale a Gaussian evidence contribution in its additive natural
coordinates. -/
noncomputable def scaleGaussianEvidence {Index : Type*}
    (factor : ℝ) (evidence : GaussianEvidence Index) : GaussianEvidence Index where
  precision := factor • evidence.precision
  naturalParameter := factor • evidence.naturalParameter

/-- Carry fresh evidence plus a declared fraction of an already consolidated
contribution.  `discount = 1` is naive reuse; `discount = 0` is calibrated
reset of the reused part while retaining all fresh evidence. -/
noncomputable def discountedEvidenceCarry {Index : Type*}
  (discount : ℝ) (consolidated fresh : GaussianEvidence Index) :
    GaussianEvidence Index :=
  fresh.add (scaleGaussianEvidence discount consolidated)

/-- Ledger after burning one contribution into slow weights and then carrying
the next period's fast evidence. -/
noncomputable def ledgerAfterConsolidation {Index : Type*}
    (prior consolidated fresh : GaussianEvidence Index) (discount : ℝ) :
    GaussianEvidence Index :=
  (prior.update consolidated).update
    (discountedEvidenceCarry discount consolidated fresh)

/-- Discounting the reused contribution to zero restores once-each additive
calibration exactly. -/
theorem discountedReset_restores_calibration {Index : Type*}
    (prior consolidated fresh : GaussianEvidence Index) :
    ledgerAfterConsolidation prior consolidated fresh 0 =
      (prior.update consolidated).update fresh := by
  apply GaussianEvidence.extensionality
  · ext i j
    simp [ledgerAfterConsolidation, discountedEvidenceCarry,
      GaussianEvidence.update, GaussianEvidence.add, scaleGaussianEvidence]
  · funext i
    simp [ledgerAfterConsolidation, discountedEvidenceCarry,
      GaussianEvidence.update, GaussianEvidence.add, scaleGaussianEvidence]

/-- Carrying the full consolidated contribution is exactly the causal-ledger
reuse pattern already proved to contain one extra copy. -/
theorem unitCarry_eq_naive_reuse {Index : Type*}
    (prior consolidated fresh : GaussianEvidence Index) :
    ledgerAfterConsolidation prior consolidated fresh 1 =
      ((prior.update consolidated).update consolidated).update fresh := by
  rw [GaussianEvidence.reused_contribution_exact_excess]
  apply GaussianEvidence.extensionality
  · ext i j
    simp [ledgerAfterConsolidation, discountedEvidenceCarry,
      GaussianEvidence.update, GaussianEvidence.add, scaleGaussianEvidence]
  · funext i
    simp [ledgerAfterConsolidation, discountedEvidenceCarry,
      GaussianEvidence.update, GaussianEvidence.add, scaleGaussianEvidence]

/-- T4 exact excess in both Gaussian natural coordinates. -/
theorem naiveConsolidateThenContinue_exact_excess {Index : Type*}
    (prior consolidated fresh : GaussianEvidence Index) :
    (ledgerAfterConsolidation prior consolidated fresh 1).precision =
        ((prior.update consolidated).update fresh).precision +
          consolidated.precision ∧
      (ledgerAfterConsolidation prior consolidated fresh 1).naturalParameter =
        ((prior.update consolidated).update fresh).naturalParameter +
          consolidated.naturalParameter := by
  rw [unitCarry_eq_naive_reuse]
  exact ⟨GaussianEvidence.reused_precision_exact prior consolidated fresh,
    GaussianEvidence.reused_naturalParameter_exact prior consolidated fresh⟩

/-- Positive and negative scalar fixture: unit carry yields precision two,
whereas the calibrated zero-discount reset yields precision one. -/
theorem scalarLedger_discount :
    (ledgerAfterConsolidation zeroScalarEvidence unitScalarEvidence
        zeroScalarEvidence 1).precision 0 0 = 2 ∧
      (ledgerAfterConsolidation zeroScalarEvidence unitScalarEvidence
        zeroScalarEvidence 0).precision 0 0 = 1 := by
  constructor <;>
    norm_num [ledgerAfterConsolidation, discountedEvidenceCarry,
      GaussianEvidence.update, GaussianEvidence.add, scaleGaussianEvidence,
      zeroScalarEvidence, unitScalarEvidence, Matrix.one_apply]

/-! ## T5: when consolidation order matters -/

/-- Linear centered one-period weight update induced by curvature `A` and
step size `step`: `I - step A`. -/
noncomputable def centeredConsolidationOperator
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (step : ℝ) (curvature : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  1 - step • curvature

/-- The operator commutator is exactly the curvature commutator scaled by the
square of the update step. -/
theorem centeredConsolidationOperator_commutator_exact
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (step : ℝ) (first second : Matrix Index Index ℝ) :
    matrixCommutator
        (centeredConsolidationOperator step first)
        (centeredConsolidationOperator step second) =
      step ^ 2 • matrixCommutator first second := by
  simp only [centeredConsolidationOperator, matrixCommutator,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  module

/-- Operational commutation of the two derived linear update operators. -/
def CurvatureConsolidationsCommute
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (step : ℝ) (first second : Matrix Index Index ℝ) : Prop :=
  Commute (centeredConsolidationOperator step first)
    (centeredConsolidationOperator step second)

/-- T5 iff: for any nonzero update step, consolidation operators commute
exactly when their generating curvatures commute. -/
theorem curvatureConsolidations_commute_iff
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (step : ℝ) (first second : Matrix Index Index ℝ) (hstep : step ≠ 0) :
    CurvatureConsolidationsCommute step first second ↔ Commute first second := by
  change Commute (centeredConsolidationOperator step first)
      (centeredConsolidationOperator step second) ↔ Commute first second
  simp only [Commute, SemiconjBy]
  constructor
  · intro hop
    have hcommutator :
        matrixCommutator
            (centeredConsolidationOperator step first)
            (centeredConsolidationOperator step second) = 0 :=
      sub_eq_zero.mpr hop.symm
    rw [centeredConsolidationOperator_commutator_exact] at hcommutator
    have hcurvature : matrixCommutator first second = 0 :=
      (smul_eq_zero.mp hcommutator).resolve_left (pow_ne_zero 2 hstep)
    exact (sub_eq_zero.mp hcurvature).symm
  · intro hcurvature
    have hcurvatureZero : matrixCommutator first second = 0 :=
      sub_eq_zero.mpr hcurvature.symm
    have hoperatorZero :
        matrixCommutator
            (centeredConsolidationOperator step first)
            (centeredConsolidationOperator step second) = 0 := by
      rw [centeredConsolidationOperator_commutator_exact, hcurvatureZero,
        smul_zero]
    exact (sub_eq_zero.mp hoperatorZero).symm

/-- The existing degree-two diagnostic is therefore a complete certificate
for order invariance in this nonzero-step linear centered model. -/
theorem curvatureConsolidations_commute_iff_zero_interference
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (step : ℝ) (first second : Matrix Index Index ℝ) (hstep : step ≠ 0) :
    CurvatureConsolidationsCommute step first second ↔
      pairwiseInterferenceEnergy first second = 0 := by
  rw [curvatureConsolidations_commute_iff step first second hstep]
  exact (pairwiseInterferenceEnergy_eq_zero_iff_commute first second).symm

/-- Positive fixture: orthogonal coordinate curvatures commute. -/
theorem orthogonalConsolidations_commute :
    CurvatureConsolidationsCommute 1
      orthogonalFirstTask.curvature orthogonalSecondTask.curvature := by
  rw [curvatureConsolidations_commute_iff 1 _ _ one_ne_zero]
  show orthogonalFirstTask.curvature * orthogonalSecondTask.curvature =
    orthogonalSecondTask.curvature * orthogonalFirstTask.curvature
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orthogonalFirstTask, orthogonalSecondTask,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Negative fixture: the oblique pair has noncommuting consolidation
operators and its two period orders produce different final parameters. -/
theorem obliqueConsolidations_order_matters :
    ¬ CurvatureConsolidationsCommute 1
        obliqueFirstTask.curvature obliqueSecondTask.curvature ∧
      sequentialTwoTaskUpdate obliqueFirstTask obliqueSecondTask 1
          obliqueParameter ≠
        sequentialTwoTaskUpdate obliqueSecondTask obliqueFirstTask 1
          obliqueParameter := by
  constructor
  · rw [curvatureConsolidations_commute_iff 1 _ _ one_ne_zero]
    intro hcommute
    exact obliqueTasks_curvature_interference.1
      (sub_eq_zero.mpr hcommute.eq.symm)
  · exact obliqueTasks_curvature_interference.2

/-! ## T6: retention across scalar quadratic periods -/

/-- Unit-curvature scalar period task centered at its requested capability. -/
noncomputable def scalarPeriodTask (center : ℝ) : QuadraticTask (Fin 1) where
  curvature := 1
  optimum := fun _ => center

noncomputable def scalarPeriodParameter (value : ℝ) : Fin 1 → ℝ :=
  fun _ => value

/-- QuadraticTwoTask's update is exactly the scalar endpoint used by the
matched-progress/H5 machinery. -/
theorem scalarPeriodTask_update_eq_gradientEndpoint
    (center initial step : ℝ) :
    (scalarPeriodTask center).update step (scalarPeriodParameter initial) 0 =
      scalarGradientEndpoint center initial step := by
  norm_num [QuadraticTask.update, QuadraticTask.gradient, scalarPeriodTask,
    scalarPeriodParameter, scalarGradientEndpoint, Matrix.mulVec, dotProduct]

/-- Retention comparison phrased as prior-period capability loss. -/
def PriorCapabilityNoWorse
    (sourceCenter initial candidate reference : ℝ) : Prop :=
  sourceForgetting sourceCenter initial candidate ≤
    sourceForgetting sourceCenter initial reference

/-- Absolute deployment budget for retaining a prior period's capability. -/
def PreservesPriorCapabilityWithin
    (sourceCenter initial endpoint budget : ℝ) : Prop :=
  sourceForgetting sourceCenter initial endpoint ≤ budget

/-- T6 positive boundary: matched target progress plus the same-sign H5
condition guarantees that the next consolidation loses no more prior-period
capability than its reference update. -/
theorem quadraticPeriodRetention_of_matchedProgress_sameBranch
    (sourceCenter targetCenter initial candidateStep referenceStep : ℝ)
    (hprogress : MatchedTargetProgress targetCenter initial
      ((scalarPeriodTask targetCenter).update candidateStep
        (scalarPeriodParameter initial) 0)
      ((scalarPeriodTask targetCenter).update referenceStep
        (scalarPeriodParameter initial) 0))
    (hbranch : SameTargetResidualBranch targetCenter
      ((scalarPeriodTask targetCenter).update candidateStep
        (scalarPeriodParameter initial) 0)
      ((scalarPeriodTask targetCenter).update referenceStep
        (scalarPeriodParameter initial) 0)) :
    PriorCapabilityNoWorse sourceCenter initial
      ((scalarPeriodTask targetCenter).update candidateStep
        (scalarPeriodParameter initial) 0)
      ((scalarPeriodTask targetCenter).update referenceStep
        (scalarPeriodParameter initial) 0) := by
  exact sameTargetResidualBranch_restores_sourceForgetting_bound
    sourceCenter targetCenter initial _ _ hprogress hbranch

/-- Unit trust bounds derive H5 rather than assuming it separately. -/
theorem quadraticPeriodRetention_of_matchedProgress_unitTrust
    (sourceCenter targetCenter initial candidateStep referenceStep : ℝ)
    (hprogress : MatchedTargetProgress targetCenter initial
      ((scalarPeriodTask targetCenter).update candidateStep
        (scalarPeriodParameter initial) 0)
      ((scalarPeriodTask targetCenter).update referenceStep
        (scalarPeriodParameter initial) 0))
    (hcandidate : UnitTrustBound candidateStep)
    (hreference : UnitTrustBound referenceStep) :
    PriorCapabilityNoWorse sourceCenter initial
      ((scalarPeriodTask targetCenter).update candidateStep
        (scalarPeriodParameter initial) 0)
      ((scalarPeriodTask targetCenter).update referenceStep
        (scalarPeriodParameter initial) 0) := by
  rw [scalarPeriodTask_update_eq_gradientEndpoint,
    scalarPeriodTask_update_eq_gradientEndpoint] at hprogress ⊢
  exact matchedProgress_unitTrustBounds_restore_sourceForgetting
    sourceCenter targetCenter initial candidateStep referenceStep
    hprogress hcandidate hreference

/-- If a reference consolidation preserves the prior capability within a
declared budget, matched progress and unit-trust H5 transport that same budget
to the candidate consolidation. -/
theorem quadraticPeriod_preserves_reference_capabilityBudget
    (sourceCenter targetCenter initial candidateStep referenceStep budget : ℝ)
    (hprogress : MatchedTargetProgress targetCenter initial
      ((scalarPeriodTask targetCenter).update candidateStep
        (scalarPeriodParameter initial) 0)
      ((scalarPeriodTask targetCenter).update referenceStep
        (scalarPeriodParameter initial) 0))
    (hcandidate : UnitTrustBound candidateStep)
    (hreference : UnitTrustBound referenceStep)
    (hbudget : PreservesPriorCapabilityWithin sourceCenter initial
      ((scalarPeriodTask targetCenter).update referenceStep
        (scalarPeriodParameter initial) 0) budget) :
    PreservesPriorCapabilityWithin sourceCenter initial
      ((scalarPeriodTask targetCenter).update candidateStep
        (scalarPeriodParameter initial) 0) budget := by
  exact (quadraticPeriodRetention_of_matchedProgress_unitTrust
    sourceCenter targetCenter initial candidateStep referenceStep
    hprogress hcandidate hreference).trans hbudget

/-- Positive retention fixture inside the unit trust region. -/
theorem halfStep_periodRetention :
    PriorCapabilityNoWorse 0 1
      ((scalarPeriodTask 2).update (1 / 2) (scalarPeriodParameter 1) 0)
      ((scalarPeriodTask 2).update (1 / 2) (scalarPeriodParameter 1) 0) := by
  exact le_rfl

/-- Negative boundary: matched progress without H5 can reverse retention.
Both endpoints are generated by actual scalar quadratic period updates. -/
theorem reflectedPeriodConsolidation_retention_failure :
    MatchedTargetProgress 1 0
        ((scalarPeriodTask 1).update (3 / 2) (scalarPeriodParameter 0) 0)
        ((scalarPeriodTask 1).update (1 / 2) (scalarPeriodParameter 0) 0) ∧
      ¬ SameTargetResidualBranch 1
        ((scalarPeriodTask 1).update (3 / 2) (scalarPeriodParameter 0) 0)
        ((scalarPeriodTask 1).update (1 / 2) (scalarPeriodParameter 0) 0) ∧
      ¬ PriorCapabilityNoWorse 0 0
        ((scalarPeriodTask 1).update (3 / 2) (scalarPeriodParameter 0) 0)
        ((scalarPeriodTask 1).update (1 / 2) (scalarPeriodParameter 0) 0) := by
  simp only [scalarPeriodTask_update_eq_gradientEndpoint]
  norm_num [scalarGradientEndpoint, MatchedTargetProgress,
    targetLossProgress, scalarQuadraticLoss, SameTargetResidualBranch,
    PriorCapabilityNoWorse, sourceForgetting]

/-- The reflected overshoot also violates the explicit quarter-unit retention
budget met by the reference half-step. -/
theorem reflectedPeriodConsolidation_breaks_capabilityBudget :
    PreservesPriorCapabilityWithin 0 0
        ((scalarPeriodTask 1).update (1 / 2) (scalarPeriodParameter 0) 0)
        (1 / 4) ∧
      ¬ PreservesPriorCapabilityWithin 0 0
        ((scalarPeriodTask 1).update (3 / 2) (scalarPeriodParameter 0) 0)
        (1 / 4) := by
  simp only [scalarPeriodTask_update_eq_gradientEndpoint]
  norm_num [PreservesPriorCapabilityWithin, sourceForgetting,
    scalarQuadraticLoss, scalarGradientEndpoint]

#print axioms naiveConsolidateThenContinue_exact_excess
#print axioms curvatureConsolidations_commute_iff_zero_interference
#print axioms obliqueConsolidations_order_matters
#print axioms quadraticPeriodRetention_of_matchedProgress_unitTrust
#print axioms quadraticPeriod_preserves_reference_capabilityBudget
#print axioms reflectedPeriodConsolidation_retention_failure

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
