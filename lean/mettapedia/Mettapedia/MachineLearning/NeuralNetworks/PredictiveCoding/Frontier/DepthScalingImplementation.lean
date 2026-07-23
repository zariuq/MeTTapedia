import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.DepthScalingRepair

/-!
# Executable correspondence for the depth-scaling repairs

This file pins the executable artifacts and closes the schedule-coordinate
gap between the paper-facing covariance presentation and the implementation's
precision multiplier.  The implementation stores precision `alpha` away from
the error wavefront and precision `1` at first arrival.  The scalar model in
`DepthScalingRepair` factors out `alpha` and uses covariance `1` away from the
wavefront and covariance `alpha` at arrival.  The theorem below proves that
these give exactly the same effective coefficient.

The implementation sources audited here are:

* `changqi97/DeepPCNs` commit
  `99472b071f4bec483ddfe7ed37c6c3c10680d8bc`;
* `changqi97/pcx` commit
  `b68e7460069eeeb081f5481a9e2ae4358f823b19`.

The remaining bridges identify the four executable mechanisms used by the
code: stored `h0` forward references, auxiliary delay buffers on residual
paths, and frozen BatchNorm statistics during the inner inference loop.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

/-! ## Pinned executable provenance -/

structure DepthRepairImplementationPin where
  repository : String
  commit : String
  deriving DecidableEq, Repr

def deepPCNsImplementationPin : DepthRepairImplementationPin where
  repository := "changqi97/DeepPCNs"
  commit := "99472b071f4bec483ddfe7ed37c6c3c10680d8bc"

def pcxDepthRepairImplementationPin : DepthRepairImplementationPin where
  repository := "changqi97/pcx"
  commit := "b68e7460069eeeb081f5481a9e2ae4358f823b19"

def depthRepairImplementationPins : List DepthRepairImplementationPin :=
  [deepPCNsImplementationPin, pcxDepthRepairImplementationPin]

theorem depthRepairImplementationPins_distinct :
    deepPCNsImplementationPin ≠ pcxDepthRepairImplementationPin := by
  decide

/-! ## Spiking-precision implementation bridge -/

/-- The executable schedule in `model.py`: base precision `alpha`, replaced
by unit precision exactly when the wavefront reaches the layer. -/
noncomputable def implementedSpikingPrecision
    (alpha : ℝ) (time distance : ℕ) : ℝ :=
  if distance = time then 1 else alpha

/-- Exact bridge from the executable energy multiplier to the covariance
chart used by the scalar formalization. -/
theorem implementedSpikingPrecision_eq_rate_div_formalCovariance
    (alpha : ℝ) (time distance : ℕ) (halpha : alpha ≠ 0) :
    implementedSpikingPrecision alpha time distance =
      alpha / spikingCovariance alpha time distance := by
  by_cases hwavefront : distance = time
  · simp [implementedSpikingPrecision, spikingCovariance, hwavefront, halpha]
  · simp [implementedSpikingPrecision, spikingCovariance, hwavefront]

/-- Positive executable fixture at the paper's default `alpha = 0.001`:
arrival precision is one and pre-arrival precision is `0.001`. -/
theorem implementedSpikingPrecision_default_positiveFixture :
    implementedSpikingPrecision (1 / 1000) 4 4 = 1 ∧
      implementedSpikingPrecision (1 / 1000) 3 4 = 1 / 1000 ∧
      implementedSpikingPrecision (1 / 1000) 4 4 =
        (1 / 1000 : ℝ) / spikingCovariance (1 / 1000) 4 4 := by
  norm_num [implementedSpikingPrecision, spikingCovariance]

/-- Negative fixture: the nonzero premise is necessary.  At `alpha = 0`,
the executable schedule still spikes to one, while `0 / 0 = 0` in Lean's
field convention. -/
theorem implementedSpikingPrecision_zero_not_covarianceRatio :
    implementedSpikingPrecision 0 2 2 ≠
      (0 : ℝ) / spikingCovariance 0 2 2 := by
  norm_num [implementedSpikingPrecision, spikingCovariance]

/-! ## Forward-reference implementation bridge -/

/-- Executable `FU` reads the stored initialization value `h0`. -/
noncomputable def executableForwardUpdateError
    (initialH0 finalActivity : ℕ → ℝ) (layer : ℕ) : ℝ :=
  finalActivity layer - initialH0 layer

theorem executableForwardUpdateError_eq_formalForwardReference
    (initialH0 finalActivity : ℕ → ℝ) (layer : ℕ) :
    executableForwardUpdateError initialH0 finalActivity layer =
      forwardReferencePredictionError initialH0 finalActivity layer := by
  rfl

/-- Positive fixture: stored `h0` remains a zero-error reference while a
settled prediction with unit accumulated drift differs at every positive
depth. -/
theorem executableForwardUpdate_unitDrift_positiveFixture
    (layer : ℕ) (hlayer : 0 < layer) :
    executableForwardUpdateError (fun _ ↦ 0) (fun _ ↦ 0) layer = 0 ∧
      standardSettledPredictionError (fun _ ↦ 0) (fun _ ↦ 0)
        (fun _ ↦ 1) layer ≠ 0 := by
  constructor
  · simp [executableForwardUpdateError]
  · simp [standardSettledPredictionError, cumulativePredictionDrift]
    exact_mod_cast Nat.ne_of_gt hlayer

/-- Negative fixture: when predictions do not drift, `h0` and settled
references induce the same error. -/
theorem executableForwardUpdate_zeroDrift_negativeFixture
    (initialH0 finalActivity : ℕ → ℝ) (layer : ℕ) :
    standardSettledPredictionError initialH0 finalActivity (fun _ ↦ 0) layer =
      executableForwardUpdateError initialH0 finalActivity layer := by
  rw [zeroDrift_standard_eq_forward]
  rfl

/-! ## Residual-buffer implementation bridge -/

/-- Executable residual branches insert one stateful auxiliary node for each
main-path layer bypassed by the skip. -/
def executableResidualAuxiliaryCount (skipped : ℕ) : ℕ := skipped

/-- Arrival time of the executable buffered skip branch. -/
def executableBufferedResidualArrivalTime (skipped : ℕ) : ℕ :=
  residualSkipArrivalTime + executableResidualAuxiliaryCount skipped

theorem executableResidualBuffers_eq_formalCount (skipped : ℕ) :
    executableResidualAuxiliaryCount skipped =
      residualAuxiliaryBufferCount skipped := by
  rfl

/-- Positive fixture: the executable auxiliary count synchronizes the skip
and main branches exactly. -/
theorem executableResidualBuffers_positiveFixture (skipped : ℕ) :
    executableBufferedResidualArrivalTime skipped =
      residualMainPathArrivalTime skipped := by
  simp [executableBufferedResidualArrivalTime,
    executableResidualAuxiliaryCount, residualSkipArrivalTime,
    residualMainPathArrivalTime]
  omega

/-- Negative fixture: omitting all executable auxiliary nodes makes a
nontrivial skip arrive strictly before its main branch. -/
theorem executableResidualBuffers_missing_negativeFixture
    (skipped : ℕ) (hskipped : 0 < skipped) :
    residualSkipArrivalTime < residualMainPathArrivalTime skipped :=
  residualSkip_arrives_early skipped hskipped

/-! ## Frozen-BatchNorm implementation bridge -/

/-- The `init_step = true` inner loop restores the prior running statistic;
its executable state transition is therefore the identity. -/
noncomputable def executableFrozenBatchNormStep (statistic : ℝ) : ℝ :=
  statistic

theorem executableFrozenBatchNormStep_eq_formalFreeze :
    executableFrozenBatchNormStep = frozenBatchStatisticStep := by
  funext statistic
  rfl

/-- Positive fixture: every number of executable inference steps preserves
the running statistic exactly. -/
theorem executableFrozenBatchNorm_positiveFixture
    (statistic : ℝ) (steps : ℕ) :
    Nat.iterate executableFrozenBatchNormStep steps statistic = statistic := by
  rw [executableFrozenBatchNormStep_eq_formalFreeze]
  exact frozenBatchStatistic_iterate_exact statistic steps

/-- Negative fixture: a live zero-momentum update on a different batch does
not implement the frozen transition. -/
theorem executableFrozenBatchNorm_live_negativeFixture :
    liveBatchStatisticStep 0 1 0 ≠ executableFrozenBatchNormStep 0 := by
  norm_num [liveBatchStatisticStep, executableFrozenBatchNormStep]

structure DepthRepairImplementationCertificate : Prop where
  precisionBridge :
    ∀ (alpha : ℝ) (time distance : ℕ), alpha ≠ 0 →
      implementedSpikingPrecision alpha time distance =
        alpha / spikingCovariance alpha time distance
  forwardBridge :
    ∀ (initialH0 finalActivity : ℕ → ℝ) (layer : ℕ),
      executableForwardUpdateError initialH0 finalActivity layer =
        forwardReferencePredictionError initialH0 finalActivity layer
  residualBridge :
    ∀ skipped : ℕ,
      executableBufferedResidualArrivalTime skipped =
        residualMainPathArrivalTime skipped
  batchNormBridge : executableFrozenBatchNormStep = frozenBatchStatisticStep

theorem depthRepairImplementation_crown :
    DepthRepairImplementationCertificate where
  precisionBridge := implementedSpikingPrecision_eq_rate_div_formalCovariance
  forwardBridge := executableForwardUpdateError_eq_formalForwardReference
  residualBridge := executableResidualBuffers_positiveFixture
  batchNormBridge := executableFrozenBatchNormStep_eq_formalFreeze

#print axioms implementedSpikingPrecision_eq_rate_div_formalCovariance
#print axioms depthRepairImplementation_crown

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
