import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedSettlingTrace
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.BroadcastProxy

/-!
# Transport from raw credit to optimizer direction

The implemented predictive rules first construct a raw local credit, then
apply global norm clipping and AdamW.  Uniform positive clipping preserves
alignment exactly.  A general optimizer transform requires its own error
budget: coordinatewise rescaling, stale moments, and decoupled weight decay can
all reverse alignment even when the raw credit is useful.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace OptimizerTransport

open scoped InnerProductSpace
open WorkNormalizedTruncation
open Instances

variable {Credit : Type*}
  [NormedAddCommGroup Credit] [InnerProductSpace ℝ Credit]

/-- Uniform clipping is represented by the scalar actually applied to every
coordinate of the raw credit. -/
noncomputable def uniformClip (scale : ℝ) (raw : Credit) : Credit :=
  scale • raw

theorem uniformClip_inner
    (exact raw : Credit) (scale : ℝ) :
    ⟪exact, uniformClip scale raw⟫_ℝ =
      scale * ⟪exact, raw⟫_ℝ := by
  simp [uniformClip, real_inner_smul_right]

/-- Any strictly positive uniform clip factor preserves strict alignment. -/
theorem uniformClip_preserves_positiveAlignment
    (exact raw : Credit) (scale : ℝ)
    (hscale : 0 < scale) (halignment : 0 < ⟪exact, raw⟫_ℝ) :
    0 < ⟪exact, uniformClip scale raw⟫_ℝ := by
  rw [uniformClip_inner]
  exact mul_pos hscale halignment

/-- An optimizer certificate is an explicit norm bound from the raw credit to
the direction that is actually subtracted from the parameters. -/
def HasOptimizerTransportError
    (raw transported : Credit) (optimizerError : ℝ) : Prop :=
  ‖transported - raw‖ ≤ optimizerError

omit [InnerProductSpace ℝ Credit] in
/-- Settling/readout error and optimizer transport error compose additively. -/
theorem transportedCreditError_le
    (exact raw transported : Credit) (rawError optimizerError : ℝ)
    (hraw : ‖raw - exact‖ ≤ rawError)
    (hoptimizer :
      HasOptimizerTransportError raw transported optimizerError) :
    ‖transported - exact‖ ≤ rawError + optimizerError := by
  calc
    ‖transported - exact‖ ≤
        ‖transported - raw‖ + ‖raw - exact‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le (transported - raw) (raw - exact)
    _ ≤ optimizerError + rawError :=
      add_le_add hoptimizer hraw
    _ = rawError + optimizerError := by ring

/-- The observed transported direction is certified when the complete raw plus
optimizer error is smaller than its own norm. -/
theorem transportedCredit_positiveAlignment
    (exact raw transported : Credit) (rawError optimizerError : ℝ)
    (hraw : ‖raw - exact‖ ≤ rawError)
    (hoptimizer :
      HasOptimizerTransportError raw transported optimizerError)
    (hrelative : rawError + optimizerError < ‖transported‖) :
    0 < ⟪exact, transported⟫_ℝ := by
  exact finiteCredit_positiveAlignment exact transported
    (rawError + optimizerError)
    (transportedCreditError_le exact raw transported rawError optimizerError
      hraw hoptimizer)
    hrelative

/-- The complete optimizer-aware radius plugs into the same finite-step task
descent theorem as a raw credit. -/
theorem transportedCredit_strictTaskDescent
    {loss : Credit → ℝ} {parameter exact raw transported : Credit}
    {rawError optimizerError curvature step : ℝ}
    (certificate :
      DirectionalTaskDescent.HasDirectionalTaskUpperModelAt loss parameter
        exact transported curvature)
    (hraw : ‖raw - exact‖ ≤ rawError)
    (hoptimizer :
      HasOptimizerTransportError raw transported optimizerError)
    (hstep : 0 < step)
    (htrust :
      step * curvature / 2 <
        ‖transported‖ *
          (‖transported‖ - (rawError + optimizerError))) :
    loss (parameter - step • transported) < loss parameter := by
  exact finiteCredit_strictTaskDescent certificate
    (transportedCreditError_le exact raw transported rawError optimizerError
      hraw hoptimizer)
    hstep htrust

/-! ## Source-relevant positive and negative boundaries -/

theorem halfClip_preserves_scalar_alignment :
    0 < ⟪(2 : ℝ), uniformClip (1 / 2) (3 : ℝ)⟫_ℝ := by
  apply uniformClip_preserves_positiveAlignment
  · norm_num
  · norm_num

noncomputable def diagonalFactor : CreditVec2 := ⟨1 / 1000, 1⟩
def alignedRaw : CreditVec2 := ⟨100, -99⟩
def exactTwo : CreditVec2 := ⟨1, 1⟩

/-- Positive coordinatewise factors are not a uniform clip: they can emphasize
the component on which raw and exact credit disagree and reverse alignment. -/
theorem positiveDiagonalTransport_can_reverse_alignment :
    0 < diagonalFactor.first ∧
      0 < diagonalFactor.second ∧
      0 < exactTwo.dot alignedRaw ∧
      exactTwo.dot (diagonalFactor.hadamard alignedRaw) < 0 := by
  norm_num [diagonalFactor, alignedRaw, exactTwo, CreditVec2.dot,
    CreditVec2.hadamard]

/-- Bias-corrected moment divided by its adaptive denominator, followed by
decoupled weight decay.  The learning-rate scalar is applied outside this
direction. -/
noncomputable def scalarAdamWDirection
    (preconditionedMoment parameter weightDecay : ℝ) : ℝ :=
  preconditionedMoment + weightDecay * parameter

/-- With the default positive weight-decay scale, a sufficiently large
oppositely signed parameter can reverse an otherwise aligned current moment. -/
theorem decoupledWeightDecay_can_reverse_current_alignment :
    (0 : ℝ) < 1 * 1 ∧
      1 * scalarAdamWDirection 1 (-200) (1 / 100) < 0 := by
  norm_num [scalarAdamWDirection]

/-- A stale first moment can oppose the current raw credit even without weight
decay; current-gradient telemetry alone cannot certify the optimizer step. -/
theorem staleMoment_can_reverse_current_alignment :
    (0 : ℝ) < 1 * 1 ∧
      1 * scalarAdamWDirection (-1) 0 0 < 0 := by
  norm_num [scalarAdamWDirection]

/-- The optimizer-error radius in the transport theorem is substantive. -/
theorem zeroOptimizerError_cannot_certify_reversed_scalar :
    ¬ HasOptimizerTransportError (1 : ℝ) (-1 : ℝ) 0 := by
  norm_num [HasOptimizerTransportError, Real.norm_eq_abs]

#print axioms uniformClip_preserves_positiveAlignment
#print axioms transportedCreditError_le
#print axioms transportedCredit_positiveAlignment
#print axioms transportedCredit_strictTaskDescent
#print axioms positiveDiagonalTransport_can_reverse_alignment
#print axioms decoupledWeightDecay_can_reverse_current_alignment
#print axioms staleMoment_can_reverse_current_alignment
#print axioms zeroOptimizerError_cannot_certify_reversed_scalar

end OptimizerTransport

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
