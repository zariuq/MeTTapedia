import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PreconditionedLearning

/-!
# State/error reparameterization and the initial sPC wavefront

This file formalizes the mathematical core of the sPC-to-ePC change of
variables from Goemaere, Oliviers, Bogacz, and Demeester, *ePC: Fast and Deep
Predictive Coding in Digital Simulation*.  The literature source is pinned to
arXiv:2505.20137v5, revised 2026-06-08; the arXiv source archive retrieved on
2026-07-15 had SHA-256
`956f8bc7cef3ab7f611ea7996601f0b070863d8aada903006160bc974f6763a8`.

The state/error correspondence below is exact for arbitrary nonlinear scalar
layers.  The differential theorem states the gradient relationship at the
coordinate-free Fréchet-derivative level.  The wavefront section separately
formalizes the paper's `λ^(L-i)` law and treats numerical detectability as an
explicit tolerance predicate, never as equality to zero in real arithmetic.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Exact nonlinear state/error correspondence -/

/-- Reconstruct the clamped state stream from a stream of prediction errors.
Index zero is the fixed input; error `n` perturbs the prediction of state
`n + 1`. -/
noncomputable def epcStateStream
    (layer : ℕ → ℝ → ℝ) (input : ℝ) (error : ℕ → ℝ) : ℕ → ℝ
  | 0 => input
  | n + 1 => layer n (epcStateStream layer input error n) + error n

/-- Extract the standard state-based prediction errors from a state stream. -/
noncomputable def spcErrorStream
    (layer : ℕ → ℝ → ℝ) (state : ℕ → ℝ) (n : ℕ) : ℝ :=
  state (n + 1) - layer n (state n)

/-- Extracting errors after recursively reconstructing states is exactly the
identity, with no regularity or linearity assumption on the layers. -/
theorem spcErrorStream_epcStateStream
    (layer : ℕ → ℝ → ℝ) (input : ℝ) (error : ℕ → ℝ) :
    spcErrorStream layer (epcStateStream layer input error) = error := by
  funext n
  simp [spcErrorStream, epcStateStream]

/-- Reconstructing states from their extracted errors returns every state
stream whose zeroth state obeys the input clamp. -/
theorem epcStateStream_spcErrorStream
    (layer : ℕ → ℝ → ℝ) (input : ℝ) (state : ℕ → ℝ)
    (hinput : state 0 = input) :
    epcStateStream layer input (spcErrorStream layer state) = state := by
  funext n
  induction n with
  | zero => simpa [epcStateStream] using hinput.symm
  | succ n ih => simp [epcStateStream, spcErrorStream, ih]

/-- Exact bijection between error streams and input-clamped state streams. -/
noncomputable def epcStateErrorEquiv
    (layer : ℕ → ℝ → ℝ) (input : ℝ) :
    (ℕ → ℝ) ≃ {state : ℕ → ℝ // state 0 = input} where
  toFun error := ⟨epcStateStream layer input error, rfl⟩
  invFun state := spcErrorStream layer state.1
  left_inv error := spcErrorStream_epcStateStream layer input error
  right_inv state := Subtype.ext
    (epcStateStream_spcErrorStream layer input state.1 state.2)

/-- Prefix sPC energy: squared state residuals plus an arbitrary terminal loss. -/
noncomputable def spcPrefixEnergy
    (depth : ℕ) (layer : ℕ → ℝ → ℝ) (state : ℕ → ℝ)
    (terminalLoss : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin depth, (spcErrorStream layer state i.val) ^ 2 +
    terminalLoss (state depth)

/-- Prefix ePC energy, written directly in error coordinates. -/
noncomputable def epcPrefixEnergy
    (depth : ℕ) (layer : ℕ → ℝ → ℝ) (input : ℝ)
    (error : ℕ → ℝ) (terminalLoss : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin depth, (error i.val) ^ 2 +
    terminalLoss (epcStateStream layer input error depth)

/-- Energy equivalence under the exact state/error bijection. -/
theorem epcPrefixEnergy_eq_spcPrefixEnergy
    (depth : ℕ) (layer : ℕ → ℝ → ℝ) (input : ℝ)
    (error : ℕ → ℝ) (terminalLoss : ℝ → ℝ) :
    epcPrefixEnergy depth layer input error terminalLoss =
      spcPrefixEnergy depth layer (epcStateStream layer input error)
        terminalLoss := by
  simp [epcPrefixEnergy, spcPrefixEnergy,
    spcErrorStream_epcStateStream]

/-! ## Differential and critical-point correspondence -/

section Differential

variable {State Error : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Error] [NormedSpace ℝ Error]

/-- Coordinate-free gradient relationship: if ePC energy is the pullback of
sPC energy along the state reconstruction, its derivative is the sPC
derivative composed with the reconstruction Jacobian. -/
theorem epcPullback_hasFDerivAt
    (toState : Error → State) (spcEnergy : State → ℝ)
    (error : Error) (jacobian : Error →L[ℝ] State)
    (spcDifferential : State →L[ℝ] ℝ)
    (hState : HasFDerivAt toState jacobian error)
    (hEnergy : HasFDerivAt spcEnergy spcDifferential (toState error)) :
    HasFDerivAt (fun e => spcEnergy (toState e))
      (spcDifferential ∘L jacobian) error := by
  exact hEnergy.comp error hState

/-- If the reconstruction Jacobian has a continuous-linear right inverse,
then composing a scalar differential with it is zero exactly when the original
differential is zero. -/
theorem differential_comp_eq_zero_iff_of_rightInverse
    (spcDifferential : State →L[ℝ] ℝ)
    (jacobian : Error →L[ℝ] State) (inverseJacobian : State →L[ℝ] Error)
    (hright : jacobian ∘L inverseJacobian = ContinuousLinearMap.id ℝ State) :
    spcDifferential ∘L jacobian = 0 ↔ spcDifferential = 0 := by
  constructor
  · intro hcomp
    apply ContinuousLinearMap.ext
    intro state
    have hjk : jacobian (inverseJacobian state) = state := by
      have := congrArg (fun f : State →L[ℝ] State => f state) hright
      simpa using this
    calc
      spcDifferential state =
          (spcDifferential ∘L jacobian) (inverseJacobian state) := by
            rw [ContinuousLinearMap.comp_apply, hjk]
      _ = 0 := by rw [hcomp]; rfl
      _ = (0 : State →L[ℝ] ℝ) state := rfl
  · rintro rfl
    simp

/-- Consequently an invertible state/error Jacobian preserves the vanishing
of the energy differential, i.e. the exact critical-point condition. -/
theorem epcCriticalDifferential_iff_spcCriticalDifferential
    (spcDifferential : State →L[ℝ] ℝ)
    (jacobian : Error →L[ℝ] State) (inverseJacobian : State →L[ℝ] Error)
    (hright : jacobian ∘L inverseJacobian = ContinuousLinearMap.id ℝ State) :
    spcDifferential ∘L jacobian = 0 ↔ spcDifferential = 0 :=
  differential_comp_eq_zero_iff_of_rightInverse
    spcDifferential jacobian inverseJacobian hright

end Differential

/-! ## Exact first-arrival attenuation -/

/-- A one-edge-per-step propagation recurrence.  Each newly reached layer
multiplies the preceding signal by the state learning rate `learningRate`. -/
noncomputable def spcWavefrontSignal
    (learningRate outputGradient : ℝ) : ℕ → ℝ
  | 0 => outputGradient
  | distance + 1 =>
      learningRate * spcWavefrontSignal learningRate outputGradient distance

/-- Closed form of the propagation recurrence. -/
theorem spcWavefrontSignal_closedForm
    (learningRate outputGradient : ℝ) (distance : ℕ) :
    spcWavefrontSignal learningRate outputGradient distance =
      learningRate ^ distance * outputGradient := by
  induction distance with
  | zero => simp [spcWavefrontSignal]
  | succ distance ih =>
      rw [spcWavefrontSignal, ih, pow_succ]
      ring

/-- The first signal reaching layer `i` in a depth-`L` chain carries exactly
the paper's `learningRate^(L-i)` factor. -/
theorem spcFirstArrivalSignal_layer_closedForm
    (learningRate outputGradient : ℝ) (depth layerIndex : ℕ)
    (_hlayer : layerIndex ≤ depth) :
    spcWavefrontSignal learningRate outputGradient (depth - layerIndex) =
      learningRate ^ (depth - layerIndex) * outputGradient :=
  spcWavefrontSignal_closedForm learningRate outputGradient _

/-- `BelowDetectionTolerance` is an external numerical acceptance policy.  It
does not identify a real signal with zero. -/
def BelowDetectionTolerance (tolerance signal : ℝ) : Prop :=
  |signal| < tolerance

/-- For every strict tolerance, a stable scalar multiplier eventually drives
the exact wavefront below that tolerance. -/
theorem spcWavefront_eventually_below_tolerance
    (learningRate outputGradient tolerance : ℝ)
    (hstable : |learningRate| < 1) (htolerance : 0 < tolerance) :
    ∃ distance,
      BelowDetectionTolerance tolerance
        (spcWavefrontSignal learningRate outputGradient distance) := by
  have hpow : Filter.Tendsto (fun n : ℕ => learningRate ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using hstable)
  have hsignal : Filter.Tendsto
      (fun n : ℕ => learningRate ^ n * outputGradient)
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hpow.mul_const outputGradient
  obtain ⟨distance, hdistance⟩ :=
    (Metric.tendsto_atTop.mp hsignal) tolerance htolerance
  refine ⟨distance, ?_⟩
  unfold BelowDetectionTolerance
  rw [spcWavefrontSignal_closedForm]
  have hmetric := hdistance distance le_rfl
  simpa [Real.dist_eq] using hmetric

/-- Positive boundary example: an exactly nonzero real signal may already be
below an explicit tolerance.  Thus tolerance loss is not real-number
underflow or an equality-to-zero theorem. -/
theorem spcWavefront_nonzero_but_below_tolerance_example :
    spcWavefrontSignal (1 / 2 : ℝ) 1 4 ≠ 0 ∧
      BelowDetectionTolerance (1 / 10 : ℝ)
        (spcWavefrontSignal (1 / 2 : ℝ) 1 4) := by
  rw [spcWavefrontSignal_closedForm]
  norm_num [BelowDetectionTolerance, abs_of_nonneg]

/-- Negative boundary: with unit multiplier and a nonzero unit output signal,
no depth enters any tolerance at or below one. -/
theorem spcWavefront_unitRate_not_below_small_tolerance
    (distance : ℕ) (tolerance : ℝ) (htolerance : tolerance ≤ 1) :
    ¬ BelowDetectionTolerance tolerance
      (spcWavefrontSignal 1 1 distance) := by
  simp [BelowDetectionTolerance, spcWavefrontSignal_closedForm, htolerance]

/-! ## One-step ePC/backprop boundary -/

/-- The first ePC error update from zero under a scalar loss gradient. -/
noncomputable def epcOneStepError
    (learningRate lossGradient : ℝ) : ℝ :=
  -learningRate * lossGradient

/-- The local PC parameter update induced by a prediction Jacobian and error. -/
noncomputable def pcLocalParameterUpdate
    (predictionJacobian error : ℝ) : ℝ :=
  -predictionJacobian * error

/-- The local parameter update computed in error coordinates is exactly the
state-based PC update after reconstruction.  The equality follows from the
nonlinear state/error inverse law, rather than from a linear-layer
assumption. -/
theorem epcLocalParameterUpdate_eq_spcLocalParameterUpdate
    (layer : ℕ → ℝ → ℝ) (input : ℝ) (error : ℕ → ℝ)
    (predictionJacobian : ℕ → ℝ) (index : ℕ) :
    pcLocalParameterUpdate (predictionJacobian index) (error index) =
      pcLocalParameterUpdate (predictionJacobian index)
        (spcErrorStream layer (epcStateStream layer input error) index) := by
  rw [spcErrorStream_epcStateStream]

/-- A single ePC step yields the corresponding backprop product, rescaled only
by the error learning rate. -/
theorem epcOneStepParameterUpdate_eq_rescaledBackprop
    (learningRate predictionJacobian lossGradient : ℝ) :
    pcLocalParameterUpdate predictionJacobian
        (epcOneStepError learningRate lossGradient) =
      learningRate * (predictionJacobian * lossGradient) := by
  simp [pcLocalParameterUpdate, epcOneStepError]
  ring

/-- At unit error learning rate, the one-step scalar update is exactly the
backprop product. -/
theorem epcOneStepParameterUpdate_unitRate_eq_backprop
    (predictionJacobian lossGradient : ℝ) :
    pcLocalParameterUpdate predictionJacobian
        (epcOneStepError 1 lossGradient) =
      predictionJacobian * lossGradient := by
  simpa using epcOneStepParameterUpdate_eq_rescaledBackprop
    1 predictionJacobian lossGradient

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
