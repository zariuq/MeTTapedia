import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FeedbackAlignmentDegeneracy

/-!
# Error-driven input modulation and antialignment

Dellaferrera and Kreiman, *Error-driven Input Modulation: solving the
credit assignment problem without a backward pass* (ICML 2022,
arXiv:2201.11665), analyze PEPITA on a whitened linear network with one hidden
layer.  With hidden weights `A`, output weights `W`, fixed feedback `F`, and
end-to-end error `E`, their continuous-time equations are

`Wdot = E Aᵀ` and `Adot = -A F E`.

The source derives antialignment by replacing `Aᵀ A` with the scalar
`‖A‖²`.  That replacement requires an isotropic input Gram matrix and is not
valid for a general matrix `A`.  The antialignment conclusion itself has a
stronger repair: the hidden-norm velocity in the first, hidden-only phase and
the overlap velocity in the second, output-only phase contain the same
Gram-weighted transport trace, in opposite signs.  Cyclicity of matrix trace
therefore proves antialignment without discarding the Gram matrix.

This file provides:

* the exact scalar equations and strict antialignment implication;
* the corrected finite-dimensional matrix theorem with the Gram matrix kept;
* the isotropic specialization that licenses the source's unweighted trace
  inference; and
* an anisotropic two-dimensional Gram fixture where hidden norm grows and the
  corrected overlap derivative is negative, while the unweighted transport
  trace is positive.

The statements concern the two decoupled infinitesimal phases used in the
source analysis.  They do not infer convergence of the simultaneous nonlinear
training dynamics or empirical efficacy.

Source artifact SHA-256:
`af65c31d19e2a03165dd3a9ba18f47ca0c749f41cd590deb84d30c505a544d92`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PEPITAAntialignment

open scoped Matrix

/-! ## Exact scalar PEPITA dynamics -/

/-- Scalar one-hidden-unit state for the whitened linear PEPITA model. -/
structure ScalarState where
  hiddenWeight : ℝ
  outputWeight : ℝ

/-- End-to-end scalar error `T - W A`. -/
def scalarError (target : ℝ) (state : ScalarState) : ℝ :=
  target - state.outputWeight * state.hiddenWeight

/-- Hidden-weight velocity `-A F E` from the error-modulated pass. -/
def scalarHiddenVelocity
    (feedback target : ℝ) (state : ScalarState) : ℝ :=
  -state.hiddenWeight * feedback * scalarError target state

/-- Output-weight velocity `E A` from the standard pass. -/
def scalarOutputVelocity
    (target : ℝ) (state : ScalarState) : ℝ :=
  scalarError target state * state.hiddenWeight

/-- Infinitesimal velocity of the squared hidden-weight norm in the
hidden-only phase. -/
def scalarHiddenNormSqVelocity
    (feedback target : ℝ) (state : ScalarState) : ℝ :=
  2 * state.hiddenWeight * scalarHiddenVelocity feedback target state

/-- Infinitesimal velocity of `F W A` in the output-only phase, with `A`
frozen. -/
def scalarFrozenHiddenOverlapVelocity
    (feedback target : ℝ) (state : ScalarState) : ℝ :=
  feedback * scalarOutputVelocity target state * state.hiddenWeight

/-- The hidden-norm velocity is the negative double of the subsequent
output-only overlap velocity. -/
theorem scalarHiddenNormSqVelocity_eq_neg_two_overlapVelocity
    (feedback target : ℝ) (state : ScalarState) :
    scalarHiddenNormSqVelocity feedback target state =
      -2 * scalarFrozenHiddenOverlapVelocity feedback target state := by
  simp [scalarHiddenNormSqVelocity, scalarFrozenHiddenOverlapVelocity,
    scalarHiddenVelocity, scalarOutputVelocity]
  ring

/-- In the scalar model, increasing hidden norm forces negative
feedback-error transport. -/
theorem scalar_feedback_mul_error_neg_of_hiddenNormSqVelocity_pos
    (feedback target : ℝ) (state : ScalarState)
    (hgrowth :
      0 < scalarHiddenNormSqVelocity feedback target state) :
    feedback * scalarError target state < 0 := by
  have hsquare : 0 ≤ state.hiddenWeight ^ 2 := sq_nonneg state.hiddenWeight
  simp [scalarHiddenNormSqVelocity, scalarHiddenVelocity] at hgrowth
  nlinarith

/-- The source's decoupled-phase scalar antialignment implication. -/
theorem scalar_overlapVelocity_neg_of_hiddenNormSqVelocity_pos
    (feedback target : ℝ) (state : ScalarState)
    (hgrowth :
      0 < scalarHiddenNormSqVelocity feedback target state) :
    scalarFrozenHiddenOverlapVelocity feedback target state < 0 := by
  rw [scalarHiddenNormSqVelocity_eq_neg_two_overlapVelocity] at hgrowth
  linarith

/-- A zero hidden weight is a genuine flat boundary: neither diagnostic
moves infinitesimally. -/
theorem scalar_zeroHiddenWeight_boundary
    (feedback target outputWeight : ℝ) :
    scalarHiddenNormSqVelocity feedback target ⟨0, outputWeight⟩ = 0 ∧
      scalarFrozenHiddenOverlapVelocity feedback target
        ⟨0, outputWeight⟩ = 0 := by
  simp [scalarHiddenNormSqVelocity, scalarFrozenHiddenOverlapVelocity,
    scalarHiddenVelocity, scalarOutputVelocity]

/-! ## Corrected matrix theorem -/

variable {input hidden output : Type}
variable [Fintype input]
variable [Fintype hidden]
variable [Fintype output]

/-- Input-space Gram matrix `Aᵀ A` of the hidden weights. -/
def inputGram (hiddenWeight : Matrix hidden input ℝ) :
    Matrix input input ℝ :=
  hiddenWeight.transpose * hiddenWeight

/-- Input-space error transport `F E`. -/
def feedbackErrorTransport
    (feedback : Matrix input output ℝ)
    (error : Matrix output input ℝ) :
    Matrix input input ℝ :=
  feedback * error

/-- Velocity of `tr(Aᵀ A)` under `Adot = -A F E`. -/
def hiddenNormSqVelocity
    (hiddenWeight : Matrix hidden input ℝ)
    (feedback : Matrix input output ℝ)
    (error : Matrix output input ℝ) : ℝ :=
  -2 * Matrix.trace
    (inputGram hiddenWeight * feedbackErrorTransport feedback error)

/-- Velocity of `tr(F W A)` under `Wdot = E Aᵀ`, with `A` frozen. -/
def frozenHiddenOverlapVelocity
    (hiddenWeight : Matrix hidden input ℝ)
    (feedback : Matrix input output ℝ)
    (error : Matrix output input ℝ) : ℝ :=
  Matrix.trace
    (feedbackErrorTransport feedback error * inputGram hiddenWeight)

/-- The two phase diagnostics use the same Gram-weighted transport trace.
This is the trace-cyclicity repair of the source derivation. -/
theorem hiddenNormSqVelocity_eq_neg_two_overlapVelocity
    (hiddenWeight : Matrix hidden input ℝ)
    (feedback : Matrix input output ℝ)
    (error : Matrix output input ℝ) :
    hiddenNormSqVelocity hiddenWeight feedback error =
      -2 * frozenHiddenOverlapVelocity hiddenWeight feedback error := by
  rw [hiddenNormSqVelocity, frozenHiddenOverlapVelocity]
  rw [Matrix.trace_mul_comm
    (inputGram hiddenWeight) (feedbackErrorTransport feedback error)]

/-- General finite-dimensional antialignment: hidden-norm growth in the first
decoupled phase forces overlap decrease in the second phase.  No isotropy
assumption is needed. -/
theorem overlapVelocity_neg_of_hiddenNormSqVelocity_pos
    (hiddenWeight : Matrix hidden input ℝ)
    (feedback : Matrix input output ℝ)
    (error : Matrix output input ℝ)
    (hgrowth :
      0 < hiddenNormSqVelocity hiddenWeight feedback error) :
    frozenHiddenOverlapVelocity hiddenWeight feedback error < 0 := by
  rw [hiddenNormSqVelocity_eq_neg_two_overlapVelocity] at hgrowth
  linarith

/-! ## Isotropic specialization -/

/-- Under an isotropic Gram matrix, Gram weighting reduces to a scalar
multiple of the unweighted transport trace. -/
theorem trace_gram_mul_of_isotropic
    [DecidableEq input]
    (gram transport : Matrix input input ℝ) (scale : ℝ)
    (hisotropic : gram = scale • (1 : Matrix input input ℝ)) :
    Matrix.trace (gram * transport) =
      scale * Matrix.trace transport := by
  rw [hisotropic]
  simp [Matrix.trace_smul]

/-- The source's intermediate conclusion `tr(F E) < 0` is valid when the
hidden Gram matrix is a positive scalar multiple of the identity. -/
theorem trace_feedbackErrorTransport_neg_of_isotropic_growth
    [DecidableEq input]
    (hiddenWeight : Matrix hidden input ℝ)
    (feedback : Matrix input output ℝ)
    (error : Matrix output input ℝ)
    (scale : ℝ) (hscale : 0 < scale)
    (hisotropic :
      inputGram hiddenWeight = scale • (1 : Matrix input input ℝ))
    (hgrowth :
      0 < hiddenNormSqVelocity hiddenWeight feedback error) :
    Matrix.trace (feedbackErrorTransport feedback error) < 0 := by
  rw [hiddenNormSqVelocity,
    trace_gram_mul_of_isotropic
      (inputGram hiddenWeight)
      (feedbackErrorTransport feedback error) scale hisotropic] at hgrowth
  nlinarith

/-! ## An anisotropic Gram boundary -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- A hidden map whose Gram matrix is `diag(4, 1)`. -/
def anisotropicHidden : Mat2 :=
  !![2, 0; 0, 1]

/-- A transport with positive ordinary trace but negative trace after
weighting by the anisotropic hidden Gram matrix. -/
def positiveTraceTransport : Mat2 :=
  !![-1, 0; 0, 2]

/-- The hidden map really induces the claimed non-isotropic Gram matrix. -/
theorem anisotropicHidden_gram :
    inputGram anisotropicHidden = !![(4 : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inputGram, anisotropicHidden, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The unweighted transport trace is positive. -/
theorem positiveTraceTransport_trace :
    Matrix.trace positiveTraceTransport = 1 := by
  norm_num [positiveTraceTransport, Matrix.trace, Fin.sum_univ_two]

/-- Gram weighting reverses the sign of the trace. -/
theorem anisotropic_weighted_trace :
    Matrix.trace (inputGram anisotropicHidden * positiveTraceTransport) =
      -2 := by
  norm_num [inputGram, anisotropicHidden, positiveTraceTransport,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Hidden norm can grow while the unweighted transport trace is positive.
Thus the source's displayed inference to `tr(F E) < 0` is invalid without an
isotropy premise, even though the corrected Gram-weighted antialignment
conclusion remains valid. -/
theorem anisotropic_growth_does_not_force_unweighted_trace_negative :
    0 < -2 *
        Matrix.trace
          (inputGram anisotropicHidden * positiveTraceTransport) ∧
      0 < Matrix.trace positiveTraceTransport ∧
      Matrix.trace
          (positiveTraceTransport * inputGram anisotropicHidden) < 0 := by
  constructor
  · rw [anisotropic_weighted_trace]
    norm_num
  constructor
  · rw [positiveTraceTransport_trace]
    norm_num
  · rw [Matrix.trace_mul_comm]
    rw [anisotropic_weighted_trace]
    norm_num

#print axioms scalar_feedback_mul_error_neg_of_hiddenNormSqVelocity_pos
#print axioms scalar_overlapVelocity_neg_of_hiddenNormSqVelocity_pos
#print axioms hiddenNormSqVelocity_eq_neg_two_overlapVelocity
#print axioms overlapVelocity_neg_of_hiddenNormSqVelocity_pos
#print axioms trace_feedbackErrorTransport_neg_of_isotropic_growth
#print axioms anisotropic_growth_does_not_force_unweighted_trace_negative

end PEPITAAntialignment

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
