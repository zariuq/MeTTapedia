import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CompositionalJacobianBounds

/-!
# Compositional evaluation-error transport

A value produced by a finite-precision runtime differs from the declared real
map for two independent reasons:

* the runtime input may already differ from the ideal input; and
* evaluating the current stage may introduce a new local error.

If the ideal stage has regional rate `R`, an incoming mismatch `δ`, and local
evaluation error `ℓ`, the outgoing mismatch is bounded by

`ℓ + R * δ`.

This file proves that recurrence for one, two, and three stages and connects it
to `RegionalJacobianBudget`.  It deliberately does not assign a value to `ℓ`:
an IEEE-754 analysis, interval checker, or another independently audited
numerical model must supply each local certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FinitePrecisionEvaluationError

noncomputable section

open CompositionalJacobianBounds

variable {X Y Z W : Type*}
  [NormedAddCommGroup X]
  [NormedAddCommGroup Y]
  [NormedAddCommGroup Z]
  [NormedAddCommGroup W]

/-- A local certificate compares a runtime stage output with exact evaluation
of the declared real map at the same runtime input.  It does not include error
already present in that input. -/
structure LocalEvaluationErrorCertificate
    (ideal : X → Y) (runtimeInput : X) (runtimeOutput : Y)
    (localError : ℝ) : Prop where
  localError_nonneg : 0 ≤ localError
  output_error_le : ‖runtimeOutput - ideal runtimeInput‖ ≤ localError

/-- One step of the evaluation-error recurrence. -/
def propagatedEvaluationError
    (rate localError inputError : ℝ) : ℝ :=
  localError + rate * inputError

@[simp] theorem propagatedEvaluationError_zero_local
    (rate inputError : ℝ) :
    propagatedEvaluationError rate 0 inputError = rate * inputError := by
  simp [propagatedEvaluationError]

@[simp] theorem propagatedEvaluationError_zero_rate
    (localError inputError : ℝ) :
    propagatedEvaluationError 0 localError inputError = localError := by
  simp [propagatedEvaluationError]

theorem propagatedEvaluationError_nonneg
    {rate localError inputError : ℝ}
    (hrate : 0 ≤ rate) (hlocal : 0 ≤ localError)
    (hinput : 0 ≤ inputError) :
    0 ≤ propagatedEvaluationError rate localError inputError := by
  exact add_nonneg hlocal (mul_nonneg hrate hinput)

/-- Local evaluation error and transported input mismatch add.  The ideal map
pair bound is pointwise so that this theorem can be used with global,
regional, or independently checked Lipschitz certificates. -/
theorem outputMismatch_le_propagatedEvaluationError
    (ideal : X → Y) (exactInput runtimeInput : X) (runtimeOutput : Y)
    (rate localError inputError : ℝ)
    (hrate : 0 ≤ rate)
    (hlocal : LocalEvaluationErrorCertificate
      ideal runtimeInput runtimeOutput localError)
    (hpair : ‖ideal runtimeInput - ideal exactInput‖ ≤
      rate * ‖runtimeInput - exactInput‖)
    (hinput : ‖runtimeInput - exactInput‖ ≤ inputError) :
    ‖runtimeOutput - ideal exactInput‖ ≤
      propagatedEvaluationError rate localError inputError := by
  rw [show runtimeOutput - ideal exactInput =
    (runtimeOutput - ideal runtimeInput) +
      (ideal runtimeInput - ideal exactInput) by abel]
  calc
    ‖(runtimeOutput - ideal runtimeInput) +
        (ideal runtimeInput - ideal exactInput)‖ ≤
      ‖runtimeOutput - ideal runtimeInput‖ +
        ‖ideal runtimeInput - ideal exactInput‖ := norm_add_le _ _
    _ ≤ localError + rate * ‖runtimeInput - exactInput‖ :=
      add_le_add hlocal.output_error_le hpair
    _ ≤ localError + rate * inputError :=
      add_le_add (le_refl localError)
        (mul_le_mul_of_nonneg_left hinput hrate)
    _ = propagatedEvaluationError rate localError inputError := rfl

/-- Specialization using the forward-rate field of a regional Jacobian
budget.  Both the runtime and ideal inputs must lie in the certified domain. -/
theorem outputMismatch_le_of_regionalJacobianBudget
    [NormedSpace ℝ X] [NormedSpace ℝ Y]
    (ideal : X → Y) (jacobian : X → X →L[ℝ] Y)
    (domain : X → Prop) (rate operatorBound variation : ℝ)
    (budget : RegionalJacobianBudget ideal jacobian domain
      rate operatorBound variation)
    (exactInput runtimeInput : X) (runtimeOutput : Y)
    (localError inputError : ℝ)
    (hexact : domain exactInput) (hruntime : domain runtimeInput)
    (hlocal : LocalEvaluationErrorCertificate
      ideal runtimeInput runtimeOutput localError)
    (hinput : ‖runtimeInput - exactInput‖ ≤ inputError) :
    ‖runtimeOutput - ideal exactInput‖ ≤
      propagatedEvaluationError rate localError inputError := by
  exact outputMismatch_le_propagatedEvaluationError
    ideal exactInput runtimeInput runtimeOutput rate localError inputError
    budget.rate_nonneg hlocal
    (budget.map_pair_bound runtimeInput exactInput hruntime hexact) hinput

/-- Two consecutive runtime stages obey the nested recurrence
`ℓ₂ + R₂ * (ℓ₁ + R₁ * δ₀)`. -/
theorem twoStageOutputMismatch_le
    (first : X → Y) (second : Y → Z)
    (exactInput runtimeInput : X)
    (runtimeFirst : Y) (runtimeSecond : Z)
    (rateFirst rateSecond localFirst localSecond inputError : ℝ)
    (hrateFirst : 0 ≤ rateFirst) (hrateSecond : 0 ≤ rateSecond)
    (hlocalFirst : LocalEvaluationErrorCertificate
      first runtimeInput runtimeFirst localFirst)
    (hlocalSecond : LocalEvaluationErrorCertificate
      second runtimeFirst runtimeSecond localSecond)
    (hpairFirst : ‖first runtimeInput - first exactInput‖ ≤
      rateFirst * ‖runtimeInput - exactInput‖)
    (hpairSecond : ‖second runtimeFirst - second (first exactInput)‖ ≤
      rateSecond * ‖runtimeFirst - first exactInput‖)
    (hinput : ‖runtimeInput - exactInput‖ ≤ inputError) :
    ‖runtimeSecond - second (first exactInput)‖ ≤
      propagatedEvaluationError rateSecond localSecond
        (propagatedEvaluationError rateFirst localFirst inputError) := by
  apply outputMismatch_le_propagatedEvaluationError
    second (first exactInput) runtimeFirst runtimeSecond
      rateSecond localSecond
      (propagatedEvaluationError rateFirst localFirst inputError)
      hrateSecond hlocalSecond hpairSecond
  exact outputMismatch_le_propagatedEvaluationError
    first exactInput runtimeInput runtimeFirst rateFirst localFirst inputError
    hrateFirst hlocalFirst hpairFirst hinput

/-- Three consecutive runtime stages obey the exact conservative recurrence
used by the three hidden blocks of the audited error-coordinate adapter. -/
theorem threeStageOutputMismatch_le
    (first : X → Y) (second : Y → Z) (third : Z → W)
    (exactInput runtimeInput : X)
    (runtimeFirst : Y) (runtimeSecond : Z) (runtimeThird : W)
    (rateFirst rateSecond rateThird
      localFirst localSecond localThird inputError : ℝ)
    (hrateFirst : 0 ≤ rateFirst) (hrateSecond : 0 ≤ rateSecond)
    (hrateThird : 0 ≤ rateThird)
    (hlocalFirst : LocalEvaluationErrorCertificate
      first runtimeInput runtimeFirst localFirst)
    (hlocalSecond : LocalEvaluationErrorCertificate
      second runtimeFirst runtimeSecond localSecond)
    (hlocalThird : LocalEvaluationErrorCertificate
      third runtimeSecond runtimeThird localThird)
    (hpairFirst : ‖first runtimeInput - first exactInput‖ ≤
      rateFirst * ‖runtimeInput - exactInput‖)
    (hpairSecond : ‖second runtimeFirst - second (first exactInput)‖ ≤
      rateSecond * ‖runtimeFirst - first exactInput‖)
    (hpairThird :
      ‖third runtimeSecond - third (second (first exactInput))‖ ≤
        rateThird * ‖runtimeSecond - second (first exactInput)‖)
    (hinput : ‖runtimeInput - exactInput‖ ≤ inputError) :
    ‖runtimeThird - third (second (first exactInput))‖ ≤
      propagatedEvaluationError rateThird localThird
        (propagatedEvaluationError rateSecond localSecond
          (propagatedEvaluationError rateFirst localFirst inputError)) := by
  apply outputMismatch_le_propagatedEvaluationError
    third (second (first exactInput)) runtimeSecond runtimeThird
      rateThird localThird
      (propagatedEvaluationError rateSecond localSecond
        (propagatedEvaluationError rateFirst localFirst inputError))
      hrateThird hlocalThird hpairThird
  exact twoStageOutputMismatch_le
    first second exactInput runtimeInput runtimeFirst runtimeSecond
    rateFirst rateSecond localFirst localSecond inputError
    hrateFirst hrateSecond hlocalFirst hlocalSecond
    hpairFirst hpairSecond hinput

/-! ## Positive and negative fixtures -/

private def doubleMap (value : ℝ) : ℝ := 2 * value

/-- With zero local error, a unit input mismatch through `x ↦ 2x` contributes
exactly two units to the output mismatch budget. -/
theorem unit_input_mismatch_is_transported :
    ‖(2 : ℝ) - doubleMap 0‖ ≤ propagatedEvaluationError 2 0 1 := by
  exact outputMismatch_le_propagatedEvaluationError
    doubleMap 0 1 2 2 0 1 (by norm_num)
    { localError_nonneg := by norm_num
      output_error_le := by norm_num [doubleMap] }
    (by norm_num [doubleMap]) (by norm_num)

/-- Input mismatch cannot be omitted even when runtime evaluation at its own
input is exact. -/
theorem input_mismatch_cannot_be_dropped :
    ¬ ‖(2 : ℝ) - doubleMap 0‖ ≤ 0 := by
  norm_num [doubleMap]

/-- Local evaluation error cannot be omitted merely because the runtime and
ideal inputs agree. -/
theorem local_evaluation_error_cannot_be_dropped :
    ¬ ‖(1 : ℝ) - doubleMap 0‖ ≤ 2 * ‖(0 : ℝ) - 0‖ := by
  norm_num [doubleMap]

#print axioms threeStageOutputMismatch_le
#print axioms input_mismatch_cannot_be_dropped
#print axioms local_evaluation_error_cannot_be_dropped

end

end FinitePrecisionEvaluationError

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
