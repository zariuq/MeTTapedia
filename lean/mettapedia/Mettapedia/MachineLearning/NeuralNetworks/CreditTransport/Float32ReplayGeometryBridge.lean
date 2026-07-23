import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointGeometry
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReplayCertificate
import Mathlib.Tactic

/-!
# Replay-to-geometry bridge

The binary32 replay checker and the regional Jacobian calculus originally
described the same affine maps through different interfaces.  This module
connects them once: a hidden replay's row-wise exact map is the decoded
checkpoint affine--SiLU transition plus its recorded, masked error packet.

Consequently every replayed hidden block receives a regional `R/J/H` budget
on any certified input ball.  The replay still supplies only pointwise
floating-point error; it does not promote that error to a uniform roundoff
model.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32ReplayGeometryBridge

open Float32CheckpointGeometry
open Float32HiddenStageReplayCertificate
open Float32ThreeHiddenStageReplayCertificate
open Float32AddMaskReplayCertificate
open Float32CheckpointMatrix
open SiLUTransitionBounds
open CompositionalJacobianBounds
open FinitePrecisionEvaluationError

noncomputable section

/-- Predicate form of the Boolean node mask embedded in one replay. -/
def replayActiveMask {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns)
    (row : Fin rows) : Prop :=
  (replay.addMask row).mask.active = true

instance replayActiveMaskDecidable {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns) :
    DecidablePred (replayActiveMask replay) :=
  fun row =>
    inferInstanceAs
      (Decidable ((replay.addMask row).mask.active = true))

/-- The recorded error packet after applying the replay's node mask. -/
noncomputable def replayMaskedError {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns) :
    EuclideanSpace ℝ (Fin rows) :=
  maskProjection (replayActiveMask replay) replay.decodedInput.2

/-- Exact geometry Jacobian associated with the replay's decoded checkpoint
weights, bias, and node mask. -/
noncomputable def replayIdealJacobian {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns) :
    EuclideanSpace ℝ (Fin columns) →
      (EuclideanSpace ℝ (Fin columns) →L[ℝ]
        EuclideanSpace ℝ (Fin rows)) :=
  rectangularMaskedAffineSiLUJacobian (replayActiveMask replay)
    (decodedLinear replay.affineSiLU.affine.weight)
    (decodedBias replay.affineSiLU.affine.bias)

/-- Forward-rate expression inherited by a replayed hidden block on a ball.
It is named separately so multi-stage certificates can reuse the exact rate
chosen by `idealBlockAtRecordedErrorBudget`. -/
noncomputable def replayRegionalRate {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns)
    (center : EuclideanSpace ℝ (Fin columns))
    (radius : ℝ) : ℝ :=
  (1 + (‖decodedLinear replay.affineSiLU.affine.weight‖ *
      (‖center‖ + radius) +
      ‖decodedBias replay.affineSiLU.affine.bias‖) / 4) *
    ‖decodedLinear replay.affineSiLU.affine.weight‖

theorem replayRegionalRate_nonneg {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns)
    (center : EuclideanSpace ℝ (Fin columns))
    (radius : ℝ) (hradius : 0 ≤ radius) :
    0 ≤ replayRegionalRate replay center radius := by
  simp only [replayRegionalRate]
  positivity

/-- The replay's exact-real block is precisely the decoded masked
affine--SiLU transition plus the recorded masked error packet. -/
theorem idealBlockAtRecordedError_eq_geometry
    {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns)
    (input : EuclideanSpace ℝ (Fin columns)) :
    replay.idealBlockAtRecordedError input =
      rectangularMaskedAffineSiLU (replayActiveMask replay)
          (decodedLinear replay.affineSiLU.affine.weight)
          (decodedBias replay.affineSiLU.affine.bias) input +
        replayMaskedError replay := by
  ext row
  by_cases h : replayActiveMask replay row
  · have hbool : (replay.addMask row).mask.active = true := h
    simp [Float32HiddenStageReplay.idealBlockAtRecordedError,
      Float32HiddenStageReplay.idealBlock,
      Float32HiddenStageReplay.decodedInput,
      rectangularMaskedAffineSiLU, composeMap, vectorSiLU,
      rectangularVectorAffine, affineMap, replayActiveMask,
      replayMaskedError, hbool, boolRat,
      replayIdealAffine_eq_decodedAffine]
  · have hbool : (replay.addMask row).mask.active = false := by
      cases hx : (replay.addMask row).mask.active
      · rfl
      · exact False.elim (h hx)
    simp [Float32HiddenStageReplay.idealBlockAtRecordedError,
      Float32HiddenStageReplay.idealBlock,
      Float32HiddenStageReplay.decodedInput,
      rectangularMaskedAffineSiLU, composeMap, vectorSiLU,
      rectangularVectorAffine, affineMap, replayActiveMask,
      replayMaskedError, hbool, boolRat,
      replayIdealAffine_eq_decodedAffine]

/-- A replayed hidden block inherits a regional checkpoint geometry budget.
The fixed recorded error changes the map's value but not its derivative,
pairwise rate, or Jacobian variation. -/
noncomputable def idealBlockAtRecordedErrorBudget
    {rows columns : ℕ}
    (replay : Float32HiddenStageReplay rows columns)
    (center : EuclideanSpace ℝ (Fin columns))
    (radius : ℝ) (hradius : 0 ≤ radius) :
    RegionalJacobianBudget replay.idealBlockAtRecordedError
      (replayIdealJacobian replay)
      (fun input => ‖input - center‖ ≤ radius)
      (replayRegionalRate replay center radius)
      (replayRegionalRate replay center radius)
      ((1 / 2 + (‖decodedLinear replay.affineSiLU.affine.weight‖ *
          (‖center‖ + radius) +
          ‖decodedBias replay.affineSiLU.affine.bias‖) / 4) *
        ‖decodedLinear replay.affineSiLU.affine.weight‖ *
        ‖decodedLinear replay.affineSiLU.affine.weight‖) := by
  let transitionBudget :=
    rectangularMaskedAffineSiLUBudget (replayActiveMask replay)
      (decodedLinear replay.affineSiLU.affine.weight)
      (decodedBias replay.affineSiLU.affine.bias)
      center radius hradius
  let errorBudget :=
    constantBudget (replayMaskedError replay)
      (fun input => ‖input - center‖ ≤ radius)
  have combined := transitionBudget.add errorBudget
  have hmap :
      replay.idealBlockAtRecordedError =
        addMap
          (rectangularMaskedAffineSiLU (replayActiveMask replay)
            (decodedLinear replay.affineSiLU.affine.weight)
            (decodedBias replay.affineSiLU.affine.bias))
          (fun _ => replayMaskedError replay) := by
    funext input
    exact idealBlockAtRecordedError_eq_geometry replay input
  rw [hmap]
  convert combined using 1
  · ext state direction
    simp [replayIdealJacobian, addJacobian]
  · simp [replayRegionalRate]
  · simp [replayRegionalRate]
  · ring

/-! ## Automatic three-stage regional transport -/

/-- Regional rate used by the first hidden stage around its recorded input. -/
noncomputable def threeStageFirstRate {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (inputError : ℝ) : ℝ :=
  replayRegionalRate replay.first replay.first.runtimePreviousCenter inputError

/-- Certified mismatch radius after the first hidden stage. -/
noncomputable def threeStageFirstMismatchRadius
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (inputError : ℝ) : ℝ :=
  propagatedEvaluationError (threeStageFirstRate replay inputError)
    (replay.first.totalCertifiedErrorRat : ℝ) inputError

/-- Regional rate used by the second hidden stage around the first recorded
output, with the preceding mismatch as its radius. -/
noncomputable def threeStageSecondRate {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (inputError : ℝ) : ℝ :=
  replayRegionalRate replay.second replay.first.decodedOutput
    (threeStageFirstMismatchRadius replay inputError)

/-- Certified mismatch radius after the second hidden stage. -/
noncomputable def threeStageSecondMismatchRadius
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (inputError : ℝ) : ℝ :=
  propagatedEvaluationError (threeStageSecondRate replay inputError)
    (replay.second.totalCertifiedErrorRat : ℝ)
    (threeStageFirstMismatchRadius replay inputError)

/-- Regional rate used by the third hidden stage around the second recorded
output, with the transported two-stage mismatch as its radius. -/
noncomputable def threeStageThirdRate {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (inputError : ℝ) : ℝ :=
  replayRegionalRate replay.third replay.second.decodedOutput
    (threeStageSecondMismatchRadius replay inputError)

/-- Exact binary32 local errors and checkpoint-derived regional rates compose
into a complete three-hidden-stage mismatch certificate.  Callers provide
only the initial exact/runtime input mismatch; every intermediate pair bound
is discharged by the replay-to-geometry bridge. -/
theorem threeStageOutputMismatch_le_from_geometry
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (hcheck : replay.check = true)
    (exactInput : EuclideanSpace ℝ (Fin inputDim))
    (inputError : ℝ) (hinputError : 0 ≤ inputError)
    (hinput :
      ‖replay.first.runtimePreviousCenter - exactInput‖ ≤ inputError) :
    ‖replay.third.decodedOutput -
      replay.third.idealBlockAtRecordedError
        (replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput))‖ ≤
      replay.totalCertifiedError
        (threeStageFirstRate replay inputError)
        (threeStageSecondRate replay inputError)
        (threeStageThirdRate replay inputError)
        inputError := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hfirstCheck : replay.first.check = true :=
    replay.first.check_eq_true_iff.mpr hvalid.1
  have hsecondCheck : replay.second.check = true :=
    replay.second.check_eq_true_iff.mpr hvalid.2.1
  have hthirdCheck : replay.third.check = true :=
    replay.third.check_eq_true_iff.mpr hvalid.2.2.1
  have hlocalFirst :=
    replay.first.toPreviousCenterLocalCertificate hfirstCheck
  have hlocalSecond :=
    replay.second.toPreviousCenterLocalCertificate hsecondCheck
  have hlocalThird :=
    replay.third.toPreviousCenterLocalCertificate hthirdCheck
  rw [replay.second_runtimeInput_eq_first_output hcheck] at hlocalSecond
  rw [replay.third_runtimeInput_eq_second_output hcheck] at hlocalThird
  let budgetFirst :=
    idealBlockAtRecordedErrorBudget replay.first
      replay.first.runtimePreviousCenter inputError hinputError
  have hfirstRate :
      0 ≤ threeStageFirstRate replay inputError := by
    simpa [threeStageFirstRate, replayRegionalRate] using budgetFirst.rate_nonneg
  have hfirstCenter :
      ‖replay.first.runtimePreviousCenter -
        replay.first.runtimePreviousCenter‖ ≤ inputError := by
    simpa using hinputError
  have hexactInput :
      ‖exactInput - replay.first.runtimePreviousCenter‖ ≤ inputError := by
    simpa [norm_sub_rev] using hinput
  have hpairFirst :
      ‖replay.first.idealBlockAtRecordedError
          replay.first.runtimePreviousCenter -
        replay.first.idealBlockAtRecordedError exactInput‖ ≤
        threeStageFirstRate replay inputError *
          ‖replay.first.runtimePreviousCenter - exactInput‖ := by
    simpa [threeStageFirstRate, replayRegionalRate] using
      budgetFirst.map_pair_bound
        replay.first.runtimePreviousCenter exactInput
        hfirstCenter hexactInput
  have hmismatchFirst :
      ‖replay.first.decodedOutput -
        replay.first.idealBlockAtRecordedError exactInput‖ ≤
        threeStageFirstMismatchRadius replay inputError := by
    exact outputMismatch_le_propagatedEvaluationError
      replay.first.idealBlockAtRecordedError exactInput
      replay.first.runtimePreviousCenter replay.first.decodedOutput
      (threeStageFirstRate replay inputError)
      (replay.first.totalCertifiedErrorRat : ℝ) inputError
      hfirstRate hlocalFirst hpairFirst hinput
  have hfirstMismatchNonneg :
      0 ≤ threeStageFirstMismatchRadius replay inputError := by
    exact propagatedEvaluationError_nonneg hfirstRate
      hlocalFirst.localError_nonneg hinputError
  let budgetSecond :=
    idealBlockAtRecordedErrorBudget replay.second
      replay.first.decodedOutput
      (threeStageFirstMismatchRadius replay inputError)
      hfirstMismatchNonneg
  have hsecondRate :
      0 ≤ threeStageSecondRate replay inputError := by
    simpa [threeStageSecondRate, replayRegionalRate] using
      budgetSecond.rate_nonneg
  have hsecondCenter :
      ‖replay.first.decodedOutput - replay.first.decodedOutput‖ ≤
        threeStageFirstMismatchRadius replay inputError := by
    simpa using hfirstMismatchNonneg
  have hfirstExactInSecond :
      ‖replay.first.idealBlockAtRecordedError exactInput -
        replay.first.decodedOutput‖ ≤
        threeStageFirstMismatchRadius replay inputError := by
    simpa [norm_sub_rev] using hmismatchFirst
  have hpairSecond :
      ‖replay.second.idealBlockAtRecordedError replay.first.decodedOutput -
        replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput)‖ ≤
        threeStageSecondRate replay inputError *
          ‖replay.first.decodedOutput -
            replay.first.idealBlockAtRecordedError exactInput‖ := by
    simpa [threeStageSecondRate, replayRegionalRate] using
      budgetSecond.map_pair_bound replay.first.decodedOutput
        (replay.first.idealBlockAtRecordedError exactInput)
        hsecondCenter hfirstExactInSecond
  have hmismatchSecond :
      ‖replay.second.decodedOutput -
        replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput)‖ ≤
        threeStageSecondMismatchRadius replay inputError := by
    exact outputMismatch_le_propagatedEvaluationError
      replay.second.idealBlockAtRecordedError
      (replay.first.idealBlockAtRecordedError exactInput)
      replay.first.decodedOutput replay.second.decodedOutput
      (threeStageSecondRate replay inputError)
      (replay.second.totalCertifiedErrorRat : ℝ)
      (threeStageFirstMismatchRadius replay inputError)
      hsecondRate hlocalSecond hpairSecond hmismatchFirst
  have hsecondMismatchNonneg :
      0 ≤ threeStageSecondMismatchRadius replay inputError := by
    exact propagatedEvaluationError_nonneg hsecondRate
      hlocalSecond.localError_nonneg hfirstMismatchNonneg
  let budgetThird :=
    idealBlockAtRecordedErrorBudget replay.third
      replay.second.decodedOutput
      (threeStageSecondMismatchRadius replay inputError)
      hsecondMismatchNonneg
  have hthirdRate :
      0 ≤ threeStageThirdRate replay inputError := by
    simpa [threeStageThirdRate, replayRegionalRate] using
      budgetThird.rate_nonneg
  have hthirdCenter :
      ‖replay.second.decodedOutput - replay.second.decodedOutput‖ ≤
        threeStageSecondMismatchRadius replay inputError := by
    simpa using hsecondMismatchNonneg
  have hsecondExactInThird :
      ‖replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput) -
        replay.second.decodedOutput‖ ≤
        threeStageSecondMismatchRadius replay inputError := by
    simpa [norm_sub_rev] using hmismatchSecond
  have hpairThird :
      ‖replay.third.idealBlockAtRecordedError replay.second.decodedOutput -
        replay.third.idealBlockAtRecordedError
          (replay.second.idealBlockAtRecordedError
            (replay.first.idealBlockAtRecordedError exactInput))‖ ≤
        threeStageThirdRate replay inputError *
          ‖replay.second.decodedOutput -
            replay.second.idealBlockAtRecordedError
              (replay.first.idealBlockAtRecordedError exactInput)‖ := by
    simpa [threeStageThirdRate, replayRegionalRate] using
      budgetThird.map_pair_bound replay.second.decodedOutput
        (replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput))
        hthirdCenter hsecondExactInThird
  exact replay.sound hcheck exactInput
    (threeStageFirstRate replay inputError)
    (threeStageSecondRate replay inputError)
    (threeStageThirdRate replay inputError)
    inputError hfirstRate hsecondRate hthirdRate
    hpairFirst hpairSecond hpairThird hinput

/-- The complete exact hidden center is bounded by the observed binary32
center plus the automatically transported checkpoint-geometry mismatch. -/
theorem threeStageExactCenter_norm_le_from_geometry
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (hcheck : replay.check = true)
    (exactInput : EuclideanSpace ℝ (Fin inputDim))
    (inputError : ℝ) (hinputError : 0 ≤ inputError)
    (hinput :
      ‖replay.first.runtimePreviousCenter - exactInput‖ ≤ inputError) :
    ‖replay.third.idealBlockAtRecordedError
        (replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput))‖ ≤
      replay.third.decodedOutputL1 +
        replay.totalCertifiedError
          (threeStageFirstRate replay inputError)
          (threeStageSecondRate replay inputError)
          (threeStageThirdRate replay inputError)
          inputError := by
  exact replay.third.exactCenter_norm_le_observedL1_add_error
    (replay.third.idealBlockAtRecordedError
      (replay.second.idealBlockAtRecordedError
        (replay.first.idealBlockAtRecordedError exactInput)))
    (replay.totalCertifiedError
      (threeStageFirstRate replay inputError)
      (threeStageSecondRate replay inputError)
      (threeStageThirdRate replay inputError)
      inputError)
    (threeStageOutputMismatch_le_from_geometry replay hcheck exactInput
      inputError hinputError hinput)

/-! ## Positive and negative fixtures -/

theorem hiddenStage_replay_geometry_agrees :
    hiddenStage.idealBlockAtRecordedError hiddenStage.runtimePreviousCenter =
      rectangularMaskedAffineSiLU (replayActiveMask hiddenStage)
          (decodedLinear hiddenStage.affineSiLU.affine.weight)
          (decodedBias hiddenStage.affineSiLU.affine.bias)
          hiddenStage.runtimePreviousCenter +
        replayMaskedError hiddenStage :=
  idealBlockAtRecordedError_eq_geometry _ _

/-- A nonzero recorded error cannot be silently dropped from the exact replay
map, even though it does not change the Jacobian. -/
def nonzeroErrorReplay : Float32HiddenStageReplay 1 1 :=
  { hiddenStage with
    errorSite :=
      fun _ => Float32AddMaskReplayCertificate.positiveQuarter }

theorem nonzero_recorded_error_cannot_be_dropped :
    nonzeroErrorReplay.idealBlockAtRecordedError
        nonzeroErrorReplay.runtimePreviousCenter ≠
      rectangularMaskedAffineSiLU (replayActiveMask nonzeroErrorReplay)
        (decodedLinear nonzeroErrorReplay.affineSiLU.affine.weight)
        (decodedBias nonzeroErrorReplay.affineSiLU.affine.bias)
        nonzeroErrorReplay.runtimePreviousCenter := by
  intro heq
  let transition :=
    rectangularMaskedAffineSiLU (replayActiveMask nonzeroErrorReplay)
      (decodedLinear nonzeroErrorReplay.affineSiLU.affine.weight)
      (decodedBias nonzeroErrorReplay.affineSiLU.affine.bias)
      nonzeroErrorReplay.runtimePreviousCenter
  have hgeometry :=
    idealBlockAtRecordedError_eq_geometry nonzeroErrorReplay
      nonzeroErrorReplay.runtimePreviousCenter
  have hadd :
      transition + replayMaskedError nonzeroErrorReplay = transition := by
    exact hgeometry.symm.trans heq
  have herror : replayMaskedError nonzeroErrorReplay = 0 := by
    have hsub := congrArg (fun value => value - transition) hadd
    simpa [add_comm] using hsub
  have hcoordinate :=
    congrArg (fun output => output (0 : Fin 1)) herror
  norm_num [replayMaskedError, replayActiveMask, nonzeroErrorReplay,
    hiddenStage, hiddenAddMask, hiddenMask,
    Float32HiddenStageReplay.decodedInput,
    Float32AddMaskReplayCertificate.positiveQuarter,
    Float32CheckpointMatrix.FiniteFloat32Word.toReal,
    Float32CheckpointMatrix.FiniteFloat32Word.toRat,
    Float32CheckpointMatrix.float32Exponent,
    Float32CheckpointMatrix.float32Mantissa] at hcoordinate

#print axioms idealBlockAtRecordedError_eq_geometry
#print axioms idealBlockAtRecordedErrorBudget
#print axioms threeStageOutputMismatch_le_from_geometry
#print axioms threeStageExactCenter_norm_le_from_geometry
#print axioms hiddenStage_replay_geometry_agrees
#print axioms nonzero_recorded_error_cannot_be_dropped

end

end Float32ReplayGeometryBridge

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
