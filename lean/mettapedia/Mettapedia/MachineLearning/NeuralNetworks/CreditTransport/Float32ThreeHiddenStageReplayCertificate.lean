import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32HiddenStageReplayCertificate
import Mathlib.Tactic

/-!
# Exact binary32 replay across three hidden stages

The audited error-coordinate adapter contains three consecutive hidden stages.
This module connects their observed center words exactly and then instantiates
the heterogeneous three-stage evaluation-error recurrence already proved in
`FinitePrecisionEvaluationError`.

Each stage retains its own exact-real map, local replay budget, and declared
point-pair transport rate.  No global Lipschitz property is inferred from the
trace.  The kernel checks the arithmetic and the two interior word-level
connections.  Source provenance and endpoint identity remain external hash-
and-verifier obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32ThreeHiddenStageReplayCertificate

open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32ActivationReplayCertificate
open Float32AffineSiLUReplayCertificate
open Float32AddMaskReplayCertificate
open Float32HiddenStageReplayCertificate
open FinitePrecisionEvaluationError
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate
open RegisteredUnaryExpressionCertificate

noncomputable section

/-- Three consecutive observed hidden stages.  The first may change width;
the second and third operate at the common hidden width. -/
structure Float32ThreeHiddenStageReplay (hiddenDim inputDim : ℕ) where
  first : Float32HiddenStageReplay hiddenDim inputDim
  second : Float32HiddenStageReplay hiddenDim hiddenDim
  third : Float32HiddenStageReplay hiddenDim hiddenDim

/-- Besides local validity, every interior center is connected by exact
binary32 word equality to the next affine input. -/
def Float32ThreeHiddenStageReplay.Valid
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim) : Prop :=
  replay.first.Valid ∧ replay.second.Valid ∧ replay.third.Valid ∧
    (∀ row,
      (replay.second.affineSiLU.affine.input row).word =
        (replay.first.addMask row).mask.output.word) ∧
    ∀ row,
      (replay.third.affineSiLU.affine.input row).word =
        (replay.second.addMask row).mask.output.word

def Float32ThreeHiddenStageReplay.check
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim) : Bool :=
  replay.first.check && replay.second.check && replay.third.check &&
    decide ((∀ row,
      (replay.second.affineSiLU.affine.input row).word =
        (replay.first.addMask row).mask.output.word) ∧
      ∀ row,
        (replay.third.affineSiLU.affine.input row).word =
          (replay.second.addMask row).mask.output.word)

theorem Float32ThreeHiddenStageReplay.check_eq_true_iff
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32ThreeHiddenStageReplay.check,
    Float32ThreeHiddenStageReplay.Valid,
    Float32HiddenStageReplay.check_eq_true_iff, and_assoc]

private theorem finiteWord_toReal_eq_of_word_eq
    {left right : FiniteFloat32Word} (hword : left.word = right.word) :
    left.toReal = right.toReal := by
  simp [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, hword]

/-- The first observed masked center is exactly the runtime input decoded by
the second stage. -/
theorem Float32ThreeHiddenStageReplay.second_runtimeInput_eq_first_output
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (hcheck : replay.check = true) :
    replay.second.runtimePreviousCenter = replay.first.decodedOutput := by
  have hwire := (replay.check_eq_true_iff.mp hcheck).2.2.2.1
  ext row
  simpa [Float32HiddenStageReplay.runtimePreviousCenter,
    Float32AffineReplay.decodedInput,
    Float32HiddenStageReplay.decodedOutput,
    Float32AddMaskReplay.decodedOutput] using
    finiteWord_toReal_eq_of_word_eq (hwire row)

/-- The second observed masked center is exactly the runtime input decoded by
the third stage. -/
theorem Float32ThreeHiddenStageReplay.third_runtimeInput_eq_second_output
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (hcheck : replay.check = true) :
    replay.third.runtimePreviousCenter = replay.second.decodedOutput := by
  have hwire := (replay.check_eq_true_iff.mp hcheck).2.2.2.2
  ext row
  simpa [Float32HiddenStageReplay.runtimePreviousCenter,
    Float32AffineReplay.decodedInput,
    Float32HiddenStageReplay.decodedOutput,
    Float32AddMaskReplay.decodedOutput] using
    finiteWord_toReal_eq_of_word_eq (hwire row)

/-- Nested conservative mismatch budget for the three observed stages. -/
def Float32ThreeHiddenStageReplay.totalCertifiedError
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (rateFirst rateSecond rateThird inputError : ℝ) : ℝ :=
  propagatedEvaluationError rateThird
    (replay.third.totalCertifiedErrorRat : ℝ)
    (propagatedEvaluationError rateSecond
      (replay.second.totalCertifiedErrorRat : ℝ)
      (propagatedEvaluationError rateFirst
        (replay.first.totalCertifiedErrorRat : ℝ) inputError))

/-- A word-connected three-stage replay obeys the existing heterogeneous
evaluation-error recurrence.  The three map-pair bounds are explicit local
obligations: this theorem does not promote them to global regularity claims. -/
theorem Float32ThreeHiddenStageReplay.sound
    {hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReplay hiddenDim inputDim)
    (hcheck : replay.check = true)
    (exactInput : EuclideanSpace ℝ (Fin inputDim))
    (rateFirst rateSecond rateThird inputError : ℝ)
    (hrateFirst : 0 ≤ rateFirst) (hrateSecond : 0 ≤ rateSecond)
    (hrateThird : 0 ≤ rateThird)
    (hpairFirst :
      ‖replay.first.idealBlockAtRecordedError
          replay.first.runtimePreviousCenter -
        replay.first.idealBlockAtRecordedError exactInput‖ ≤
          rateFirst * ‖replay.first.runtimePreviousCenter - exactInput‖)
    (hpairSecond :
      ‖replay.second.idealBlockAtRecordedError replay.first.decodedOutput -
        replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput)‖ ≤
        rateSecond *
          ‖replay.first.decodedOutput -
            replay.first.idealBlockAtRecordedError exactInput‖)
    (hpairThird :
      ‖replay.third.idealBlockAtRecordedError replay.second.decodedOutput -
        replay.third.idealBlockAtRecordedError
          (replay.second.idealBlockAtRecordedError
            (replay.first.idealBlockAtRecordedError exactInput))‖ ≤
        rateThird *
          ‖replay.second.decodedOutput -
            replay.second.idealBlockAtRecordedError
              (replay.first.idealBlockAtRecordedError exactInput)‖)
    (hinput :
      ‖replay.first.runtimePreviousCenter - exactInput‖ ≤ inputError) :
    ‖replay.third.decodedOutput -
      replay.third.idealBlockAtRecordedError
        (replay.second.idealBlockAtRecordedError
          (replay.first.idealBlockAtRecordedError exactInput))‖ ≤
      replay.totalCertifiedError rateFirst rateSecond rateThird inputError := by
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
  exact threeStageOutputMismatch_le
    replay.first.idealBlockAtRecordedError
    replay.second.idealBlockAtRecordedError
    replay.third.idealBlockAtRecordedError
    exactInput replay.first.runtimePreviousCenter
    replay.first.decodedOutput replay.second.decodedOutput
    replay.third.decodedOutput
    rateFirst rateSecond rateThird
    (replay.first.totalCertifiedErrorRat : ℝ)
    (replay.second.totalCertifiedErrorRat : ℝ)
    (replay.third.totalCertifiedErrorRat : ℝ)
    inputError hrateFirst hrateSecond hrateThird
    hlocalFirst hlocalSecond hlocalThird
    hpairFirst hpairSecond hpairThird hinput

/-! ## Positive and negative executable fixtures -/

/-- Exact enclosure of `exp 0 = 1`, used only to construct an executable
zero-valued SiLU stage for the wiring fixtures. -/
def expZero : ExpEnclosure where
  argument := 0
  terms := 1
  lower := 1
  upper := 1

theorem expZero_is_accepted : expZero.check = true := by
  norm_num [expZero, ExpEnclosure.check, ExpEnclosure.Valid,
    expTaylorRat, expTaylorErrorRat, Finset.sum_range_succ, Nat.factorial]

def siluZero : ActivationEnclosure where
  operation := .silu
  argument := 0
  runtimeValue := 0
  localError := 0
  outputLower := 0
  outputUpper := 0
  expCertificate := expZero

theorem siluZero_is_accepted : siluZero.check = true := by
  norm_num [siluZero, ActivationEnclosure.check, expZero,
    ExpEnclosure.check, ExpEnclosure.Valid, expTaylorRat,
    expTaylorErrorRat, activationLowerRat, activationUpperRat,
    sigmoidLowerRat, sigmoidUpperRat, Finset.sum_range_succ, Nat.factorial]

def zeroActivationReplay : Float32ActivationReplay where
  input := Float32HiddenStageReplayCertificate.zeroWord
  output := Float32HiddenStageReplayCertificate.zeroWord
  enclosure := .direct siluZero

theorem zeroActivationReplay_is_accepted :
    zeroActivationReplay.check = true := by
  simp only [Float32ActivationReplay.check, zeroActivationReplay,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue]
  rw [siluZero_is_accepted]
  norm_num [siluZero, Float32HiddenStageReplayCertificate.zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

/-- A constant-zero affine stage that consumes the first fixture's observed
`5/16` center word. -/
def zeroAffineAfterFirst : Float32AffineReplay 1 1 where
  input := ![Float32ActivationReplayCertificate.positiveFiveSixteenths]
  weight := ![Float32HiddenStageReplayCertificate.zeroWord]
  bias := ![Float32HiddenStageReplayCertificate.zeroWord]
  output := ![Float32HiddenStageReplayCertificate.zeroWord]
  localError := 0

/-- The same constant-zero affine stage after the center has become zero. -/
def zeroAffineAfterZero : Float32AffineReplay 1 1 where
  input := ![Float32HiddenStageReplayCertificate.zeroWord]
  weight := ![Float32HiddenStageReplayCertificate.zeroWord]
  bias := ![Float32HiddenStageReplayCertificate.zeroWord]
  output := ![Float32HiddenStageReplayCertificate.zeroWord]
  localError := 0

theorem zeroAffineAfterFirst_is_accepted :
    zeroAffineAfterFirst.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, zeroAffineAfterFirst,
    Float32ActivationReplayCertificate.positiveFiveSixteenths,
    Float32HiddenStageReplayCertificate.zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa, rowMajorIndex]

theorem zeroAffineAfterZero_is_accepted :
    zeroAffineAfterZero.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, zeroAffineAfterZero,
    Float32HiddenStageReplayCertificate.zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa, rowMajorIndex]

def zeroAffineSiLUAfterFirst : Float32AffineSiLUReplay 1 1 where
  affine := zeroAffineAfterFirst
  activation := fun _ ↦ zeroActivationReplay
  radius := 1

def zeroAffineSiLUAfterZero : Float32AffineSiLUReplay 1 1 where
  affine := zeroAffineAfterZero
  activation := fun _ ↦ zeroActivationReplay
  radius := 1

theorem zeroAffineSiLUAfterFirst_is_accepted :
    zeroAffineSiLUAfterFirst.check = true := by
  apply (Float32AffineSiLUReplay.check_eq_true_iff
    zeroAffineSiLUAfterFirst).mpr
  refine ⟨(Float32AffineReplay.check_eq_true_iff zeroAffineAfterFirst).mp
      zeroAffineAfterFirst_is_accepted,
    by norm_num [zeroAffineSiLUAfterFirst], ?_⟩
  intro row
  fin_cases row
  exact ⟨(Float32ActivationReplay.check_eq_true_iff zeroActivationReplay).mp
      zeroActivationReplay_is_accepted, rfl, rfl,
    by norm_num [zeroAffineSiLUAfterFirst, zeroAffineAfterFirst,
      Float32HiddenStageReplayCertificate.zeroWord,
      FiniteFloat32Word.toRat, float32Exponent, float32Mantissa], by norm_num
        [zeroAffineSiLUAfterFirst, zeroAffineAfterFirst,
          Float32AffineReplay.idealOutputRat,
          Float32ActivationReplayCertificate.positiveFiveSixteenths,
          Float32HiddenStageReplayCertificate.zeroWord,
          FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
          rowMajorIndex]⟩

theorem zeroAffineSiLUAfterZero_is_accepted :
    zeroAffineSiLUAfterZero.check = true := by
  apply (Float32AffineSiLUReplay.check_eq_true_iff
    zeroAffineSiLUAfterZero).mpr
  refine ⟨(Float32AffineReplay.check_eq_true_iff zeroAffineAfterZero).mp
      zeroAffineAfterZero_is_accepted,
    by norm_num [zeroAffineSiLUAfterZero], ?_⟩
  intro row
  fin_cases row
  exact ⟨(Float32ActivationReplay.check_eq_true_iff zeroActivationReplay).mp
      zeroActivationReplay_is_accepted, rfl, rfl,
    by norm_num [zeroAffineSiLUAfterZero, zeroAffineAfterZero,
      Float32HiddenStageReplayCertificate.zeroWord,
      FiniteFloat32Word.toRat, float32Exponent, float32Mantissa], by norm_num
        [zeroAffineSiLUAfterZero, zeroAffineAfterZero,
          Float32AffineReplay.idealOutputRat,
          Float32HiddenStageReplayCertificate.zeroWord,
          FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
          rowMajorIndex]⟩

def zeroAddMask : Float32AddMaskReplay where
  add :=
    { left := Float32HiddenStageReplayCertificate.zeroWord
      right := Float32HiddenStageReplayCertificate.zeroWord
      output := Float32HiddenStageReplayCertificate.zeroWord
      localError := 0 }
  mask :=
    { active := true
      input := Float32HiddenStageReplayCertificate.zeroWord
      output := Float32HiddenStageReplayCertificate.zeroWord
      localError := 0 }

theorem zeroAddMask_is_accepted : zeroAddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, zeroAddMask, boolRat,
    Float32HiddenStageReplayCertificate.zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def zeroHiddenStageAfterFirst : Float32HiddenStageReplay 1 1 where
  affineSiLU := zeroAffineSiLUAfterFirst
  errorSite := fun _ ↦ Float32HiddenStageReplayCertificate.zeroWord
  addMask := fun _ ↦ zeroAddMask

def zeroHiddenStageAfterZero : Float32HiddenStageReplay 1 1 where
  affineSiLU := zeroAffineSiLUAfterZero
  errorSite := fun _ ↦ Float32HiddenStageReplayCertificate.zeroWord
  addMask := fun _ ↦ zeroAddMask

theorem zeroHiddenStageAfterFirst_is_accepted :
    zeroHiddenStageAfterFirst.check = true := by
  apply (Float32HiddenStageReplay.check_eq_true_iff
    zeroHiddenStageAfterFirst).mpr
  refine ⟨(Float32AffineSiLUReplay.check_eq_true_iff
      zeroAffineSiLUAfterFirst).mp zeroAffineSiLUAfterFirst_is_accepted, ?_⟩
  intro row
  fin_cases row
  exact ⟨(Float32AddMaskReplay.check_eq_true_iff zeroAddMask).mp
    zeroAddMask_is_accepted, rfl, rfl⟩

theorem zeroHiddenStageAfterZero_is_accepted :
    zeroHiddenStageAfterZero.check = true := by
  apply (Float32HiddenStageReplay.check_eq_true_iff
    zeroHiddenStageAfterZero).mpr
  refine ⟨(Float32AffineSiLUReplay.check_eq_true_iff
      zeroAffineSiLUAfterZero).mp zeroAffineSiLUAfterZero_is_accepted, ?_⟩
  intro row
  fin_cases row
  exact ⟨(Float32AddMaskReplay.check_eq_true_iff zeroAddMask).mp
    zeroAddMask_is_accepted, rfl, rfl⟩

def threeStageFixture : Float32ThreeHiddenStageReplay 1 1 where
  first := Float32HiddenStageReplayCertificate.hiddenStage
  second := zeroHiddenStageAfterFirst
  third := zeroHiddenStageAfterZero

theorem threeStageFixture_is_accepted : threeStageFixture.check = true := by
  apply (Float32ThreeHiddenStageReplay.check_eq_true_iff
    threeStageFixture).mpr
  exact ⟨(Float32HiddenStageReplay.check_eq_true_iff
      Float32HiddenStageReplayCertificate.hiddenStage).mp
        Float32HiddenStageReplayCertificate.hiddenStage_is_accepted,
    (Float32HiddenStageReplay.check_eq_true_iff
      zeroHiddenStageAfterFirst).mp zeroHiddenStageAfterFirst_is_accepted,
    (Float32HiddenStageReplay.check_eq_true_iff
      zeroHiddenStageAfterZero).mp zeroHiddenStageAfterZero_is_accepted,
    by intro row; fin_cases row; rfl,
    by intro row; fin_cases row; rfl⟩

/-- Each component is independently valid, but the second stage consumes zero
instead of the first stage's observed `5/16` center. -/
def miswiredThreeStageFixture : Float32ThreeHiddenStageReplay 1 1 :=
  { threeStageFixture with second := zeroHiddenStageAfterZero }

theorem miswiredThreeStageFixture_is_rejected :
    miswiredThreeStageFixture.check = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  have hwire :=
    (Float32ThreeHiddenStageReplay.check_eq_true_iff
      miswiredThreeStageFixture).mp hcheck
  have hrow := hwire.2.2.2.1 (0 : Fin 1)
  norm_num [miswiredThreeStageFixture, threeStageFixture,
    zeroHiddenStageAfterZero, zeroAffineSiLUAfterZero, zeroAffineAfterZero,
    Float32HiddenStageReplayCertificate.hiddenStage,
    Float32HiddenStageReplayCertificate.hiddenAddMask,
    Float32HiddenStageReplayCertificate.hiddenMask,
    Float32HiddenStageReplayCertificate.zeroWord,
    Float32ActivationReplayCertificate.positiveFiveSixteenths] at hrow

#print axioms Float32ThreeHiddenStageReplay.check_eq_true_iff
#print axioms Float32ThreeHiddenStageReplay.second_runtimeInput_eq_first_output
#print axioms Float32ThreeHiddenStageReplay.third_runtimeInput_eq_second_output
#print axioms Float32ThreeHiddenStageReplay.sound
#print axioms threeStageFixture_is_accepted
#print axioms miswiredThreeStageFixture_is_rejected

end

end Float32ThreeHiddenStageReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
