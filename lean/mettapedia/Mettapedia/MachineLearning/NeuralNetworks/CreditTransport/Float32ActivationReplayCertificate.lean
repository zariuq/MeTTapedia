import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalRangeReducedActivationEnclosureCertificate

/-!
# Binary32 activation replay certificates

A source trace can expose the exact binary32 words entering and leaving one
sigmoid or SiLU call.  This file checks those words against a rational
activation enclosure and exports a theorem about their exact decoded real
values.

The result certifies a concrete observed input/output pair.  It does not claim
that every invocation of a hardware or library kernel implements the exact
real activation, and it does not establish that an unbound pair of words came
from a particular execution.  Source provenance remains a separate gate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32ActivationReplayCertificate

open Float32CheckpointMatrix
open RationalActivationEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate
open RegisteredUnaryExpressionCertificate

noncomputable section

/-- A concrete binary32 input/output pair tied to a checked rational
activation enclosure. -/
structure Float32ActivationReplay where
  input : FiniteFloat32Word
  output : FiniteFloat32Word
  enclosure : ActivationCertificate
  deriving Repr

/-- Propositional meaning mirrored by `Float32ActivationReplay.check`. -/
def Float32ActivationReplay.Valid
    (certificate : Float32ActivationReplay) : Prop :=
  certificate.enclosure.Valid ∧
  certificate.enclosure.argument = certificate.input.toRat ∧
  certificate.enclosure.runtimeValue = certificate.output.toRat

/-- Executable replay checker for one finite binary32 activation pair. -/
def Float32ActivationReplay.check
    (certificate : Float32ActivationReplay) : Bool :=
  certificate.enclosure.check &&
    decide (certificate.enclosure.argument = certificate.input.toRat ∧
      certificate.enclosure.runtimeValue = certificate.output.toRat)

theorem Float32ActivationReplay.check_eq_true_iff
    (certificate : Float32ActivationReplay) :
    certificate.check = true ↔ certificate.Valid := by
  simp [Float32ActivationReplay.check, Float32ActivationReplay.Valid,
    ActivationCertificate.check_eq_true_iff]

/-- An accepted replay bounds the exact decoded binary32 output against the
registered exact-real activation at the exact decoded binary32 input. -/
theorem Float32ActivationReplay.sound
    (certificate : Float32ActivationReplay)
    (hcheck : certificate.check = true) :
    |certificate.output.toReal -
        certificate.enclosure.operation.realMap certificate.input.toReal| ≤
      (certificate.enclosure.localError : ℝ) := by
  rcases certificate.check_eq_true_iff.mp hcheck with
    ⟨henclosure, hinput, houtput⟩
  have henclosureCheck : certificate.enclosure.check = true :=
    certificate.enclosure.check_eq_true_iff.mpr henclosure
  have hsound := certificate.enclosure.sound henclosureCheck
  have hinputReal :
      (certificate.enclosure.argument : ℝ) = certificate.input.toReal := by
    rw [hinput, certificate.input.cast_toRat]
  have houtputReal :
      (certificate.enclosure.runtimeValue : ℝ) = certificate.output.toReal := by
    rw [houtput, certificate.output.cast_toRat]
  rwa [hinputReal, houtputReal] at hsound

/-! ## Accepted and corrupted finite-word fixtures -/

def positiveHalf : FiniteFloat32Word where
  word := 1056964608
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveFiveEighths : FiniteFloat32Word where
  word := 1059061760
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveFiveSixteenths : FiniteFloat32Word where
  word := 1050673152
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveTwo : FiniteFloat32Word where
  word := 1073741824
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveSevenEighths : FiniteFloat32Word where
  word := 1063256064
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

theorem positiveHalf_toRat : positiveHalf.toRat = 1 / 2 := by
  norm_num [positiveHalf, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa]

theorem positiveFiveEighths_toRat : positiveFiveEighths.toRat = 5 / 8 := by
  norm_num [positiveFiveEighths, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa]

theorem positiveFiveSixteenths_toRat :
    positiveFiveSixteenths.toRat = 5 / 16 := by
  norm_num [positiveFiveSixteenths, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa]

theorem positiveTwo_toRat : positiveTwo.toRat = 2 := by
  norm_num [positiveTwo, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa]

theorem positiveSevenEighths_toRat : positiveSevenEighths.toRat = 7 / 8 := by
  norm_num [positiveSevenEighths, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa]

def sigmoidHalfReplay : Float32ActivationReplay where
  input := positiveHalf
  output := positiveFiveEighths
  enclosure := .direct sigmoidHalf

theorem sigmoidHalfReplay_is_accepted : sigmoidHalfReplay.check = true := by
  simp only [Float32ActivationReplay.check, sigmoidHalfReplay,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue]
  rw [sigmoidHalf_is_accepted]
  norm_num [sigmoidHalf, positiveHalf_toRat, positiveFiveEighths_toRat]

theorem sigmoidHalfReplay_sound :
    |positiveFiveEighths.toReal - Real.sigmoid positiveHalf.toReal| ≤
      (1 / 100 : ℝ) := by
  have hsound := sigmoidHalfReplay.sound sigmoidHalfReplay_is_accepted
  have hcast :
      |positiveFiveEighths.toReal - Real.sigmoid positiveHalf.toReal| ≤
        (((1 : ℚ) / 100 : ℚ) : ℝ) := by
    simpa only [sigmoidHalfReplay, sigmoidHalf,
      ActivationCertificate.operation, ActivationCertificate.localError,
      RegisteredUnaryOp.realMap]
      using hsound
  norm_num at hcast ⊢
  exact hcast

def siluHalfReplay : Float32ActivationReplay where
  input := positiveHalf
  output := positiveFiveSixteenths
  enclosure := .direct siluHalf

theorem siluHalfReplay_is_accepted : siluHalfReplay.check = true := by
  simp only [Float32ActivationReplay.check, siluHalfReplay,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue]
  rw [siluHalf_is_accepted]
  norm_num [siluHalf, positiveHalf_toRat, positiveFiveSixteenths_toRat]

/-- A concrete finite-word replay whose exponential enclosure uses power-of-two
range reduction rather than the direct small-argument Taylor path. -/
def sigmoidTwoReplay : Float32ActivationReplay where
  input := positiveTwo
  output := positiveSevenEighths
  enclosure := .rangeReduced generatedSigmoidTwo

theorem sigmoidTwoReplay_is_accepted : sigmoidTwoReplay.check = true := by
  simp only [Float32ActivationReplay.check, sigmoidTwoReplay,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue]
  rw [generatedSigmoidTwo_is_accepted]
  norm_num [generatedSigmoidTwo, positiveTwo_toRat,
    positiveSevenEighths_toRat]

theorem sigmoidTwoReplay_sound :
    |positiveSevenEighths.toReal - Real.sigmoid positiveTwo.toReal| ≤
      (2697 / 362632 : ℝ) := by
  have hsound := sigmoidTwoReplay.sound sigmoidTwoReplay_is_accepted
  have hcast :
      |positiveSevenEighths.toReal - Real.sigmoid positiveTwo.toReal| ≤
        (((2697 : ℚ) / 362632 : ℚ) : ℝ) := by
    simpa only [sigmoidTwoReplay, generatedSigmoidTwo,
      ActivationCertificate.operation, ActivationCertificate.localError,
      RegisteredUnaryOp.realMap]
      using hsound
  norm_num at hcast ⊢
  exact hcast

def mismatchedOutputReplay : Float32ActivationReplay :=
  { sigmoidHalfReplay with output := positiveOne }

theorem mismatchedOutputReplay_is_rejected :
    mismatchedOutputReplay.check = false := by
  simp only [mismatchedOutputReplay, sigmoidHalfReplay,
    Float32ActivationReplay.check, ActivationCertificate.check,
    ActivationCertificate.argument, ActivationCertificate.runtimeValue]
  rw [sigmoidHalf_is_accepted]
  norm_num [sigmoidHalf, Float32CheckpointMatrix.positiveOne_toRat]

def tooTightReplay : Float32ActivationReplay :=
  { sigmoidHalfReplay with enclosure := .direct tooTightSigmoidHalf }

theorem tooTightReplay_is_rejected : tooTightReplay.check = false := by
  simp [tooTightReplay, sigmoidHalfReplay, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, tooTightSigmoidHalf_is_rejected]

#print axioms Float32ActivationReplay.check_eq_true_iff
#print axioms Float32ActivationReplay.sound
#print axioms sigmoidHalfReplay_sound
#print axioms sigmoidTwoReplay_sound
#print axioms mismatchedOutputReplay_is_rejected
#print axioms tooTightReplay_is_rejected

end

end Float32ActivationReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
