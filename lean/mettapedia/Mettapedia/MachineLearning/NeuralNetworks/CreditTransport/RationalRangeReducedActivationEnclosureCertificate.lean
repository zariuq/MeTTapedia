import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalActivationEnclosureCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalRangeReducedExpEnclosureCertificate

/-!
# Range-reduced rational activation certificates

This file lifts the power-of-two exponential enclosure through sigmoid and
SiLU, then provides one tagged activation-certificate type that covers both
the original direct Taylor path and the range-reduced path.  Downstream
checkers can therefore remain agnostic about how the exponential interval was
obtained while the kernel still checks the selected construction.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RationalRangeReducedActivationEnclosureCertificate

open RegisteredUnaryExpressionCertificate
open RationalActivationEnclosureCertificate
open RationalExpEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate

noncomputable section

/-- Source-facing sigmoid or SiLU record backed by a range-reduced
exponential certificate. -/
structure RangeReducedActivationEnclosure where
  operation : RegisteredUnaryOp
  argument : ℚ
  runtimeValue : ℚ
  localError : ℚ
  outputLower : ℚ
  outputUpper : ℚ
  expCertificate : RangeReducedExpEnclosure
  deriving Repr

def RangeReducedActivationEnclosure.Valid
    (certificate : RangeReducedActivationEnclosure) : Prop :=
  match certificate.operation with
  | .square => False
  | .sigmoid | .silu =>
      certificate.expCertificate.argument = -certificate.argument ∧
      certificate.expCertificate.Valid ∧
      0 < certificate.expCertificate.lower ∧
      0 ≤ certificate.localError ∧
      certificate.outputLower ≤ activationLowerRat certificate.operation
        certificate.argument certificate.expCertificate.lower
        certificate.expCertificate.upper ∧
      activationUpperRat certificate.operation certificate.argument
          certificate.expCertificate.lower certificate.expCertificate.upper ≤
        certificate.outputUpper ∧
      certificate.runtimeValue - certificate.localError ≤
        certificate.outputLower ∧
      certificate.outputUpper ≤
        certificate.runtimeValue + certificate.localError

def RangeReducedActivationEnclosure.check
    (certificate : RangeReducedActivationEnclosure) : Bool :=
  match certificate.operation with
  | .square => false
  | .sigmoid | .silu =>
      decide (certificate.expCertificate.argument = -certificate.argument) &&
      (certificate.expCertificate.check &&
        (decide (0 < certificate.expCertificate.lower) &&
         (decide (0 ≤ certificate.localError) &&
          (decide (certificate.outputLower ≤
            activationLowerRat certificate.operation certificate.argument
              certificate.expCertificate.lower certificate.expCertificate.upper) &&
           (decide (activationUpperRat certificate.operation certificate.argument
              certificate.expCertificate.lower certificate.expCertificate.upper ≤
                certificate.outputUpper) &&
            (decide (certificate.runtimeValue - certificate.localError ≤
                certificate.outputLower) &&
             decide (certificate.outputUpper ≤
                certificate.runtimeValue + certificate.localError)))))))

theorem RangeReducedActivationEnclosure.check_eq_true_iff
    (certificate : RangeReducedActivationEnclosure) :
    certificate.check = true ↔ certificate.Valid := by
  cases hop : certificate.operation <;>
    simp [RangeReducedActivationEnclosure.check,
      RangeReducedActivationEnclosure.Valid, hop,
      RangeReducedExpEnclosure.check_eq_true_iff]

theorem RangeReducedActivationEnclosure.Valid.localError_nonneg
    {certificate : RangeReducedActivationEnclosure}
    (hvalid : certificate.Valid) : 0 ≤ certificate.localError := by
  cases hoperation : certificate.operation with
  | square =>
      simp only [RangeReducedActivationEnclosure.Valid, hoperation] at hvalid
  | sigmoid | silu =>
      simp only [RangeReducedActivationEnclosure.Valid, hoperation] at hvalid
      exact hvalid.2.2.2.1

/-- Every accepted range-reduced activation record bounds its runtime output
against the registered exact-real activation. -/
theorem RangeReducedActivationEnclosure.sound
    (certificate : RangeReducedActivationEnclosure)
    (hcheck : certificate.check = true) :
    |(certificate.runtimeValue : ℝ) -
        certificate.operation.realMap (certificate.argument : ℝ)| ≤
      (certificate.localError : ℝ) := by
  have hvalid := certificate.check_eq_true_iff.mp hcheck
  cases hop : certificate.operation with
  | square =>
      simp only [RangeReducedActivationEnclosure.Valid, hop] at hvalid
  | sigmoid | silu =>
      simp only [RangeReducedActivationEnclosure.Valid, hop] at hvalid
      rcases hvalid with
        ⟨hexpArgument, hexpValid, hexpLowerPositive, hlocalNonneg,
          houtLower, houtUpper, hruntimeLower, hruntimeUpper⟩
      have hexpCheck : certificate.expCertificate.check = true :=
        certificate.expCertificate.check_eq_true_iff.mpr hexpValid
      have hexpSound := certificate.expCertificate.sound hexpCheck
      have hexpArgumentReal :
          (certificate.expCertificate.argument : ℝ) =
            -(certificate.argument : ℝ) := by
        exact_mod_cast hexpArgument
      rw [hexpArgumentReal] at hexpSound
      have hcandidates := exact_output_mem_candidates certificate.operation
        hexpLowerPositive hexpSound.1 hexpSound.2 (by simp [hop])
      have houtLowerReal :
          (certificate.outputLower : ℝ) ≤
            (activationLowerRat certificate.operation certificate.argument
              certificate.expCertificate.lower
              certificate.expCertificate.upper : ℝ) := by
        rw [hop]
        exact_mod_cast houtLower
      have houtUpperReal :
          (activationUpperRat certificate.operation certificate.argument
              certificate.expCertificate.lower
              certificate.expCertificate.upper : ℝ) ≤
            (certificate.outputUpper : ℝ) := by
        rw [hop]
        exact_mod_cast houtUpper
      have hruntimeLowerReal :
          (certificate.runtimeValue : ℝ) - certificate.localError ≤
            certificate.outputLower := by
        exact_mod_cast hruntimeLower
      have hruntimeUpperReal :
          (certificate.outputUpper : ℝ) ≤
            certificate.runtimeValue + certificate.localError := by
        exact_mod_cast hruntimeUpper
      have hlow :
          (certificate.runtimeValue : ℝ) - certificate.localError ≤
            certificate.operation.realMap (certificate.argument : ℝ) :=
        hruntimeLowerReal.trans <| houtLowerReal.trans hcandidates.1
      have hhigh :
          certificate.operation.realMap (certificate.argument : ℝ) ≤
            certificate.runtimeValue + certificate.localError :=
        hcandidates.2.trans <| houtUpperReal.trans hruntimeUpperReal
      have hresult :
          |(certificate.runtimeValue : ℝ) -
              certificate.operation.realMap (certificate.argument : ℝ)| ≤
            (certificate.localError : ℝ) := by
        rw [abs_sub_le_iff]
        constructor <;> linarith
      simpa only [hop] using hresult

/-- Unified checked activation leaf.  The tag is explicit in the serialized
proof object, so a producer cannot silently replace direct Taylor checking by
range reduction or conversely. -/
inductive ActivationCertificate where
  | direct (certificate : ActivationEnclosure)
  | rangeReduced (certificate : RangeReducedActivationEnclosure)
  deriving Repr

def ActivationCertificate.operation : ActivationCertificate → RegisteredUnaryOp
  | .direct certificate => certificate.operation
  | .rangeReduced certificate => certificate.operation

def ActivationCertificate.argument : ActivationCertificate → ℚ
  | .direct certificate => certificate.argument
  | .rangeReduced certificate => certificate.argument

def ActivationCertificate.runtimeValue : ActivationCertificate → ℚ
  | .direct certificate => certificate.runtimeValue
  | .rangeReduced certificate => certificate.runtimeValue

def ActivationCertificate.localError : ActivationCertificate → ℚ
  | .direct certificate => certificate.localError
  | .rangeReduced certificate => certificate.localError

def ActivationCertificate.Valid : ActivationCertificate → Prop
  | .direct certificate => certificate.Valid
  | .rangeReduced certificate => certificate.Valid

def ActivationCertificate.check : ActivationCertificate → Bool
  | .direct certificate => certificate.check
  | .rangeReduced certificate => certificate.check

theorem ActivationCertificate.check_eq_true_iff
    (certificate : ActivationCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  cases certificate with
  | direct certificate => exact certificate.check_eq_true_iff
  | rangeReduced certificate => exact certificate.check_eq_true_iff

theorem ActivationCertificate.Valid.localError_nonneg
    {certificate : ActivationCertificate} (hvalid : certificate.Valid) :
    0 ≤ certificate.localError := by
  cases certificate with
  | direct certificate =>
      exact ActivationEnclosure.Valid.localError_nonneg hvalid
  | rangeReduced certificate =>
      exact RangeReducedActivationEnclosure.Valid.localError_nonneg hvalid

/-- Unified activation soundness theorem consumed by recursive mixed and
binary32 replay checkers. -/
theorem ActivationCertificate.sound (certificate : ActivationCertificate)
    (hcheck : certificate.check = true) :
    |(certificate.runtimeValue : ℝ) -
        certificate.operation.realMap (certificate.argument : ℝ)| ≤
      (certificate.localError : ℝ) := by
  cases certificate with
  | direct certificate => exact certificate.sound hcheck
  | rangeReduced certificate => exact certificate.sound hcheck

/-! ## Positive and corrupt fixtures -/

def sigmoidTwo : RangeReducedActivationEnclosure where
  operation := .sigmoid
  argument := 2
  runtimeValue := 7 / 8
  localError := 1 / 100
  outputLower := sigmoidLowerRat expNegTwo.upper
  outputUpper := sigmoidUpperRat expNegTwo.lower
  expCertificate := expNegTwo

theorem sigmoidTwo_is_accepted : sigmoidTwo.check = true := by
  simp only [RangeReducedActivationEnclosure.check, sigmoidTwo]
  rw [expNegTwo_is_accepted]
  norm_num [expNegTwo, expNegHalf, expScale, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat]

theorem sigmoidTwo_sound :
    |((7 / 8 : ℚ) : ℝ) - Real.sigmoid 2| ≤ (((1 / 100 : ℚ) : ℝ)) := by
  simpa [sigmoidTwo, RegisteredUnaryOp.realMap] using
    sigmoidTwo.sound sigmoidTwo_is_accepted

/-- Exact record emitted by the source-side rational generator for the
binary32 pair `2.0 ↦ 0.875`, using five Taylor terms at the reduced argument
`-1`.  The kernel recomputes every endpoint rather than trusting the producer. -/
def generatedExpNegTwo : RangeReducedExpEnclosure where
  argument := -2
  halvings := 1
  reduced := {
    argument := -1
    terms := 5
    lower := 73 / 200
    upper := 77 / 200
  }
  lower := 5329 / 40000
  upper := 5929 / 40000

theorem generatedExpNegTwo_is_accepted : generatedExpNegTwo.check = true := by
  norm_num [generatedExpNegTwo, RangeReducedExpEnclosure.check,
    ExpEnclosure.check, expScale, expTaylorRat, expTaylorErrorRat,
    Finset.sum_range_succ, Nat.factorial]

def generatedSigmoidTwo : RangeReducedActivationEnclosure where
  operation := .sigmoid
  argument := 2
  runtimeValue := 7 / 8
  localError := 2697 / 362632
  outputLower := 40000 / 45929
  outputUpper := 40000 / 45329
  expCertificate := generatedExpNegTwo

theorem generatedSigmoidTwo_is_accepted : generatedSigmoidTwo.check = true := by
  simp only [RangeReducedActivationEnclosure.check, generatedSigmoidTwo]
  rw [generatedExpNegTwo_is_accepted]
  norm_num [generatedExpNegTwo, activationLowerRat, activationUpperRat,
    sigmoidLowerRat, sigmoidUpperRat]

theorem generatedSigmoidTwo_sound :
    |((7 / 8 : ℚ) : ℝ) - Real.sigmoid 2| ≤
      (((2697 / 362632 : ℚ) : ℝ)) := by
  simpa [generatedSigmoidTwo, RegisteredUnaryOp.realMap] using
    generatedSigmoidTwo.sound generatedSigmoidTwo_is_accepted

def mismatchedSigmoidTwo : RangeReducedActivationEnclosure :=
  { sigmoidTwo with expCertificate := { expNegTwo with argument := -3 } }

theorem mismatchedSigmoidTwo_is_rejected :
    mismatchedSigmoidTwo.check = false := by
  simp [mismatchedSigmoidTwo, sigmoidTwo,
    RangeReducedActivationEnclosure.check]

#print axioms RangeReducedActivationEnclosure.check_eq_true_iff
#print axioms RangeReducedActivationEnclosure.sound
#print axioms ActivationCertificate.check_eq_true_iff
#print axioms ActivationCertificate.sound
#print axioms sigmoidTwo_sound
#print axioms generatedSigmoidTwo_sound
#print axioms mismatchedSigmoidTwo_is_rejected

end

end RationalRangeReducedActivationEnclosureCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
