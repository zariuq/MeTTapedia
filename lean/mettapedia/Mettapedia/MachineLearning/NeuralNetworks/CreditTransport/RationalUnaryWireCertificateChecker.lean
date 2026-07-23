import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalActivationEnclosureCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalExpressionCertificateChecker

/-!
# Decidable rational unary-wire certificates

The algebraic wire checker deliberately keeps exact rational semantics and
therefore rejects unary nodes.  This file adds one certified sigmoid or SiLU
node above an accepted algebraic wire.  The local transcendental enclosure is
checked separately, while the kernel reconstructs input-error transport and
the final exact-range and runtime-error certificates.

This first layer is intentionally nonrecursive.  It preserves the algebraic
checker's exact-rational invariant and provides the proof-carrying bridge
needed by a later recursively typed mixed expression language.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RationalUnaryWireCertificateChecker

open FinitePrecisionExpressionCertificate
open RegisteredUnaryExpressionCertificate
open RationalExpressionCertificateChecker
open RationalActivationEnclosureCertificate

noncomputable section

universe u

/-- Rational form of the registered exact-output radius. -/
def registeredOutputRadiusRat (operation : RegisteredUnaryOp) (radius : ℚ) : ℚ :=
  match operation with
  | .square => radius ^ 2
  | .sigmoid => 1
  | .silu => radius

/-- Rational form of the registered pairwise transport rate. -/
def registeredPairRateRat (operation : RegisteredUnaryOp) (radius : ℚ) : ℚ :=
  match operation with
  | .square => 2 * radius
  | .sigmoid => 1 / 4
  | .silu => 1 + radius / 4

@[simp] theorem cast_registeredOutputRadiusRat
    (operation : RegisteredUnaryOp) (radius : ℚ) :
    (registeredOutputRadiusRat operation radius : ℝ) =
      operation.outputRadius (radius : ℝ) := by
  cases operation <;>
    simp [registeredOutputRadiusRat, RegisteredUnaryOp.outputRadius]

@[simp] theorem cast_registeredPairRateRat
    (operation : RegisteredUnaryOp) (radius : ℚ) :
    (registeredPairRateRat operation radius : ℝ) =
      operation.pairRate (radius : ℝ) := by
  cases operation <;>
    norm_num [registeredPairRateRat, RegisteredUnaryOp.pairRate]

/-- A checked unary node above an accepted algebraic wire.  The runtime value
and local error live in the activation enclosure; the outer fields claim the
transported exact range and global runtime error. -/
structure UnaryWireCertificate (Variable : Type u) where
  operation : RegisteredUnaryOp
  body : WireCertificate Variable
  activation : ActivationEnclosure
  exactRadius : ℚ
  errorRadius : ℚ
  deriving Repr

def UnaryWireCertificate.runtimeValue {Variable : Type u}
    (certificate : UnaryWireCertificate Variable) : ℚ :=
  certificate.activation.runtimeValue

def UnaryWireCertificate.expression {Variable : Type u}
    (certificate : UnaryWireCertificate Variable) : RegisteredExpr Variable :=
  .unary certificate.operation certificate.body.expression

/-- Propositional meaning mirrored exactly by the executable checker. -/
def UnaryWireCertificate.Valid {Variable : Type u}
    (environment : Variable → ℚ)
    (certificate : UnaryWireCertificate Variable) : Prop :=
  certificate.body.Valid environment ∧
  certificate.activation.Valid ∧
  certificate.activation.operation = certificate.operation ∧
  certificate.activation.argument = certificate.body.runtimeValue ∧
  0 ≤ certificate.exactRadius ∧
  registeredOutputRadiusRat certificate.operation certificate.body.exactRadius ≤
    certificate.exactRadius ∧
  0 ≤ certificate.errorRadius ∧
  certificate.activation.localError +
      registeredPairRateRat certificate.operation
        (certificate.body.exactRadius + certificate.body.errorRadius) *
        certificate.body.errorRadius ≤
    certificate.errorRadius

/-- Executable checker for one certified sigmoid or SiLU wire. -/
def UnaryWireCertificate.check {Variable : Type u}
    (environment : Variable → ℚ)
    (certificate : UnaryWireCertificate Variable) : Bool :=
  certificate.body.check environment &&
  (certificate.activation.check &&
    decide (certificate.activation.operation = certificate.operation ∧
      certificate.activation.argument = certificate.body.runtimeValue ∧
      0 ≤ certificate.exactRadius ∧
      registeredOutputRadiusRat certificate.operation
          certificate.body.exactRadius ≤ certificate.exactRadius ∧
      0 ≤ certificate.errorRadius ∧
      certificate.activation.localError +
          registeredPairRateRat certificate.operation
            (certificate.body.exactRadius + certificate.body.errorRadius) *
            certificate.body.errorRadius ≤ certificate.errorRadius))

theorem UnaryWireCertificate.check_eq_true_iff {Variable : Type u}
    (environment : Variable → ℚ)
    (certificate : UnaryWireCertificate Variable) :
    certificate.check environment = true ↔ certificate.Valid environment := by
  simp [UnaryWireCertificate.check, UnaryWireCertificate.Valid,
    WireCertificate.check_eq_true_iff,
    ActivationEnclosure.check_eq_true_iff]

/-- Accepted unary wires compile to the generic exact-range certificate. -/
theorem UnaryWireCertificate.valid_exactRangeCertificate {Variable : Type u}
    {environment : Variable → ℚ}
    (certificate : UnaryWireCertificate Variable)
    (hvalid : certificate.Valid environment) :
    ExactRangeCertificate (realEnvironment environment)
      certificate.expression.toScalarExpr (certificate.exactRadius : ℝ) := by
  rcases hvalid with
    ⟨hbody, _, _, _, _, hrange, _⟩
  have hbase := registeredUnaryRange certificate.operation
    (certificate.body.valid_exactRangeCertificate hbody)
  apply ExactRangeCertificate.weaken hbase
  rw [← cast_registeredOutputRadiusRat]
  exact_mod_cast hrange

/-- The accepted algebraic body runtime lies in the exact-range radius plus
its certified runtime-error radius. -/
private theorem body_runtime_mem_enlargedRadius {Variable : Type u}
    {environment : Variable → ℚ} (body : WireCertificate Variable)
    (hvalid : body.Valid environment) :
    |(body.runtimeValue : ℝ)| ≤
      (body.exactRadius : ℝ) + (body.errorRadius : ℝ) := by
  have herror := (body.valid_evaluationErrorCertificate hvalid).sound
  have hrange := (body.valid_exactRangeCertificate hvalid).sound
  calc
    |(body.runtimeValue : ℝ)| =
        |((body.runtimeValue : ℝ) -
            body.expression.toScalarExpr.realEval (realEnvironment environment)) +
          body.expression.toScalarExpr.realEval (realEnvironment environment)| := by
            congr 1
            ring
    _ ≤ |(body.runtimeValue : ℝ) -
            body.expression.toScalarExpr.realEval (realEnvironment environment)| +
          |body.expression.toScalarExpr.realEval (realEnvironment environment)| :=
      abs_add_le _ _
    _ ≤ (body.errorRadius : ℝ) + (body.exactRadius : ℝ) :=
      add_le_add herror hrange
    _ = (body.exactRadius : ℝ) + (body.errorRadius : ℝ) := by ring

/-- Accepted unary wires compile to the generic proof-carrying runtime-error
certificate.  The input region is enlarged by the accepted body error so both
the runtime and exact inputs inhabit the pairwise-rate region. -/
theorem UnaryWireCertificate.valid_evaluationErrorCertificate
    {Variable : Type u} {environment : Variable → ℚ}
    (certificate : UnaryWireCertificate Variable)
    (hvalid : certificate.Valid environment) :
    EvaluationErrorCertificate (realEnvironment environment)
      certificate.expression.toScalarExpr (certificate.runtimeValue : ℝ)
      (certificate.errorRadius : ℝ) := by
  rcases hvalid with
    ⟨hbody, hactivation, hoperation, hargument, _, _, _, hclaimed⟩
  have hbodyError := certificate.body.valid_evaluationErrorCertificate hbody
  have hbodyRange := certificate.body.valid_exactRangeCertificate hbody
  have herrorNonneg := certificate.body.valid_errorRadius_nonneg hbody
  have herrorNonnegReal : 0 ≤ (certificate.body.errorRadius : ℝ) := by
    exact_mod_cast herrorNonneg
  have henlargedRange :
      ExactRangeCertificate (realEnvironment environment)
        certificate.body.expression.toScalarExpr
        ((certificate.body.exactRadius : ℝ) +
          (certificate.body.errorRadius : ℝ)) :=
    ExactRangeCertificate.weaken hbodyRange (by
      linarith)
  have hactivationCheck : certificate.activation.check = true :=
    certificate.activation.check_eq_true_iff.mpr hactivation
  have hlocal := certificate.activation.sound hactivationCheck
  rw [hoperation, hargument] at hlocal
  have hbase := registeredUnaryError certificate.operation hbodyError
    henlargedRange (body_runtime_mem_enlargedRadius certificate.body hbody)
    (by exact_mod_cast hactivation.localError_nonneg) hlocal
  apply EvaluationErrorCertificate.weaken hbase
  have hclaimedReal :
      (certificate.activation.localError : ℝ) +
          (registeredPairRateRat certificate.operation
              (certificate.body.exactRadius + certificate.body.errorRadius) : ℝ) *
            (certificate.body.errorRadius : ℝ) ≤
        (certificate.errorRadius : ℝ) := by
    exact_mod_cast hclaimed
  simpa [Rat.cast_add, cast_registeredPairRateRat] using hclaimedReal

/-- Kernel theorem exported by the unary checker. -/
theorem UnaryWireCertificate.check_sound {Variable : Type u}
    {environment : Variable → ℚ}
    (certificate : UnaryWireCertificate Variable)
    (hcheck : certificate.check environment = true) :
    |(certificate.runtimeValue : ℝ) -
        certificate.expression.realEval (realEnvironment environment)| ≤
      (certificate.errorRadius : ℝ) := by
  have hvalid := (certificate.check_eq_true_iff environment).mp hcheck
  have hsound := (certificate.valid_evaluationErrorCertificate hvalid).sound
  simpa [RegisteredExpr.toScalarExpr_realEval] using hsound

/-! ## Positive and corrupt-record fixtures -/

private abbrev OneVariable := Fin 1

private def environment : OneVariable → ℚ := fun _ => 1 / 2

private def input : WireCertificate OneVariable :=
  .var 0 (1 / 2) (1 / 2) 0

private def sigmoidWire : UnaryWireCertificate OneVariable where
  operation := .sigmoid
  body := input
  activation := sigmoidHalf
  exactRadius := 1
  errorRadius := 1 / 100

theorem sigmoidWire_is_accepted : sigmoidWire.check environment = true := by
  simp only [UnaryWireCertificate.check, sigmoidWire]
  rw [sigmoidHalf_is_accepted]
  norm_num [input, environment, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, registeredOutputRadiusRat,
    registeredPairRateRat, sigmoidHalf]

theorem sigmoidWire_sound :
    |((5 / 8 : ℚ) : ℝ) - Real.sigmoid (1 / 2)| ≤ ((1 / 100 : ℚ) : ℝ) := by
  simpa [sigmoidWire, sigmoidHalf, input, UnaryWireCertificate.runtimeValue,
    UnaryWireCertificate.expression, WireCertificate.expression,
    RegisteredExpr.realEval, realEnvironment, environment,
    RegisteredUnaryOp.realMap] using
      sigmoidWire.check_sound sigmoidWire_is_accepted

private def siluWire : UnaryWireCertificate OneVariable where
  operation := .silu
  body := input
  activation := siluHalf
  exactRadius := 1 / 2
  errorRadius := 1 / 100

theorem siluWire_is_accepted : siluWire.check environment = true := by
  simp only [UnaryWireCertificate.check, siluWire]
  rw [siluHalf_is_accepted]
  norm_num [input, environment, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, registeredOutputRadiusRat,
    registeredPairRateRat, siluHalf]

private def understatedSigmoidError : UnaryWireCertificate OneVariable :=
  { sigmoidWire with errorRadius := 0 }

theorem understated_sigmoid_error_is_rejected :
    understatedSigmoidError.check environment = false := by
  norm_num [understatedSigmoidError, sigmoidWire, input, environment,
    UnaryWireCertificate.check, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, registeredOutputRadiusRat,
    registeredPairRateRat, sigmoidHalf, sigmoidHalf_is_accepted]

private def mismatchedSigmoidArgument : UnaryWireCertificate OneVariable :=
  { sigmoidWire with activation := { sigmoidHalf with argument := 0 } }

theorem mismatched_sigmoid_argument_is_rejected :
    mismatchedSigmoidArgument.check environment = false := by
  norm_num [mismatchedSigmoidArgument, sigmoidWire, input, environment,
    UnaryWireCertificate.check, WireCertificate.check,
    WireCertificate.runtimeValue, sigmoidHalf, ActivationEnclosure.check]

#print axioms UnaryWireCertificate.check_eq_true_iff
#print axioms UnaryWireCertificate.valid_exactRangeCertificate
#print axioms UnaryWireCertificate.valid_evaluationErrorCertificate
#print axioms UnaryWireCertificate.check_sound
#print axioms sigmoidWire_sound
#print axioms understated_sigmoid_error_is_rejected
#print axioms mismatched_sigmoid_argument_is_rejected

end

end RationalUnaryWireCertificateChecker

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
