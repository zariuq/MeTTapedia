import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalUnaryWireCertificateChecker
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalRangeReducedActivationEnclosureCertificate

/-!
# Recursive rational mixed-expression certificates

This module extends the accepted algebraic wire leaves with recursively nested
addition, multiplication, Boolean masking, and checked sigmoid or SiLU nodes.
Every transcendental node carries its own rational activation enclosure.  The
kernel reconstructs exact ranges and runtime-error transport through the whole
tree; merely naming a unary operation never suffices.

Binary32 provenance is intentionally separate.  A producer may decode traced
words to the rational runtime fields here, but the word-to-rational binding is
checked by `Float32ActivationReplayCertificate`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RationalMixedExpressionCertificateChecker

open FinitePrecisionExpressionCertificate
open RegisteredUnaryExpressionCertificate
open RationalExpressionCertificateChecker
open RationalActivationEnclosureCertificate
open RationalUnaryWireCertificateChecker
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

universe u

/-- Recursive proof-carrying wire format.  Accepted algebraic wires form the
leaves; mixed operations may then be nested without restriction. -/
inductive MixedCertificate (Variable : Type u) where
  | algebraic (body : WireCertificate Variable)
  | add (left right : MixedCertificate Variable)
      (runtimeValue exactRadius localError errorRadius : ℚ)
  | multiply (left right : MixedCertificate Variable)
      (runtimeValue exactRadius localError errorRadius : ℚ)
  | mask (active : Bool) (body : MixedCertificate Variable)
      (runtimeValue exactRadius localError errorRadius : ℚ)
  | unary (operation : RegisteredUnaryOp) (body : MixedCertificate Variable)
      (activation : ActivationCertificate) (exactRadius errorRadius : ℚ)
  deriving Repr

def MixedCertificate.runtimeValue {Variable : Type u} :
    MixedCertificate Variable → ℚ
  | .algebraic body => body.runtimeValue
  | .add _ _ runtimeValue _ _ _ => runtimeValue
  | .multiply _ _ runtimeValue _ _ _ => runtimeValue
  | .mask _ _ runtimeValue _ _ _ => runtimeValue
  | .unary _ _ activation _ _ => activation.runtimeValue

def MixedCertificate.exactRadius {Variable : Type u} :
    MixedCertificate Variable → ℚ
  | .algebraic body => body.exactRadius
  | .add _ _ _ exactRadius _ _ => exactRadius
  | .multiply _ _ _ exactRadius _ _ => exactRadius
  | .mask _ _ _ exactRadius _ _ => exactRadius
  | .unary _ _ _ exactRadius _ => exactRadius

def MixedCertificate.errorRadius {Variable : Type u} :
    MixedCertificate Variable → ℚ
  | .algebraic body => body.errorRadius
  | .add _ _ _ _ _ errorRadius => errorRadius
  | .multiply _ _ _ _ _ errorRadius => errorRadius
  | .mask _ _ _ _ _ errorRadius => errorRadius
  | .unary _ _ _ _ errorRadius => errorRadius

def MixedCertificate.expression {Variable : Type u} :
    MixedCertificate Variable → RegisteredExpr Variable
  | .algebraic body => body.expression
  | .add left right _ _ _ _ => .add left.expression right.expression
  | .multiply left right _ _ _ _ => .multiply left.expression right.expression
  | .mask active body _ _ _ _ => .mask active body.expression
  | .unary operation body _ _ _ => .unary operation body.expression

/-- Propositional meaning mirrored by `MixedCertificate.check`. -/
def MixedCertificate.Valid {Variable : Type u}
    (environment : Variable → ℚ) : MixedCertificate Variable → Prop
  | .algebraic body => body.Valid environment
  | .add left right runtimeValue exactRadius localError errorRadius =>
      left.Valid environment ∧ right.Valid environment ∧
      0 ≤ exactRadius ∧ left.exactRadius + right.exactRadius ≤ exactRadius ∧
      0 ≤ localError ∧
      |runtimeValue - (left.runtimeValue + right.runtimeValue)| ≤ localError ∧
      0 ≤ errorRadius ∧
      localError + left.errorRadius + right.errorRadius ≤ errorRadius
  | .multiply left right runtimeValue exactRadius localError errorRadius =>
      left.Valid environment ∧ right.Valid environment ∧
      0 ≤ exactRadius ∧ left.exactRadius * right.exactRadius ≤ exactRadius ∧
      0 ≤ localError ∧
      |runtimeValue - left.runtimeValue * right.runtimeValue| ≤ localError ∧
      0 ≤ errorRadius ∧
      localError + left.errorRadius * (right.exactRadius + right.errorRadius) +
        left.exactRadius * right.errorRadius ≤ errorRadius
  | .mask active body runtimeValue exactRadius localError errorRadius =>
      body.Valid environment ∧
      0 ≤ exactRadius ∧ boolRational active * body.exactRadius ≤ exactRadius ∧
      0 ≤ localError ∧
      |runtimeValue - boolRational active * body.runtimeValue| ≤ localError ∧
      0 ≤ errorRadius ∧
      localError + boolRational active * body.errorRadius ≤ errorRadius
  | .unary operation body activation exactRadius errorRadius =>
      body.Valid environment ∧ activation.Valid ∧
      activation.operation = operation ∧
      activation.argument = body.runtimeValue ∧
      0 ≤ exactRadius ∧
      registeredOutputRadiusRat operation body.exactRadius ≤ exactRadius ∧
      0 ≤ errorRadius ∧
      activation.localError +
          registeredPairRateRat operation (body.exactRadius + body.errorRadius) *
            body.errorRadius ≤ errorRadius

/-- Executable recursive checker. -/
def MixedCertificate.check {Variable : Type u}
    (environment : Variable → ℚ) : MixedCertificate Variable → Bool
  | .algebraic body => body.check environment
  | .add left right runtimeValue exactRadius localError errorRadius =>
      left.check environment && (right.check environment &&
        decide (0 ≤ exactRadius ∧
          left.exactRadius + right.exactRadius ≤ exactRadius ∧
          0 ≤ localError ∧
          |runtimeValue - (left.runtimeValue + right.runtimeValue)| ≤ localError ∧
          0 ≤ errorRadius ∧
          localError + left.errorRadius + right.errorRadius ≤ errorRadius))
  | .multiply left right runtimeValue exactRadius localError errorRadius =>
      left.check environment && (right.check environment &&
        decide (0 ≤ exactRadius ∧
          left.exactRadius * right.exactRadius ≤ exactRadius ∧
          0 ≤ localError ∧
          |runtimeValue - left.runtimeValue * right.runtimeValue| ≤ localError ∧
          0 ≤ errorRadius ∧
          localError + left.errorRadius * (right.exactRadius + right.errorRadius) +
            left.exactRadius * right.errorRadius ≤ errorRadius))
  | .mask active body runtimeValue exactRadius localError errorRadius =>
      body.check environment &&
        decide (0 ≤ exactRadius ∧
          boolRational active * body.exactRadius ≤ exactRadius ∧
          0 ≤ localError ∧
          |runtimeValue - boolRational active * body.runtimeValue| ≤ localError ∧
          0 ≤ errorRadius ∧
          localError + boolRational active * body.errorRadius ≤ errorRadius)
  | .unary operation body activation exactRadius errorRadius =>
      body.check environment && (activation.check &&
        decide (activation.operation = operation ∧
          activation.argument = body.runtimeValue ∧
          0 ≤ exactRadius ∧
          registeredOutputRadiusRat operation body.exactRadius ≤ exactRadius ∧
          0 ≤ errorRadius ∧
          activation.localError +
              registeredPairRateRat operation
                (body.exactRadius + body.errorRadius) * body.errorRadius ≤
            errorRadius))

theorem MixedCertificate.check_eq_true_iff {Variable : Type u}
    (environment : Variable → ℚ) (certificate : MixedCertificate Variable) :
    certificate.check environment = true ↔ certificate.Valid environment := by
  induction certificate with
  | algebraic body =>
      simp [MixedCertificate.check, MixedCertificate.Valid,
        WireCertificate.check_eq_true_iff]
  | add left right _ _ _ _ leftIH rightIH =>
      simp [MixedCertificate.check, MixedCertificate.Valid, leftIH, rightIH]
  | multiply left right _ _ _ _ leftIH rightIH =>
      simp [MixedCertificate.check, MixedCertificate.Valid, leftIH, rightIH]
  | mask active body _ _ _ _ bodyIH =>
      simp [MixedCertificate.check, MixedCertificate.Valid, bodyIH]
  | unary operation body activation _ _ bodyIH =>
      simp [MixedCertificate.check, MixedCertificate.Valid, bodyIH,
        ActivationCertificate.check_eq_true_iff]

theorem MixedCertificate.valid_exactRadius_nonneg {Variable : Type u}
    {environment : Variable → ℚ} {certificate : MixedCertificate Variable}
    (hvalid : certificate.Valid environment) :
    0 ≤ certificate.exactRadius := by
  cases certificate with
  | algebraic body => exact body.valid_exactRadius_nonneg hvalid
  | add | multiply | mask | unary =>
      simp only [MixedCertificate.Valid] at hvalid
      simp only [MixedCertificate.exactRadius]
      aesop

theorem MixedCertificate.valid_errorRadius_nonneg {Variable : Type u}
    {environment : Variable → ℚ} {certificate : MixedCertificate Variable}
    (hvalid : certificate.Valid environment) :
    0 ≤ certificate.errorRadius := by
  cases certificate with
  | algebraic body => exact body.valid_errorRadius_nonneg hvalid
  | add | multiply | mask | unary =>
      simp only [MixedCertificate.Valid] at hvalid
      simp only [MixedCertificate.errorRadius]
      aesop

/-- Accepted mixed trees compile recursively to the generic exact-range
certificate. -/
theorem MixedCertificate.valid_exactRangeCertificate {Variable : Type u}
    {environment : Variable → ℚ} (certificate : MixedCertificate Variable)
    (hvalid : certificate.Valid environment) :
    ExactRangeCertificate (realEnvironment environment)
      certificate.expression.toScalarExpr (certificate.exactRadius : ℝ) := by
  induction certificate with
  | algebraic body => exact body.valid_exactRangeCertificate hvalid
  | add left right runtimeValue exactRadius localError errorRadius leftIH rightIH =>
      rcases hvalid with ⟨hleft, hright, _, hrange, _⟩
      apply ExactRangeCertificate.weaken
        (ExactRangeCertificate.add (leftIH hleft) (rightIH hright))
      exact_mod_cast hrange
  | multiply left right runtimeValue exactRadius localError errorRadius leftIH rightIH =>
      rcases hvalid with ⟨hleft, hright, _, hrange, _⟩
      apply ExactRangeCertificate.weaken
        (ExactRangeCertificate.multiply (leftIH hleft) (rightIH hright))
      exact_mod_cast hrange
  | mask active body runtimeValue exactRadius localError errorRadius bodyIH =>
      rcases hvalid with ⟨hbody, _, hrange, _⟩
      apply ExactRangeCertificate.weaken
        (ExactRangeCertificate.mask active (bodyIH hbody))
      cases active <;> norm_num [boolRational, boolScalar] at hrange ⊢ <;>
        exact_mod_cast hrange
  | unary operation body activation exactRadius errorRadius bodyIH =>
      rcases hvalid with ⟨hbody, _, _, _, _, hrange, _⟩
      have hbase := registeredUnaryRange operation (bodyIH hbody)
      apply ExactRangeCertificate.weaken hbase
      rw [← cast_registeredOutputRadiusRat]
      exact_mod_cast hrange

/-- Accepted mixed trees compile recursively to the generic runtime-error
certificate. -/
theorem MixedCertificate.valid_evaluationErrorCertificate {Variable : Type u}
    {environment : Variable → ℚ} (certificate : MixedCertificate Variable)
    (hvalid : certificate.Valid environment) :
    EvaluationErrorCertificate (realEnvironment environment)
      certificate.expression.toScalarExpr (certificate.runtimeValue : ℝ)
      (certificate.errorRadius : ℝ) := by
  induction certificate with
  | algebraic body => exact body.valid_evaluationErrorCertificate hvalid
  | add left right runtimeValue exactRadius localError errorRadius leftIH rightIH =>
      rcases hvalid with
        ⟨hleft, hright, _, _, hlocalNonneg, hlocal, _, hclaimed⟩
      have hbase := EvaluationErrorCertificate.add (leftIH hleft) (rightIH hright)
        (runtimeValue : ℝ) (localError : ℝ) (by exact_mod_cast hlocalNonneg)
        (by exact_mod_cast hlocal)
      apply EvaluationErrorCertificate.weaken hbase
      exact_mod_cast hclaimed
  | multiply left right runtimeValue exactRadius localError errorRadius
      leftIH rightIH =>
      rcases hvalid with
        ⟨hleft, hright, _, _, hlocalNonneg, hlocal, _, hclaimed⟩
      have hbase := EvaluationErrorCertificate.multiply
        (leftIH hleft) (rightIH hright)
        (left.valid_exactRangeCertificate hleft)
        (right.valid_exactRangeCertificate hright)
        (runtimeValue : ℝ) (localError : ℝ) (by exact_mod_cast hlocalNonneg)
        (by exact_mod_cast hlocal)
      apply EvaluationErrorCertificate.weaken hbase
      exact_mod_cast hclaimed
  | mask active body runtimeValue exactRadius localError errorRadius bodyIH =>
      rcases hvalid with
        ⟨hbody, _, _, hlocalNonneg, hlocal, _, hclaimed⟩
      have hbase := EvaluationErrorCertificate.mask active (bodyIH hbody)
        (runtimeValue : ℝ) (localError : ℝ) (by exact_mod_cast hlocalNonneg)
        (by
          cases active <;> norm_num [boolRational, boolScalar] at hlocal ⊢ <;>
            exact_mod_cast hlocal)
      apply EvaluationErrorCertificate.weaken hbase
      cases active <;> norm_num [boolRational, boolScalar] at hclaimed ⊢ <;>
        exact_mod_cast hclaimed
  | unary operation body activation exactRadius errorRadius bodyIH =>
      rcases hvalid with
        ⟨hbody, hactivation, hoperation, hargument, _, _, _, hclaimed⟩
      have hbodyError := bodyIH hbody
      have hbodyRange := body.valid_exactRangeCertificate hbody
      have hbodyRuntime :
          |(body.runtimeValue : ℝ)| ≤
            (body.exactRadius : ℝ) + (body.errorRadius : ℝ) := by
        calc
          |(body.runtimeValue : ℝ)| =
              |((body.runtimeValue : ℝ) -
                  body.expression.toScalarExpr.realEval
                    (realEnvironment environment)) +
                body.expression.toScalarExpr.realEval
                  (realEnvironment environment)| := by
                    congr 1
                    ring
          _ ≤ |(body.runtimeValue : ℝ) -
                  body.expression.toScalarExpr.realEval
                    (realEnvironment environment)| +
                |body.expression.toScalarExpr.realEval
                  (realEnvironment environment)| := abs_add_le _ _
          _ ≤ (body.errorRadius : ℝ) + (body.exactRadius : ℝ) :=
            add_le_add hbodyError.sound hbodyRange.sound
          _ = (body.exactRadius : ℝ) + (body.errorRadius : ℝ) := by ring
      have henlargedRange :
          ExactRangeCertificate (realEnvironment environment)
            body.expression.toScalarExpr
            ((body.exactRadius : ℝ) + (body.errorRadius : ℝ)) :=
        ExactRangeCertificate.weaken hbodyRange (by
          have hnonneg := body.valid_errorRadius_nonneg hbody
          have hnonnegReal : 0 ≤ (body.errorRadius : ℝ) := by
            exact_mod_cast hnonneg
          linarith)
      have hactivationCheck : activation.check = true :=
        activation.check_eq_true_iff.mpr hactivation
      have hlocal := activation.sound hactivationCheck
      rw [hoperation, hargument] at hlocal
      have hbase := registeredUnaryError operation hbodyError henlargedRange
        hbodyRuntime
        (by exact_mod_cast hactivation.localError_nonneg) hlocal
      apply EvaluationErrorCertificate.weaken hbase
      change
        (activation.localError : ℝ) +
              operation.pairRate
                ((body.exactRadius : ℝ) + (body.errorRadius : ℝ)) *
                (body.errorRadius : ℝ) ≤ (errorRadius : ℝ)
      have hclaimedReal :
          (activation.localError : ℝ) +
              (registeredPairRateRat operation
                (body.exactRadius + body.errorRadius) : ℝ) *
                (body.errorRadius : ℝ) ≤ (errorRadius : ℝ) := by
        exact_mod_cast hclaimed
      simpa [Rat.cast_add, cast_registeredPairRateRat] using hclaimedReal

/-- Kernel theorem exported by the recursive checker. -/
theorem MixedCertificate.check_sound {Variable : Type u}
    {environment : Variable → ℚ} (certificate : MixedCertificate Variable)
    (hcheck : certificate.check environment = true) :
    |(certificate.runtimeValue : ℝ) -
        certificate.expression.realEval (realEnvironment environment)| ≤
      (certificate.errorRadius : ℝ) := by
  have hvalid := (certificate.check_eq_true_iff environment).mp hcheck
  have hsound := (certificate.valid_evaluationErrorCertificate hvalid).sound
  simpa [RegisteredExpr.toScalarExpr_realEval] using hsound

/-! ## Nested positive and negative fixtures -/

private abbrev OneVariable := Fin 1
private def environment : OneVariable → ℚ := fun _ => 1 / 2
private def algebraicInput : WireCertificate OneVariable :=
  .var 0 (1 / 2) (1 / 2) 0
private def algebraicZero : WireCertificate OneVariable :=
  .constant 0 0 0 0

private def input : MixedCertificate OneVariable := .algebraic algebraicInput
private def zero : MixedCertificate OneVariable := .algebraic algebraicZero

private def mixedBody : MixedCertificate OneVariable :=
  .add input zero (1 / 2) (1 / 2) 0 0

private def nestedSigmoid : MixedCertificate OneVariable :=
  .unary .sigmoid mixedBody (.direct sigmoidHalf) 1 (1 / 100)

private def nestedOuterAdd : MixedCertificate OneVariable :=
  .add nestedSigmoid zero (5 / 8) 1 0 (1 / 100)

theorem nestedOuterAdd_is_accepted :
    nestedOuterAdd.check environment = true := by
  simp only [nestedOuterAdd, nestedSigmoid, mixedBody, input, zero,
    MixedCertificate.check, ActivationCertificate.check,
    ActivationCertificate.operation, ActivationCertificate.argument,
    ActivationCertificate.localError]
  rw [sigmoidHalf_is_accepted]
  norm_num [
    algebraicInput, algebraicZero, environment, MixedCertificate.check,
    MixedCertificate.runtimeValue, MixedCertificate.exactRadius,
    MixedCertificate.errorRadius, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, registeredOutputRadiusRat,
    registeredPairRateRat, ActivationCertificate.runtimeValue,
    sigmoidHalf, sigmoidHalf_is_accepted]

theorem nestedOuterAdd_sound :
    |((5 / 8 : ℚ) : ℝ) - (Real.sigmoid (1 / 2) + 0)| ≤
      (((1 / 100 : ℚ) : ℝ)) := by
  simpa [nestedOuterAdd, nestedSigmoid, mixedBody, input, zero,
    algebraicInput, algebraicZero, environment, MixedCertificate.runtimeValue,
    MixedCertificate.errorRadius, MixedCertificate.expression, WireCertificate.expression,
    ActivationCertificate.runtimeValue, ActivationCertificate.localError,
    RegisteredExpr.realEval, realEnvironment, RegisteredUnaryOp.realMap] using
      nestedOuterAdd.check_sound nestedOuterAdd_is_accepted

private def understatedNestedError : MixedCertificate OneVariable :=
  .add nestedSigmoid zero (5 / 8) 1 0 0

theorem understatedNestedError_is_rejected :
    understatedNestedError.check environment = false := by
  simp only [understatedNestedError, nestedSigmoid, mixedBody, input, zero,
    MixedCertificate.check, ActivationCertificate.check,
    ActivationCertificate.operation, ActivationCertificate.argument,
    ActivationCertificate.localError]
  rw [sigmoidHalf_is_accepted]
  norm_num [
    algebraicInput, algebraicZero, environment, MixedCertificate.check,
    MixedCertificate.runtimeValue, MixedCertificate.exactRadius,
    MixedCertificate.errorRadius, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, registeredOutputRadiusRat,
    registeredPairRateRat, ActivationCertificate.runtimeValue,
    sigmoidHalf, sigmoidHalf_is_accepted]

private def rangeEnvironment : OneVariable → ℚ := fun _ => 2
private def rangeAlgebraicInput : WireCertificate OneVariable :=
  .var 0 2 2 0
private def rangeInput : MixedCertificate OneVariable :=
  .algebraic rangeAlgebraicInput

/-- A recursive unary leaf using the checked power-of-two range-reduction path. -/
private def rangeReducedSigmoid : MixedCertificate OneVariable :=
  .unary .sigmoid rangeInput (.rangeReduced sigmoidTwo) 1 (1 / 100)

theorem rangeReducedSigmoid_is_accepted :
    rangeReducedSigmoid.check rangeEnvironment = true := by
  simp only [rangeReducedSigmoid, rangeInput, MixedCertificate.check,
    ActivationCertificate.check, ActivationCertificate.operation,
    ActivationCertificate.argument, ActivationCertificate.localError]
  rw [sigmoidTwo_is_accepted]
  norm_num [rangeAlgebraicInput, rangeEnvironment, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, MixedCertificate.runtimeValue,
    MixedCertificate.errorRadius, registeredOutputRadiusRat,
    registeredPairRateRat, sigmoidTwo]

theorem rangeReducedSigmoid_sound :
    |((7 / 8 : ℚ) : ℝ) - Real.sigmoid 2| ≤ (((1 / 100 : ℚ) : ℝ)) := by
  simpa [rangeReducedSigmoid, rangeInput, rangeAlgebraicInput, rangeEnvironment,
    MixedCertificate.runtimeValue, MixedCertificate.errorRadius,
    MixedCertificate.expression, WireCertificate.expression,
    ActivationCertificate.runtimeValue, ActivationCertificate.localError,
    RegisteredExpr.realEval, realEnvironment, RegisteredUnaryOp.realMap,
    sigmoidTwo] using
      rangeReducedSigmoid.check_sound rangeReducedSigmoid_is_accepted

#print axioms MixedCertificate.check_eq_true_iff
#print axioms MixedCertificate.valid_exactRangeCertificate
#print axioms MixedCertificate.valid_evaluationErrorCertificate
#print axioms MixedCertificate.check_sound
#print axioms nestedOuterAdd_sound
#print axioms understatedNestedError_is_rejected
#print axioms rangeReducedSigmoid_sound

end

end RationalMixedExpressionCertificateChecker

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
