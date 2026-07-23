import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionEvaluationError

/-!
# Proof-carrying finite-precision expression certificates

An external numerical analyzer may propose exact-value ranges and local
finite-precision errors, but the global error bound should be reconstructed by
the proof kernel.  This file supplies a small scalar expression language and
two indexed certificate languages:

* `ExactRangeCertificate` bounds the exact real value of every expression;
* `EvaluationErrorCertificate` bounds a runtime value against that exact real
  value and composes local arithmetic errors through the expression tree.

Addition, multiplication, Boolean masking, and externally certified unary
maps are included.  Multiplication keeps the cross-error term rather than
treating it as linear.  Unary nodes require both a local runtime-evaluation
bound and a pairwise rate bound.  Thus the checker can consume a future
interval, affine-arithmetic, or Taylor certificate without trusting its global
error aggregation.

No floating-point evaluation order or rounding constant is assumed here.
Those remain source-specific leaves of the certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FinitePrecisionExpressionCertificate

noncomputable section

open FinitePrecisionEvaluationError

universe u

/-- Scalar real expressions sufficient to describe one coordinate of an
affine, masked, nonlinear transition.  A unary node stores its exact real
semantics; a later source binding may restrict these nodes to a finite registry
such as SiLU or sigmoid. -/
inductive ScalarExpr (Variable : Type u) where
  | variable (name : Variable)
  | constant (value : ℝ)
  | add (left right : ScalarExpr Variable)
  | multiply (left right : ScalarExpr Variable)
  | mask (active : Bool) (body : ScalarExpr Variable)
  | unary (map : ℝ → ℝ) (body : ScalarExpr Variable)

/-- Real scalar represented by a Boolean mask. -/
def boolScalar : Bool → ℝ
  | false => 0
  | true => 1

/-- Exact real semantics of a scalar expression. -/
def ScalarExpr.realEval {Variable : Type u}
    (environment : Variable → ℝ) : ScalarExpr Variable → ℝ
  | .variable name => environment name
  | .constant value => value
  | .add left right => left.realEval environment + right.realEval environment
  | .multiply left right =>
      left.realEval environment * right.realEval environment
  | .mask active body => boolScalar active * body.realEval environment
  | .unary map body => map (body.realEval environment)

/-- A proof-carrying absolute range for the exact real evaluation.  The
constructors replay range aggregation through the expression tree.  Unary
ranges remain explicit leaves because their validation depends on the chosen
nonlinear certificate system. -/
inductive ExactRangeCertificate {Variable : Type u}
    (environment : Variable → ℝ) :
    (expression : ScalarExpr Variable) → (radius : ℝ) → Prop where
  | ofVariable (name : Variable) (radius : ℝ)
      (radius_nonneg : 0 ≤ radius)
      (value_le : |environment name| ≤ radius) :
      ExactRangeCertificate environment (.variable name) radius
  | constant (value radius : ℝ)
      (radius_nonneg : 0 ≤ radius)
      (value_le : |value| ≤ radius) :
      ExactRangeCertificate environment (.constant value) radius
  | add {left right : ScalarExpr Variable}
      {leftRadius rightRadius : ℝ}
      (leftCertificate : ExactRangeCertificate environment left leftRadius)
      (rightCertificate : ExactRangeCertificate environment right rightRadius) :
      ExactRangeCertificate environment (.add left right)
        (leftRadius + rightRadius)
  | multiply {left right : ScalarExpr Variable}
      {leftRadius rightRadius : ℝ}
      (leftCertificate : ExactRangeCertificate environment left leftRadius)
      (rightCertificate : ExactRangeCertificate environment right rightRadius) :
      ExactRangeCertificate environment (.multiply left right)
        (leftRadius * rightRadius)
  | mask {body : ScalarExpr Variable} {radius : ℝ}
      (active : Bool)
      (bodyCertificate : ExactRangeCertificate environment body radius) :
      ExactRangeCertificate environment (.mask active body)
        (boolScalar active * radius)
  | unary {body : ScalarExpr Variable} (map : ℝ → ℝ)
      {bodyRadius outputRadius : ℝ}
      (bodyCertificate : ExactRangeCertificate environment body bodyRadius)
      (outputRadius_nonneg : 0 ≤ outputRadius)
      (output_le : |map (body.realEval environment)| ≤ outputRadius) :
      ExactRangeCertificate environment (.unary map body) outputRadius
  | weaken {expression : ScalarExpr Variable} {radius largerRadius : ℝ}
      (certificate : ExactRangeCertificate environment expression radius)
      (radius_le : radius ≤ largerRadius) :
      ExactRangeCertificate environment expression largerRadius

namespace ExactRangeCertificate

theorem radius_nonneg {Variable : Type u} {environment : Variable → ℝ}
    {expression : ScalarExpr Variable} {radius : ℝ}
    (certificate : ExactRangeCertificate environment expression radius) :
    0 ≤ radius := by
  induction certificate with
  | ofVariable _ _ hnonneg _ => exact hnonneg
  | constant _ _ hnonneg _ => exact hnonneg
  | add leftCertificate rightCertificate leftIH rightIH =>
      exact add_nonneg leftIH rightIH
  | multiply leftCertificate rightCertificate leftIH rightIH =>
      exact mul_nonneg leftIH rightIH
  | mask active bodyCertificate bodyIH =>
      exact mul_nonneg (by cases active <;> norm_num [boolScalar]) bodyIH
  | unary _ bodyCertificate hnonneg _ bodyIH => exact hnonneg
  | weaken certificate radius_le ih => exact ih.trans radius_le

/-- Kernel-checked range soundness. -/
theorem sound {Variable : Type u} {environment : Variable → ℝ}
    {expression : ScalarExpr Variable} {radius : ℝ}
    (certificate : ExactRangeCertificate environment expression radius) :
    |expression.realEval environment| ≤ radius := by
  induction certificate with
  | ofVariable _ _ _ hvalue => exact hvalue
  | constant _ _ _ hvalue => exact hvalue
  | add leftCertificate rightCertificate leftIH rightIH =>
      rw [ScalarExpr.realEval]
      exact (abs_add_le _ _).trans (add_le_add leftIH rightIH)
  | multiply leftCertificate rightCertificate leftIH rightIH =>
      rw [ScalarExpr.realEval, abs_mul]
      exact mul_le_mul leftIH rightIH (abs_nonneg _)
        (ExactRangeCertificate.radius_nonneg leftCertificate)
  | mask active bodyCertificate bodyIH =>
      cases active with
      | false => simp [ScalarExpr.realEval, boolScalar]
      | true =>
          simp only [ScalarExpr.realEval, boolScalar, one_mul]
          exact bodyIH
  | unary _ _ _ hvalue _ => exact hvalue
  | weaken _ radius_le ih => exact ih.trans radius_le

end ExactRangeCertificate

/-- A proof-carrying runtime error bound.  Each constructor records the local
runtime operation error and computes a global bound from its children.

For multiplication, if the left and right child errors are `eL` and `eR` and
the exact absolute ranges are `rL` and `rR`, the transported nonlocal error is

`eL * (rR + eR) + rL * eR`.

The `eL * eR` contribution is therefore retained. -/
inductive EvaluationErrorCertificate {Variable : Type u}
    (environment : Variable → ℝ) :
    (expression : ScalarExpr Variable) →
    (runtimeValue errorRadius : ℝ) → Prop where
  | ofVariable (name : Variable) (runtimeValue errorRadius : ℝ)
      (errorRadius_nonneg : 0 ≤ errorRadius)
      (error_le : |runtimeValue - environment name| ≤ errorRadius) :
      EvaluationErrorCertificate environment (.variable name)
        runtimeValue errorRadius
  | constant (value runtimeValue errorRadius : ℝ)
      (errorRadius_nonneg : 0 ≤ errorRadius)
      (error_le : |runtimeValue - value| ≤ errorRadius) :
      EvaluationErrorCertificate environment (.constant value)
        runtimeValue errorRadius
  | add {left right : ScalarExpr Variable}
      {leftRuntime rightRuntime leftError rightError : ℝ}
      (leftCertificate : EvaluationErrorCertificate environment left
        leftRuntime leftError)
      (rightCertificate : EvaluationErrorCertificate environment right
        rightRuntime rightError)
      (runtimeValue localError : ℝ)
      (localError_nonneg : 0 ≤ localError)
      (localError_le : |runtimeValue - (leftRuntime + rightRuntime)| ≤ localError) :
      EvaluationErrorCertificate environment (.add left right) runtimeValue
        (localError + leftError + rightError)
  | multiply {left right : ScalarExpr Variable}
      {leftRuntime rightRuntime leftError rightError : ℝ}
      {leftRadius rightRadius : ℝ}
      (leftCertificate : EvaluationErrorCertificate environment left
        leftRuntime leftError)
      (rightCertificate : EvaluationErrorCertificate environment right
        rightRuntime rightError)
      (leftRange : ExactRangeCertificate environment left leftRadius)
      (rightRange : ExactRangeCertificate environment right rightRadius)
      (runtimeValue localError : ℝ)
      (localError_nonneg : 0 ≤ localError)
      (localError_le : |runtimeValue - leftRuntime * rightRuntime| ≤ localError) :
      EvaluationErrorCertificate environment (.multiply left right) runtimeValue
        (localError + leftError * (rightRadius + rightError) +
          leftRadius * rightError)
  | mask {body : ScalarExpr Variable} {bodyRuntime bodyError : ℝ}
      (active : Bool)
      (bodyCertificate : EvaluationErrorCertificate environment body
        bodyRuntime bodyError)
      (runtimeValue localError : ℝ)
      (localError_nonneg : 0 ≤ localError)
      (localError_le :
        |runtimeValue - boolScalar active * bodyRuntime| ≤ localError) :
      EvaluationErrorCertificate environment (.mask active body) runtimeValue
        (localError + boolScalar active * bodyError)
  | unary {body : ScalarExpr Variable} (map : ℝ → ℝ)
      {bodyRuntime bodyError : ℝ}
      (bodyCertificate : EvaluationErrorCertificate environment body
        bodyRuntime bodyError)
      (runtimeValue rate localError : ℝ)
      (rate_nonneg : 0 ≤ rate)
      (localError_nonneg : 0 ≤ localError)
      (localError_le : |runtimeValue - map bodyRuntime| ≤ localError)
      (pairRate_le :
        |map bodyRuntime - map (body.realEval environment)| ≤
          rate * |bodyRuntime - body.realEval environment|) :
      EvaluationErrorCertificate environment (.unary map body) runtimeValue
        (localError + rate * bodyError)
  | weaken {expression : ScalarExpr Variable}
      {runtimeValue errorRadius largerRadius : ℝ}
      (certificate : EvaluationErrorCertificate environment expression
        runtimeValue errorRadius)
      (radius_le : errorRadius ≤ largerRadius) :
      EvaluationErrorCertificate environment expression runtimeValue largerRadius

namespace EvaluationErrorCertificate

theorem errorRadius_nonneg {Variable : Type u} {environment : Variable → ℝ}
    {expression : ScalarExpr Variable} {runtimeValue errorRadius : ℝ}
    (certificate : EvaluationErrorCertificate environment expression
      runtimeValue errorRadius) :
    0 ≤ errorRadius := by
  induction certificate with
  | ofVariable _ _ _ hnonneg _ => exact hnonneg
  | constant _ _ _ hnonneg _ => exact hnonneg
  | add leftCertificate rightCertificate _ _ hlocal _ leftIH rightIH =>
      exact add_nonneg (add_nonneg hlocal leftIH) rightIH
  | multiply leftCertificate rightCertificate leftRange rightRange _ _ hlocal _
      leftIH rightIH =>
      exact add_nonneg
        (add_nonneg hlocal
          (mul_nonneg leftIH
            (add_nonneg
              (ExactRangeCertificate.radius_nonneg rightRange) rightIH)))
        (mul_nonneg (ExactRangeCertificate.radius_nonneg leftRange) rightIH)
  | mask active bodyCertificate _ _ hlocal _ bodyIH =>
      exact add_nonneg hlocal
        (mul_nonneg (by cases active <;> norm_num [boolScalar]) bodyIH)
  | unary _ bodyCertificate _ _ _ hrate hlocal _ _ bodyIH =>
      exact add_nonneg hlocal (mul_nonneg hrate bodyIH)
  | weaken certificate radius_le ih => exact ih.trans radius_le

/-- Local addition error plus both operand errors bounds the exact-real result. -/
theorem add_error_le
    (leftExact rightExact leftRuntime rightRuntime runtimeValue : ℝ)
    (leftError rightError localError : ℝ)
    (hlocal : |runtimeValue - (leftRuntime + rightRuntime)| ≤ localError)
    (hleft : |leftRuntime - leftExact| ≤ leftError)
    (hright : |rightRuntime - rightExact| ≤ rightError) :
    |runtimeValue - (leftExact + rightExact)| ≤
      localError + leftError + rightError := by
  calc
    |runtimeValue - (leftExact + rightExact)| =
        |(runtimeValue - (leftRuntime + rightRuntime)) +
          (leftRuntime - leftExact) + (rightRuntime - rightExact)| := by
          congr 1
          ring
    _ ≤ |runtimeValue - (leftRuntime + rightRuntime)| +
          |leftRuntime - leftExact| + |rightRuntime - rightExact| :=
        abs_add_three _ _ _
    _ ≤ localError + leftError + rightError :=
      add_le_add (add_le_add hlocal hleft) hright

/-- Multiplication transports operand errors with exact operand ranges and
retains their cross-error term. -/
theorem multiply_error_le
    (leftExact rightExact leftRuntime rightRuntime runtimeValue : ℝ)
    (leftError rightError leftRadius rightRadius localError : ℝ)
    (hleftError_nonneg : 0 ≤ leftError)
    (hleftRadius_nonneg : 0 ≤ leftRadius)
    (hlocal : |runtimeValue - leftRuntime * rightRuntime| ≤ localError)
    (hleft : |leftRuntime - leftExact| ≤ leftError)
    (hright : |rightRuntime - rightExact| ≤ rightError)
    (hleftRange : |leftExact| ≤ leftRadius)
    (hrightRange : |rightExact| ≤ rightRadius) :
    |runtimeValue - leftExact * rightExact| ≤
      localError + leftError * (rightRadius + rightError) +
        leftRadius * rightError := by
  have hrightRuntime : |rightRuntime| ≤ rightRadius + rightError := by
    calc
      |rightRuntime| = |(rightRuntime - rightExact) + rightExact| := by
        congr 1
        ring
      _ ≤ |rightRuntime - rightExact| + |rightExact| := abs_add_le _ _
      _ ≤ rightError + rightRadius := add_le_add hright hrightRange
      _ = rightRadius + rightError := add_comm _ _
  have hleftProduct :
      |(leftRuntime - leftExact) * rightRuntime| ≤
        leftError * (rightRadius + rightError) := by
    rw [abs_mul]
    exact mul_le_mul hleft hrightRuntime (abs_nonneg _) hleftError_nonneg
  have hrightProduct :
      |leftExact * (rightRuntime - rightExact)| ≤
        leftRadius * rightError := by
    rw [abs_mul]
    exact mul_le_mul hleftRange hright (abs_nonneg _) hleftRadius_nonneg
  calc
    |runtimeValue - leftExact * rightExact| =
        |(runtimeValue - leftRuntime * rightRuntime) +
          (leftRuntime - leftExact) * rightRuntime +
          leftExact * (rightRuntime - rightExact)| := by
          congr 1
          ring
    _ ≤ |runtimeValue - leftRuntime * rightRuntime| +
          |(leftRuntime - leftExact) * rightRuntime| +
          |leftExact * (rightRuntime - rightExact)| := abs_add_three _ _ _
    _ ≤ localError + leftError * (rightRadius + rightError) +
          leftRadius * rightError :=
      add_le_add (add_le_add hlocal hleftProduct) hrightProduct

/-- A Boolean mask transports at most its selected child error. -/
theorem mask_error_le
    (active : Bool) (exact runtime runtimeValue errorRadius localError : ℝ)
    (hlocal : |runtimeValue - boolScalar active * runtime| ≤ localError)
    (hbody : |runtime - exact| ≤ errorRadius) :
    |runtimeValue - boolScalar active * exact| ≤
      localError + boolScalar active * errorRadius := by
  calc
    |runtimeValue - boolScalar active * exact| =
        |(runtimeValue - boolScalar active * runtime) +
          boolScalar active * (runtime - exact)| := by
          congr 1
          ring
    _ ≤ |runtimeValue - boolScalar active * runtime| +
          |boolScalar active * (runtime - exact)| := abs_add_le _ _
    _ = |runtimeValue - boolScalar active * runtime| +
          |boolScalar active| * |runtime - exact| := by rw [abs_mul]
    _ ≤ localError + boolScalar active * errorRadius := by
      cases active with
      | false => simpa [boolScalar] using hlocal
      | true => simpa [boolScalar] using add_le_add hlocal hbody

/-- Local nonlinear evaluation error and a checked pairwise rate transport the
child error. -/
theorem unary_error_le
    (map : ℝ → ℝ) (exact runtime runtimeValue rate errorRadius localError : ℝ)
    (hrate : 0 ≤ rate)
    (hlocalError_nonneg : 0 ≤ localError)
    (hlocal : |runtimeValue - map runtime| ≤ localError)
    (hpair : |map runtime - map exact| ≤ rate * |runtime - exact|)
    (hbody : |runtime - exact| ≤ errorRadius) :
    |runtimeValue - map exact| ≤ localError + rate * errorRadius := by
  have hlocalCertificate : LocalEvaluationErrorCertificate map
      runtime runtimeValue localError := by
    exact
      { localError_nonneg := hlocalError_nonneg
        output_error_le := by simpa [Real.norm_eq_abs] using hlocal }
  simpa [Real.norm_eq_abs, propagatedEvaluationError] using
    outputMismatch_le_propagatedEvaluationError map exact runtime runtimeValue
      rate localError errorRadius hrate hlocalCertificate
      (by simpa [Real.norm_eq_abs] using hpair)
      (by simpa [Real.norm_eq_abs] using hbody)

/-- Kernel-checked global evaluation-error soundness. -/
theorem sound {Variable : Type u} {environment : Variable → ℝ}
    {expression : ScalarExpr Variable} {runtimeValue errorRadius : ℝ}
    (certificate : EvaluationErrorCertificate environment expression
      runtimeValue errorRadius) :
    |runtimeValue - expression.realEval environment| ≤ errorRadius := by
  induction certificate with
  | ofVariable _ _ _ _ herror => exact herror
  | constant _ _ _ _ herror => exact herror
  | add leftCertificate rightCertificate runtimeValue localError _ hlocal
      leftIH rightIH =>
      rw [ScalarExpr.realEval]
      exact add_error_le _ _ _ _ runtimeValue _ _ localError
        hlocal leftIH rightIH
  | multiply leftCertificate rightCertificate leftRange rightRange
      runtimeValue localError _ hlocal leftIH rightIH =>
      rw [ScalarExpr.realEval]
      exact multiply_error_le _ _ _ _ runtimeValue _ _ _ _ localError
        leftCertificate.errorRadius_nonneg
        (ExactRangeCertificate.radius_nonneg leftRange)
        hlocal leftIH rightIH leftRange.sound rightRange.sound
  | mask active bodyCertificate runtimeValue localError _ hlocal bodyIH =>
      rw [ScalarExpr.realEval]
      exact mask_error_le active _ _ runtimeValue _ localError hlocal bodyIH
  | unary map bodyCertificate runtimeValue rate localError hrate hlocalNonneg
      hlocal hpair bodyIH =>
      rw [ScalarExpr.realEval]
      exact unary_error_le map _ _ runtimeValue rate _ localError hrate
        hlocalNonneg hlocal hpair bodyIH
  | weaken _ radius_le ih => exact ih.trans radius_le

end EvaluationErrorCertificate

/-! ## Positive and negative fixtures -/

private abbrev OneVariable := Fin 1

private def exactEnvironment : OneVariable → ℝ := fun _ => 2

private def inputExpr : ScalarExpr OneVariable := .variable 0

private def squarePlusOne : ScalarExpr OneVariable :=
  .add (.multiply inputExpr inputExpr) (.constant 1)

private def inputRange : ExactRangeCertificate exactEnvironment inputExpr 2 :=
  .ofVariable 0 2 (by norm_num) (by norm_num [exactEnvironment])

private def inputError : EvaluationErrorCertificate exactEnvironment inputExpr
    (21 / 10 : ℝ) (1 / 10 : ℝ) :=
  .ofVariable 0 (21 / 10) (1 / 10) (by norm_num)
    (by norm_num [exactEnvironment])

private def squareError : EvaluationErrorCertificate exactEnvironment
    (.multiply inputExpr inputExpr) (441 / 100 : ℝ) (41 / 100 : ℝ) := by
  convert EvaluationErrorCertificate.multiply inputError inputError
    inputRange inputRange (441 / 100) 0 (by norm_num) (by norm_num) using 1;
    norm_num

private def squarePlusOneError : EvaluationErrorCertificate exactEnvironment
    squarePlusOne (541 / 100 : ℝ) (41 / 100 : ℝ) := by
  have hone : EvaluationErrorCertificate exactEnvironment (.constant 1)
      1 0 := .constant 1 1 0 (by norm_num) (by norm_num)
  convert EvaluationErrorCertificate.add squareError hone
    (541 / 100) 0 (by norm_num) (by norm_num) using 1 <;>
    norm_num [squarePlusOne]

/-- The multiplication certificate retains the exact cross-error and is tight
on this rational fixture. -/
theorem squarePlusOne_runtime_error_is_certified :
    |(541 / 100 : ℝ) - squarePlusOne.realEval exactEnvironment| ≤ 41 / 100 := by
  exact squarePlusOneError.sound

/-- A false mask suppresses an inherited input error when mask evaluation
itself is exact. -/
theorem false_mask_suppresses_input_error :
    EvaluationErrorCertificate exactEnvironment (.mask false inputExpr) 0 0 := by
  convert EvaluationErrorCertificate.mask false inputError 0 0
    (by norm_num) (by norm_num [boolScalar]) using 1;
    norm_num [boolScalar]

private def squareMap (value : ℝ) : ℝ := value ^ 2

/-- Unary nonlinear nodes are admitted only with an explicit pairwise-rate and
local-evaluation certificate. -/
theorem nonlinear_square_node_certified :
    EvaluationErrorCertificate exactEnvironment (.unary squareMap inputExpr)
      (441 / 100 : ℝ) (41 / 100 : ℝ) := by
  convert EvaluationErrorCertificate.unary squareMap inputError
    (441 / 100) (41 / 10) 0 (by norm_num) (by norm_num)
      (by norm_num [squareMap])
      (by norm_num [squareMap, inputExpr, ScalarExpr.realEval,
        exactEnvironment]) using 1;
    norm_num

/-- No proof-carrying certificate can assign zero global error to the rounded
square fixture. -/
theorem zero_error_corrupt_certificate_rejected :
    ¬ EvaluationErrorCertificate exactEnvironment
      (.multiply inputExpr inputExpr) (441 / 100 : ℝ) 0 := by
  intro certificate
  have hsound := certificate.sound
  norm_num [ScalarExpr.realEval, inputExpr, exactEnvironment] at hsound

private def tenTimesInput : ScalarExpr OneVariable :=
  .multiply (.constant 10) inputExpr

private def zeroEnvironment : OneVariable → ℝ := fun _ => 0

/-- Multiplication may amplify a child error by an operand range; merely
copying the child radius is unsound. -/
theorem multiplication_range_factor_cannot_be_dropped :
    ¬ EvaluationErrorCertificate zeroEnvironment tenTimesInput 10 1 := by
  intro certificate
  have hsound := certificate.sound
  norm_num [tenTimesInput, inputExpr, ScalarExpr.realEval, zeroEnvironment] at hsound

#print axioms ExactRangeCertificate.sound
#print axioms EvaluationErrorCertificate.sound
#print axioms zero_error_corrupt_certificate_rejected
#print axioms multiplication_range_factor_cannot_be_dropped

end

end FinitePrecisionExpressionCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
