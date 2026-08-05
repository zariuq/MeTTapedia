import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionExpressionCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SiLUTransitionBounds

/-!
# Registered nonlinear expression certificates

The generic expression theorem accepts an arbitrary real unary map together
with an explicit pairwise-rate proof.  This file supplies the finite public
vocabulary used by source-bound certificates.  A registered opcode has exact
real semantics, a regional output range, and a regional pairwise rate.  The
only accepted nonlinear opcodes are square, sigmoid, and SiLU.

This layer does not certify floating-point evaluation of any opcode.  Its
constructor still requires a local runtime-evaluation error.  It controls the
exact operation and the transport of already-certified input error.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RegisteredUnaryExpressionCertificate

open Set
open FinitePrecisionExpressionCertificate
open SiLUTransitionBounds

noncomputable section

universe u

/-- Finite vocabulary of unary operations admitted by source-bound scalar
expression certificates. -/
inductive RegisteredUnaryOp where
  | square
  | sigmoid
  | silu
  deriving DecidableEq, Repr

/-- Exact real semantics of a registered unary opcode. -/
def RegisteredUnaryOp.realMap : RegisteredUnaryOp → ℝ → ℝ
  | .square => fun value => value ^ 2
  | .sigmoid => Real.sigmoid
  | .silu => sourceSiLU

/-- Conservative output radius on the symmetric input interval
`[-radius, radius]`. -/
def RegisteredUnaryOp.outputRadius : RegisteredUnaryOp → ℝ → ℝ
  | .square, radius => radius ^ 2
  | .sigmoid, _ => 1
  | .silu, radius => radius

/-- Pairwise transport rate on the symmetric input interval
`[-radius, radius]`. -/
def RegisteredUnaryOp.pairRate : RegisteredUnaryOp → ℝ → ℝ
  | .square, radius => 2 * radius
  | .sigmoid, _ => 1 / 4
  | .silu, radius => 1 + radius / 4

theorem RegisteredUnaryOp.outputRadius_nonneg
    (operation : RegisteredUnaryOp) {radius : ℝ} (hradius : 0 ≤ radius) :
    0 ≤ operation.outputRadius radius := by
  cases operation <;> simp [RegisteredUnaryOp.outputRadius, hradius]

theorem RegisteredUnaryOp.pairRate_nonneg
    (operation : RegisteredUnaryOp) {radius : ℝ} (hradius : 0 ≤ radius) :
    0 ≤ operation.pairRate radius := by
  cases operation <;> simp [RegisteredUnaryOp.pairRate] <;> positivity

private theorem sigmoidDerivative_le_quarter (value : ℝ) :
    Real.sigmoid value * (1 - Real.sigmoid value) ≤ (1 / 4 : ℝ) := by
  nlinarith [sq_nonneg (Real.sigmoid value - (1 / 2 : ℝ))]

private theorem scalarRegion_mem_Icc
    {radius value : ℝ} (hvalue : |value| ≤ radius) :
    value ∈ Icc (-radius) radius := by
  simpa [abs_le] using hvalue

/-- The registered rate controls the exact output difference whenever both
arguments lie in the declared symmetric region. -/
theorem RegisteredUnaryOp.pair_bound
    (operation : RegisteredUnaryOp) {radius left right : ℝ}
    (hradius : 0 ≤ radius) (hleft : |left| ≤ radius)
    (hright : |right| ≤ radius) :
    |operation.realMap left - operation.realMap right| ≤
      operation.pairRate radius * |left - right| := by
  cases operation with
  | square =>
      have hsum : |left + right| ≤ 2 * radius := by
        calc
          |left + right| ≤ |left| + |right| := abs_add_le _ _
          _ ≤ radius + radius := add_le_add hleft hright
          _ = 2 * radius := by ring
      calc
        |RegisteredUnaryOp.square.realMap left -
            RegisteredUnaryOp.square.realMap right| =
            |left - right| * |left + right| := by
              rw [RegisteredUnaryOp.realMap, show left ^ 2 - right ^ 2 =
                (left - right) * (left + right) by ring, abs_mul]
        _ ≤ |left - right| * (2 * radius) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        _ = RegisteredUnaryOp.square.pairRate radius * |left - right| := by
          simp [RegisteredUnaryOp.pairRate]
          ring
  | sigmoid =>
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        (f := Real.sigmoid) (s := Icc (-radius) radius)
        (x := right) (y := left) (C := (1 / 4 : ℝ))
        (fun value _ => (Real.hasDerivAt_sigmoid value).differentiableAt)
        (fun value _ => by
          rw [(Real.hasDerivAt_sigmoid value).deriv, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (Real.sigmoid_nonneg value)
              (sub_nonneg.mpr (Real.sigmoid_le_one value)))]
          exact sigmoidDerivative_le_quarter value)
        (convex_Icc _ _) (scalarRegion_mem_Icc hright)
        (scalarRegion_mem_Icc hleft)
      simpa [RegisteredUnaryOp.realMap, RegisteredUnaryOp.pairRate,
        Real.norm_eq_abs] using h
  | silu =>
      have h := (sourceSiLUBudget radius hradius).map_pair_bound
        left right hleft hright
      simpa [RegisteredUnaryOp.realMap, RegisteredUnaryOp.pairRate,
        Real.norm_eq_abs] using h

/-- The registered output radius controls the exact output whenever the input
lies in the declared symmetric region. -/
theorem RegisteredUnaryOp.output_bound
    (operation : RegisteredUnaryOp) {radius value : ℝ}
    (hradius : 0 ≤ radius) (hvalue : |value| ≤ radius) :
    |operation.realMap value| ≤ operation.outputRadius radius := by
  cases operation with
  | square =>
      rw [RegisteredUnaryOp.realMap, RegisteredUnaryOp.outputRadius,
        abs_sq]
      calc
        value ^ 2 = |value| ^ 2 := by rw [sq_abs]
        _ ≤ radius ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hvalue 2
  | sigmoid =>
      rw [RegisteredUnaryOp.realMap, RegisteredUnaryOp.outputRadius,
        abs_of_nonneg (Real.sigmoid_nonneg value)]
      exact Real.sigmoid_le_one value
  | silu =>
      calc
        |RegisteredUnaryOp.silu.realMap value| =
            |value| * |Real.sigmoid value| := by
              rw [RegisteredUnaryOp.realMap, sourceSiLU, abs_mul]
        _ ≤ radius * 1 := by
          apply mul_le_mul hvalue
          · rw [abs_of_nonneg (Real.sigmoid_nonneg value)]
            exact Real.sigmoid_le_one value
          · exact abs_nonneg _
          · exact hradius
        _ = RegisteredUnaryOp.silu.outputRadius radius := by
          simp [RegisteredUnaryOp.outputRadius]

/-- Scalar expression syntax whose unary nodes cannot contain an arbitrary
host-language function. -/
inductive RegisteredExpr (Variable : Type u) where
  | var (name : Variable)
  | constant (value : ℝ)
  | add (left right : RegisteredExpr Variable)
  | multiply (left right : RegisteredExpr Variable)
  | mask (active : Bool) (body : RegisteredExpr Variable)
  | unary (operation : RegisteredUnaryOp) (body : RegisteredExpr Variable)

/-- Compiler from the finite registered syntax to the generic theorem layer. -/
def RegisteredExpr.toScalarExpr {Variable : Type u} :
    RegisteredExpr Variable → ScalarExpr Variable
  | .var name => .variable name
  | .constant value => .constant value
  | .add left right => .add left.toScalarExpr right.toScalarExpr
  | .multiply left right => .multiply left.toScalarExpr right.toScalarExpr
  | .mask active body => .mask active body.toScalarExpr
  | .unary operation body => .unary operation.realMap body.toScalarExpr

/-- Exact semantics of registered expressions. -/
def RegisteredExpr.realEval {Variable : Type u}
    (environment : Variable → ℝ) : RegisteredExpr Variable → ℝ
  | .var name => environment name
  | .constant value => value
  | .add left right => left.realEval environment + right.realEval environment
  | .multiply left right =>
      left.realEval environment * right.realEval environment
  | .mask active body => boolScalar active * body.realEval environment
  | .unary operation body => operation.realMap (body.realEval environment)

@[simp] theorem RegisteredExpr.toScalarExpr_realEval
    {Variable : Type u} (environment : Variable → ℝ)
    (expression : RegisteredExpr Variable) :
    expression.toScalarExpr.realEval environment = expression.realEval environment := by
  induction expression with
  | var => rfl
  | constant => rfl
  | add left right leftIH rightIH => simp [RegisteredExpr.toScalarExpr,
      ScalarExpr.realEval, RegisteredExpr.realEval, leftIH, rightIH]
  | multiply left right leftIH rightIH => simp [RegisteredExpr.toScalarExpr,
      ScalarExpr.realEval, RegisteredExpr.realEval, leftIH, rightIH]
  | mask active body bodyIH => simp [RegisteredExpr.toScalarExpr,
      ScalarExpr.realEval, RegisteredExpr.realEval, bodyIH]
  | unary operation body bodyIH => simp [RegisteredExpr.toScalarExpr,
      ScalarExpr.realEval, RegisteredExpr.realEval, bodyIH]

/-- Construct the exact-range certificate of a registered unary node. -/
def registeredUnaryRange
    {Variable : Type u} {environment : Variable → ℝ}
    (operation : RegisteredUnaryOp) {body : ScalarExpr Variable}
    {radius : ℝ} (bodyCertificate :
      ExactRangeCertificate environment body radius) :
    ExactRangeCertificate environment (.unary operation.realMap body)
      (operation.outputRadius radius) :=
  .unary operation.realMap bodyCertificate
    (operation.outputRadius_nonneg bodyCertificate.radius_nonneg)
    (operation.output_bound bodyCertificate.radius_nonneg bodyCertificate.sound)

/-- Construct the runtime-error certificate of a registered unary node.
The local floating-point bound is deliberately supplied separately. -/
def registeredUnaryError
    {Variable : Type u} {environment : Variable → ℝ}
    (operation : RegisteredUnaryOp) {body : ScalarExpr Variable}
    {bodyRuntime bodyError radius runtimeValue localError : ℝ}
    (bodyCertificate : EvaluationErrorCertificate environment body
      bodyRuntime bodyError)
    (bodyRange : ExactRangeCertificate environment body radius)
    (hruntime : |bodyRuntime| ≤ radius)
    (runtimeError_nonneg : 0 ≤ localError)
    (runtimeError_le :
      |runtimeValue - operation.realMap bodyRuntime| ≤ localError) :
    EvaluationErrorCertificate environment (.unary operation.realMap body)
      runtimeValue (localError + operation.pairRate radius * bodyError) :=
  .unary operation.realMap bodyCertificate runtimeValue
    (operation.pairRate radius) localError
    (operation.pairRate_nonneg bodyRange.radius_nonneg)
    runtimeError_nonneg runtimeError_le
    (operation.pair_bound bodyRange.radius_nonneg hruntime bodyRange.sound)

/-! ## Positive and negative fixtures -/

private abbrev OneVariable := Fin 1

private def exactEnvironment : OneVariable → ℝ := fun _ => 1

private def input : ScalarExpr OneVariable := .variable 0

private def inputRange : ExactRangeCertificate exactEnvironment input 2 :=
  .ofVariable 0 2 (by norm_num) (by norm_num [exactEnvironment])

private def inputError : EvaluationErrorCertificate exactEnvironment input 2 1 :=
  .ofVariable 0 2 1 (by norm_num) (by norm_num [exactEnvironment])

/-- The registered square node reconstructs the sharp four-unit regional
transport rate rather than accepting an arbitrary function certificate. -/
theorem registered_square :
    EvaluationErrorCertificate exactEnvironment
      (.unary RegisteredUnaryOp.square.realMap input) 4 4 := by
  convert registeredUnaryError (runtimeValue := 4) (localError := 0)
      RegisteredUnaryOp.square inputError inputRange
      (by norm_num) (by norm_num) (by norm_num [RegisteredUnaryOp.realMap]) using 1;
    norm_num [RegisteredUnaryOp.pairRate]

/-- A unit rate is insufficient for square between one and two. -/
theorem square_unit_rate_rejected :
    ¬ |RegisteredUnaryOp.square.realMap 2 -
        RegisteredUnaryOp.square.realMap 1| ≤
      (1 : ℝ) * |2 - 1| := by
  norm_num [RegisteredUnaryOp.realMap]

#print axioms RegisteredUnaryOp.pair_bound
#print axioms RegisteredUnaryOp.output_bound
#print axioms RegisteredExpr.toScalarExpr_realEval
#print axioms registered_square
#print axioms square_unit_rate_rejected

end

end RegisteredUnaryExpressionCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
