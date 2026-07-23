import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegisteredUnaryExpressionCertificate

/-!
# Decidable rational expression-certificate checker

This file provides a finite wire representation and an executable checker for
the algebraic subset of scalar finite-precision certificates.  Every numeric
field is rational.  The checker recursively validates exact ranges, local
runtime errors, transported child errors, and claimed global errors for
variables, constants, addition, multiplication, and Boolean masks.

Registered unary opcodes are part of the wire syntax but are rejected.  Their
exact real rates are proved separately, while validating their floating-point
evaluation requires a source-bound transcendental enclosure.  Consequently a
producer cannot obtain a global theorem merely by naming SiLU or sigmoid.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RationalExpressionCertificateChecker

open FinitePrecisionExpressionCertificate
open RegisteredUnaryExpressionCertificate

universe u

/-- Rational scalar used by Boolean mask evaluation. -/
def boolRational : Bool → ℚ
  | false => 0
  | true => 1

/-- Finite certificate wire format.  Each constructor records the claimed
exact range and global runtime error at that node.  Arithmetic nodes also
record the local error of the runtime operation. -/
inductive WireCertificate (Variable : Type u) where
  | var (name : Variable) (runtimeValue exactRadius errorRadius : ℚ)
  | constant (exactValue runtimeValue exactRadius errorRadius : ℚ)
  | add (left right : WireCertificate Variable)
      (runtimeValue exactRadius localError errorRadius : ℚ)
  | multiply (left right : WireCertificate Variable)
      (runtimeValue exactRadius localError errorRadius : ℚ)
  | mask (active : Bool) (body : WireCertificate Variable)
      (runtimeValue exactRadius localError errorRadius : ℚ)
  | unary (operation : RegisteredUnaryOp) (body : WireCertificate Variable)
      (runtimeValue exactRadius localError errorRadius : ℚ)
  deriving Repr

/-- Runtime value carried by a wire record. -/
def WireCertificate.runtimeValue {Variable : Type u} :
    WireCertificate Variable → ℚ
  | .var _ runtimeValue _ _ => runtimeValue
  | .constant _ runtimeValue _ _ => runtimeValue
  | .add _ _ runtimeValue _ _ _ => runtimeValue
  | .multiply _ _ runtimeValue _ _ _ => runtimeValue
  | .mask _ _ runtimeValue _ _ _ => runtimeValue
  | .unary _ _ runtimeValue _ _ _ => runtimeValue

/-- Claimed exact absolute range carried by a wire record. -/
def WireCertificate.exactRadius {Variable : Type u} :
    WireCertificate Variable → ℚ
  | .var _ _ exactRadius _ => exactRadius
  | .constant _ _ exactRadius _ => exactRadius
  | .add _ _ _ exactRadius _ _ => exactRadius
  | .multiply _ _ _ exactRadius _ _ => exactRadius
  | .mask _ _ _ exactRadius _ _ => exactRadius
  | .unary _ _ _ exactRadius _ _ => exactRadius

/-- Claimed global runtime-error radius carried by a wire record. -/
def WireCertificate.errorRadius {Variable : Type u} :
    WireCertificate Variable → ℚ
  | .var _ _ _ errorRadius => errorRadius
  | .constant _ _ _ errorRadius => errorRadius
  | .add _ _ _ _ _ errorRadius => errorRadius
  | .multiply _ _ _ _ _ errorRadius => errorRadius
  | .mask _ _ _ _ _ errorRadius => errorRadius
  | .unary _ _ _ _ _ errorRadius => errorRadius

/-- Rational exact semantics of the algebraic wire subset.  The unary branch
is deliberately assigned no mathematical meaning here; validity makes that
branch impossible. -/
def WireCertificate.exactValue {Variable : Type u}
    (environment : Variable → ℚ) : WireCertificate Variable → ℚ
  | .var name _ _ _ => environment name
  | .constant exactValue _ _ _ => exactValue
  | .add left right _ _ _ _ =>
      left.exactValue environment + right.exactValue environment
  | .multiply left right _ _ _ _ =>
      left.exactValue environment * right.exactValue environment
  | .mask active body _ _ _ _ =>
      boolRational active * body.exactValue environment
  | .unary _ _ _ _ _ _ => 0

/-- Registered real expression named by the wire record. -/
def WireCertificate.expression {Variable : Type u} :
    WireCertificate Variable → RegisteredExpr Variable
  | .var name _ _ _ => .var name
  | .constant exactValue _ _ _ => .constant exactValue
  | .add left right _ _ _ _ => .add left.expression right.expression
  | .multiply left right _ _ _ _ =>
      .multiply left.expression right.expression
  | .mask active body _ _ _ _ => .mask active body.expression
  | .unary operation body _ _ _ _ => .unary operation body.expression

/-- Exact real environment induced by a rational wire environment. -/
def realEnvironment {Variable : Type u}
    (environment : Variable → ℚ) : Variable → ℝ :=
  fun name => environment name

/-- Propositional meaning of a valid wire certificate.  It mirrors the
Boolean checker below and is used only to state its soundness. -/
def WireCertificate.Valid {Variable : Type u}
    (environment : Variable → ℚ) : WireCertificate Variable → Prop
  | .var name runtimeValue exactRadius errorRadius =>
      0 ≤ exactRadius ∧ |environment name| ≤ exactRadius ∧
      0 ≤ errorRadius ∧ |runtimeValue - environment name| ≤ errorRadius
  | .constant exactValue runtimeValue exactRadius errorRadius =>
      0 ≤ exactRadius ∧ |exactValue| ≤ exactRadius ∧
      0 ≤ errorRadius ∧ |runtimeValue - exactValue| ≤ errorRadius
  | .add left right runtimeValue exactRadius localError errorRadius =>
      left.Valid environment ∧ right.Valid environment ∧
      (0 ≤ exactRadius ∧ left.exactRadius + right.exactRadius ≤ exactRadius ∧
       0 ≤ localError ∧
         |runtimeValue - (left.runtimeValue + right.runtimeValue)| ≤ localError ∧
       0 ≤ errorRadius ∧
         localError + left.errorRadius + right.errorRadius ≤ errorRadius)
  | .multiply left right runtimeValue exactRadius localError errorRadius =>
      left.Valid environment ∧ right.Valid environment ∧
      (0 ≤ exactRadius ∧ left.exactRadius * right.exactRadius ≤ exactRadius ∧
       0 ≤ localError ∧
         |runtimeValue - left.runtimeValue * right.runtimeValue| ≤ localError ∧
       0 ≤ errorRadius ∧
         localError + left.errorRadius *
            (right.exactRadius + right.errorRadius) +
            left.exactRadius * right.errorRadius ≤ errorRadius)
  | .mask active body runtimeValue exactRadius localError errorRadius =>
      body.Valid environment ∧
      (0 ≤ exactRadius ∧ boolRational active * body.exactRadius ≤ exactRadius ∧
       0 ≤ localError ∧
         |runtimeValue - boolRational active * body.runtimeValue| ≤ localError ∧
       0 ≤ errorRadius ∧
         localError + boolRational active * body.errorRadius ≤ errorRadius)
  | .unary _ _ _ _ _ _ => False

/-- Executable Boolean checker for the wire format. -/
def WireCertificate.check {Variable : Type u}
    (environment : Variable → ℚ) : WireCertificate Variable → Bool
  | .var name runtimeValue exactRadius errorRadius =>
      decide (0 ≤ exactRadius ∧ |environment name| ≤ exactRadius ∧
        0 ≤ errorRadius ∧ |runtimeValue - environment name| ≤ errorRadius)
  | .constant exactValue runtimeValue exactRadius errorRadius =>
      decide (0 ≤ exactRadius ∧ |exactValue| ≤ exactRadius ∧
        0 ≤ errorRadius ∧ |runtimeValue - exactValue| ≤ errorRadius)
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
          localError + left.errorRadius *
              (right.exactRadius + right.errorRadius) +
              left.exactRadius * right.errorRadius ≤ errorRadius))
  | .mask active body runtimeValue exactRadius localError errorRadius =>
      body.check environment &&
        decide (0 ≤ exactRadius ∧
          boolRational active * body.exactRadius ≤ exactRadius ∧
          0 ≤ localError ∧
          |runtimeValue - boolRational active * body.runtimeValue| ≤ localError ∧
          0 ≤ errorRadius ∧
          localError + boolRational active * body.errorRadius ≤ errorRadius)
  | .unary _ _ _ _ _ _ => false

theorem WireCertificate.check_eq_true_iff {Variable : Type u}
    (environment : Variable → ℚ) (certificate : WireCertificate Variable) :
    certificate.check environment = true ↔ certificate.Valid environment := by
  induction certificate with
  | var => simp [WireCertificate.check, WireCertificate.Valid]
  | constant => simp [WireCertificate.check, WireCertificate.Valid]
  | add left right _ _ _ _ leftIH rightIH =>
      simp [WireCertificate.check, WireCertificate.Valid, leftIH, rightIH]
  | multiply left right _ _ _ _ leftIH rightIH =>
      simp [WireCertificate.check, WireCertificate.Valid, leftIH, rightIH]
  | mask active body _ _ _ _ bodyIH =>
      simp [WireCertificate.check, WireCertificate.Valid, bodyIH]
  | unary => simp [WireCertificate.check, WireCertificate.Valid]

theorem WireCertificate.valid_exactRadius_nonneg {Variable : Type u}
    {environment : Variable → ℚ} {certificate : WireCertificate Variable}
    (hvalid : certificate.Valid environment) :
    0 ≤ certificate.exactRadius := by
  cases certificate <;> simp only [WireCertificate.Valid] at hvalid <;>
    simp only [WireCertificate.exactRadius] <;> aesop

theorem WireCertificate.valid_errorRadius_nonneg {Variable : Type u}
    {environment : Variable → ℚ} {certificate : WireCertificate Variable}
    (hvalid : certificate.Valid environment) :
    0 ≤ certificate.errorRadius := by
  cases certificate <;> simp only [WireCertificate.Valid] at hvalid <;>
    simp only [WireCertificate.errorRadius] <;> aesop

private theorem add_error_le_rat
    (leftExact rightExact leftRuntime rightRuntime runtimeValue : ℚ)
    (leftError rightError localError : ℚ)
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

private theorem multiply_error_le_rat
    (leftExact rightExact leftRuntime rightRuntime runtimeValue : ℚ)
    (leftError rightError leftRadius rightRadius localError : ℚ)
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
      |leftExact * (rightRuntime - rightExact)| ≤ leftRadius * rightError := by
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

private theorem mask_error_le_rat
    (active : Bool) (exact runtime runtimeValue errorRadius localError : ℚ)
    (hlocal : |runtimeValue - boolRational active * runtime| ≤ localError)
    (hbody : |runtime - exact| ≤ errorRadius) :
    |runtimeValue - boolRational active * exact| ≤
      localError + boolRational active * errorRadius := by
  cases active with
  | false => simpa [boolRational] using hlocal
  | true =>
      have hlocal' : |runtimeValue - runtime| ≤ localError := by
        simpa [boolRational] using hlocal
      simpa [boolRational] using
        add_error_le_rat exact 0 runtime 0 runtimeValue errorRadius 0 localError
          (by simpa using hlocal') hbody (by norm_num)

/-- Exact rational values lie inside every accepted wire range. -/
theorem WireCertificate.valid_exactRange {Variable : Type u}
    {environment : Variable → ℚ} (certificate : WireCertificate Variable)
    (hvalid : certificate.Valid environment) :
    |certificate.exactValue environment| ≤ certificate.exactRadius := by
  induction certificate with
  | var name runtimeValue exactRadius errorRadius =>
      exact hvalid.2.1
  | constant exactValue runtimeValue exactRadius errorRadius =>
      exact hvalid.2.1
  | add left right runtimeValue exactRadius localError errorRadius leftIH rightIH =>
      rcases hvalid with ⟨hleft, hright, _, hrange, _⟩
      calc
        |left.exactValue environment + right.exactValue environment| ≤
            |left.exactValue environment| + |right.exactValue environment| :=
          abs_add_le _ _
        _ ≤ left.exactRadius + right.exactRadius :=
          add_le_add (leftIH hleft) (rightIH hright)
        _ ≤ exactRadius := hrange
  | multiply left right runtimeValue exactRadius localError errorRadius
      leftIH rightIH =>
      rcases hvalid with ⟨hleft, hright, _, hrange, _⟩
      rw [WireCertificate.exactValue, abs_mul]
      exact (mul_le_mul (leftIH hleft) (rightIH hright) (abs_nonneg _)
        (left.valid_exactRadius_nonneg hleft)).trans hrange
  | mask active body runtimeValue exactRadius localError errorRadius bodyIH =>
      rcases hvalid with ⟨hbody, hnonneg, hrange, _⟩
      cases active with
      | false =>
          simpa [WireCertificate.exactValue, WireCertificate.exactRadius,
            boolRational] using hnonneg
      | true =>
          have hrange' : body.exactRadius ≤ exactRadius := by
            simpa [boolRational] using hrange
          simpa [WireCertificate.exactValue, WireCertificate.exactRadius,
            boolRational] using
            (bodyIH hbody).trans hrange'
  | unary operation body runtimeValue exactRadius localError errorRadius bodyIH =>
      exact False.elim hvalid

/-- Accepted wire errors bound the rational runtime/exact mismatch. -/
theorem WireCertificate.valid_error {Variable : Type u}
    {environment : Variable → ℚ} (certificate : WireCertificate Variable)
    (hvalid : certificate.Valid environment) :
    |certificate.runtimeValue - certificate.exactValue environment| ≤
      certificate.errorRadius := by
  induction certificate with
  | var name runtimeValue exactRadius errorRadius =>
      exact hvalid.2.2.2
  | constant exactValue runtimeValue exactRadius errorRadius =>
      exact hvalid.2.2.2
  | add left right runtimeValue exactRadius localError errorRadius leftIH rightIH =>
      rcases hvalid with
        ⟨hleft, hright, _, _, _, hlocal, _, hclaimed⟩
      exact (add_error_le_rat _ _ _ _ runtimeValue _ _ localError hlocal
        (leftIH hleft) (rightIH hright)).trans hclaimed
  | multiply left right runtimeValue exactRadius localError errorRadius
      leftIH rightIH =>
      rcases hvalid with
        ⟨hleft, hright, _, _, _, hlocal, _, hclaimed⟩
      exact (multiply_error_le_rat _ _ _ _ runtimeValue
        left.errorRadius right.errorRadius left.exactRadius right.exactRadius
        localError (left.valid_errorRadius_nonneg hleft)
        (left.valid_exactRadius_nonneg hleft) hlocal
        (leftIH hleft) (rightIH hright)
        (left.valid_exactRange hleft) (right.valid_exactRange hright)).trans
          hclaimed
  | mask active body runtimeValue exactRadius localError errorRadius bodyIH =>
      rcases hvalid with ⟨hbody, _, _, _, hlocal, _, hclaimed⟩
      exact (mask_error_le_rat active _ _ runtimeValue body.errorRadius
        localError hlocal (bodyIH hbody)).trans hclaimed
  | unary operation body runtimeValue exactRadius localError errorRadius bodyIH =>
      exact False.elim hvalid

/-- On accepted records, the registered real expression agrees with the
rational algebraic semantics embedded into the reals. -/
theorem WireCertificate.valid_realEval_eq {Variable : Type u}
    {environment : Variable → ℚ} (certificate : WireCertificate Variable)
    (hvalid : certificate.Valid environment) :
    certificate.expression.realEval (realEnvironment environment) =
      (certificate.exactValue environment : ℝ) := by
  induction certificate with
  | var => rfl
  | constant => rfl
  | add left right _ _ _ _ leftIH rightIH =>
      simp only [WireCertificate.expression, RegisteredExpr.realEval,
        WireCertificate.exactValue, Rat.cast_add]
      rw [leftIH hvalid.1, rightIH hvalid.2.1]
  | multiply left right _ _ _ _ leftIH rightIH =>
      simp only [WireCertificate.expression, RegisteredExpr.realEval,
        WireCertificate.exactValue, Rat.cast_mul]
      rw [leftIH hvalid.1, rightIH hvalid.2.1]
  | mask active body _ _ _ _ bodyIH =>
      rcases hvalid with ⟨hbody, _⟩
      cases active with
      | false =>
          simp [WireCertificate.expression, RegisteredExpr.realEval,
            WireCertificate.exactValue, boolScalar, boolRational]
      | true =>
          simpa [WireCertificate.expression, RegisteredExpr.realEval,
            WireCertificate.exactValue, boolScalar, boolRational] using
            bodyIH hbody
  | unary => exact False.elim hvalid

/-- Compile an accepted algebraic wire into the generic proof-carrying exact-
range language.  This bridge lets later certificate layers reuse the generic
unary and transition constructors without reproving the algebraic subtree. -/
theorem WireCertificate.valid_exactRangeCertificate {Variable : Type u}
    {environment : Variable → ℚ} (certificate : WireCertificate Variable)
    (hvalid : certificate.Valid environment) :
    ExactRangeCertificate (realEnvironment environment)
      certificate.expression.toScalarExpr (certificate.exactRadius : ℝ) := by
  induction certificate with
  | var name runtimeValue exactRadius errorRadius =>
      rcases hvalid with ⟨hradius, hvalue, _⟩
      exact .ofVariable name exactRadius
        (by exact_mod_cast hradius) (by
          simp only [realEnvironment]
          exact_mod_cast hvalue)
  | constant exactValue runtimeValue exactRadius errorRadius =>
      rcases hvalid with ⟨hradius, hvalue, _⟩
      exact .constant exactValue exactRadius
        (by exact_mod_cast hradius) (by exact_mod_cast hvalue)
  | add left right runtimeValue exactRadius localError errorRadius leftIH rightIH =>
      rcases hvalid with ⟨hleft, hright, _, hrange, _⟩
      exact .weaken (.add (leftIH hleft) (rightIH hright)) (by
        exact_mod_cast hrange)
  | multiply left right runtimeValue exactRadius localError errorRadius
      leftIH rightIH =>
      rcases hvalid with ⟨hleft, hright, _, hrange, _⟩
      exact .weaken (.multiply (leftIH hleft) (rightIH hright)) (by
        exact_mod_cast hrange)
  | mask active body runtimeValue exactRadius localError errorRadius bodyIH =>
      rcases hvalid with ⟨hbody, _, hrange, _⟩
      exact .weaken (.mask active (bodyIH hbody)) (by
        cases active <;> simp [boolRational, boolScalar] at hrange ⊢ <;>
          exact_mod_cast hrange)
  | unary => exact False.elim hvalid

/-- Compile an accepted algebraic wire into the generic proof-carrying
runtime-error language.  The resulting tree records the same local arithmetic
errors and the same global weakening that the Boolean checker replayed. -/
theorem WireCertificate.valid_evaluationErrorCertificate {Variable : Type u}
    {environment : Variable → ℚ} (certificate : WireCertificate Variable)
    (hvalid : certificate.Valid environment) :
    EvaluationErrorCertificate (realEnvironment environment)
      certificate.expression.toScalarExpr (certificate.runtimeValue : ℝ)
      (certificate.errorRadius : ℝ) := by
  induction certificate with
  | var name runtimeValue exactRadius errorRadius =>
      rcases hvalid with ⟨_, _, herror, hbound⟩
      exact .ofVariable name runtimeValue errorRadius
        (by exact_mod_cast herror) (by
          simp only [realEnvironment]
          exact_mod_cast hbound)
  | constant exactValue runtimeValue exactRadius errorRadius =>
      rcases hvalid with ⟨_, _, herror, hbound⟩
      exact .constant exactValue runtimeValue errorRadius
        (by exact_mod_cast herror) (by exact_mod_cast hbound)
  | add left right runtimeValue exactRadius localError errorRadius leftIH rightIH =>
      rcases hvalid with
        ⟨hleft, hright, _, _, hlocalNonneg, hlocal, _, hclaimed⟩
      exact .weaken
        (.add (leftIH hleft) (rightIH hright) runtimeValue localError
          (by exact_mod_cast hlocalNonneg) (by exact_mod_cast hlocal)) (by
            exact_mod_cast hclaimed)
  | multiply left right runtimeValue exactRadius localError errorRadius
      leftIH rightIH =>
      rcases hvalid with
        ⟨hleft, hright, _, _, hlocalNonneg, hlocal, _, hclaimed⟩
      exact .weaken
        (.multiply (leftIH hleft) (rightIH hright)
          (left.valid_exactRangeCertificate hleft)
          (right.valid_exactRangeCertificate hright)
          runtimeValue localError (by exact_mod_cast hlocalNonneg)
          (by exact_mod_cast hlocal)) (by exact_mod_cast hclaimed)
  | mask active body runtimeValue exactRadius localError errorRadius bodyIH =>
      rcases hvalid with
        ⟨hbody, _, _, hlocalNonneg, hlocal, _, hclaimed⟩
      exact .weaken
        (.mask active (bodyIH hbody) runtimeValue localError
          (by exact_mod_cast hlocalNonneg) (by
            cases active <;> simp [boolRational, boolScalar] at hlocal ⊢ <;>
              exact_mod_cast hlocal)) (by
                cases active <;>
                  simp [boolRational, boolScalar] at hclaimed ⊢ <;>
                  exact_mod_cast hclaimed)
  | unary => exact False.elim hvalid

/-- Kernel theorem exported by the executable checker. -/
theorem WireCertificate.check_sound {Variable : Type u}
    {environment : Variable → ℚ} (certificate : WireCertificate Variable)
    (hcheck : certificate.check environment = true) :
    |(certificate.runtimeValue : ℝ) -
        certificate.expression.realEval (realEnvironment environment)| ≤
      (certificate.errorRadius : ℝ) := by
  have hvalid := (certificate.check_eq_true_iff environment).mp hcheck
  have hq := certificate.valid_error hvalid
  have hr :
      |(certificate.runtimeValue : ℝ) -
          (certificate.exactValue environment : ℝ)| ≤
        (certificate.errorRadius : ℝ) := by
    exact_mod_cast hq
  rw [certificate.valid_realEval_eq hvalid]
  exact hr

/-! ## Positive and corrupt-record fixtures -/

private abbrev OneVariable := Fin 1

private def environment : OneVariable → ℚ := fun _ => 2

private def input : WireCertificate OneVariable :=
  .var 0 (21 / 10) 2 (1 / 10)

private def square : WireCertificate OneVariable :=
  .multiply input input (441 / 100) 4 0 (41 / 100)

private def squarePlusOne : WireCertificate OneVariable :=
  .add square (.constant 1 1 1 0) (541 / 100) 5 0 (41 / 100)

/-- A complete rational multiplication-and-addition record is accepted by
kernel reduction. -/
theorem squarePlusOne_is_accepted :
    squarePlusOne.check environment = true := by
  norm_num [squarePlusOne, square, input, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, environment]

/-- The accepted wire record yields a theorem about the compiled real
expression. -/
theorem squarePlusOne_real_error :
    |((541 / 100 : ℚ) : ℝ) -
        squarePlusOne.expression.realEval (realEnvironment environment)| ≤
      ((41 / 100 : ℚ) : ℝ) := by
  exact squarePlusOne.check_sound squarePlusOne_is_accepted

private def corruptGlobalError : WireCertificate OneVariable :=
  .add square (.constant 1 1 1 0) (541 / 100) 5 0 0

/-- Understating the composed global error is rejected. -/
theorem corrupt_global_error_is_rejected :
    corruptGlobalError.check environment = false := by
  norm_num [corruptGlobalError, square, input, WireCertificate.check,
    WireCertificate.runtimeValue, WireCertificate.exactRadius,
    WireCertificate.errorRadius, environment]

private def corruptInputRange : WireCertificate OneVariable :=
  .var 0 2 1 0

/-- A range claim smaller than the exact input magnitude is rejected. -/
theorem corrupt_input_range_is_rejected :
    corruptInputRange.check environment = false := by
  norm_num [corruptInputRange, WireCertificate.check, environment]

private def unsupportedSiLU : WireCertificate OneVariable :=
  .unary .silu input 0 0 0 0

/-- Naming a registered nonlinear operation is not a substitute for a
source-bound transcendental evaluation certificate. -/
theorem unsupported_silu_is_rejected :
    unsupportedSiLU.check environment = false := by
  rfl

#print axioms WireCertificate.check_eq_true_iff
#print axioms WireCertificate.valid_exactRange
#print axioms WireCertificate.valid_error
#print axioms WireCertificate.valid_exactRangeCertificate
#print axioms WireCertificate.valid_evaluationErrorCertificate
#print axioms WireCertificate.check_sound
#print axioms corrupt_global_error_is_rejected
#print axioms unsupported_silu_is_rejected

end RationalExpressionCertificateChecker

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
