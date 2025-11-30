/-
# MeTTa Implementation Verification

Formal verification of the MeTTa implementation of PLN formulas against the
mathematical derivations.

## The Implementation

We verify the code from `metta/pln/dependent-types/DeductionDTL.metta` and
`metta/common/formula/DeductionFormula.metta`.

MeTTa Formula:
`(+ (* $ABs $BCs) (/ (* (- 1 $ABs) (- $Cs (* $Bs $BCs))) (- 1 $Bs)))`

## The Specification

We prove this matches `plnDeductionStrength` derived in `Mettapedia.Logic.PLNDerivation`.

## References

- `hyperon/pln-experimental/metta/common/formula/DeductionFormula.metta`
-/

import Mettapedia.Logic.PLNDerivation

namespace Mettapedia.Implementation.MettaVerification

open Mettapedia.Logic.PLN

/-! ## MeTTa Interpreter Semantics

We define a minimal embedding of MeTTa arithmetic expressions to verify the formula.
-/

/-- Minimal MeTTa arithmetic operations -/
inductive MettaExpr where
  | Const : ℝ → MettaExpr
  | Var : String → MettaExpr
  | Add : MettaExpr → MettaExpr → MettaExpr
  | Sub : MettaExpr → MettaExpr → MettaExpr
  | Mul : MettaExpr → MettaExpr → MettaExpr
  | Div : MettaExpr → MettaExpr → MettaExpr

/-- Environment for variable lookup -/
def Env := String → ℝ

/-- Evaluator for MeTTa expressions -/
noncomputable def eval (env : Env) : MettaExpr → ℝ
  | .Const c => c
  | .Var s => env s
  | .Add a b => eval env a + eval env b
  | .Sub a b => eval env a - eval env b
  | .Mul a b => eval env a * eval env b
  | .Div a b => eval env a / eval env b

/-! ## The Deduction Formula Code

We explicitly reconstruct the AST of the MeTTa code.
Code: (+ (* AB BC) (/ (* (- 1 AB) (- C (* B BC))) (- 1 B)))
-/

def deductionCode : MettaExpr :=
  .Add
    (.Mul (.Var "sAB") (.Var "sBC"))
    (.Div
      (.Mul
        (.Sub (.Const 1) (.Var "sAB"))
        (.Sub (.Var "sC") (.Mul (.Var "sB") (.Var "sBC"))))
      (.Sub (.Const 1) (.Var "sB")))

/-! ## Verification Theorem

We prove that for any valid environment, the MeTTa code evaluates to the
exact mathematical formula derived in `PLNDerivation`.
-/

theorem metta_deduction_correct (env : Env)
    (hB : env "sB" ≠ 1) :
    eval env deductionCode =
      plnDeductionStrength (env "sAB") (env "sBC") (env "sB") (env "sC") := by
  -- Unfold the evaluation of the AST
  simp only [deductionCode, eval]
  -- Unfold the mathematical definition
  unfold plnDeductionStrength
  -- They should be syntactically identical
  rfl

/-! ## Consistency Checks

We also verify the consistency conditions from `DeductionFormula.metta`.
-/

/-- MeTTa: `(clamp (/ (- (+ $As $Bs) 1) $As) 0 1)` -/
def smallestInterCode : MettaExpr :=
  .Div (.Sub (.Add (.Var "sA") (.Var "sB")) (.Const 1)) (.Var "sA")
  -- Note: We verify the inner math; clamp is a separate logic

theorem smallest_intersection_correct (env : Env) (hA : env "sA" ≠ 0) :
    eval env smallestInterCode = (env "sA" + env "sB" - 1) / env "sA" := by
  simp [smallestInterCode, eval]

end Mettapedia.Implementation.MettaVerification
