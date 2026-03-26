import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.Arithmetic

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Try to evaluate a pure arithmetic/comparison operator.
    Returns `some [result]` if the operator applies, `none` otherwise. -/
def evalArithmetic (ctor : String) (args : List Pattern) : Option (List Pattern) :=
  match ctor, args with
  -- Arithmetic (2 args, int)
  | "+", [a, b] => do let x ← Pattern.toInt? a; let y ← Pattern.toInt? b; pure [Pattern.ofInt (x + y)]
  | "-", [a, b] => do let x ← Pattern.toInt? a; let y ← Pattern.toInt? b; pure [Pattern.ofInt (x - y)]
  | "*", [a, b] => do let x ← Pattern.toInt? a; let y ← Pattern.toInt? b; pure [Pattern.ofInt (x * y)]
  | "/", [a, b] => do
      let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
      if y == 0 then none else pure [Pattern.ofInt (x / y)]
  | "%", [a, b] => do
      let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
      if y == 0 then none else pure [Pattern.ofInt (x % y)]
  -- Unary minus
  | "-", [a] => do let x ← Pattern.toInt? a; pure [Pattern.ofInt (-x)]
  -- Comparison (2 args, int)
  | "<", [a, b] => do let x ← Pattern.toInt? a; let y ← Pattern.toInt? b; pure [Pattern.ofBool (x < y)]
  | ">", [a, b] => do let x ← Pattern.toInt? a; let y ← Pattern.toInt? b; pure [Pattern.ofBool (x > y)]
  | "<=", [a, b] => do let x ← Pattern.toInt? a; let y ← Pattern.toInt? b; pure [Pattern.ofBool (x ≤ y)]
  | ">=", [a, b] => do let x ← Pattern.toInt? a; let y ← Pattern.toInt? b; pure [Pattern.ofBool (x ≥ y)]
  | "==", [a, b] =>
      -- Only compare if both are atoms (no sub-expressions to reduce)
      match a, b with
      | .apply _ [], .apply _ [] => pure [Pattern.ofBool (a == b)]
      | .apply _ [], .fvar _ => pure [Pattern.ofBool (a == b)]
      | .fvar _, .apply _ [] => pure [Pattern.ofBool (a == b)]
      | .fvar _, .fvar _ => pure [Pattern.ofBool (a == b)]
      | _, _ => none  -- args need reduction first
  | "!=", [a, b] =>
      match a, b with
      | .apply _ [], .apply _ [] => pure [Pattern.ofBool (a != b)]
      | .apply _ [], .fvar _ => pure [Pattern.ofBool (a != b)]
      | .fvar _, .apply _ [] => pure [Pattern.ofBool (a != b)]
      | .fvar _, .fvar _ => pure [Pattern.ofBool (a != b)]
      | _, _ => none
  | _, _ => none

end Algorithms.MeTTa.Eval.Step.Arithmetic
