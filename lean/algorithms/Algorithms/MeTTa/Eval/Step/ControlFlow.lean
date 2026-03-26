import Algorithms.MeTTa.Eval.Core
import Algorithms.MeTTa.Eval.Step.Rules

namespace Algorithms.MeTTa.Eval.Step.ControlFlow

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

private def isTruthy : Pattern → Bool
  | .apply "True" [] => true
  | _ => false

/-- Control flow operators. These return reducts (one-step only, no eval recursion).

    Design: operators like `if`, `let`, `case` return their REDUCED BODY as a reduct.
    The evaluator will then process that reduct in the next step.
    This keeps `step?` non-recursive. -/
def evalControlFlow (s : Session) (ctor : String) (args : List Pattern) :
    Option (List Pattern) :=
  match ctor, args with
  -- if: only fires when condition is an atom (True/False). Otherwise defers to arg reduction.
  | "if", [.apply "True" [], thenBr, _elseBr] => some [thenBr]
  | "if", [.apply "False" [], _thenBr, elseBr] => some [elseBr]
  | "if", [.apply "True" [], thenBr] => some [thenBr]
  | "if", [.apply "False" [], _thenBr] => some []
  | "if", [_, _, _] => none  -- condition not yet reduced → arg reduction
  | "if", [_, _] => none
  -- let, let*, collapse, chain, progn, prog1: handled in Eval.lean

  -- nop: evaluate for side effects, return empty tuple
  | "nop", _ => some [.apply "()" []]

  -- cut: succeed immediately
  | "cut", _ => some [.apply "()" []]

  -- once: return first result only (from a list)
  | "once", [arg] => some [arg]

  -- catch: try expr, on error use fallback
  | "catch", [expr, _handler, fallback] =>
      -- Simplified: just return the expr as a reduct.
      -- If it reduces to an Error, the fallback handling needs the evaluator.
      -- For now, just pass through.
      some [expr]
  | "catch", [expr] => some [expr]

  -- case: multi-way pattern match
  | "case", [keyExpr, .apply _ branches] =>
      -- Try each branch: (pattern result) pairs
      let result := branches.findSome? fun branch =>
        match branch with
        | .apply _ [pat, result] =>
            match Rules.matchPattern pat keyExpr with
            | some bindings => some (Rules.applyBindings bindings result)
            | none => none
        | _ => none
      match result with
      | some r => some [r]
      | none => some []  -- no branch matched

  | _, _ => none

end Algorithms.MeTTa.Eval.Step.ControlFlow
