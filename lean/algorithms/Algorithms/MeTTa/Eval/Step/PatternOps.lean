import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.PatternOps

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Convert expression to element list: `(a b c)` → `[a, b, c]`. -/
private def exprElems : Pattern → List Pattern
  | .apply "" tl => tl
  | .apply hd tl => .apply hd [] :: tl
  | other => [other]

/-- Construct expression from element list: `[a, b, c]` → `(a b c)`. -/
private def mkExpr : List Pattern → Pattern
  | [] => .apply "()" []
  | (.apply hd []) :: tl => .apply hd tl
  | hd :: tl => .apply "" (hd :: tl)

/-- Pure pattern operations. -/
def evalPatternOp (ctor : String) (args : List Pattern) : Option (List Pattern) :=
  match ctor, args with
  -- car-atom: first element of expression
  | "car-atom", [expr] =>
      match exprElems expr with
      | hd :: _ => some [hd]
      | [] => none
  -- cdr-atom: rest elements as expression
  | "cdr-atom", [expr] =>
      match exprElems expr with
      | _ :: tl => some [mkExpr tl]
      | [] => none
  -- cons-atom: prepend element to expression
  | "cons-atom", [hd, expr] => some [mkExpr (hd :: exprElems expr)]
  -- Pair accessors (2-element expressions)
  | "first-from-pair", [expr] =>
      match exprElems expr with
      | a :: _ => some [a]
      | _ => none
  | "second-from-pair", [expr] =>
      match exprElems expr with
      | _ :: b :: _ => some [b]
      | _ => none
  -- Index
  | "index-atom", [expr, idx] => do
      let i ← Pattern.toInt? idx
      let elems := exprElems expr
      if h : i.toNat < elems.length then some [elems[i.toNat]]
      else none
  -- Length
  | "length", [expr] => some [Pattern.ofInt (exprElems expr).length]
  -- Predicates
  | "is-var", [.fvar _] => some [Pattern.ofBool true]
  | "is-var", [_] => some [Pattern.ofBool false]
  | "is-expr", [.apply _ _] => some [Pattern.ofBool true]
  | "is-expr", [_] => some [Pattern.ofBool false]
  -- Membership
  | "is-member", [x, expr] =>
      some [Pattern.ofBool (exprElems expr |>.any (· == x))]
  -- Identity
  | "id", [x] => some [x]
  -- Structural equality
  | "=", [a, b] => some [Pattern.ofBool (a == b)]
  | _, _ => none

end Algorithms.MeTTa.Eval.Step.PatternOps
