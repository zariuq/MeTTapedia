import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.Meta

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Meta/evaluation operators.
    These return their argument as a reduct — the evaluator handles
    the actual recursive evaluation. This keeps step? non-recursive.

    `eval` and `reduce` just pass through their arg.
    `quote` blocks evaluation (returns the quoted form as normal).
    `repr` converts to string representation.
    `atom-of` extracts atom candidates. -/
def evalMeta (ctor : String) (args : List Pattern) : Option (List Pattern) :=
  match ctor, args with
  -- eval: evaluate expression (just pass through — evaluator handles it)
  | "eval", [arg] => some [arg]
  -- reduce: same as eval for now
  | "reduce", [arg] => some [arg]
  -- quote: block evaluation, return as-is (this IS the normal form)
  | "quote", [_arg] => none  -- quote terms are normal forms
  -- repr: convert to string
  | "repr", [arg] => some [.apply (reprPattern arg) []]
  -- atom-of: extract atom
  | "atom-of", [.apply c []] => some [.apply c []]
  | "atom-of", [_] => some []
  -- Expr: tuple constructor (just return as-is)
  | "Expr", _ => none  -- Expr terms are normal forms
  -- chain: (chain expr var template) — bind expr result to var in template
  | "chain", [expr, .fvar _var, _tmpl] =>
      -- Return expr as a reduct. The binding happens when the result comes back.
      -- Simplified: just evaluate the expression.
      some [expr]
  | _, _ => none
where
  reprPattern : Pattern → String
    | .apply c [] => c
    | .apply c args => s!"({c} {" ".intercalate (args.map reprPattern)})"
    | .fvar n => s!"${n}"
    | .lambda _ => "<lambda>"
    | _ => "?"

end Algorithms.MeTTa.Eval.Step.Meta
