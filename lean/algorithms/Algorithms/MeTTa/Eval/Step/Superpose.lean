import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.Superpose

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Convert an expression to its list of elements.
    In MeTTa, `(a b c)` is `.apply "a" [b, c]` — the head IS the first element.
    So the elements are `[.apply "a" [], b, c]` (head reconstructed as atom + tail). -/
private def exprElems : Pattern → List Pattern
  | .apply hd tl => .apply hd [] :: tl
  | other => [other]

def evalSuperpose (ctor : String) (args : List Pattern) : Option (List Pattern) :=
  match ctor, args with
  -- superpose: branch over all elements of the expression
  | "superpose", [expr] => some (exprElems expr)
  -- collapse: pass-through (evaluator handles collection in Eval.lean)
  | "collapse", [_arg] => none  -- handled by eval?, not step?
  -- msort: same element extraction as superpose
  | "msort", [expr] => some (exprElems expr)
  | _, _ => none

end Algorithms.MeTTa.Eval.Step.Superpose
