import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.Logic

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

private def isTruthy : Pattern → Bool
  | .apply "True" [] => true
  | _ => false

/-- Boolean/logical operators. -/
def evalLogic (ctor : String) (args : List Pattern) : Option (List Pattern) :=
  match ctor, args with
  | "not", [a] => some [Pattern.ofBool (!isTruthy a)]
  | "and", args => some [Pattern.ofBool (args.all isTruthy)]
  | "or", args => some [Pattern.ofBool (args.any isTruthy)]
  | "xor", args =>
      let count := args.filter isTruthy |>.length
      some [Pattern.ofBool (count % 2 == 1)]
  | _, _ => none

end Algorithms.MeTTa.Eval.Step.Logic
