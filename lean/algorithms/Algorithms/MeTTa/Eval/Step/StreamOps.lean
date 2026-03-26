import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.StreamOps

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Stream operations: unique, union, intersection, subtraction.
    These operate on tuples (represented as `.apply "" elems`). -/
def evalStreamOp (ctor : String) (args : List Pattern) : Option (List Pattern) :=
  match ctor, args with
  | "unique", [.apply _ elems] =>
      let unique := elems.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
      some [.apply "" unique]
  | "union", [.apply _ a, .apply _ b] =>
      some [.apply "" (a ++ b)]
  | "intersection", [.apply _ a, .apply _ b] =>
      let common := a.filter (fun x => b.contains x)
      some [.apply "" common]
  | "subtraction", [.apply _ a, .apply _ b] =>
      let diff := a.filter (fun x => !b.contains x)
      some [.apply "" diff]
  | _, _ => none

end Algorithms.MeTTa.Eval.Step.StreamOps
