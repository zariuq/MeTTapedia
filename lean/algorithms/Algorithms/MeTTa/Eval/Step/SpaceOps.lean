import Algorithms.MeTTa.Eval.Core

namespace Algorithms.MeTTa.Eval.Step.SpaceOps

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

/-- Stateful space operations. These modify `s.space` and return a new session. -/
def evalSpaceOp (s : Session) (ctor : String) (args : List Pattern) :
    Option (Session × List Pattern) :=
  match ctor, args with
  -- add-atom: add a fact to the space
  | "add-atom", [_space, fact] =>
      some ({ s with space := fact :: s.space }, [.apply "()" []])
  | "add-atom!", [_space, fact] =>
      some ({ s with space := fact :: s.space }, [.apply "()" []])

  -- remove-atom: remove first matching fact
  | "remove-atom", [_space, fact] =>
      let space' := s.space.filter (· != fact)
      some ({ s with space := space' }, [.apply "()" []])
  | "remove-atom!", [_space, fact] =>
      let space' := s.space.filter (· != fact)
      some ({ s with space := space' }, [.apply "()" []])

  -- get-atoms: return all atoms as a tuple
  | "get-atoms", [_space] =>
      some (s, [.apply "" s.space])
  | "get-atoms!", [_space] =>
      some (s, [.apply "" s.space])

  -- remove-all-atoms: clear space
  | "remove-all-atoms", [_space] =>
      some ({ s with space := [] }, [.apply "()" []])
  | "remove-all-atoms!", [_space] =>
      some ({ s with space := [] }, [.apply "()" []])

  | _, _ => none

end Algorithms.MeTTa.Eval.Step.SpaceOps
