import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Source control composition with zero or many body answers

Conditions and bound values are single-answer computations; their selected
bodies may produce zero, one or many ordered answers and may change the store.
These rules retain the existing evaluator's continuations and shared-state
sequence. An empty body is not a Boolean false answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

theorem if_answers (program : Program) (bindings : Subst) (before middle after : Effects.State)
    (condition value yes no : Atom) (answers : List Atom)
    (tested : PureReturns program bindings before condition middle value)
    (chosen : Returns program bindings middle (if value == Effects.boolean true then yes else no) after answers) :
    Returns program bindings before (.expression [.symbol "if", condition, yes, no]) after answers := by
  refine .step (step_transition rfl)
    (path_trans (path_with_caller_frames program [.branch bindings yes no] tested) ?_)
  exact .step (step_transition rfl) (single_sequence_answers program middle after _ answers chosen)

theorem let_answers (program : Program) (bindings bound : Subst) (before middle after : Effects.State)
    (pattern expression body value : Atom) (answers : List Atom)
    (computed : PureReturns program bindings before expression middle value)
    (matched : matchBinding bindings pattern value = some bound)
    (continued : Returns program bound middle body after answers) :
    Returns program bindings before (.expression [.symbol "let", pattern, expression, body]) after answers := by
  refine .step (step_transition rfl)
    (path_trans (path_with_caller_frames program [.bind bindings pattern body] computed) ?_)
  refine .step ?_ (single_sequence_answers program middle after (.evaluate bound body) answers continued)
  apply step_transition
  simp [withFrames, finished, step, matched]

end Mettapedia.Languages.MeTTa.PeTTa.Eval
