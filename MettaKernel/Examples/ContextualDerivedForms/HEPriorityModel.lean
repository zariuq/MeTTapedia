import Mettapedia.Languages.MeTTa.ContextualTransform.HEPriorityControls

/-! Executable consumer of the stateful source-phase and common-cursor laws.
The explicit store host is a calibration model, not CeTTa native conformance. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.ContextualTransform.HEPriorityControls
open Mettapedia.Machines

def describe (label : String) (state : StatefulPriorityTraversal.State Bool World) : IO Unit := do
  IO.println s!"{label}: available={reprStr ((values state).map Atom.toString)} store={reprStr ((state.world false).map Atom.toString)} closed={state.control.isClosed}"

def describeCursor (label : String) (fuel : Nat) (tasks : List RecursiveTasks.Contextual.Task) : IO Unit := do
  let result := Cursor.advance (StoreAndDemand.FirstAnswer.provider poll)
    (StoreAndDemand.FirstAnswer.client Spec.Eval.Completed.Result Unit) (fun _ _ => 1)
    fuel (StoreAndDemand.FirstAnswer.start poll (load tasks))
  match result.2 with
  | .paused ⟨_,_,saved⟩ =>
      IO.println s!"{label}: paused store={reprStr ((saved.world false).map Atom.toString)}"
  | .done ⟨_,reply,saved⟩ =>
      let answer := match reply with
        | .answer row => s!"answer={row.1.erase.toString}"
        | .exhausted => "exhausted"
        | .interrupted => "interrupted"
        | .raised _ => "raised"
      IO.println s!"{label}: {answer} store={reprStr ((saved.world false).map Atom.toString)}"

def main : IO Unit := do
  describe "first" firstResult
  describe "drain" fullResult
  describe "pause" pausedResult
  describe "resume" (firstMachine.runSlice 100 pausedResult).1
  describe "restart" (firstMachine.runSlice 100
    (OrderedPriorityTraversal.initial program pausedResult.world)).1
  describe "errors" (firstMachine.runSlice 100 (load errorsOnly)).1
  describe "error-prefix" (firstMachine.runSlice 9 (load errorsOnly)).1
  describeCursor "cursor-success" 100 program
  describeCursor "cursor-error" 100 errorsOnly
  describeCursor "cursor-pause" 3 program
  describeCursor "cursor-empty" 100 []
  describeCursor "cursor-unavailable" 100
    [.atom [] [] (.symbol "unserved") Atom.undefinedType Spec.Eval.Completed.Frame.empty]
