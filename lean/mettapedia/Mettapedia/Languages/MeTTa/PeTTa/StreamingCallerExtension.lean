import Mettapedia.Languages.MeTTa.PeTTa.StreamingDemand
import Mettapedia.Data.List.FirstSelectionTransport

/-!
# Extending actual streaming work by a caller and older alternatives

The extension preserves the source world's state, I/O, allocations and private
code. Saved collection callers receive the same outer continuation as tasks.
The outer answer history is retained independently of a producer's history.
This is a map on the existing machine state, not another evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.CallerExtension

open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

def task (caller : List Frame) (source : Task) : Task :=
  ⟨source.control,source.frames ++ caller⟩

def job (caller : List Frame) : Job → Job
  | .execute source => .execute (task caller source)
  | .collect key bindings frames bank => .collect key bindings (frames ++ caller) bank
  | .handler key => .handler key
  | .first key => .first key

def plug (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) (source : State) : State :=
  {source with agenda := source.agenda.map (job caller) ++ older,answers := earned}

theorem first_marker (caller : List Frame) (key : Nat) (source : Job) :
    firstMarker key (job caller source) = firstMarker key source := by cases source <;> rfl

theorem handler_marker (caller : List Frame) (key : Nat) (source : Job) :
    handlerMarker key (job caller source) = handlerMarker key source := by cases source <;> rfl

theorem collection_change (caller : List Frame) (key : Nat) (answer : Unifying.Answer) (source : Job) :
    collectionChange key answer (job caller source) = (collectionChange key answer source).map (job caller) := by
  cases source with
  | execute | handler | first => rfl
  | collect found bindings frames bank =>
      simp only [job,collectionChange]
      split <;> rfl

theorem later_answers (caller : List Frame) (older source : List Job) (answers : List Unifying.Answer)
    (frames : List Frame) :
    (laterAnswers answers frames source).map (job caller) ++ older =
      laterAnswers answers (frames ++ caller) (source.map (job caller) ++ older) := by
  cases answers <;> rfl

theorem handles_append {frames : List Frame} {key : Nat} (found : Handles frames key) (caller : List Frame) :
    Handles (frames ++ caller) key := by
  induction found with
  | here key rest => exact .here key (rest ++ caller)
  | source found ih => exact .source ih
  | collection found ih => exact .collection ih
  | first found ih => exact .first ih

theorem placement_plug {state target : State} {after : Unifying.Configuration}
    {frames : List Frame} {source : List Job}
    (placed : Placement state after frames source target)
    (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) :
    Placement (plug caller older earned state) after (frames ++ caller)
      (source.map (job caller) ++ older) (plug caller older earned target) := by
  cases placed with
  | plain shape => exact .plain shape
  | collection shape => exact .collection shape
  | handler shape => exact .handler shape
  | waiting shape ordinary =>
      simpa only [plug,job,task,List.map_cons,List.cons_append,List.append_assoc] using
        Placement.waiting (state := plug caller older earned state) shape ordinary

theorem delivery_plug {registry : SpaceSemantics.Program} {state target : State}
    {answer : Unifying.Answer} {frames : List Frame} {source : List Job}
    (delivered : Delivery registry state answer frames source target) (nonempty : frames ≠ [])
    (caller : List Frame) (older : List Job) (earned : List Unifying.Answer) :
    Delivery registry (plug caller older earned state) answer (frames ++ caller)
      (source.map (job caller) ++ older) (plug caller older earned target) := by
  cases delivered with
  | root => exact False.elim (nonempty rfl)
  | source source placement =>
      exact .source source (placement_plug placement caller older earned)
  | collection recorded =>
      exact .collection (recorded.map_append (job caller) (collection_change caller _ _) older)
  | handler key rest source => exact .handler key (rest ++ caller) (source.map (job caller) ++ older)
  | first found => exact .first (found.map_append (job caller) (first_marker caller _) older)

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.CallerExtension
