import Mettapedia.Languages.MeTTa.HE.StatefulPriorityTraversal
import Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls
import Mettapedia.Machines.OrderedPriorityDemand

/-!
# Stateful HE priority and first-demand controls

The explicit host is the existing ordered-store model. Its executable local
provider implements only its native instruction, and every supplied transition
is proved to be an actual contextual HE worker step. Unsupported child work
remains pending. No whole evaluation or source completion is supplied by a host.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEPriorityControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual
namespace Traversal
export Mettapedia.Machines.OrderedPriorityTraversal
  (Control State initial output tick core firstCore)
end Traversal

abbrev World := HEWorldControls.World

/-- This provider is a single host instruction, not an evaluator callback. -/
def next (label : Bool) (world : World) : StatefulPriorityTraversal.Child Bool →
    Option (World × StatefulPriorityTraversal.Child Bool)
  | (.work (.minimal _ _ _ (.expression _
      [.symbol "call-native",.symbol "model-store",.symbol command,argument]) frame),stack) =>
      let reply := HEWorldControls.execute label world (.symbol command) argument.erase
      some (reply.2,(.returning (reply.1.map (fun value => (Entry.Value.ofAtom value,frame))),stack))
  | _ => none

theorem next_sound (label : Bool) (policy : Policy) (world : World)
    (child : StatefulPriorityTraversal.Child Bool) (reached : World)
    (after : StatefulPriorityTraversal.Child Bool)
    (computed : next label world child = some (reached,after)) :
    StatefulPriorityTraversal.advance HEWorldControls.environment policy label world child reached after := by
  unfold next at computed
  split at computed
  · cases computed
    apply RecursiveMachine.Contextual.WorldLocalStep.native
    exact ⟨by simp [Entry.Value.erase],by simp [Entry.Value.erase],by simp [Entry.Value.erase]⟩
  · contradiction

def task (command argument : String) : Task :=
  .minimal [] [] none (HEWorldControls.command command (.symbol argument)) Frame.empty

def emptyWorld : World := fun _ => []

def program : List Task :=
  [task "silent-put" "before",task "bad" "provisional",
    task "put" "first",task "silent-put" "later"]

def firstMachine : Mettapedia.Machines.MachineCore (List Task × World) :=
  Traversal.firstCore StatefulPriorityTraversal.start (next false)
    StatefulPriorityTraversal.finished (StatefulPriorityTraversal.isError .unmarked)

def fullMachine : Mettapedia.Machines.MachineCore (List Task × World) :=
  Traversal.core StatefulPriorityTraversal.start (next false)
    StatefulPriorityTraversal.finished (StatefulPriorityTraversal.isError .unmarked)

def poll := Mettapedia.Machines.OrderedPriorityDemand.poll StatefulPriorityTraversal.start
  (next false) StatefulPriorityTraversal.finished (StatefulPriorityTraversal.isError .unmarked)

def load (tasks : List Task) : StatefulPriorityTraversal.State Bool World :=
  Traversal.initial tasks emptyWorld

def firstResult := (firstMachine.runSlice 100 (load program)).1
def fullResult := (fullMachine.runSlice 100 (load program)).1
def pausedResult := (firstMachine.runSlice 3 (load program)).1

def values (state : StatefulPriorityTraversal.State Bool World) : List Atom :=
  (StatefulPriorityTraversal.readOutput .unmarked state).map (fun row => row.1.erase)

attribute [local simp] values firstResult fullResult pausedResult firstMachine fullMachine
  Traversal.firstCore Traversal.core load program task HEWorldControls.command
  HEReturnAndSpaces.native HEWorldControls.execute HEWorldControls.failure next
  Mettapedia.Machines.MachineCore.runSlice
  Mettapedia.Machines.OrderedPriorityTraversal.firstTick Traversal.tick Traversal.output
  Mettapedia.Machines.OrderedPriorityTraversal.Control.isClosed Traversal.initial
  StatefulPriorityTraversal.start StatefulPriorityTraversal.finished
  StatefulPriorityTraversal.readOutput StatefulPriorityTraversal.isError readResult
  Entry.Value.ofAtom Entry.Value.erase isErrorAtom
  Mettapedia.Machines.HEProducerCompletion.ingest
  Mettapedia.Machines.HEProducerCompletion.collect
  Mettapedia.Machines.HEProducerCompletion.present
  Mettapedia.Machines.HEProducerCompletion.visible
  Mettapedia.Machines.HEProducerCompletion.empty

theorem first_retains_earlier_effects_and_skips_later :
    values firstResult = [.expression []] ∧
      firstResult.world false = [.symbol "before",.symbol "first"] ∧
      firstResult.world true = [] ∧ firstResult.control.isClosed = false := by simp +decide

theorem full_drain_keeps_later_effect_and_same_success :
    values fullResult = [.expression []] ∧
      fullResult.world false = [.symbol "before",.symbol "first",.symbol "later"] ∧
      fullResult.control.isClosed = true := by simp +decide

theorem pause_has_reached_effect_without_completion :
    values pausedResult = [] ∧ pausedResult.world false = [.symbol "before"] ∧
      pausedResult.control.isClosed = false := by simp +decide

theorem first_uses_checked_worker_steps :
    ∃ raw, StatefulPriorityTraversal.Steps HEWorldControls.environment .unmarked false
      (load program) raw firstResult :=
  Mettapedia.Machines.OrderedPriorityTraversal.firstSlice_sound
    (next_sound false .unmarked) 100 (load program)

theorem common_cursor_returns_one_success :
    let result := firstMachine.runSlice 100 (load program)
    Mettapedia.Machines.Cursor.advance
      (Mettapedia.Machines.StoreAndDemand.FirstAnswer.provider poll)
      (Mettapedia.Machines.StoreAndDemand.FirstAnswer.client Result Unit) (fun _ _ => 1)
      (result.2 + 2) (Mettapedia.Machines.StoreAndDemand.FirstAnswer.start poll (load program)) =
        (result.2 + 1,.done ⟨(),.answer (.expression .active [],Frame.empty),result.1⟩) :=
  Mettapedia.Machines.OrderedPriorityDemand.common_cursor_after_slice 100 (load program)
    (.expression .active [],Frame.empty) (by simp +decide)

theorem full_uses_checked_worker_steps :
    ∃ raw, StatefulPriorityTraversal.Steps HEWorldControls.environment .unmarked false
      (load program) raw fullResult :=
  Mettapedia.Machines.OrderedPriorityTraversal.runSlice_sound
    (next_sound false .unmarked) 100 (load program)

theorem reached_first_is_inert (allowance : Nat) :
    firstMachine.runSlice allowance firstResult = (firstResult,0) :=
  Mettapedia.Machines.OrderedPriorityTraversal.first_output_stops firstResult (by simp +decide) allowance

theorem split_resumes_actual_prefix :
    firstMachine.runSlice 103 (load program) =
      let earlier := firstMachine.runSlice 3 (load program)
      let resumed := firstMachine.runSlice 100 earlier.1
      (resumed.1,earlier.2 + resumed.2) :=
  Mettapedia.Machines.OrderedPriorityTraversal.first_split (load program) 3 100

theorem resuming_does_not_repeat_before :
    (firstMachine.runSlice 100 pausedResult).1.world false = [.symbol "before",.symbol "first"] ∧
      (firstMachine.runSlice 100 (Traversal.initial program pausedResult.world)).1.world false =
        [.symbol "before",.symbol "before",.symbol "first"] := by simp +decide

def errorsOnly : List Task :=
  [task "silent-put" "before",task "bad" "same",task "bad" "same"]

theorem errors_are_released_only_after_closure :
    let result := (firstMachine.runSlice 100 (load errorsOnly)).1
    values result = [HEWorldControls.failure (.symbol "same"),HEWorldControls.failure (.symbol "same")] ∧
      result.world false = [.symbol "before"] ∧ result.control.isClosed = true := by simp +decide [errorsOnly]

/-- All fallback errors are retained by phase completion; the actual first
consumer receives only the first occurrence, including when errors duplicate. -/
theorem common_cursor_returns_one_fallback_error :
    let result := firstMachine.runSlice 100 (load errorsOnly)
    Mettapedia.Machines.Cursor.advance
      (Mettapedia.Machines.StoreAndDemand.FirstAnswer.provider poll)
      (Mettapedia.Machines.StoreAndDemand.FirstAnswer.client Result Unit) (fun _ _ => 1)
      (result.2 + 2) (Mettapedia.Machines.StoreAndDemand.FirstAnswer.start poll (load errorsOnly)) =
        (result.2 + 1,.done ⟨(),.answer (Entry.Value.ofAtom
          (HEWorldControls.failure (.symbol "same")),Frame.empty),result.1⟩) :=
  Mettapedia.Machines.OrderedPriorityDemand.common_cursor_after_slice 100 (load errorsOnly)
    (Entry.Value.ofAtom (HEWorldControls.failure (.symbol "same")),Frame.empty)
      (by simp +decide [errorsOnly])

theorem error_prefix_is_not_yet_a_public_error :
    let result := (firstMachine.runSlice 9 (load errorsOnly)).1
    values result = [] ∧ result.bank.fallbackRev.length = 1 ∧
      result.world false = [.symbol "before"] ∧ result.control.isClosed = false := by simp +decide [errorsOnly]

/-- Binary source preference and root omission are separate policies. -/
theorem empty_is_not_an_error_in_this_phase :
    StatefulPriorityTraversal.isError .unmarked (.symbol "Empty",Frame.empty) = false := by simp

end Mettapedia.Languages.MeTTa.ContextualTransform.HEPriorityControls
