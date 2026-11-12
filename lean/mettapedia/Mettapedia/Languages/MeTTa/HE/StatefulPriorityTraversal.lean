import Mettapedia.Languages.MeTTa.HE.RecursiveExecution
import Mettapedia.Machines.OrderedPriorityTraversal

/-!
# Stateful HE source phases through incremental priority traversal

Children are the existing contextual worker's actual retained controls and
continuations. Its local rules perform matching, binding, context changes and
world operations. The traversal never asks a service to evaluate a whole child.
Independent stateful source judgments supply both completed preservation and
reflection; no completed derivation is required to take an individual step.

This adapter opens the ordered phase between completed source children. It
does not reorder or stream through a child's operand-evaluation barrier. The
source's binary error preference is retained at its own phase, independently
of any later root Empty-omission policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.StatefulPriorityTraversal

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual
open Mettapedia.Machines.OrderedProtocol.Completion
namespace Traversal
export Mettapedia.Machines.OrderedPriorityTraversal
  (Control State ControlStep Step Steps initial output Residual)
end Traversal

variable {Context World : Type}

abbrev Child (Context : Type) := Control Context × List Continuation

def start (task : Task) : Child Context := (.work task,[])

def finished : Child Context → Option (List Result)
  | (.returning rows,[]) => some rows
  | _ => none

abbrev advance (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    (world : World) (before : Child Context) (reached : World) (after : Child Context) : Prop :=
  RecursiveMachine.Contextual.WorldLocalStep (admission := environment.arguments)
    environment.view environment.services environment.dispatch environment.lookup policy
      world label before reached after

def childSource (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    (child : Child Context) (world : World) (results : List Result) (final : World) : Prop :=
  ∃ current middle, child.1.WorldSourceRel environment policy label world current middle ∧
    WorldStackRel environment policy label middle child.2 current results final

theorem start_source {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {task : Task} {world final : World} {rows : List Result}
    (source : childSource environment policy label (start task) world rows final) :
    task.WorldSourceRel environment policy label world rows final := by
  obtain ⟨current,middle,controlled,continued⟩ := source
  cases continued
  cases controlled with
  | work source => exact source

theorem child_source_back {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {world reached final : World} {before after : Child Context} {rows}
    (edge : advance environment policy label world before reached after)
    (source : childSource environment policy label after reached rows final) :
    childSource environment policy label before world rows final := by
  obtain ⟨current,middle,controlled,continued⟩ := source
  obtain ⟨earlier,earlierWorld,earlierSource,saved⟩ :=
    RecursiveCorrectness.Contextual.Stateful.local_source_back edge controlled continued
  exact ⟨earlier,earlierWorld,earlierSource,saved⟩

theorem finished_source {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {child : Child Context} {world : World} {rows : List Result}
    (done : finished child = some rows) :
    childSource environment policy label child world rows world := by
  rcases child with ⟨control,stack⟩
  cases control <;> cases stack <;> simp [finished] at done
  subst rows
  exact ⟨_,world,.returning _,.nil _⟩

theorem child_complete {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {task : Task} {world final : World} {rows : List Result}
    (source : task.WorldSourceRel environment policy label world rows final) :
    ∃ child, Relation.ReflTransGen
      (fun first last : World × Child Context =>
        advance environment policy label first.1 first.2 last.1 last.2)
      (world,start task) (final,child) ∧ finished child = some rows :=
  ⟨(.returning rows,[]),RecursiveExecution.Contextual.Stateful.task_complete source [],rfl⟩

/-- Classification reads the completed occurrence's own binding frame. It
does not inspect a future world or reconstruct the occurrence. -/
def isError (policy : Policy) (row : Result) : Bool :=
  isErrorAtom (readResult policy row).1.erase

abbrev State (Context World : Type) := Traversal.State Task (Child Context) World Result

abbrev Steps (environment : WorldEnvironment Context World) (policy : Policy) (label : Context)
    (before : State Context World) (raw : List Result) (after : State Context World) : Prop :=
  Traversal.Steps start (advance environment policy label) finished (isError policy) before raw after

def readOutput (policy : Policy) (state : State Context World) : List Result :=
  (Traversal.output (isError policy) state).map (readResult policy)

/-- A complete traversal reflects exactly the source children in order and
in the reached worlds. Empty result blocks retain their effects. -/
theorem completed_raw {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {tasks : List Task} {world : World} {after : State Context World} {raw}
    (path : Steps environment policy label (Traversal.initial tasks world) raw after)
    (closed : after.control = .closed) :
    OrderedStateFlatMapRel (fun task => task.WorldSourceRel environment policy label)
      tasks world raw after.world := by
  have rest : Traversal.Residual
      (fun task => task.WorldSourceRel environment policy label)
      (childSource environment policy label) after.control after.world [] after.world := by
    rw [closed]
    exact ⟨rfl,rfl⟩
  have source := path.source_back
    (fun _ _ _ _ => start_source)
    (fun _ _ _ _ _ _ => child_source_back)
    (fun _ _ _ => finished_source) rest
  simpa only [Traversal.initial,Traversal.Residual,List.append_nil] using source

theorem source_executes {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {tasks : List Task} {world final : World} {raw}
    (source : OrderedStateFlatMapRel (fun task => task.WorldSourceRel environment policy label)
      tasks world raw final) :
    Steps environment policy label (Traversal.initial tasks world) raw
      ⟨.closed,final,Mettapedia.Machines.HEProducerCompletion.collect (isError policy) true raw
        Mettapedia.Machines.HEProducerCompletion.empty⟩ :=
  Mettapedia.Machines.OrderedPriorityTraversal.source_executes
    (fun _ _ _ _ => child_complete) source _

theorem completed_priority {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {tasks : List Task} {world : World} {after : State Context World} {raw}
    (path : Steps environment policy label (Traversal.initial tasks world) raw after)
    (closed : after.control = .closed) :
    SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      (raw.map (readResult policy)) (readOutput policy after) := by
  exact (Mettapedia.Machines.OrderedPriorityTraversal.closed_output_priority path
    (by simp [closed,Mettapedia.Machines.OrderedPriorityTraversal.Control.isClosed])).map
      (readResult policy) (fun _ => rfl)

/-- Completion is equivalent in both directions, rather than a supplied
whole-evaluator agreement premise. Prefixes remain separately observable. -/
theorem phase_iff {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {tasks : List Task} {world final : World} {selected : List Result} :
    (∃ raw, OrderedStateFlatMapRel (fun task => task.WorldSourceRel environment policy label)
        tasks world raw final ∧
      SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
        (raw.map (readResult policy)) selected) ↔
    ∃ after raw, Steps environment policy label (Traversal.initial tasks world) raw after ∧
      after.control = .closed ∧ after.world = final ∧ readOutput policy after = selected := by
  constructor
  · rintro ⟨raw,source,priority⟩
    have path := source_executes source
    exact ⟨_,raw,path,rfl,rfl,(completed_priority path rfl).functional priority⟩
  · rintro ⟨after,raw,path,closed,reached,same⟩
    exact ⟨raw,reached ▸ completed_raw path closed,same ▸ completed_priority path closed⟩

def callTasks (live : List Atom) (scope : List String) (expected : Atom) (rows : List Result) : List Task :=
  rows.map fun row => .call live scope row.1 expected row.2

/-- The actual source call frontier is the shared traversal's work list. -/
theorem calls_exact {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {live scope expected} {rows results : List Result} {world final : World} :
    Stateful.CallsRel environment label world live scope expected rows results final (policy := policy) ↔
      OrderedStateFlatMapRel (fun task => task.WorldSourceRel environment policy label)
        (callTasks live scope expected rows) world results final := by
  induction rows generalizing world results with
  | nil =>
      constructor
      · intro source; cases source; exact .nil _
      · intro source; cases source; exact .nil
  | cons head tail ih =>
      constructor
      · intro source
        cases source with
        | cons first rest => exact .cons first (ih.mp rest)
      · intro target
        cases target with
        | cons first rest => exact .cons first (ih.mpr rest)

theorem call_phase_iff {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {live scope expected} {rows selected : List Result} {world final : World} :
    (∃ raw, Stateful.CallsRel environment label world live scope expected rows raw final
        (policy := policy) ∧
      SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
        (raw.map (readResult policy)) selected) ↔
    ∃ after raw, Steps environment policy label
        (Traversal.initial (callTasks live scope expected rows) world) raw after ∧
      after.control = .closed ∧ after.world = final ∧ readOutput policy after = selected := by
  simp only [calls_exact]
  exact phase_iff

/-- The tuple rule consumes the very same priority phase. Its operand phase
has already finished, so this theorem does not skip required operands. -/
theorem tuple_from_stream {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {world tupleWorld final : World} {live scope value expected frame readiness operator arguments rows}
    {after : State Context World} {raw : List Result}
    (entered : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase expected .interpret)
    (shape : frame.read policy value = .expression readiness (operator :: arguments))
    (untyped : Spec.Type.TypeOccurrencesRel ((environment.view world label).atoms : Multiset Atom)
      operator.erase {Atom.undefinedType})
    (tuple : Stateful.TupleRel environment label world (expected :: live) scope
      (operator :: arguments) frame rows tupleWorld (policy := policy))
    (path : Steps environment policy label
      (Traversal.initial (callTasks live scope expected rows) tupleWorld) raw after)
    (closed : after.control = .closed) (reached : after.world = final) :
    Stateful.AtomRel environment label world live scope value expected frame
      ((readOutput policy after).map (publishResult policy (frame.read policy value).erase)) final
      (policy := policy) := by
  apply Stateful.AtomRel.tuple entered shape untyped tuple
  · exact reached ▸ calls_exact.mpr (completed_raw path closed)
  · exact completed_priority path closed

def invocationTasks (live : List Atom) (scope : List String) (expected : Atom)
    (signature : SelectedTypePolicy) (operator : Entry.Value) (arguments : List Entry.Value)
    (frames : List Frame) : List Task :=
  frames.map fun frame => .invocations live scope expected signature operator arguments [frame]

/-- A selected type frame owns function preparation and the subsequent call
phase. The next selected frame sees the world left by both, not a snapshot. -/
theorem invocations_exact {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {live scope} {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value} {frames : List Frame}
    {results : List Result} {world final : World} :
    Stateful.InvocationsRel environment label world live scope expected signature operator arguments
        frames results final (policy := policy) ↔
      OrderedStateFlatMapRel (fun task => task.WorldSourceRel environment policy label)
        (invocationTasks live scope expected signature operator arguments frames) world results final := by
  induction frames generalizing world results with
  | nil =>
      constructor
      · intro source; cases source; exact .nil _
      · intro source; cases source; exact .nil
  | cons frame frames ih =>
      constructor
      · intro source
        cases source with
        | cons first second tail =>
            rename_i middle childWorld interpreted called rest
            have one : Stateful.InvocationsRel environment label world live scope expected signature
                operator arguments [frame] called childWorld (policy := policy) := by
              simpa only [List.append_nil] using Stateful.InvocationsRel.cons first second
                (Stateful.InvocationsRel.nil (environment := environment) (label := label)
                  (live := live) (scope := scope) (expected := expected) (signature := signature)
                  (operator := operator) (arguments := arguments) (policy := policy))
            exact .cons one (ih.mp tail)
      · intro source
        cases source with
        | cons one tail =>
            cases one with
            | cons first second done =>
                cases done
                simpa only [List.append_nil] using Stateful.InvocationsRel.cons first second (ih.mpr tail)

theorem invocation_phase_iff {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {live scope} {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value} {frames : List Frame}
    {selected : List Result} {world final : World} :
    (∃ raw, Stateful.InvocationsRel environment label world live scope expected signature operator arguments
        frames raw final (policy := policy) ∧
      SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
        (raw.map (readResult policy)) selected) ↔
    ∃ after raw, Steps environment policy label
        (Traversal.initial (invocationTasks live scope expected signature operator arguments frames) world)
          raw after ∧ after.control = .closed ∧ after.world = final ∧ readOutput policy after = selected := by
  simp only [invocations_exact]
  exact phase_iff

theorem function_from_stream {environment : WorldEnvironment Context World} {policy : Policy} {label : Context}
    {world final : World} {live scope value expected frame readiness operator arguments signature frames}
    {after : State Context World} {raw : List Result}
    (entered : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase expected .interpret)
    (shape : frame.read policy value = .expression readiness (operator :: arguments))
    (selected : environment.arguments.selection (environment.view world label) environment.lookup
      policy live scope (frame.read policy value).erase operator.erase expected frame (.selected signature frames))
    (path : Steps environment policy label
      (Traversal.initial (invocationTasks live scope expected signature operator arguments frames) world) raw after)
    (closed : after.control = .closed) (reached : after.world = final) :
    Stateful.AtomRel environment label world live scope value expected frame
      ((readOutput policy after).map (publishResult policy (frame.read policy value).erase)) final
      (policy := policy) := by
  apply Stateful.AtomRel.function entered shape selected
  · exact reached ▸ invocations_exact.mpr (completed_raw path closed)
  · exact completed_priority path closed

end Mettapedia.Languages.MeTTa.HE.StatefulPriorityTraversal
