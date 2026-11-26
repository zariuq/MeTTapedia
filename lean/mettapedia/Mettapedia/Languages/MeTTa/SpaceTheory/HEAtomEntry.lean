import Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused

/-!
# HE's typed atom-entry boundary

Reading an activation and classifying the demand are separate from
interpreting a resulting instruction. Delivery does not inspect a
space. Casts and interpretation use the reached context's declarations.
The code that schedules the next request is determined by which
independent primitive judgment supplied the reply.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEAtomEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentService CastLookup CastResultRel Frame Policy Result WorldEnvironment diagnosticResults)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation Task)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith)
open HEFocused (Focus Parent Leaf)

structure Request where
  live : List Atom
  scope : List String
  value : Entry.Value
  expected : Atom
  frame : Frame

def Request.task (r : Request) : Task := .atom r.live r.scope r.value r.expected r.frame

def Request.recognize : Task → Option Request
  | .atom live scope value expected frame => some ⟨live, scope, value, expected, frame⟩
  | _ => none

@[simp] theorem Request.recognize_task (r : Request) : recognize r.task = some r := by cases r; rfl

theorem Request.recognize_exact {task : Task} {r : Request} (found : recognize task = some r) : r.task = task := by
  cases task <;> cases found
  rfl

theorem Request.task_injective : Function.Injective Request.task := by
  intro first second same
  have found := congrArg recognize same
  simpa only [recognize_task, Option.some.injEq] using found

def Request.read (p : Policy) (r : Request) : Entry.Value := r.frame.read p r.value

def Request.action (p : Policy) (r : Request) (a : Entry.Action) : Prop :=
  Entry.Rel p.reentry (r.read p).status (r.read p).erase r.expected a

inductive Reply where
  | deliver
  | cast (answers : List Result)
  | tuple (head : Entry.Value) (arguments : List Entry.Value)
  | selected (head : Entry.Value) (arguments : List Entry.Value) (signature : SelectedTypePolicy) (frames : List Frame)
  | fallback (head : Entry.Value) (arguments : List Entry.Value) (diagnostics : List Atom)
  | failed (head : Entry.Value) (arguments : List Entry.Value) (diagnostics : List Atom)

def Reply.action : Reply → Entry.Action
  | .deliver => .deliver
  | .cast _ => .cast
  | _ => .interpret

def Request.expression (p : Policy) (r : Request) (head : Entry.Value) (arguments : List Entry.Value) : Prop :=
  ∃ ready, r.read p = .expression ready (head :: arguments)

def Licensed (admission : ArgumentService) (space : Space) (lookup : CastLookup)
    (p : Policy) (r : Request) (reply : Reply) : Prop :=
  r.action p reply.action ∧
  match reply with
  | .deliver => True
  | .cast answers =>
    let types := lookup (invocationTypeScope r.scope r.live (r.read p).erase r.expected r.frame.bindings) space
    ∃ raw,
      TypeCastBatchRel space (r.read p).erase r.expected r.frame.bindings raw
        (lookup := types) (matching := p.matching.Rel) ∧
      List.Forall₂ (CastResultRel p types r.frame (r.read p) r.expected) raw answers
  | .tuple head arguments =>
    r.expression p head arguments ∧ TypeOccurrencesRel (space.atoms : Multiset Atom) head.erase {Atom.undefinedType}
  | .selected head arguments signature frames =>
    r.expression p head arguments ∧
      admission.selection space lookup p r.live r.scope (r.read p).erase head.erase r.expected r.frame
        (.selected signature frames)
  | .fallback head arguments errors =>
    r.expression p head arguments ∧
      admission.selection space lookup p r.live r.scope (r.read p).erase head.erase r.expected r.frame
        (.exhausted errors true)
  | .failed head arguments errors =>
    r.expression p head arguments ∧
      admission.selection space lookup p r.live r.scope (r.read p).erase head.erase r.expected r.frame
        (.exhausted errors false)

def continuation (p : Policy) (r : Request) : Reply → Leaf × List Continuation
  | .deliver => (.returning [(r.read p, r.frame)], [])
  | .cast answers => (.returning answers, [])
  | .tuple head arguments =>
    (.work (.tuple (r.expected :: r.live) r.scope (head :: arguments) r.frame),
      [.calls r.live r.scope r.expected, .publish (r.read p).erase])
  | .selected head arguments signature frames =>
    (.work (.invocations r.live r.scope r.expected signature head arguments frames), [.publish (r.read p).erase])
  | .fallback head arguments errors =>
    (.work (.tuple (r.expected :: r.live) r.scope (head :: arguments) r.frame),
      [.calls r.live r.scope r.expected, .diagnostics errors r.frame, .publish (r.read p).erase])
  | .failed _ _ errors =>
    (.returning (diagnosticResults errors r.frame), [.publish (r.read p).erase])

variable {Context World : Type}

theorem step_iff (env : WorldEnvironment Context World) (policy : Policy)
    (r : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (next : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup policy
      ⟨world, scope, .work r.task, stack, parents, emitted⟩ next ↔
      ∃ reply, Licensed env.arguments (env.view world scope) env.lookup policy r reply ∧
        next = ⟨world, scope, (continuation policy r reply).1, (continuation policy r reply).2 ++ stack,
          parents, emitted⟩ := by
  constructor
  · intro moved
    rcases r with ⟨live, names, value, expected, frame⟩
    cases moved with
    | perform step =>
      change WorldLocalStepWith env.arguments env.view env.services env.dispatch env.lookup policy world scope
        (.work (.atom live names value expected frame), stack) _ _ at step
      cases step with
      | core incoming _ localStep outgoing =>
        cases incoming
        cases localStep with
        | delivered entry =>
          cases outgoing
          exact ⟨.deliver, ⟨entry, trivial⟩, rfl⟩
        | cast entry checked leaves =>
          cases outgoing
          exact ⟨.cast _, ⟨entry, _, checked, leaves⟩, rfl⟩
        | atomTuple entry expression types =>
          cases outgoing
          exact ⟨.tuple _ _, ⟨entry, ⟨_, expression⟩, types⟩, rfl⟩
        | atomFunction entry expression signatures =>
          cases outgoing
          exact ⟨.selected _ _ _ _, ⟨entry, ⟨_, expression⟩, signatures⟩, rfl⟩
        | atomFallback entry expression signatures =>
          cases outgoing
          exact ⟨.fallback _ _ _, ⟨entry, ⟨_, expression⟩, signatures⟩, rfl⟩
        | atomSelectionFailed entry expression signatures =>
          cases outgoing
          exact ⟨.failed _ _ _, ⟨entry, ⟨_, expression⟩, signatures⟩, rfl⟩
  · rintro ⟨reply, licensed, rfl⟩
    let before : Focus Context World := ⟨world, scope, .work r.task, stack, parents, emitted⟩
    cases reply with
    | deliver =>
      exact HEFocused.Move.perform (before := before) (.core (.work r.task) rfl (.delivered licensed.1) (.returning _))
    | cast answers =>
      obtain ⟨raw, read, projected⟩ := licensed.2
      exact HEFocused.Move.perform (before := before) (.core (.work r.task) rfl (.cast licensed.1 read projected) (.returning _))
    | tuple head args =>
      obtain ⟨⟨ready, value⟩, typed⟩ := licensed.2
      exact HEFocused.Move.perform (before := before) (.core (.work r.task) rfl (.atomTuple licensed.1 value typed) (.work _))
    | selected head args signature frames =>
      obtain ⟨⟨ready, value⟩, selected⟩ := licensed.2
      exact HEFocused.Move.perform (before := before) (.core (.work r.task) rfl (.atomFunction licensed.1 value selected) (.work _))
    | fallback head args errors =>
      obtain ⟨⟨ready, value⟩, fallback⟩ := licensed.2
      exact HEFocused.Move.perform (before := before) (.core (.work r.task) rfl (.atomFallback licensed.1 value fallback) (.work _))
    | failed head args errors =>
      obtain ⟨⟨ready, value⟩, rejected⟩ := licensed.2
      exact HEFocused.Move.perform (before := before)
        (.core (.work r.task) rfl (.atomSelectionFailed licensed.1 value rejected) (.returning _))

/-- The Atom demand has exactly the delivered outcome, regardless of
the space, the declarations, the dispatch, and the occurrence readiness. -/
theorem atom_demand_iff (env : WorldEnvironment Context World) (policy : Policy)
    (r : Request) (raw : r.expected = Atom.atomType) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) (next : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup policy
        ⟨world, scope, .work r.task, stack, parents, emitted⟩ next ↔
      next = ⟨world, scope, .returning [(r.read policy, r.frame)], stack, parents, emitted⟩ := by
  have deliver : r.action policy .deliver := by
    rw [Request.action, raw]
    exact Entry.atom_demand _ _ _
  rw [step_iff]
  constructor
  · rintro ⟨reply, licensed, follows⟩
    have same := Entry.functional licensed.1 deliver
    cases reply <;> first | exact follows | cases same
  · intro follows
    exact ⟨.deliver, ⟨deliver, trivial⟩, follows⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.HEAtomEntry
