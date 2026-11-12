import Mettapedia.Languages.MeTTa.PeTTa.StreamingReturns

/-!
# Source rules for streaming control composition

The small-step rules distinguish ordinary source phases, alternatives,
packet delivery, collection, committed first demand and caught faults.
Ordinary phases cite the existing independent Unifying.Transition judgment;
the remaining rules describe the controller's own scheduling obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Unifying (Answer Control)
open List.FirstSelection (After)

def phaseControl : Control → Bool
  | .returned _ | .sequence _ _ | .fault _ => false
  | .evaluate _ (.expression [.symbol "collapse",_]) => false
  | .evaluate _ (.expression [.symbol "once",_]) => false
  | _ => true

theorem step_phase (registry : SpaceSemantics.Program) (state : State) (task : Task)
    (older : List Job) (agenda : state.agenda = .execute task :: older)
    (phase : phaseControl task.control = true) :
    step registry state =
      (Unifying.step registry (state.world.configuration task.control)).bind fun after =>
        enqueuePhase state after task.frames older := by
  simp only [step,agenda]
  split <;> simp_all [phaseControl]

inductive Transition (registry : SpaceSemantics.Program) : State → State → Prop where
  | collection_done {state : State} {key bindings caller answers older}
      (agenda : state.agenda = .collect key bindings caller answers :: older) :
      Transition registry state
        {state with
          world := {state.world with uses := state.world.uses + answers.length}
          agenda := .execute ⟨.returned
            [⟨.expression (Unifying.copies state.world.uses answers),bindings⟩],caller⟩ :: older}
  | handler_done {state : State} {key older}
      (agenda : state.agenda = .handler key :: older) :
      Transition registry state {state with agenda := older}
  | first_done {state : State} {key older}
      (agenda : state.agenda = .first key :: older) :
      Transition registry state {state with agenda := older}
  | empty {state : State} {frames older}
      (agenda : state.agenda = .execute ⟨.returned [],frames⟩ :: older) :
      Transition registry state {state with agenda := older}
  | answer {state target : State} {answer answers frames older}
      (agenda : state.agenda = .execute ⟨.returned (answer :: answers),frames⟩ :: older)
      (delivered : Delivery registry state answer frames (laterAnswers answers frames older) target) :
      Transition registry state target
  | alternatives {state : State} {controls answers frames older}
      (agenda : state.agenda = .execute ⟨.sequence controls answers,frames⟩ :: older) :
      Transition registry state
        {state with
          agenda := laterAnswers answers frames
            ((controls.map fun control => .execute ⟨control,frames⟩) ++ older)}
  | collection_enter {state : State} {bindings expression frames older}
      (agenda : state.agenda = .execute
        ⟨.evaluate bindings (.expression [.symbol "collapse",expression]),frames⟩ :: older) :
      Transition registry state (openCollection state bindings (.evaluate bindings expression) frames older)
  | first_enter {state : State} {bindings expression frames older}
      (agenda : state.agenda = .execute
        ⟨.evaluate bindings (.expression [.symbol "once",expression]),frames⟩ :: older) :
      Transition registry state (openFirst state (.evaluate bindings expression) frames older)
  | caught {state : State} {reason frames older key remaining}
      (agenda : state.agenda = .execute ⟨.fault reason,frames⟩ :: older)
      (handler : Handles frames key) (closed : After (handlerMarker key) older remaining) :
      Transition registry state {state with agenda := remaining}
  | phase {state target : State} {task older after}
      (agenda : state.agenda = .execute task :: older)
      (ordinary : phaseControl task.control = true)
      (source : Unifying.Transition registry (state.world.configuration task.control) after)
      (placed : Placement state after task.frames older target) :
      Transition registry state target

theorem Transition.computed {registry : SpaceSemantics.Program} {before after : State}
    (transition : Transition registry before after) : step registry before = some after := by
  cases transition with
  | collection_done agenda => simp only [step,agenda]
  | handler_done agenda => simp only [step,agenda]
  | first_done agenda => simp only [step,agenda]
  | empty agenda => simp only [step,agenda]
  | alternatives agenda => simp only [step,agenda]
  | collection_enter agenda => simp only [step,agenda]
  | first_enter agenda => simp only [step,agenda]
  | answer agenda delivered => simpa only [step,agenda] using delivered.computed
  | caught agenda handler closed =>
      simp only [step,agenda,handler.computed,bind,Option.bind_some,closed.computed]
  | phase agenda ordinary source placed =>
      rw [step_phase _ _ _ _ agenda ordinary]
      exact Option.bind_eq_some_iff.mpr ⟨_,Unifying.transition_step source,placed.computed⟩

inductive Intercepted : Control → Prop where
  | returned (answers) : Intercepted (.returned answers)
  | sequence (controls answers) : Intercepted (.sequence controls answers)
  | fault (reason) : Intercepted (.fault reason)
  | collection (bindings expression) : Intercepted (.evaluate bindings
      (.expression [.symbol "collapse",expression]))
  | first (bindings expression) : Intercepted (.evaluate bindings
      (.expression [.symbol "once",expression]))

theorem intercepted_of_not_phase (control : Control) (phase : phaseControl control ≠ true) :
    Intercepted control := by
  cases control with
  | returned answers => exact .returned answers
  | sequence controls answers => exact .sequence controls answers
  | fault reason => exact .fault reason
  | dynamic bindings head values => exact False.elim (phase rfl)
  | arguments bindings target rest held index => exact False.elim (phase rfl)
  | evaluate bindings expression =>
      unfold phaseControl at phase
      split at phase <;> aesop (add safe constructors Intercepted)

theorem transition_of_computed (registry : SpaceSemantics.Program) (before after : State)
    (computed : step registry before = some after) : Transition registry before after := by
  cases agenda : before.agenda with
  | nil => simp only [step,agenda] at computed; cases computed
  | cons job older =>
      cases job with
      | collect key bindings caller answers =>
          simp only [step,agenda,Option.some.injEq] at computed
          subst after
          exact .collection_done agenda
      | handler key =>
          simp only [step,agenda,Option.some.injEq] at computed
          subst after
          exact .handler_done agenda
      | first key =>
          simp only [step,agenda,Option.some.injEq] at computed
          subst after
          exact .first_done agenda
      | execute task =>
          by_cases ordinary : phaseControl task.control = true
          · rw [step_phase _ _ _ _ agenda ordinary] at computed
            obtain ⟨reached,source,placed⟩ := Option.bind_eq_some_iff.mp computed
            exact .phase agenda ordinary (Unifying.step_transition source)
              (placement_of_computed before reached task.frames older after placed)
          · have intercepted := intercepted_of_not_phase task.control ordinary
            rcases task with ⟨control,frames⟩
            cases intercepted with
            | returned answers =>
                cases answers with
                | nil =>
                    simp only [step,agenda,Option.some.injEq] at computed
                    subst after
                    exact .empty agenda
                | cons first rest =>
                    have delivered : returnAnswer registry before first frames
                        (laterAnswers rest frames older) = some after := by
                      simpa only [step,agenda] using computed
                    exact .answer agenda ((delivery_iff _ _ _ _ _ _).mp delivered)
            | sequence controls answers =>
                simp only [step,agenda,Option.some.injEq] at computed
                subst after
                exact .alternatives agenda
            | collection bindings expression =>
                simp only [step,agenda,Option.some.injEq] at computed
                subst after
                exact .collection_enter agenda
            | first bindings expression =>
                simp only [step,agenda,Option.some.injEq] at computed
                subst after
                exact .first_enter agenda
            | fault reason =>
                simp only [step,agenda,bind,Option.bind_eq_some_iff,Option.some.injEq] at computed
                obtain ⟨key,handler,remaining,closed,rfl⟩ := computed
                exact .caught agenda (handles_of_computed frames key handler)
                  ((List.FirstSelection.after_iff _ _ _).mp closed)

theorem step_iff_transition (registry : SpaceSemantics.Program) (before after : State) :
    step registry before = some after ↔ Transition registry before after :=
  ⟨transition_of_computed registry before after,Transition.computed⟩

end Mettapedia.Languages.MeTTa.PeTTa.Streaming
