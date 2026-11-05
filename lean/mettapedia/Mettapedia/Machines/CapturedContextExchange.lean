import Mathlib.Data.List.Basic

/-!
# Exchanging retained dynamic contexts with their caller

The reference keeps outside state separately from a query's current dynamic
value and its inner restoration snapshots. The implementation keeps one active
value, a stack of saved values and an authoritative paused local snapshot.
On resume it rebases only the outermost saved slot to the current outside
value. Inner snapshots remain unchanged.

Only active capture frames are modeled. Native frame filtering, stack/pointer
validity, payload copying and callbacks, GC, atomicity and thread lifetime are
separate obligations. Protocol faults totalize unsupported activation order;
valid driver entry/leave pairing remains a native premise. Physical slices and
source accounts are not priced here.
An absent native snapshot means its storage is not authoritative; stale bits
in a disabled snapshot slot are unobservable in this model.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.CapturedContextExchange

universe u v
variable {Options : Type u}

inductive Stop where
  | complete
  | cancel
  deriving DecidableEq, Repr

inductive Action (Options : Type u) where
  | enter (value : Options)
  | exit
  | writeLocal (value : Options)
  | pause
  | outsideWrite (value : Options)
  | resume
  | stop (reason : Stop)
  | observe
  deriving DecidableEq, Repr

inductive Event (Options : Type u) where
  | entered (value : Options)
  | restored (value : Options)
  | localWritten (value : Options)
  | paused (outside : Options)
  | outsideWritten (value : Options)
  | resumed (value : Options)
  | stopped (reason : Stop)
  | observed (value : Options)
  | protocolFault
  deriving DecidableEq, Repr

structure Transition (State : Type v) (Options : Type u) where
  next : State
  events : List (Event Options)

namespace Reference

structure Capture (Options : Type u) where
  current : Options
  parents : List Options
  deriving DecidableEq, Repr

inductive State (Options : Type u) where
  | running (outside : Options) (capture : Option (Capture Options))
  | paused (outside : Options) (capture : Option (Capture Options))
  | finished (outside : Options)
  deriving DecidableEq, Repr

def localValue (outside : Options) : Option (Capture Options) → Options
  | none => outside
  | some capture => capture.current

def finish (outside : Options) (capture : Option (Capture Options)) (reason : Stop) :
    Transition (State Options) Options :=
  ⟨.finished outside,
    (match capture with
      | none => []
      | some capture => capture.parents.map Event.restored ++ [.restored outside]) ++ [.stopped reason]⟩

def step (state : State Options) : Action Options → Transition (State Options) Options
  | .enter value => match state with
      | .running outside none => ⟨.running outside (some ⟨value, []⟩), [.entered value]⟩
      | .running outside (some capture) =>
          ⟨.running outside (some ⟨value, capture.current :: capture.parents⟩), [.entered value]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .exit => match state with
      | .running outside (some ⟨_, parent :: rest⟩) =>
          ⟨.running outside (some ⟨parent, rest⟩), [.restored parent]⟩
      | .running outside (some ⟨_, []⟩) => ⟨.running outside none, [.restored outside]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .writeLocal value => match state with
      | .running _ none => ⟨.running value none, [.localWritten value]⟩
      | .running outside (some capture) =>
          ⟨.running outside (some {capture with current := value}), [.localWritten value]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .pause => match state with
      | .running outside capture => ⟨.paused outside capture, [.paused outside]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .outsideWrite value => match state with
      | .paused _ capture => ⟨.paused value capture, [.outsideWritten value]⟩
      | .finished _ => ⟨.finished value, [.outsideWritten value]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .resume => match state with
      | .paused outside capture =>
          ⟨.running outside capture, [.resumed (localValue outside capture)]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .stop reason => match state with
      | .running outside capture => finish outside capture reason
      | .paused outside capture =>
          let result := finish outside capture reason
          ⟨result.next, .resumed (localValue outside capture) :: result.events⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .observe =>
      ⟨state, [.observed (match state with
        | .running outside capture => localValue outside capture
        | .paused outside _ | .finished outside => outside)]⟩

end Reference

namespace Native

inductive State (Options : Type u) where
  | running (active : Options) (saved : List Options)
  | paused (active : Options) (saved : List Options) (snapshot : Option Options)
  | finished (active : Options)
  deriving DecidableEq, Repr

/-- The last active capture encountered in a top-first frame scan owns the
outer restoration slot. No value equality is used to identify that slot. -/
def outer : List Options → Option Options
  | [] => none
  | value :: rest => match outer rest with
      | none => some value
      | some outside => some outside

def replaceOuter (outside : Options) : List Options → List Options
  | [] => []
  | [_] => [outside]
  | first :: second :: rest => first :: replaceOuter outside (second :: rest)

def unwind : List Options → Options → Options × List (Event Options)
  | [], active => (active, [])
  | saved :: rest, _ =>
      let later := unwind rest saved
      (later.1, .restored saved :: later.2)

def finish (active : Options) (saved : List Options) (reason : Stop) :
    Transition (State Options) Options :=
  let result := unwind saved active
  ⟨.finished result.1, result.2 ++ [.stopped reason]⟩

def resume (active : Options) (saved : List Options) (snapshot : Option Options) :
    Transition (State Options) Options :=
  match snapshot with
  | none => ⟨.running active saved, [.resumed active]⟩
  | some localValue => ⟨.running localValue (replaceOuter active saved), [.resumed localValue]⟩

def step (state : State Options) : Action Options → Transition (State Options) Options
  | .enter value => match state with
      | .running active saved => ⟨.running value (active :: saved), [.entered value]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .exit => match state with
      | .running _ (saved :: rest) => ⟨.running saved rest, [.restored saved]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .writeLocal value => match state with
      | .running _ saved => ⟨.running value saved, [.localWritten value]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .pause => match state with
      | .running active saved => match outer saved with
          | none => ⟨.paused active saved none, [.paused active]⟩
          | some outside => ⟨.paused outside saved (some active), [.paused outside]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .outsideWrite value => match state with
      | .paused _ saved snapshot => ⟨.paused value saved snapshot, [.outsideWritten value]⟩
      | .finished _ => ⟨.finished value, [.outsideWritten value]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .resume => match state with
      | .paused active saved snapshot => resume active saved snapshot
      | _ => ⟨state, [.protocolFault]⟩
  | .stop reason => match state with
      | .running active saved => finish active saved reason
      | .paused active saved snapshot =>
          let resumed := resume active saved snapshot
          match resumed.next with
          | .running localValue frames =>
              let result := finish localValue frames reason
              ⟨result.next, resumed.events ++ result.events⟩
          | _ => ⟨state, [.protocolFault]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .observe =>
      ⟨state, [.observed (match state with
        | .running active _ | .paused active _ _ | .finished active => active)]⟩

end Native

theorem outer_append_singleton (inner : List Options) (outside : Options) :
    Native.outer (inner ++ [outside]) = some outside := by
  induction inner with
  | nil => rfl
  | cons first rest ih => simp [Native.outer, ih]

theorem replace_outer_preserves_inner_snapshots (inner : List Options) (old current : Options) :
    Native.replaceOuter current (inner ++ [old]) = inner ++ [current] := by
  induction inner with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second rest => exact congrArg (List.cons first) ih

theorem unwind_saved_slots_in_order (inner : List Options) (outside active : Options) :
    Native.unwind (inner ++ [outside]) active =
      (outside, inner.map Event.restored ++ [.restored outside]) := by
  induction inner generalizing active with
  | nil => rfl
  | cons first rest ih => simp [Native.unwind, ih]

/-- While paused, the last saved slot may be stale: the live outside value
is authoritative. Running rebases that boundary before any frame resumes. -/
def Represents : Reference.State Options → Native.State Options → Prop
  | .running outside none, .running active saved => saved = [] ∧ active = outside
  | .running outside (some capture), .running active saved =>
      saved = capture.parents ++ [outside] ∧ active = capture.current
  | .paused outside none, .paused active saved snapshot =>
      saved = [] ∧ snapshot = none ∧ active = outside
  | .paused outside (some capture), .paused active saved snapshot =>
      (∃ stale, saved = capture.parents ++ [stale]) ∧ snapshot = some capture.current ∧ active = outside
  | .finished outside, .finished active => active = outside
  | _, _ => False

theorem step_refines (reference : Reference.State Options) (native : Native.State Options)
    (represented : Represents reference native) (action : Action Options) :
    Represents (Reference.step reference action).next (Native.step native action).next ∧
      (Reference.step reference action).events = (Native.step native action).events := by
  cases reference with
  | running outside capture =>
      cases native with
      | running active saved =>
          cases capture with
          | none =>
              change saved = [] ∧ active = outside at represented
              obtain ⟨rfl, rfl⟩ := represented
              cases action <;>
                simp [Reference.step, Native.step, Reference.finish, Native.finish,
                  Native.unwind, Native.outer, Represents, Reference.localValue]
          | some capture =>
              rcases capture with ⟨current, parents⟩
              change saved = parents ++ [outside] ∧ active = current at represented
              obtain ⟨rfl, rfl⟩ := represented
              cases action <;>
                simp [Reference.step, Native.step, Reference.finish, Native.finish,
                  outer_append_singleton, unwind_saved_slots_in_order, Represents, Reference.localValue,
                  List.append_assoc]
              all_goals cases parents <;> simp
      | paused active saved snapshot => cases capture <;> cases represented
      | finished active => cases capture <;> cases represented
  | paused outside capture =>
      cases native with
      | paused active saved snapshot =>
          cases capture with
          | none =>
              change saved = [] ∧ snapshot = none ∧ active = outside at represented
              obtain ⟨rfl, rfl, rfl⟩ := represented
              cases action <;>
                simp [Reference.step, Native.step, Reference.finish, Native.finish,
                  Native.unwind, Native.resume, Represents, Reference.localValue]
          | some capture =>
              rcases capture with ⟨current, parents⟩
              change (∃ stale, saved = parents ++ [stale]) ∧
                snapshot = some current ∧ active = outside at represented
              obtain ⟨⟨stale, rfl⟩, rfl, rfl⟩ := represented
              cases action <;>
                simp [Reference.step, Native.step, Reference.finish, Native.finish,
                  Native.resume, replace_outer_preserves_inner_snapshots,
                  unwind_saved_slots_in_order, Represents, Reference.localValue]
      | running active saved => cases capture <;> cases represented
      | finished active => cases capture <;> cases represented
  | finished outside =>
      cases native with
      | finished active =>
          change active = outside at represented
          subst active
          cases action <;> simp [Reference.step, Native.step, Represents]
      | running active saved => cases represented
      | paused active saved snapshot => cases represented

def run {State : Type v} (step : State → Action Options → Transition State Options) :
    State → List (Action Options) → Transition State Options
  | state, [] => ⟨state, []⟩
  | state, action :: rest =>
      let first := step state action
      let later := run step first.next rest
      ⟨later.next, first.events ++ later.events⟩

/-- Finite physical interruptions and arbitrary intervening outside writes
preserve query-local state, complete restoration stacks and event chronology. -/
theorem finite_trace_refines (reference : Reference.State Options) (native : Native.State Options)
    (represented : Represents reference native) (actions : List (Action Options)) :
    Represents (run Reference.step reference actions).next (run Native.step native actions).next ∧
      (run Reference.step reference actions).events = (run Native.step native actions).events := by
  induction actions generalizing reference native with
  | nil => exact ⟨represented, rfl⟩
  | cons action rest ih =>
      obtain ⟨next, events⟩ := step_refines reference native represented action
      obtain ⟨final, later⟩ := ih _ _ next
      exact ⟨final, by simp only [run, events, later]⟩

theorem pause_saves_the_actual_local_context (parents : List Options) (outside current : Options) :
    Native.step (.running current (parents ++ [outside])) .pause =
      ⟨.paused outside (parents ++ [outside]) (some current), [.paused outside]⟩ := by
  simp [Native.step, outer_append_singleton]

theorem resume_refreshes_only_the_outer_boundary
    (parents : List Options) (stale outside current : Options) :
    Native.step (.paused outside (parents ++ [stale]) (some current)) .resume =
      ⟨.running current (parents ++ [outside]), [.resumed current]⟩ := by
  simp [Native.step, Native.resume, replace_outer_preserves_inner_snapshots]

theorem running_finish_restores_the_boundary (parents : List Options)
    (outside current : Options) (reason : Stop) :
    Native.step (.running current (parents ++ [outside])) (.stop reason) =
      ⟨.finished outside, parents.map Event.restored ++ [.restored outside, .stopped reason]⟩ := by
  simp [Native.step, Native.finish, unwind_saved_slots_in_order, List.append_assoc]

/-- Both normal completion and cancellation preserve intervening outside
writes. They first reenter the retained context, then restore every inner
snapshot and finally the current outside boundary. -/
theorem paused_finish_preserves_intervening_outside_state
    (parents : List Options) (stale outside current : Options) (reason : Stop) :
    Native.step (.paused outside (parents ++ [stale]) (some current)) (.stop reason) =
      ⟨.finished outside,
        .resumed current :: (parents.map Event.restored ++ [.restored outside, .stopped reason])⟩ := by
  simp [Native.step, Native.resume, Native.finish, replace_outer_preserves_inner_snapshots,
    unwind_saved_slots_in_order, List.append_assoc]

theorem uncaptured_resume_uses_live_outside_state (outside : Options) :
    Native.step (.paused outside [] none) .resume =
      ⟨.running outside [], [.resumed outside]⟩ := rfl

theorem exchange_roundtrip_without_outside_writes
    (parents : List Options) (outside current : Options) :
    run Native.step (.running current (parents ++ [outside])) [.pause, .resume] =
      ⟨.running current (parents ++ [outside]), [.paused outside, .resumed current]⟩ := by
  simp [run, pause_saves_the_actual_local_context, resume_refreshes_only_the_outer_boundary]

theorem paused_exchange_refreshes_boundary_without_query_work
    (parents : List Options) (stale outside current : Options) :
    run Native.step (.paused outside (parents ++ [stale]) (some current)) [.resume, .pause] =
      ⟨.paused outside (parents ++ [outside]) (some current), [.resumed current, .paused outside]⟩ := by
  simp [run, resume_refreshes_only_the_outer_boundary, pause_saves_the_actual_local_context]

namespace Controls

def initial : Native.State Nat := .running 0 []
def paused : Native.State Nat := .paused 7 [10, 0] (some 21)

theorem nested_snapshot_exchange_preserves_both_contexts :
    Native.step paused .resume = ⟨.running 21 [10, 7], [.resumed 21]⟩ ∧
      Native.step (Native.step paused .resume).next .exit = ⟨.running 10 [7], [.restored 10]⟩ := by
  exact ⟨rfl, rfl⟩

theorem pause_hides_the_query_local_value :
    let result := run Native.step initial [.enter 10, .enter 20, .writeLocal 21, .pause, .observe]
    result.next = .paused 0 [10, 0] (some 21) ∧
      result.events = [.entered 10, .entered 20, .localWritten 21, .paused 0, .observed 0] := by decide

theorem uncaptured_pause_has_no_stale_local_snapshot :
    let result := run Native.step initial [.pause, .outsideWrite 5, .resume, .stop .complete]
    result.next = .finished 5 ∧
      result.events = [.paused 0, .outsideWritten 5, .resumed 5, .stopped .complete] := by decide

theorem repeated_pauses_keep_the_latest_outside_update :
    let result := run Native.step initial [.enter 10, .enter 20, .writeLocal 21,
      .pause, .outsideWrite 7, .resume, .exit, .pause, .outsideWrite 9, .resume, .stop .cancel]
    result.next = .finished 9 ∧
      result.events = [.entered 10, .entered 20, .localWritten 21, .paused 0, .outsideWritten 7,
        .resumed 21, .restored 10, .paused 7, .outsideWritten 9, .resumed 10,
        .restored 9, .stopped .cancel] := by decide

theorem completion_and_cancellation_restore_in_the_same_order :
    (Native.step paused (.stop .complete)).events =
        [.resumed 21, .restored 10, .restored 7, .stopped .complete] ∧
      (Native.step paused (.stop .cancel)).events =
        [.resumed 21, .restored 10, .restored 7, .stopped .cancel] := by decide

theorem cancellation_from_pause_preserves_outside_writes :
    (Native.step paused (.stop .cancel)).next = .finished 7 := by decide

theorem reentry_without_query_progress_still_refreshes_the_boundary :
    (run Native.step paused [.resume, .pause]).next = .paused 7 [10, 7] (some 21) := by decide

theorem stale_outer_saved_slot_loses_intervening_outside_state :
    let correct := (Native.step paused .resume).next
    let faulty : Native.State Nat := .running 21 [10, 0]
    (Native.step correct (.stop .complete)).next = .finished 7 ∧
      (Native.step faulty (.stop .complete)).next = .finished 0 := by decide

/-- A correct final outside value alone would miss the wrong context used
while the query body resumes. -/
theorem dropped_local_snapshot_changes_the_running_observation :
    let correct := (Native.step paused .resume).next
    let faulty : Native.State Nat := .running 7 [10, 7]
    (Native.step correct (.stop .complete)).next = (Native.step faulty (.stop .complete)).next ∧
      (Native.step correct .observe).events = [.observed 21] ∧
      (Native.step faulty .observe).events = [.observed 7] := by decide

theorem rebasing_all_saved_slots_destroys_the_inner_snapshot :
    let correct := (Native.step paused .resume).next
    let faulty : Native.State Nat := .running 21 [7, 7]
    (Native.step correct (.stop .complete)).next = (Native.step faulty (.stop .complete)).next ∧
      (Native.step correct .exit).events = [.restored 10] ∧
      (Native.step faulty .exit).events = [.restored 7] := by decide

theorem reversed_unwind_has_a_different_result_and_trace :
    Native.unwind [10, 7] 21 = (7, [.restored 10, .restored 7]) ∧
      Native.unwind [7, 10] 21 = (10, [.restored 7, .restored 10]) := by decide

theorem leaking_local_context_while_paused_is_observable :
    let correct := (Native.step (.running 21 [10, 0]) .pause).next
    let faulty : Native.State Nat := .paused 21 [10, 0] (some 21)
    (Native.step correct .observe).events = [.observed 0] ∧
      (Native.step faulty .observe).events = [.observed 21] := by decide

theorem selecting_the_first_capture_is_not_the_outer_boundary :
    Native.outer [10, 0] = some 0 ∧ ([10, 0] : List Nat).head? = some 10 := by decide

theorem cancelling_without_reentry_restores_stale_outside_state :
    (Native.step paused (.stop .cancel)).next = .finished 7 ∧
      (Native.unwind [10, 0] 7).1 = 0 := by decide

theorem completed_context_does_not_undo_later_outside_updates :
    let finished := (Native.step paused (.stop .complete)).next
    (run Native.step finished [.outsideWrite 99, .observe]).events =
      [.outsideWritten 99, .observed 99] := by decide

end Controls

end Mettapedia.Machines.CapturedContextExchange
