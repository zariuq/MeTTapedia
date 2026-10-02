import Mettapedia.Machines.IncrementalConformance.ForeignState

/-!
# Foreign lifecycle observations

The state simulation is strengthened to retain each call's success or rejection
through interleaved checkpoint, rollback, fork and cancellation commands. Each
step executes its foreign call once. A missing owner is a distinct protocol
observation, never silently reported as a successful solver call.

This uses the admitted pure finite-domain service of `ForeignState`. The model
does not turn rejection into a language-level exception or choose a search
policy. Native handlers still determine what rejection, missing ownership and
actual foreign exceptions mean at the language boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.ForeignStateTrace

open ForeignState

inductive Reply where
  | administrative
  | missingOwner
  | returned (accepted : Bool)
  deriving DecidableEq, Repr

variable {Owner Var Val Attr State : Type} [DecidableEq Owner]

/-- The call result is shared between reporting and the state update. -/
def step (call : Event Var Val Attr → State → Bool × State)
    (command : Command Owner Var Val Attr) (sessions : Sessions Owner State) :
    Reply × Sessions Owner State :=
  match command with
  | .call owner event =>
      match sessions owner with
      | none => (.missingOwner, sessions)
      | some frame =>
          let result := frame.call (call event)
          (.returned result.1, Function.update sessions owner (some result.2))
  | other => (.administrative, sessionStep call other sessions)

theorem step_state (call : Event Var Val Attr → State → Bool × State)
    (command : Command Owner Var Val Attr) (sessions : Sessions Owner State) :
    (step call command sessions).2 = sessionStep call command sessions := by
  cases command with
  | call owner event =>
      cases found : sessions owner with
      | none =>
          simp only [step, found, sessionStep, ForeignState.modify, Option.map_none]
          exact (Function.update_eq_self_iff.mpr found.symm).symm
      | some frame => simp [step, found, sessionStep, ForeignState.modify]
  | checkpoint owner => rfl
  | rollback owner => rfl
  | fork source target => rfl
  | cancel owner => rfl
  | cleanup => rfl

variable [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val]

theorem step_reply_related (command : Command Owner Var Val Attr)
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) :
    (step referenceCall command reference).1 = (step retainedCall command retained).1 := by
  cases command with
  | call owner event =>
      have atOwner := related owner
      cases hr : reference owner with
      | none =>
          have hn : retained owner = none := by
            cases hn : retained owner with
            | none => rfl
            | some n => rw [hr, hn] at atOwner; cases atOwner
          simp [step, hr, hn]
      | some r =>
          cases hn : retained owner with
          | none => rw [hr, hn] at atOwner; cases atOwner
          | some n =>
              rw [hr, hn] at atOwner
              have frames : FramesRelated r n := by cases atOwner; assumption
              simp only [step, hr, hn]
              exact congrArg Reply.returned (frame_call_related event frames).1
  | checkpoint owner => rfl
  | rollback owner => rfl
  | fork source target => rfl
  | cancel owner => rfl
  | cleanup => rfl

theorem step_related (command : Command Owner Var Val Attr)
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) :
    (step referenceCall command reference).1 = (step retainedCall command retained).1 ∧
    SessionsRelated (step referenceCall command reference).2
      (step retainedCall command retained).2 := by
  refine ⟨step_reply_related command related, ?_⟩
  rw [step_state, step_state]
  exact sessionStep_related command related

def run {State : Type} (call : Event Var Val Attr → State → Bool × State) :
    List (Command Owner Var Val Attr) → Sessions Owner State →
    List Reply × Sessions Owner State
  | [], sessions => ([], sessions)
  | command :: commands, sessions =>
      let now := step call command sessions
      let later := run call commands now.2
      (now.1 :: later.1, later.2)

/-- The observable verdict sequence is preserved as well as every branch's
current state and saved snapshots, for any finite lifecycle interleaving. -/
theorem run_related (commands : List (Command Owner Var Val Attr))
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) :
    (run referenceCall commands reference).1 = (run retainedCall commands retained).1 ∧
    SessionsRelated (run referenceCall commands reference).2
      (run retainedCall commands retained).2 := by
  induction commands generalizing reference retained with
  | nil => exact ⟨rfl, related⟩
  | cons command commands ih =>
      obtain ⟨same, next⟩ := step_related command related
      obtain ⟨tailSame, final⟩ := ih next
      exact ⟨congrArg₂ List.cons same tailSame, final⟩

namespace Controls

abbrev S := Retained Bool Bool Nat
abbrev E := Event Bool Bool Nat
abbrev C := Command Bool Bool Bool Nat

def start : Sessions Bool S := fun owner =>
  if owner then none else some ⟨initial, []⟩

def commands : List C :=
  [.call false (.post (.equal false true)), .checkpoint false,
   .call false (.post (.bind false true)),
   .call false (.post (.bind true false)), .rollback false,
   .call false (.post (.bind true false)), .cancel false,
   .call false (.putAttribute false 42)]

theorem rejection_rollback_and_cancellation_visible :
    (run retainedCall commands start).1 =
      [.returned true, .administrative, .returned true, .returned false,
       .administrative, .returned true, .administrative, .missingOwner] := by
  decide

/-- The same final state does not justify erasing a rejected-call report. -/
theorem final_state_does_not_determine_trace :
    (run retainedCall
      ([.call false (.post (.bind false true)),
        .call false (.post (.bind false false)), .cleanup] : List C) start).2 =
      (run retainedCall [.cleanup] start).2 ∧
    (run retainedCall
      ([.call false (.post (.bind false true)),
        .call false (.post (.bind false false)), .cleanup] : List C) start).1 ≠
      (run retainedCall [.cleanup] start).1 := by
  constructor
  · funext owner; rfl
  · decide

end Controls
end Mettapedia.Machines.IncrementalConformance.ForeignStateTrace
