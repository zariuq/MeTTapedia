import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes
import Mettapedia.Machines.StoreAndDemand.FirstAnswer

/-!
# The actual streaming source as a first-answer provider

Only a packet at the root continuation is an answer. Progress executes an
actual controller step; exhaustion, raised faults and interruption remain
distinct. The common first-answer client stops without inspecting later
alternatives and retains the paid source residual. Provider request counts
are not a claim about native instructions or equal old evaluator cutoffs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming

open Unifying (Answer)
open Mettapedia.Machines.StoreAndDemand

def rootPacket (state : State) : Option Answer :=
  match state.agenda with
  | .execute ⟨.returned (answer :: _),[]⟩ :: _ => some answer
  | _ => none

def pull (registry : SpaceSemantics.Program) (state : State) :
    FirstAnswer.Reply Answer Effects.Fault × State :=
  match observe state with
  | .complete _ => (.exhausted,state)
  | .fault reason _ => (.raised reason,state)
  | .suspended _ =>
      match step registry state with
      | none => (.interrupted,state)
      | some reached =>
          match rootPacket state with
          | none => (.progress,reached)
          | some answer => (.answer answer,reached)

theorem pull_root (registry : SpaceSemantics.Program) (state : State) (answer : Answer)
    (answers : List Answer) (older : List Job)
    (agenda : state.agenda = .execute ⟨.returned (answer :: answers),[]⟩ :: older) :
    pull registry state = (.answer answer,
      {state with agenda := laterAnswers answers [] older,answers := state.answers ++ [answer]}) := by
  simp only [pull,observe,agenda,step,returnAnswer,rootPacket]

theorem progress_transition {registry : SpaceSemantics.Program} {before after : State}
    (progress : pull registry before = (.progress,after)) : Transition registry before after := by
  unfold pull at progress
  cases observation : observe before with
  | complete state => simp only [observation,Prod.mk.injEq] at progress; cases progress.1
  | fault reason state => simp only [observation,Prod.mk.injEq] at progress; cases progress.1
  | suspended state =>
      rw [observation] at progress
      cases taken : step registry before with
      | none => simp only [taken,Prod.mk.injEq] at progress; cases progress.1
      | some reached =>
          cases packet : rootPacket before with
          | none =>
              simp only [taken,packet,Prod.mk.injEq,true_and] at progress
              subst after
              exact transition_of_computed registry _ _ taken
          | some answer => simp only [taken,packet,Prod.mk.injEq] at progress; cases progress.1

theorem answer_transition {registry : SpaceSemantics.Program} {before after : State} {answer : Answer}
    (answered : pull registry before = (.answer answer,after)) : Transition registry before after := by
  unfold pull at answered
  cases observation : observe before with
  | complete state => simp only [observation,Prod.mk.injEq] at answered; cases answered.1
  | fault reason state => simp only [observation,Prod.mk.injEq] at answered; cases answered.1
  | suspended state =>
      rw [observation] at answered
      cases taken : step registry before with
      | none => simp only [taken,Prod.mk.injEq] at answered; cases answered.1
      | some reached =>
          cases packet : rootPacket before with
          | none => simp only [taken,packet,Prod.mk.injEq] at answered; cases answered.1
          | some value =>
              simp only [taken,packet,Prod.mk.injEq] at answered
              obtain ⟨_,rfl⟩ := answered
              exact transition_of_computed registry _ _ taken

theorem progress_path {registry : SpaceSemantics.Program} {before after : State} {count : Nat}
    (progress : FirstAnswer.Progress (pull registry) before count after) :
    Relation.ReflTransGen (Transition registry) before after := by
  induction progress with
  | nil => exact .refl
  | step observed _ ih => exact Relation.ReflTransGen.head (progress_transition observed) ih

/-- The common consumer is connected to the actual source provider. Its
prefix hypotheses are concrete pull steps, not a supplied execution equality. -/
theorem first_after_progress {registry : SpaceSemantics.Program} {before ready after : State} {count : Nat}
    (progress : FirstAnswer.Progress (pull registry) before count ready)
    (answer : Answer) (answered : pull registry ready = (.answer answer,after)) :
    Mettapedia.Machines.Cursor.advance (FirstAnswer.provider (pull registry))
      (FirstAnswer.client Answer Effects.Fault) (fun _ _ => 1) (count + 2)
      (FirstAnswer.start (pull registry) before) =
        (count + 1,.done ⟨(),FirstAnswer.Result.answer answer,after⟩) :=
  FirstAnswer.first_after_progress (pull registry) progress answer answered

theorem paid_first_answer_reachable {registry : SpaceSemantics.Program}
    {before ready after : State} {count : Nat}
    (progress : FirstAnswer.Progress (pull registry) before count ready)
    {answer : Answer} (answered : pull registry ready = (.answer answer,after)) :
    Relation.ReflTransGen (Transition registry) before after :=
  (progress_path progress).tail (answer_transition answered)

end Mettapedia.Languages.MeTTa.PeTTa.Streaming
