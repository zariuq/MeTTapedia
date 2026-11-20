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

theorem progress_exact {registry : SpaceSemantics.Program} {before after : State}
    (progress : pull registry before = (.progress,after)) :
    Transition registry before after ∧ rootPacket before = none := by
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
              exact ⟨transition_of_computed registry _ _ taken, rfl⟩
          | some answer => simp only [taken,packet,Prod.mk.injEq] at progress; cases progress.1

theorem progress_transition {registry : SpaceSemantics.Program} {before after : State}
    (progress : pull registry before = (.progress,after)) : Transition registry before after :=
  (progress_exact progress).1

/-- A paid answer on the root provider is a concrete delivery at its
empty caller, with exactly the uninspected suffix still on the agenda. -/
theorem answer_exact {registry : SpaceSemantics.Program} {before after : State} {answer : Answer}
    (answered : pull registry before = (.answer answer,after)) :
    ∃ rest older, before.agenda = .execute ⟨.returned (answer :: rest),[]⟩ :: older ∧
      after = {before with agenda := laterAnswers rest [] older, answers := before.answers ++ [answer]} := by
  have atRoot : rootPacket before = some answer := by
    unfold pull at answered
    cases observed : observe before with
    | complete state => simp only [observed,Prod.mk.injEq] at answered; cases answered.1
    | fault reason state => simp only [observed,Prod.mk.injEq] at answered; cases answered.1
    | suspended state =>
      rw [observed] at answered
      cases taken : step registry before with
      | none => simp only [taken,Prod.mk.injEq] at answered; cases answered.1
      | some reached =>
        cases packet : rootPacket before with
        | none => simp only [taken,packet,Prod.mk.injEq] at answered; cases answered.1
        | some value =>
          simp only [taken,packet,Prod.mk.injEq,FirstAnswer.Reply.answer.injEq] at answered
          obtain ⟨rfl,_⟩ := answered
          rfl
  unfold rootPacket at atRoot
  split at atRoot
  · rename_i value rest older agenda
    obtain rfl := Option.some.inj atRoot
    rw [pull_root registry before value rest older agenda] at answered
    exact ⟨rest,older,agenda,(Prod.mk.inj answered).2.symm⟩
  · cases atRoot

theorem answer_transition {registry : SpaceSemantics.Program} {before after : State} {answer : Answer}
    (answered : pull registry before = (.answer answer,after)) : Transition registry before after := by
  obtain ⟨_,_,agenda,rfl⟩ := answer_exact answered
  exact .answer agenda (.root _)

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

/-- If preparation of a written query cannot complete, the provider
does not report either an empty answer or exhaustion. The location
answer and the caller stay at the paid frontier. -/
theorem query_capture_interrupted {registry : SpaceSemantics.Program}
    {before : State} {answer : Answer} {more : List Answer}
    {pattern body : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    {caller : List Frame} {older : List Job}
    (opened : before.agenda = .execute
      ⟨.returned (answer :: more),.source (.query pattern body) :: caller⟩ :: older)
    (unready : Unifying.queries before.world.state pattern body before.world.uses [answer] = none) :
    pull registry before = (.interrupted,before) ∧
      ∀ fuel, observe (advance registry fuel before) = .suspended before := by
  have source : Unifying.step registry (before.world.configuration (.returned [answer]) [.query pattern body]) =
      none := by simp [Unifying.step, World.configuration, unready]
  have stopped : step registry before = none := by
    simp [step, opened, returnAnswer, bind, source]
  have waiting : observe before = .suspended before := by simp [observe, opened]
  refine ⟨by simp [pull, waiting, stopped], fun fuel => ?_⟩
  rw [advance, Mettapedia.Machines.BoundedDeterministicRun.run_of_none _ _ stopped, waiting]

end Mettapedia.Languages.MeTTa.PeTTa.Streaming
