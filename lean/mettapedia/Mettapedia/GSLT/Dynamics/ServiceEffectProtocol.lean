import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Submitted service calls followed by effectful continuations

A request is retained through three different transitions: the actual service
returns its indexed reply, an available continuation completes through a
supplied operational backend, and an exact answer occurrence is emitted.
Replies without continuations remain observable replies; they are not false
propositions or successful empty computations.

The backend relation is independent data. Its exactness hypothesis is used
only by the correspondence theorems, never by the transition constructors.
Clients must instantiate it with an actual implementation and prove that
implementation exact. The resulting OSLF predicate concerns three protocol
steps, not three arbitrary machine microsteps.

This is a typed protocol. It does not claim a parser or a decoder for raw
external requests or proof bytes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ServiceEffectProtocol

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uRequest uReply uState uAnswer uIntent

variable {Request : Type uRequest} {Reply : Request → Type uReply}
  {State : Type uState} {Answer : Type uAnswer} {Intent : Type uIntent}

/-- Actual invocation and continuation selection, without correctness fields. -/
structure Protocol (Request : Type uRequest) (Reply : Request → Type uReply)
    (State : Type uState) (Answer : Type uAnswer) (Intent : Type uIntent) where
  invoke : (request : Request) → Reply request
  continuation : (request : Request) → Reply request →
    Option (Program State Answer Intent)

abbrev Completion := Program State Answer Intent → State → BranchTrace →
  List (WorldResult State Answer Intent) → Prop

/-- Exact complete worlds, including branch identity, local state, intent
order and repeated answer occurrences. This is not only answer support. -/
def CompletionExact (complete : Completion (State := State) (Answer := Answer)
    (Intent := Intent)) : Prop :=
  ∀ program state branch worlds,
    complete program state branch worlds ↔ worlds = runWorldsAt program state branch

/-- The submitted request and actual reply survive completion and emission. -/
inductive Term (protocol : Protocol Request Reply State Answer Intent) where
  | request (input : Request) (initial : State) (branch : BranchTrace)
  | returned (input : Request) (initial : State) (branch : BranchTrace)
      (reply : Reply input)
  | completed (input : Request) (initial : State) (branch : BranchTrace)
      (reply : Reply input) (worlds : List (WorldResult State Answer Intent))
  | answer (input : Request) (initial : State) (branch : BranchTrace)
      (reply : Reply input) (worlds : List (WorldResult State Answer Intent))
      (occurrence : Fin worlds.length)

/-- Invocation is one service crossing. Continuation completion is licensed
by the supplied backend, not by a second call to a reference evaluator. -/
inductive Step (protocol : Protocol Request Reply State Answer Intent)
    (complete : Completion (State := State) (Answer := Answer) (Intent := Intent)) :
    Term protocol → Term protocol → Prop where
  | invoked (input : Request) (initial : State) (branch : BranchTrace) :
      Step protocol complete (.request input initial branch)
        (.returned input initial branch (protocol.invoke input))
  | completed {input initial branch reply program worlds}
      (selected : protocol.continuation input reply = some program)
      (execution : complete program initial branch worlds) :
      Step protocol complete (.returned input initial branch reply)
        (.completed input initial branch reply worlds)
  | emitted (input : Request) (initial : State) (branch : BranchTrace)
      (reply : Reply input) (worlds : List (WorldResult State Answer Intent))
      (occurrence : Fin worlds.length) :
      Step protocol complete (.completed input initial branch reply worlds)
        (.answer input initial branch reply worlds occurrence)

/-- The equations of protocol states are literal equality. This does not
identify a guest calculus's equations or native identity proofs with it. -/
abbrev gslt (protocol : Protocol Request Reply State Answer Intent)
    (complete : Completion (State := State) (Answer := Answer) (Intent := Intent)) : GSLT :=
  { Term := Term protocol
    equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
    rewrites := Step protocol complete
    rewrites_resp_left := by
      rintro source _ target rfl step
      exact ⟨target, step, rfl⟩
    rewrites_resp_right := by
      rintro source target _ step rfl
      exact step }

variable (protocol : Protocol Request Reply State Answer Intent)
  (complete : Completion (State := State) (Answer := Answer) (Intent := Intent))

theorem request_step_iff (input : Request) (initial : State) (branch : BranchTrace)
    (target : Term protocol) :
    (gslt protocol complete).Step (.request input initial branch) target ↔
      target = .returned input initial branch (protocol.invoke input) := by
  constructor
  · intro step
    cases step
    rfl
  · rintro rfl
    exact Step.invoked input initial branch

theorem returned_step_iff (input : Request) (initial : State) (branch : BranchTrace)
    (reply : Reply input) (target : Term protocol) :
    (gslt protocol complete).Step (.returned input initial branch reply) target ↔
      ∃ program worlds,
        protocol.continuation input reply = some program ∧
        complete program initial branch worlds ∧
        target = .completed input initial branch reply worlds := by
  constructor
  · intro step
    cases step with
    | completed selected execution => exact ⟨_, _, selected, execution, rfl⟩
  · rintro ⟨program, worlds, selected, execution, rfl⟩
    exact Step.completed selected execution

theorem completed_step_iff (input : Request) (initial : State) (branch : BranchTrace)
    (reply : Reply input) (worlds : List (WorldResult State Answer Intent))
    (target : Term protocol) :
    (gslt protocol complete).Step (.completed input initial branch reply worlds) target ↔
      ∃ occurrence : Fin worlds.length,
        target = .answer input initial branch reply worlds occurrence := by
  constructor
  · intro step
    cases step with
    | emitted _ _ _ _ _ occurrence => exact ⟨occurrence, rfl⟩
  · rintro ⟨occurrence, rfl⟩
    exact Step.emitted input initial branch reply worlds occurrence

/-- Lack of an executable continuation does not prevent the service reply
from existing, but it prevents continuation execution. -/
theorem no_step_of_no_continuation (input : Request) (initial : State)
    (branch : BranchTrace) (reply : Reply input)
    (absent : protocol.continuation input reply = none) (target : Term protocol) :
    ¬ (gslt protocol complete).Step (.returned input initial branch reply) target := by
  rw [returned_step_iff]
  rintro ⟨program, worlds, selected, _, _⟩
  rw [absent] at selected
  cases selected

def observesAnswer
    (observation : (input : Request) → Reply input → WorldResult State Answer Intent → Prop) :
    Term protocol → Prop
  | .answer input _ _ reply worlds occurrence => observation input reply (worlds.get occurrence)
  | _ => False

/-- A generated OSLF observation of the exact emitted occurrence. -/
def produces
    (observation : (input : Request) → Reply input → WorldResult State Answer Intent → Prop) :
    Term protocol → Prop :=
  gsltDiamond (gslt protocol complete)
    (gsltDiamond (gslt protocol complete)
      (gsltDiamond (gslt protocol complete) (observesAnswer protocol observation)))

/-- The generated three-stage modality retains the submitted request, actual
reply, selected continuation, complete world list and its exact occurrence. -/
theorem produces_request_iff
    (observation : (input : Request) → Reply input → WorldResult State Answer Intent → Prop)
    (input : Request) (initial : State) (branch : BranchTrace) :
    produces protocol complete observation (.request input initial branch) ↔
      ∃ program worlds, ∃ occurrence : Fin worlds.length,
        protocol.continuation input (protocol.invoke input) = some program ∧
        complete program initial branch worlds ∧
        observation input (protocol.invoke input) (worlds.get occurrence) := by
  unfold produces
  rw [gsltDiamond_spec]
  constructor
  · rintro ⟨replyTerm, invoked, meaning⟩
    obtain rfl := (request_step_iff protocol complete input initial branch replyTerm).mp invoked
    rw [gsltDiamond_spec] at meaning
    obtain ⟨completedTerm, completed, meaning⟩ := meaning
    obtain ⟨program, worlds, selected, execution, rfl⟩ :=
      (returned_step_iff protocol complete input initial branch _ completedTerm).mp completed
    rw [gsltDiamond_spec] at meaning
    obtain ⟨answerTerm, emitted, observed⟩ := meaning
    obtain ⟨occurrence, rfl⟩ :=
      (completed_step_iff protocol complete input initial branch _ worlds answerTerm).mp emitted
    exact ⟨program, worlds, occurrence, selected, execution, observed⟩
  · rintro ⟨program, worlds, occurrence, selected, execution, observed⟩
    refine ⟨.returned input initial branch (protocol.invoke input),
      Step.invoked input initial branch, ?_⟩
    rw [gsltDiamond_spec]
    refine ⟨.completed input initial branch (protocol.invoke input) worlds,
      Step.completed selected execution, ?_⟩
    rw [gsltDiamond_spec]
    exact ⟨.answer input initial branch (protocol.invoke input) worlds occurrence,
      Step.emitted input initial branch (protocol.invoke input) worlds occurrence, observed⟩

/-- Exactness belongs to the backend and transfers to the derived protocol
meaning. The protocol itself never defines backend execution by this result. -/
theorem produces_request_iff_worlds (exactness : CompletionExact complete)
    (observation : (input : Request) → Reply input → WorldResult State Answer Intent → Prop)
    (input : Request) (initial : State) (branch : BranchTrace) :
    produces protocol complete observation (.request input initial branch) ↔
      ∃ program, ∃ occurrence : Fin (runWorldsAt program initial branch).length,
        protocol.continuation input (protocol.invoke input) = some program ∧
        observation input (protocol.invoke input)
          ((runWorldsAt program initial branch).get occurrence) := by
  rw [produces_request_iff]
  constructor
  · rintro ⟨program, worlds, occurrence, selected, execution, observed⟩
    obtain rfl := (exactness program initial branch worlds).mp execution
    exact ⟨program, occurrence, selected, observed⟩
  · rintro ⟨program, occurrence, selected, observed⟩
    exact ⟨program, runWorldsAt program initial branch, occurrence, selected,
      (exactness program initial branch _).mpr rfl, observed⟩

/-- A stopped reply cannot acquire an answer observation through a backend. -/
theorem no_answer_of_no_continuation
    (observation : (input : Request) → Reply input → WorldResult State Answer Intent → Prop)
    (input : Request) (initial : State) (branch : BranchTrace)
    (absent : protocol.continuation input (protocol.invoke input) = none) :
    ¬ produces protocol complete observation (.request input initial branch) := by
  rw [produces_request_iff]
  rintro ⟨program, worlds, occurrence, selected, _, _⟩
  rw [absent] at selected
  cases selected

/-- The same stopped request still has a real, observable service reply. -/
theorem reply_remains_observable (input : Request) (initial : State) (branch : BranchTrace) :
    gsltDiamond (gslt protocol complete)
      (fun term => term = .returned input initial branch (protocol.invoke input))
      (.request input initial branch) := by
  rw [gsltDiamond_spec]
  exact ⟨_, Step.invoked input initial branch, rfl⟩

/-- A consumer can use a coarser world readout only when its own observation
factors through that readout. This never grants a different consumer access
to information that was forgotten. -/
theorem produces_readout_iff {View : Type*}
    (readout : WorldResult State Answer Intent → View)
    (observation : (input : Request) → Reply input → WorldResult State Answer Intent → Prop)
    (viewObservation : (input : Request) → Reply input → View → Prop)
    (factors : ∀ input reply world,
      observation input reply world ↔ viewObservation input reply (readout world))
    (input : Request) (initial : State) (branch : BranchTrace) :
    produces protocol complete observation (.request input initial branch) ↔
      produces protocol complete
        (fun input reply world => viewObservation input reply (readout world))
        (.request input initial branch) := by
  simp only [produces_request_iff, factors]

#print axioms produces_request_iff
#print axioms produces_request_iff_worlds
#print axioms no_answer_of_no_continuation
#print axioms produces_readout_iff

end Mettapedia.GSLT.Dynamics.ServiceEffectProtocol
