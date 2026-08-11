import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Dynamics.ProofRelevantNeed

/-!
# Optional evaluation ownership for proof-relevant Need

Some Need machines require only a black-hole marker; concurrent or branching
machines additionally record which evaluator owns a cell.  Ownership is not
forced into the base protocol.  This module supplies an owned protocol and a
proved erasure into the owner-free protocol.

Commit and retry events carry the owner that began evaluation.  Their indexed
step constructors can therefore be formed only for the current owner.  The
erasure is operationally sound but intentionally non-injective: owner identity
is real information that the base Need GSLT does not observe.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed.Ownership

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.InteractionEvent

universe uCell uOwner uOrigin uValue uStableFault uRetryableFault

inductive CellState
    (Owner : Type uOwner) (Origin : Type uOrigin) (Value : Type uValue)
    (StableFault : Type uStableFault) where
  | absent
  | suspended (origin : Origin)
  | evaluating (origin : Origin) (owner : Owner)
  | cachedValue (origin : Origin) (value : Value)
  | cachedStableFault (origin : Origin) (fault : StableFault)
deriving DecidableEq, Repr

inductive Event
    (Cell : Type uCell) (Owner : Type uOwner) (Origin : Type uOrigin)
    (Value : Type uValue) (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) where
  | allocate (cell : Cell) (origin : Origin)
  | resample (source fresh : Cell) (origin : Origin)
  | beginEvaluation (cell : Cell) (origin : Origin) (owner : Owner)
  | commitValue (cell : Cell) (origin : Origin) (owner : Owner) (value : Value)
  | commitStableFault
      (cell : Cell) (origin : Origin) (owner : Owner) (fault : StableFault)
  | retry
      (cell : Cell) (origin : Origin) (owner : Owner) (fault : RetryableFault)
  | observeValue (cell : Cell) (origin : Origin) (value : Value)
  | observeStableFault
      (cell : Cell) (origin : Origin) (fault : StableFault)
  | inspectOrigin (cell : Cell) (origin : Origin)
deriving DecidableEq, Repr

variable {Cell : Type uCell} {Owner : Type uOwner} {Origin : Type uOrigin}
  {Value : Type uValue} {StableFault : Type uStableFault}

local notation "OwnedState" => CellState Owner Origin Value StableFault

/-- Exact owner-sensitive cell transitions. -/
inductive Step (RetryableFault : Type uRetryableFault) (cell : Cell) :
    OwnedState ->
      Event Cell Owner Origin Value StableFault RetryableFault ->
      OwnedState -> Type _ where
  | allocate (origin : Origin) :
      Step RetryableFault cell .absent (.allocate cell origin)
        (.suspended origin)
  | resample (source : Cell) (origin : Origin)
      (fresh : source = cell -> False) :
      Step RetryableFault cell .absent (.resample source cell origin)
        (.suspended origin)
  | beginEvaluation (origin : Origin) (owner : Owner) :
      Step RetryableFault cell (.suspended origin)
        (.beginEvaluation cell origin owner) (.evaluating origin owner)
  | commitValue (origin : Origin) (owner : Owner) (value : Value) :
      Step RetryableFault cell (.evaluating origin owner)
        (.commitValue cell origin owner value) (.cachedValue origin value)
  | commitStableFault
      (origin : Origin) (owner : Owner) (fault : StableFault) :
      Step RetryableFault cell (.evaluating origin owner)
        (.commitStableFault cell origin owner fault)
        (.cachedStableFault origin fault)
  | retry (origin : Origin) (owner : Owner) (fault : RetryableFault) :
      Step RetryableFault cell (.evaluating origin owner)
        (.retry cell origin owner fault) (.suspended origin)
  | observeValue (origin : Origin) (value : Value) :
      Step RetryableFault cell (.cachedValue origin value)
        (.observeValue cell origin value) (.cachedValue origin value)
  | observeStableFault (origin : Origin) (fault : StableFault) :
      Step RetryableFault cell (.cachedStableFault origin fault)
        (.observeStableFault cell origin fault)
        (.cachedStableFault origin fault)
  | inspectSuspended (origin : Origin) :
      Step RetryableFault cell (.suspended origin)
        (.inspectOrigin cell origin) (.suspended origin)
  | inspectEvaluating (origin : Origin) (owner : Owner) :
      Step RetryableFault cell (.evaluating origin owner)
        (.inspectOrigin cell origin) (.evaluating origin owner)
  | inspectValue (origin : Origin) (value : Value) :
      Step RetryableFault cell (.cachedValue origin value)
        (.inspectOrigin cell origin) (.cachedValue origin value)
  | inspectStableFault (origin : Origin) (fault : StableFault) :
      Step RetryableFault cell (.cachedStableFault origin fault)
        (.inspectOrigin cell origin) (.cachedStableFault origin fault)

/-- Forget evaluator ownership but retain cache status and outcome. -/
def eraseState : CellState Owner Origin Value StableFault ->
    ProofRelevantNeed.CellState Origin Value StableFault
  | .absent => .absent
  | .suspended origin => .suspended origin
  | .evaluating origin _ => .evaluating origin
  | .cachedValue origin value => .cachedValue origin value
  | .cachedStableFault origin fault => .cachedStableFault origin fault

/-- Forget evaluator ownership from an exact event. -/
def eraseEvent :
    Event Cell Owner Origin Value StableFault RetryableFault ->
      ProofRelevantNeed.Event Cell Origin Value StableFault RetryableFault
  | .allocate cell origin => .allocate cell origin
  | .resample source fresh origin => .resample source fresh origin
  | .beginEvaluation cell origin _ => .beginEvaluation cell origin
  | .commitValue cell origin _ value => .commitValue cell origin value
  | .commitStableFault cell origin _ fault =>
      .commitStableFault cell origin fault
  | .retry cell origin _ fault => .retry cell origin fault
  | .observeValue cell origin value => .observeValue cell origin value
  | .observeStableFault cell origin fault =>
      .observeStableFault cell origin fault
  | .inspectOrigin cell origin => .inspectOrigin cell origin

/-- Every owner-sensitive transition remains a valid base Need transition
after ownership erasure. -/
def Step.erase {RetryableFault : Type uRetryableFault} {cell : Cell}
    {source target : CellState Owner Origin Value StableFault}
    {event : Event Cell Owner Origin Value StableFault RetryableFault}
    (step : Step RetryableFault cell source event target) :
    ProofRelevantNeed.Step RetryableFault cell (eraseState source)
      (eraseEvent event) (eraseState target) := by
  cases step with
  | allocate => exact .allocate _
  | resample source origin fresh => exact .resample source origin fresh
  | beginEvaluation => exact .beginEvaluation _
  | commitValue => exact .commitValue _ _
  | commitStableFault => exact .commitStableFault _ _
  | retry => exact .retry _ _
  | observeValue => exact .observeValue _ _
  | observeStableFault => exact .observeStableFault _ _
  | inspectSuspended => exact .inspectSuspended _
  | inspectEvaluating => exact .inspectEvaluating _
  | inspectValue => exact .inspectValue _ _
  | inspectStableFault => exact .inspectStableFault _ _

/-! ## Owner-sensitive traces -/

/-- A chronological trace retains evaluator ownership on every event that
claims, commits, or reopens a cell. -/
inductive Trace (RetryableFault : Type uRetryableFault) (cell : Cell) :
    OwnedState -> OwnedState -> Type _ where
  | refl (state : OwnedState) : Trace RetryableFault cell state state
  | tail {source middle target : OwnedState}
      (event : Event Cell Owner Origin Value StableFault RetryableFault)
      (step : Step RetryableFault cell source event middle)
      (rest : Trace RetryableFault cell middle target) :
      Trace RetryableFault cell source target

namespace Trace

variable {RetryableFault : Type uRetryableFault} {cell : Cell}

/-- Regard one exact event as a one-event trace. -/
def singleton {source target : OwnedState}
    (event : Event Cell Owner Origin Value StableFault RetryableFault)
    (step : Step RetryableFault cell source event target) :
    Trace RetryableFault cell source target :=
  .tail event step (.refl target)

/-- Retain the exact owner-sensitive event sequence. -/
def events : {source target : OwnedState} ->
    Trace RetryableFault cell source target ->
      List (Event Cell Owner Origin Value StableFault RetryableFault)
  | _, _, .refl _ => []
  | _, _, .tail event _ rest => event :: rest.events

@[simp] theorem events_singleton {source target : OwnedState}
    (event : Event Cell Owner Origin Value StableFault RetryableFault)
    (step : Step RetryableFault cell source event target) :
    (singleton event step).events = [event] :=
  rfl

/-- Owner-sensitive traces compose chronologically. -/
def trans {source middle target : OwnedState}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    Trace RetryableFault cell source target :=
  match first with
  | .refl _ => second
  | .tail event step rest => .tail event step (rest.trans second)

@[simp] theorem events_trans {source middle target : OwnedState}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).events = first.events ++ second.events := by
  induction first with
  | refl => simp [trans, events]
  | tail event step rest inductionHypothesis =>
      simp only [trans, events, List.cons_append, inductionHypothesis]

/-- Ownership erasure acts on whole traces, not merely isolated events. -/
def erase {source target : OwnedState}
    (trace : Trace RetryableFault cell source target) :
    ProofRelevantNeed.Trace RetryableFault cell (eraseState source)
      (eraseState target) :=
  match trace with
  | .refl state => .refl (eraseState state)
  | .tail event step rest =>
      .tail (eraseEvent event) step.erase rest.erase

@[simp] theorem erase_events {source target : OwnedState}
    (trace : Trace RetryableFault cell source target) :
    trace.erase.events = trace.events.map eraseEvent := by
  induction trace with
  | refl => rfl
  | tail event step rest inductionHypothesis =>
      simp only [erase, ProofRelevantNeed.Trace.events, events, List.map_cons,
        inductionHypothesis]

@[simp] theorem erase_trans {source middle target : OwnedState}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).erase = first.erase.trans second.erase := by
  induction first with
  | refl => rfl
  | tail event step rest inductionHypothesis =>
      simp only [trans, erase, inductionHypothesis,
        ProofRelevantNeed.Trace.trans]

end Trace

/-- Endpoint GSLT of the owned protocol. -/
def theory (RetryableFault : Type uRetryableFault) (cell : Cell) : GSLT where
  Term := CellState Owner Origin Value StableFault
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty (Sigma fun event => Step RetryableFault cell source event target)
  rewrites_resp_left := by
    intro source source' target equal edge
    subst source'
    exact ⟨target, edge, rfl⟩
  rewrites_resp_right := by
    intro source target target' edge equal
    subst target'
    exact edge

/-- Owner-sensitive interaction sites expose exact events while retaining
their indexed transition evidence. -/
def interactionPresentation (RetryableFault : Type uRetryableFault)
    (cell : Cell) :
    InteractionPresentation
      (theory (Owner := Owner) (Origin := Origin) (Value := Value)
        (StableFault := StableFault) RetryableFault cell) where
  Site := Event Cell Owner Origin Value StableFault RetryableFault
  Event := fun event source target =>
    Step RetryableFault cell source event target
  sound := fun evidence => ⟨⟨_, evidence⟩⟩

/-- The owner-sensitive presentation covers every endpoint step of its
theory; presentation does not discard any admitted event occurrence. -/
theorem interactionPresentation_complete
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    (interactionPresentation (Owner := Owner) (Origin := Origin)
      (Value := Value) (StableFault := StableFault)
      RetryableFault cell).Complete := by
  intro source target edge
  rcases edge with ⟨⟨event, evidence⟩⟩
  exact ⟨⟨event, evidence⟩⟩

/-- Owner erasure is an operational translation, not an asserted equality of
the two protocols. -/
def forgetOwnership (RetryableFault : Type uRetryableFault) (cell : Cell) :
    OperationalTranslation
      (theory (Owner := Owner) (Origin := Origin) (Value := Value)
        (StableFault := StableFault) RetryableFault cell)
      (ProofRelevantNeed.cellTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) RetryableFault cell) where
  mapTerm := eraseState
  mapEquiv := fun equal => congrArg eraseState equal
  mapStep := by
    intro source target edge
    rcases edge with ⟨⟨event, evidence⟩⟩
    exact ⟨⟨eraseEvent event, Step.erase evidence⟩⟩

/-! ## Separating canaries -/

namespace Canary

def ownedCommit :
    Step (Cell := Nat) (Owner := Bool) (Origin := Nat) (Value := Nat)
      (StableFault := Nat) Nat 0 (.evaluating 7 true)
      (.commitValue 0 7 true 11) (.cachedValue 7 11) :=
  .commitValue 7 true 11

theorem owned_commit_erases_to_need :
    Nonempty
      (ProofRelevantNeed.Step (Cell := Nat) (Origin := Nat) (Value := Nat)
        (StableFault := Nat) Nat 0 (.evaluating 7)
        (.commitValue 0 7 11) (.cachedValue 7 11)) :=
  ⟨Step.erase ownedCommit⟩

/-- The owner index rejects a commit by a different evaluator. -/
theorem wrong_owner_cannot_commit :
    IsEmpty
      (Step (Cell := Nat) (Owner := Bool) (Origin := Nat) (Value := Nat)
        (StableFault := Nat) Nat 0 (.evaluating 7 true)
        (.commitValue 0 7 false 11) (.cachedValue 7 11)) :=
  ⟨by intro impossible; cases impossible⟩

/-- Ownership is genuinely forgotten; the state map is not injective. -/
theorem eraseState_not_injective :
    ¬ Function.Injective
      (eraseState : CellState Bool Nat Nat Nat ->
        ProofRelevantNeed.CellState Nat Nat Nat) := by
  intro injective
  have equal := injective (show
    eraseState (CellState.evaluating 7 false) =
      eraseState (CellState.evaluating 7 true) from rfl)
  cases equal

end Canary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed.Ownership
