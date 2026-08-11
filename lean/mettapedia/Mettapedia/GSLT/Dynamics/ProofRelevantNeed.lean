import Mettapedia.GSLT.Core.InteractionEvent

/-!
# A proof-relevant call-by-need cell protocol

This module isolates the generic cell protocol shared by lazy evaluators.  It
does not define an object-language evaluator: evaluation begins and commits an
already justified outcome through separate events.  A language realization
must supply the computation that licenses those commits.

The protocol distinguishes immutable origin inspection, first evaluation,
cached observation, stable faults, retryable faults, and explicit resampling.
Its events are `Type`-valued evidence and therefore retain occurrence identity
after endpoint erasure to a GSLT.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

universe uCell uOrigin uValue uStableFault uRetryableFault uCost

/-- Outcomes are polarized by their update behavior.  Values and stable faults
remain cached; a retryable fault reopens the suspension. -/
inductive Outcome
    (Value : Type uValue) (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) where
  | value (value : Value)
  | stableFault (fault : StableFault)
  | retryableFault (fault : RetryableFault)
deriving DecidableEq, Repr

/-- The local state of one named suspension cell.  Every live state retains
the immutable origin needed by non-forcing inspection. -/
inductive CellState
    (Origin : Type uOrigin) (Value : Type uValue)
    (StableFault : Type uStableFault) where
  | absent
  | suspended (origin : Origin)
  | evaluating (origin : Origin)
  | cachedValue (origin : Origin) (value : Value)
  | cachedStableFault (origin : Origin) (fault : StableFault)
deriving DecidableEq, Repr

namespace CellState

variable {Origin : Type uOrigin} {Value : Type uValue}
  {StableFault : Type uStableFault}

/-- Public origin inspection is partial only for an unallocated cell. -/
def origin? : CellState Origin Value StableFault -> Option Origin
  | .absent => none
  | .suspended origin => some origin
  | .evaluating origin => some origin
  | .cachedValue origin _ => some origin
  | .cachedStableFault origin _ => some origin

@[simp] theorem origin?_absent :
    (CellState.absent : CellState Origin Value StableFault).origin? = none :=
  rfl

@[simp] theorem origin?_suspended (origin : Origin) :
    (CellState.suspended origin : CellState Origin Value StableFault).origin? =
      some origin :=
  rfl

@[simp] theorem origin?_evaluating (origin : Origin) :
    (CellState.evaluating origin : CellState Origin Value StableFault).origin? =
      some origin :=
  rfl

@[simp] theorem origin?_cachedValue (origin : Origin) (value : Value) :
    (CellState.cachedValue origin value :
      CellState Origin Value StableFault).origin? = some origin :=
  rfl

@[simp] theorem origin?_cachedStableFault
    (origin : Origin) (fault : StableFault) :
    (CellState.cachedStableFault origin fault :
      CellState Origin Value StableFault).origin? = some origin :=
  rfl

end CellState

/-- Exact protocol events.  Cell identities and payloads remain data even when
two events authorize equal source and target states. -/
inductive Event
    (Cell : Type uCell) (Origin : Type uOrigin) (Value : Type uValue)
    (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) where
  | allocate (cell : Cell) (origin : Origin)
  | resample (source fresh : Cell) (origin : Origin)
  | beginEvaluation (cell : Cell) (origin : Origin)
  | commitValue (cell : Cell) (origin : Origin) (value : Value)
  | commitStableFault (cell : Cell) (origin : Origin) (fault : StableFault)
  | retry (cell : Cell) (origin : Origin) (fault : RetryableFault)
  | observeValue (cell : Cell) (origin : Origin) (value : Value)
  | observeStableFault
      (cell : Cell) (origin : Origin) (fault : StableFault)
  | inspectOrigin (cell : Cell) (origin : Origin)
deriving DecidableEq, Repr

namespace Event

variable {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
  {StableFault : Type uStableFault}
  {RetryableFault : Type uRetryableFault}

/-- Evaluation work is charged at the transition that claims ownership of an
unevaluated cell, not at every subsequent observation. -/
def evaluationCount :
    Event Cell Origin Value StableFault RetryableFault -> Nat
  | .beginEvaluation _ _ => 1
  | _ => 0

/-- Cached demands are explicit observations.  Non-forcing origin inspection
has its own event and is not counted as observing a computed outcome. -/
def outcomeObservationCount :
    Event Cell Origin Value StableFault RetryableFault -> Nat
  | .observeValue _ _ _ => 1
  | .observeStableFault _ _ _ => 1
  | _ => 0

/-- Origin inspection remains distinguishable from outcome observation. -/
def inspectionCount :
    Event Cell Origin Value StableFault RetryableFault -> Nat
  | .inspectOrigin _ _ => 1
  | _ => 0

end Event

/-! ## The typed cell protocol -/

variable {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
  {StableFault : Type uStableFault}

local notation "State" => CellState Origin Value StableFault

/-- A proof-relevant protocol edge for one fixed cell.  Evaluation itself is
deliberately outside this relation: a commit event is evidence that the guest
calculus or capability supplied the named outcome. -/
inductive Step (RetryableFault : Type uRetryableFault) (cell : Cell) :
    State -> Event Cell Origin Value StableFault RetryableFault -> State ->
      Type _ where
  | allocate (origin : Origin) :
      Step RetryableFault cell .absent (.allocate cell origin)
        (.suspended origin)
  | resample (source : Cell) (origin : Origin)
      (fresh : source = cell -> False) :
      Step RetryableFault cell .absent (.resample source cell origin)
        (.suspended origin)
  | beginEvaluation (origin : Origin) :
      Step RetryableFault cell (.suspended origin)
        (.beginEvaluation cell origin)
        (.evaluating origin)
  | commitValue (origin : Origin) (value : Value) :
      Step RetryableFault cell (.evaluating origin)
        (.commitValue cell origin value)
        (.cachedValue origin value)
  | commitStableFault (origin : Origin) (fault : StableFault) :
      Step RetryableFault cell (.evaluating origin)
        (.commitStableFault cell origin fault)
        (.cachedStableFault origin fault)
  | retry (origin : Origin) (fault : RetryableFault) :
      Step RetryableFault cell (.evaluating origin)
        (.retry cell origin fault)
        (.suspended origin)
  | observeValue (origin : Origin) (value : Value) :
      Step RetryableFault cell (.cachedValue origin value)
        (.observeValue cell origin value)
        (.cachedValue origin value)
  | observeStableFault (origin : Origin) (fault : StableFault) :
      Step RetryableFault cell (.cachedStableFault origin fault)
        (.observeStableFault cell origin fault)
        (.cachedStableFault origin fault)
  | inspectSuspended (origin : Origin) :
      Step RetryableFault cell (.suspended origin)
        (.inspectOrigin cell origin)
        (.suspended origin)
  | inspectEvaluating (origin : Origin) :
      Step RetryableFault cell (.evaluating origin)
        (.inspectOrigin cell origin)
        (.evaluating origin)
  | inspectValue (origin : Origin) (value : Value) :
      Step RetryableFault cell (.cachedValue origin value)
        (.inspectOrigin cell origin)
        (.cachedValue origin value)
  | inspectStableFault (origin : Origin) (fault : StableFault) :
      Step RetryableFault cell (.cachedStableFault origin fault)
        (.inspectOrigin cell origin)
        (.cachedStableFault origin fault)

/-- A chronological, occurrence-preserving protocol trace. -/
inductive Trace (RetryableFault : Type uRetryableFault) (cell : Cell) :
    State -> State -> Type _ where
  | refl (state : State) : Trace RetryableFault cell state state
  | tail {source middle target : State}
      (event : Event Cell Origin Value StableFault RetryableFault)
      (step : Step RetryableFault cell source event middle)
      (rest : Trace RetryableFault cell middle target) :
      Trace RetryableFault cell source target

namespace Trace

variable {RetryableFault : Type uRetryableFault} {cell : Cell}

/-- Retain the exact chronological event sequence. -/
def events : {source target : State} ->
    Trace RetryableFault cell source target ->
    List (Event Cell Origin Value StableFault RetryableFault)
  | _, _, .refl _ => []
  | _, _, .tail event _ rest => event :: rest.events

def evaluationCount : {source target : State} ->
    Trace RetryableFault cell source target -> Nat
  | _, _, .refl _ => 0
  | _, _, .tail event _ rest =>
      event.evaluationCount + rest.evaluationCount

def outcomeObservationCount :
    {source target : State} -> Trace RetryableFault cell source target -> Nat
  | _, _, .refl _ => 0
  | _, _, .tail event _ rest =>
      event.outcomeObservationCount + rest.outcomeObservationCount

def inspectionCount : {source target : State} ->
    Trace RetryableFault cell source target -> Nat
  | _, _, .refl _ => 0
  | _, _, .tail event _ rest =>
      event.inspectionCount + rest.inspectionCount

/-- Trace composition retains chronological occurrences. -/
def trans {source middle target : State}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    Trace RetryableFault cell source target :=
  match first with
  | .refl _ => second
  | .tail event step rest => .tail event step (rest.trans second)

@[simp] theorem events_trans {source middle target : State}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).events = first.events ++ second.events := by
  induction first with
  | refl => simp [trans, events]
  | tail event step rest inductionHypothesis =>
      simp only [trans, events, List.cons_append, inductionHypothesis]

@[simp] theorem evaluationCount_trans {source middle target : State}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).evaluationCount =
      first.evaluationCount + second.evaluationCount := by
  induction first with
  | refl => simp [trans, evaluationCount]
  | tail event step rest inductionHypothesis =>
      simp only [trans, evaluationCount, inductionHypothesis]
      omega

@[simp] theorem outcomeObservationCount_trans
    {source middle target : State}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).outcomeObservationCount =
      first.outcomeObservationCount + second.outcomeObservationCount := by
  induction first with
  | refl => simp [trans, outcomeObservationCount]
  | tail event step rest inductionHypothesis =>
      simp only [trans, outcomeObservationCount, inductionHypothesis]
      omega

@[simp] theorem inspectionCount_trans {source middle target : State}
    (first : Trace RetryableFault cell source middle)
    (second : Trace RetryableFault cell middle target) :
    (first.trans second).inspectionCount =
      first.inspectionCount + second.inspectionCount := by
  induction first with
  | refl => simp [trans, inspectionCount]
  | tail event step rest inductionHypothesis =>
      simp only [trans, inspectionCount, inductionHypothesis]
      omega

/-- A trace preserves every state predicate preserved by each of its exact
protocol events. -/
theorem preserves {P : State -> Prop} {source target : State}
    (closed : ∀ {before after : State}
      (event : Event Cell Origin Value StableFault RetryableFault),
      P before -> Step RetryableFault cell before event after -> P after)
    (trace : Trace RetryableFault cell source target) (initial : P source) :
    P target := by
  induction trace with
  | refl => exact initial
  | tail event step rest inductionHypothesis =>
      exact inductionHypothesis (closed event initial step)

/-- Evaluation count is zero along any invariant region whose outgoing
protocol events are non-evaluating. -/
theorem evaluationCount_eq_zero_of_invariant
    {P : State -> Prop} {source target : State}
    (closed : ∀ {before after : State}
      (event : Event Cell Origin Value StableFault RetryableFault),
      P before -> Step RetryableFault cell before event after ->
        event.evaluationCount = 0 ∧ P after)
    (trace : Trace RetryableFault cell source target) (initial : P source) :
    trace.evaluationCount = 0 := by
  induction trace with
  | refl => rfl
  | tail event step rest inductionHypothesis =>
      obtain ⟨eventZero, nextInvariant⟩ := closed event initial step
      simp [evaluationCount, eventZero, inductionHypothesis nextInvariant]

end Trace

/-! ## GSLT and interaction presentation -/

/-- Endpoint erasure of the typed protocol. -/
def cellTheory (RetryableFault : Type uRetryableFault) (cell : Cell) : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty
      (Sigma fun event : Event Cell Origin Value StableFault RetryableFault =>
        Step RetryableFault cell source event target)
  rewrites_resp_left := by
    intro source source' target equal edge
    subst source'
    exact ⟨target, edge, rfl⟩
  rewrites_resp_right := by
    intro source target target' edge equal
    subst target'
    exact edge

/-- The event itself is the interaction site.  Its indexed `Step` proof is
the occurrence evidence erased by the ordinary GSLT relation. -/
def interactionPresentation (RetryableFault : Type uRetryableFault)
    (cell : Cell) :
    InteractionPresentation
      (cellTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) RetryableFault cell) where
  Site := Event Cell Origin Value StableFault RetryableFault
  Event := fun event source target =>
    Step RetryableFault cell source event target
  sound := fun edge => ⟨⟨_, edge⟩⟩

/-- The presentation loses no cell-protocol edge. -/
theorem interactionPresentation_complete
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    (interactionPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell).Complete := by
  intro source target edge
  rcases edge with ⟨⟨event, evidence⟩⟩
  exact ⟨⟨event, evidence⟩⟩

/-- Every exact trace erases to ordinary finite GSLT reachability. -/
theorem Trace.toMultiStep {cell : Cell} {source target : State}
    (trace : Trace RetryableFault cell source target) :
    (cellTheory (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell).MultiStep source target := by
  induction trace with
  | refl state =>
      exact @GSLT.MultiStep.refl
        (cellTheory (Origin := Origin) (Value := Value)
          (StableFault := StableFault) RetryableFault cell) state
  | tail event step rest inductionHypothesis =>
      exact @GSLT.MultiStep.step
        (cellTheory (Origin := Origin) (Value := Value)
          (StableFault := StableFault) RetryableFault cell)
        _ _ _ ⟨⟨event, step⟩⟩ inductionHypothesis

/-! ## Protocol laws -/

/-- Inspection never forces or mutates a cell. -/
theorem inspect_preserves_state {cell : Cell} {origin : Origin}
    {source target : State}
    (step : Step RetryableFault cell source
      (.inspectOrigin cell origin) target) :
    target = source := by
  cases step <;> rfl

/-- A cached value cannot begin evaluation again. -/
theorem cachedValue_cannot_beginEvaluation
    (cell : Cell) (origin : Origin) (value : Value)
    (nextOrigin : Origin) (target : State) :
    IsEmpty
      (Step RetryableFault cell (.cachedValue origin value)
        (.beginEvaluation cell nextOrigin) target) :=
  ⟨by intro step; cases step⟩

/-- A cached stable fault cannot begin evaluation again. -/
theorem cachedStableFault_cannot_beginEvaluation
    (cell : Cell) (origin : Origin) (fault : StableFault)
    (nextOrigin : Origin) (target : State) :
    IsEmpty
      (Step RetryableFault cell (.cachedStableFault origin fault)
        (.beginEvaluation cell nextOrigin) target) :=
  ⟨by intro step; cases step⟩

/-- Every trace from a cached value consists only of observations and origin
inspections and therefore preserves the cache exactly. -/
theorem Trace.from_cachedValue_preserves
    {cell : Cell} {origin : Origin} {value : Value} {target : State}
    (trace : Trace RetryableFault cell (.cachedValue origin value) target) :
    target = .cachedValue origin value := by
  apply trace.preserves
    (P := fun state => state = .cachedValue origin value) ?_ rfl
  intro before after event beforeCached step
  subst before
  cases step <;> rfl

/-- Cached-value traces perform no new evaluation. -/
theorem Trace.from_cachedValue_no_evaluation
    {cell : Cell} {origin : Origin} {value : Value} {target : State}
    (trace : Trace RetryableFault cell (.cachedValue origin value) target) :
    trace.evaluationCount = 0 := by
  apply trace.evaluationCount_eq_zero_of_invariant
    (P := fun state => state = .cachedValue origin value) ?_ rfl
  intro before after event beforeCached step
  subst before
  cases step <;> exact ⟨rfl, rfl⟩

/-- Stable-fault traces also preserve the exact cached outcome. -/
theorem Trace.from_cachedStableFault_preserves
    {cell : Cell} {origin : Origin} {fault : StableFault} {target : State}
    (trace : Trace RetryableFault cell
      (.cachedStableFault origin fault) target) :
    target = .cachedStableFault origin fault := by
  apply trace.preserves
    (P := fun state => state = .cachedStableFault origin fault) ?_ rfl
  intro before after event beforeCached step
  subst before
  cases step <;> rfl

/-- Stable-fault observations perform no new evaluation. -/
theorem Trace.from_cachedStableFault_no_evaluation
    {cell : Cell} {origin : Origin} {fault : StableFault} {target : State}
    (trace : Trace RetryableFault cell
      (.cachedStableFault origin fault) target) :
    trace.evaluationCount = 0 := by
  apply trace.evaluationCount_eq_zero_of_invariant
    (P := fun state => state = .cachedStableFault origin fault) ?_ rfl
  intro before after event beforeCached step
  subst before
  cases step <;> exact ⟨rfl, rfl⟩

/-- Retryable faults reopen precisely the same immutable origin. -/
def retry_reopens (cell : Cell) (origin : Origin)
    (fault : RetryableFault) :
    Step (Origin := Origin) (Value := Value) (StableFault := StableFault)
      RetryableFault cell (.evaluating origin) (.retry cell origin fault)
      (.suspended origin) :=
  .retry origin fault

/-! ## Event-indexed cost -/

/-- Any exact event valuation induces the generic interaction-event cost
interface.  No endpoint factorization is assumed. -/
def eventCost (RetryableFault : Type uRetryableFault) (cell : Cell)
    (Cost : Type uCost)
    (cost : Event Cell Origin Value StableFault RetryableFault -> Cost) :
    (interactionPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell).EventCost Cost where
  cost := fun {site} {_source _target} _ => cost site

/-! ## Positive and negative canaries -/

namespace Canary

abbrev DemoState := CellState Nat Nat Nat
abbrev DemoEvent := Event Nat Nat Nat Nat Nat

def successfulTrace :
    Trace (Origin := Nat) (Value := Nat) (StableFault := Nat)
      (RetryableFault := Nat) 0 .absent (.cachedValue 7 11) :=
  .tail (.allocate 0 7) (.allocate 7)
    (.tail (.beginEvaluation 0 7) (.beginEvaluation 7)
      (.tail (.commitValue 0 7 11) (.commitValue 7 11)
        (.tail (.observeValue 0 7 11) (.observeValue 7 11)
          (.tail (.inspectOrigin 0 7) (.inspectValue 7 11)
            (.refl (.cachedValue 7 11))))))

theorem successfulTrace_counts :
    successfulTrace.evaluationCount = 1 ∧
      successfulTrace.outcomeObservationCount = 1 ∧
      successfulTrace.inspectionCount = 1 := by
  decide

/-- A retry is observably different from a stable fault: it reopens the cell
and permits a later evaluation. -/
def retryTrace :
    Trace (Origin := Nat) (Value := Nat) (StableFault := Nat)
      (RetryableFault := Nat) 0 (.suspended 7) (.evaluating 7) :=
  .tail (.beginEvaluation 0 7) (.beginEvaluation 7)
    (.tail (.retry 0 7 99) (.retry 7 99)
      (.tail (.beginEvaluation 0 7) (.beginEvaluation 7)
        (.refl (.evaluating 7))))

theorem retryTrace_evaluates_twice : retryTrace.evaluationCount = 2 := by
  decide

def demoCost :
    (interactionPresentation (Origin := Nat) (Value := Nat)
      (StableFault := Nat) (RetryableFault := Nat) 0).EventCost Nat :=
  eventCost (Origin := Nat) (Value := Nat) (StableFault := Nat)
    Nat 0 Nat fun event =>
    match event with
    | .observeValue _ _ _ => 1
    | .inspectOrigin _ _ => 2
    | _ => 0

def observedValue :
    (interactionPresentation (Origin := Nat) (Value := Nat)
      (StableFault := Nat) (RetryableFault := Nat) 0).Enabled
        (.cachedValue 7 11) where
  site := .observeValue 0 7 11
  target := .cachedValue 7 11
  evidence := .observeValue 7 11

def inspectedValue :
    (interactionPresentation (Origin := Nat) (Value := Nat)
      (StableFault := Nat) (RetryableFault := Nat) 0).Enabled
        (.cachedValue 7 11) where
  site := .inspectOrigin 0 7
  target := .cachedValue 7 11
  evidence := .inspectValue 7 11

/-- Equal endpoints do not determine cost: cached outcome observation and
non-forcing origin inspection are distinct events. -/
theorem cost_not_determined_by_endpoints :
    ¬ demoCost.FactorsThroughEndpoints := by
  apply demoCost.not_factorsThroughEndpoints_of_parallel_costs
    (first := observedValue.evidence) (second := inspectedValue.evidence)
  decide

/-- Negative canary: an absent cell cannot be inspected. -/
theorem absent_cannot_be_inspected (cell : Nat) (origin : Nat)
    (target : DemoState) :
    IsEmpty
      (Step (Origin := Nat) (Value := Nat) (StableFault := Nat)
        (RetryableFault := Nat) cell .absent
        (.inspectOrigin cell origin) target) :=
  ⟨by intro step; cases step⟩

end Canary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed
