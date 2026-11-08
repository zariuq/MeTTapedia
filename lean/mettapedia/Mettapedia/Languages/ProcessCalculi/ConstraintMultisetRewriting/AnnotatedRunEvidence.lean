import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes
import Mettapedia.GSLT.Coordination.Deduplication

/-!
# Evidence-rich histories over annotated runs

`HistoryMonad` records the event type it is given.  A thin firing alphabet
therefore cannot expose solver witnesses, origins, actors, search worlds or
query answers, even though the history construction itself loses none of
them.  This module separates that choice of alphabet from the underlying
step.

Successful firings carry arbitrary evidence and project to the existing
firing.  Non-firing attempts are recorded as loops.  Environment events are
kept as transitions in their own right: erasing them is sound only under an
additional hypothesis, because an input can change the state.  Thus there are
two honest forgetful maps:

* erase attempts to obtain a scripted run of firings and environment events;
* on an environment-free run, erase all evidence to obtain today's firing
  run.

No guard-cut field is introduced here.  Guard cuts remain owned by the
split-phase execution development.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence

open Mettapedia.GSLT

universe uF uRich uAttempt uEnvironment uState uWitness uProvenance uWorld uRound uAnswers
  uSchema uRenaming uActor uSource uPayload uKey

/-- Stable source information for one firing.  The schema and actor are
different: a fixed schema may have no installation occurrence, while a
standing rule has an actor whose revision and lifetime matter. -/
structure Provenance (Schema : Type uSchema) (Renaming : Type uRenaming)
    (Actor : Type uActor) where
  schema : Schema
  freshening : Renaming
  actor : Option Actor

/-- Evidence attached to one successful firing.  `firing` is the old event;
the other fields refine its history without changing its transition. -/
structure FiringEvidence (Firing : Type uF) (Witness : Type uWitness)
    (Provenance : Type uProvenance) (World : Type uWorld) (Round : Type uRound)
    (Answers : Type uAnswers) where
  firing : Firing
  witness : Witness
  provenance : Provenance
  world : World
  round : Round
  /-- Ordered scanner answers, guard verdicts or other evidence beyond the
  unordered occurrence identities already stored in `PredicateQueryAdmission.Query.seen`. -/
  queryEvidence : Answers

/-- A completed attempt that did not fire.  Its answer table and physical
charge remain observable even though its semantic state is unchanged. -/
structure AttemptRecord (Answers : Type uAnswers) (Task : Type uActor)
    (World : Type uWorld) (Round : Type uRound) where
  outcome : ContextualAttemptOutcomes.Outcome
  nonfiring : outcome ≠ .fired
  answers : Answers
  task : Task
  world : World
  round : Round
  charge : Nat

/-- Inputs come from a named source.  Outputs carry an idempotence key so a
replay can deliver them at most once. -/
inductive EnvironmentEvent (Source : Type uSource) (Payload : Type uPayload)
    (Key : Type uKey) where
  | input (source : Source) (payload : Payload)
  | output (key : Key) (payload : Payload)

/-- The richest finite event alphabet used here. -/
inductive Event (Firing : Type uRich) (Attempt : Type uAttempt)
    (Environment : Type uEnvironment) where
  | fired (firing : Firing)
  | attempted (attempt : Attempt)
  | environment (event : Environment)

namespace Event

variable {Firing : Type uRich} {Attempt : Type uAttempt} {Environment : Type uEnvironment}
  {Base : Type uF}

/-- Erase evidence from a successful firing and erase non-firing attempts.
Environment events remain explicit. -/
def core? (forget : Firing → Base) : Event Firing Attempt Environment → Option (Base ⊕ Environment)
  | .fired firing => some (.inl (forget firing))
  | .attempted _ => none
  | .environment event => some (.inr event)

/-- Erase every event except successful firings.  This is an execution
projection only for runs without environment events. -/
def firing? (forget : Firing → Base) : Event Firing Attempt Environment → Option Base
  | .fired firing => some (forget firing)
  | .attempted _ => none
  | .environment _ => none

end Event

variable {Firing : Type uRich} {Attempt : Type uAttempt} {Environment : Type uEnvironment}
  {Base : Type uF} {State : Type uState}

def coreWord (forget : Firing → Base) (events : List (Event Firing Attempt Environment)) :
    List (Base ⊕ Environment) :=
  events.filterMap (Event.core? forget)

def firingWord (forget : Firing → Base) (events : List (Event Firing Attempt Environment)) :
    List Base :=
  events.filterMap (Event.firing? forget)

@[simp] theorem coreWord_append (forget : Firing → Base)
    (first second : List (Event Firing Attempt Environment)) :
    coreWord forget (first ++ second) = coreWord forget first ++ coreWord forget second := by
  simp [coreWord]

@[simp] theorem firingWord_append (forget : Firing → Base)
    (first second : List (Event Firing Attempt Environment)) :
    firingWord forget (first ++ second) = firingWord forget first ++ firingWord forget second := by
  simp [firingWord]

/-- The history monad with a richer event alphabet.  Its step is exactly the
old labelled step after forgetting the evidence. -/
def liftLabels {S : GSLT} (labels : Mettapedia.GSLT.Causality.HistoryMonad.EventLabels S Base)
    (forget : Firing → Base) :
    Mettapedia.GSLT.Causality.HistoryMonad.EventLabels S Firing where
  labelled source target firing := labels.labelled source target (forget firing)
  sound := labels.sound
  resp_left := labels.resp_left
  resp_right := labels.resp_right

theorem lifted_history_step_iff {S : GSLT}
    (labels : Mettapedia.GSLT.Causality.HistoryMonad.EventLabels S Base)
    (forget : Firing → Base) {x y : S.Term × FreeMonoid Firing} :
    (Mettapedia.GSLT.Causality.HistoryMonad.history (liftLabels labels forget)).Step x y ↔
      ∃ firing, labels.labelled x.1 y.1 (forget firing) ∧
        y.2 = x.2 * FreeMonoid.of firing := by
  exact Mettapedia.GSLT.Causality.HistoryMonad.history_step_iff (liftLabels labels forget)

/-- The monoid homomorphism that forgets attempts, environment events and all
evidence fields while retaining the successful firing word. -/
def eraseHistory (forget : Firing → Base) :
    FreeMonoid (Event Firing Attempt Environment) → FreeMonoid Base :=
  FreeMonoid.lift fun
    | .fired firing => FreeMonoid.of (forget firing)
    | .attempted _ => 1
    | .environment _ => 1

@[simp] theorem eraseHistory_fired (forget : Firing → Base) (firing : Firing) :
    eraseHistory (Attempt := Attempt) (Environment := Environment) forget
      (FreeMonoid.of (.fired firing)) = FreeMonoid.of (forget firing) := by
  simp [eraseHistory]

@[simp] theorem eraseHistory_attempted (forget : Firing → Base) (attempt : Attempt) :
    eraseHistory (Firing := Firing) (Environment := Environment) forget
      (FreeMonoid.of (.attempted attempt)) = 1 := by
  simp [eraseHistory]

@[simp] theorem eraseHistory_environment (forget : Firing → Base) (event : Environment) :
    eraseHistory (Firing := Firing) (Attempt := Attempt) forget
      (FreeMonoid.of (.environment event)) = 1 := by
  simp [eraseHistory]

theorem eraseHistory_ofList (forget : Firing → Base)
    (events : List (Event Firing Attempt Environment)) :
    eraseHistory forget (FreeMonoid.ofList events) = FreeMonoid.ofList (firingWord forget events) := by
  rw [eraseHistory, FreeMonoid.lift_ofList]
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | fired firing =>
          simpa [firingWord, Event.firing?, FreeMonoid.ofList_cons] using
            congrArg (FreeMonoid.of (forget firing) * ·) ih
      | attempted attempt =>
          simpa [firingWord, List.filterMap_cons, Event.firing?] using ih
      | environment event =>
          simpa [firingWord, List.filterMap_cons, Event.firing?] using ih

/-- Scripted execution after non-firing attempts have been erased. -/
inductive CoreRun (step : Base → State → State → Prop)
    (environmentStep : Environment → State → State → Prop) :
    State → List (Base ⊕ Environment) → State → Prop where
  | nil (state) : CoreRun step environmentStep state [] state
  | firing {before middle after firing rest}
      (advanced : step firing before middle)
      (later : CoreRun step environmentStep middle rest after) :
      CoreRun step environmentStep before (.inl firing :: rest) after
  | environment {before middle after event rest}
      (advanced : environmentStep event before middle)
      (later : CoreRun step environmentStep middle rest after) :
      CoreRun step environmentStep before (.inr event :: rest) after

/-- Evidence-rich execution.  Attempts are loops by construction. -/
inductive Run (forget : Firing → Base) (step : Base → State → State → Prop)
    (environmentStep : Environment → State → State → Prop) :
    State → List (Event Firing Attempt Environment) → State → Prop where
  | nil (state) : Run forget step environmentStep state [] state
  | firing {before middle after firing rest}
      (advanced : step (forget firing) before middle)
      (later : Run forget step environmentStep middle rest after) :
      Run forget step environmentStep before (.fired firing :: rest) after
  | attempted {before after attempt rest}
      (later : Run forget step environmentStep before rest after) :
      Run forget step environmentStep before (.attempted attempt :: rest) after
  | environment {before middle after event rest}
      (advanced : environmentStep event before middle)
      (later : Run forget step environmentStep middle rest after) :
      Run forget step environmentStep before (.environment event :: rest) after

namespace Run

/-- Erasing non-firing attempts is a functor on finite executions. -/
theorem eraseAttempts {forget : Firing → Base} {step : Base → State → State → Prop}
    {environmentStep : Environment → State → State → Prop}
    {before after : State} {events : List (Event Firing Attempt Environment)}
    (run : Run forget step environmentStep before events after) :
    CoreRun step environmentStep before (coreWord forget events) after := by
  induction run with
  | nil state => exact .nil state
  | firing advanced later ih => exact .firing advanced ih
  | attempted later ih => exact ih
  | environment advanced later ih => exact .environment advanced ih

end Run

/-- An event word containing firings and attempts but no environment input or
output. -/
inductive NoEnvironment : List (Event Firing Attempt Environment) → Prop where
  | nil : NoEnvironment []
  | firing (firing : Firing) {rest} : NoEnvironment rest →
      NoEnvironment (.fired firing :: rest)
  | attempted (attempt : Attempt) {rest} : NoEnvironment rest →
      NoEnvironment (.attempted attempt :: rest)

/-- Today's firing-only execution relation. -/
inductive FiringRun (step : Base → State → State → Prop) :
    State → List Base → State → Prop where
  | nil (state) : FiringRun step state [] state
  | cons {before middle after firing rest} (advanced : step firing before middle)
      (later : FiringRun step middle rest after) :
      FiringRun step before (firing :: rest) after

namespace Run

/-- On an environment-free history, erasing attempts and evidence gives
exactly a run of today's firings. -/
theorem forget_noEnvironment {forget : Firing → Base} {step : Base → State → State → Prop}
    {environmentStep : Environment → State → State → Prop}
    {before after : State} {events : List (Event Firing Attempt Environment)}
    (run : Run forget step environmentStep before events after)
    (free : NoEnvironment events) :
    FiringRun step before (firingWord forget events) after := by
  induction run with
  | nil state => exact .nil state
  | firing advanced later ih =>
      cases free with
      | firing _ freeRest => exact .cons advanced (ih freeRest)
  | attempted later ih =>
      cases free with
      | attempted _ freeRest => exact ih freeRest
  | environment advanced later ih => cases free

end Run

/-- Determinism of one labelled transition family. -/
def Functional {Event State : Type*} (step : Event → State → State → Prop) : Prop :=
  ∀ event before first second, step event before first → step event before second → first = second

namespace Run

/-- Replay theorem: the same initial state, rich event word and deterministic
firing/environment interpreters have one final state. -/
theorem final_unique {forget : Firing → Base} {step : Base → State → State → Prop}
    {environmentStep : Environment → State → State → Prop}
    (stepFunctional : Functional step) (environmentFunctional : Functional environmentStep)
    {before first second : State} {events : List (Event Firing Attempt Environment)}
    (left : Run forget step environmentStep before events first)
    (right : Run forget step environmentStep before events second) : first = second := by
  induction left generalizing second with
  | nil state => cases right; rfl
  | @firing before middle after firing rest advanced later ih =>
      cases right with
      | firing advanced' later' =>
          have same := stepFunctional (forget firing) before middle _ advanced advanced'
          subst same
          exact ih later'
  | @attempted before after attempt rest later ih =>
      cases right with
      | attempted later' => exact ih later'
  | @environment before middle after event rest advanced later ih =>
      cases right with
      | environment advanced' later' =>
          have same := environmentFunctional event before middle _ advanced advanced'
          subst same
          exact ih later'

end Run

/-- Sum the cost of non-firing attempts.  It is intentionally invisible to
`eraseHistory`. -/
def attemptCharge {Answers Task World Round : Type*} :
    List (Event Firing (AttemptRecord Answers Task World Round) Environment) → Nat
  | [] => 0
  | .fired _ :: rest => attemptCharge rest
  | .attempted attempt :: rest => attempt.charge + attemptCharge rest
  | .environment _ :: rest => attemptCharge rest

@[simp] theorem attemptCharge_append {Answers Task World Round : Type*}
    (first second : List (Event Firing (AttemptRecord Answers Task World Round) Environment)) :
    attemptCharge (first ++ second) = attemptCharge first + attemptCharge second := by
  induction first with
  | nil => simp [attemptCharge]
  | cons event rest ih => cases event <;> simp [attemptCharge, ih, Nat.add_assoc]

namespace EnvironmentEvent

variable {Source : Type uSource} {Payload : Type uPayload} {Key : Type uKey}

def outputKey? : EnvironmentEvent Source Payload Key → Option Key
  | .input _ _ => none
  | .output key _ => some key

end EnvironmentEvent

def outputDeliveries {Source : Type uSource} {Payload : Type uPayload} {Key : Type uKey}
    (events : List (EnvironmentEvent Source Payload Key)) : List Key :=
  events.filterMap EnvironmentEvent.outputKey?

/-- Replayed output deliveries are applied at most once when their keys pass
through the existing deduplicating receiver. -/
theorem replayed_outputs_at_most_once {Source : Type uSource} {Payload : Type uPayload}
    {Key : Type uKey} [DecidableEq Key]
    (events : List (EnvironmentEvent Source Payload Key)) :
    (Mettapedia.GSLT.Coordination.Deduplication.receiveAll
      Mettapedia.GSLT.Coordination.Deduplication.Receiver.empty
      (outputDeliveries events)).applied.Nodup :=
  Mettapedia.GSLT.Coordination.Deduplication.applied_nodup _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence
