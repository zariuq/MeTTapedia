import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceChannelBoundary
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Reduction
import Mettapedia.GSLT.Core.GSLT

/-!
# Located space/channel interaction

This module gives persistent space observation and linear channel contact one
shared, protocol-neutral state model.  A state maps locations to occurrence
stores.  The access mode remains explicit:

* `observe` leaves the complete network unchanged;
* `consume` removes one occurrence at one location;
* actions at distinct locations commute;
* competing consumes at one singleton location cannot both run.

The commuting theorem is a static scheduling license: an implementation may
execute distinct-location interactions in parallel without selecting a new
semantics.  Same-location contact remains an atomic transaction.

The final section connects this boundary to the direct `COMM` redex of the
MeTTa-calculus.  It concerns the direct rule shape; contextual and structural
closure remain the responsibility of the existing reduction modules.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open SpaceChannelBoundary
open Mettapedia.OSLF.MeTTaIL.Match

universe u v

variable {Location : Type u} {Atom : Type v}

/-- Whether an interaction observes an occurrence persistently or consumes
one occurrence linearly. -/
inductive AccessMode where
  | observe
  | consume
deriving DecidableEq, Repr

/-- A request is ordinary protocol data: mode, location, and sought atom. -/
structure Request (Location : Type u) (Atom : Type v) where
  mode : AccessMode
  location : Location
  atom : Atom

/-- A located network is a family of occurrence stores. -/
abbrev Network (Location : Type u) (Atom : Type v) :=
  Location → Store Atom

/-- Protocol-neutral access semantics over a located network. -/
inductive LocatedStep [DecidableEq Location] :
    AccessMode → Location → Atom →
      Network Location Atom → Network Location Atom → Prop where
  | observe {location : Location} {atom : Atom}
      {state : Network Location Atom}
      (present : atom ∈ state location) :
      LocatedStep .observe location atom state state
  | consume {location : Location} {atom : Atom}
      {state : Network Location Atom} (rest : Store Atom)
      (atLocation : state location = atom ::ₘ rest) :
      LocatedStep .consume location atom state
        (Function.update state location rest)

namespace LocatedStep

variable [DecidableEq Location]

theorem observe_iff
    {location : Location} {atom : Atom}
    {source target : Network Location Atom} :
    LocatedStep .observe location atom source target ↔
      atom ∈ source location ∧ target = source := by
  constructor
  · intro step
    cases step with
    | observe present => exact ⟨present, rfl⟩
  · rintro ⟨present, rfl⟩
    exact .observe present

theorem consume_iff
    {location : Location} {atom : Atom}
    {source target : Network Location Atom} :
    LocatedStep .consume location atom source target ↔
      ∃ rest,
        source location = atom ::ₘ rest ∧
        target = Function.update source location rest := by
  constructor
  · intro step
    cases step with
    | consume rest atLocation => exact ⟨rest, atLocation, rfl⟩
  · rintro ⟨rest, atLocation, rfl⟩
    exact .consume rest atLocation

/-- Every interaction is framed: locations other than the selected one are
unchanged. -/
theorem preserves_other_location
    {mode : AccessMode} {location other : Location} {atom : Atom}
    {source target : Network Location Atom}
    (different : other ≠ location)
    (step : LocatedStep mode location atom source target) :
    target other = source other := by
  cases step with
  | observe present => rfl
  | consume rest atLocation => simp [different]

/-- Located observation projects exactly to persistent observation of the
selected store. -/
theorem observe_projects_to_persistentRead
    {location : Location} {atom : Atom}
    {source target : Network Location Atom}
    (step : LocatedStep .observe location atom source target) :
    PersistentRead atom (source location) (target location) := by
  cases step with
  | observe present => exact .found present

/-- Located consumption projects exactly to a linear take at the selected
store. -/
theorem consume_projects_to_linearTake
    {location : Location} {atom : Atom}
    {source target : Network Location Atom}
    (step : LocatedStep .consume location atom source target) :
    LinearTake atom (source location) (target location) := by
  cases step with
  | consume rest atLocation =>
      simpa [atLocation] using (LinearTake.found (atom := atom) rest)

/-- Consuming a located occurrence decreases the local cardinality by one. -/
theorem consume_local_card
    {location : Location} {atom : Atom}
    {source target : Network Location Atom}
    (step : LocatedStep .consume location atom source target) :
    (source location).card = (target location).card + 1 :=
  linearTake_card (consume_projects_to_linearTake step)

/-- **Parallelization theorem.** Interactions at distinct locations form a
diamond, for every combination of persistent and linear access. -/
theorem distinct_locations_commute
    {firstMode secondMode : AccessMode}
    {firstLocation secondLocation : Location}
    {firstAtom secondAtom : Atom}
    {source afterFirst afterSecond : Network Location Atom}
    (different : firstLocation ≠ secondLocation)
    (first : LocatedStep firstMode firstLocation firstAtom source afterFirst)
    (second : LocatedStep secondMode secondLocation secondAtom source afterSecond) :
    ∃ joined,
      LocatedStep secondMode secondLocation secondAtom afterFirst joined ∧
      LocatedStep firstMode firstLocation firstAtom afterSecond joined := by
  cases first with
  | observe firstPresent =>
      cases second with
      | observe secondPresent =>
          exact ⟨source, .observe secondPresent, .observe firstPresent⟩
      | consume secondRest secondAt =>
          refine ⟨Function.update source secondLocation secondRest,
            .consume secondRest secondAt, .observe ?_⟩
          simpa [Function.update_apply, different] using firstPresent
  | consume firstRest firstAt =>
      cases second with
      | observe secondPresent =>
          refine ⟨Function.update source firstLocation firstRest,
            .observe ?_, .consume firstRest firstAt⟩
          simpa [Function.update_apply, different.symm] using secondPresent
      | consume secondRest secondAt =>
          let joined :=
            Function.update
              (Function.update source firstLocation firstRest)
              secondLocation secondRest
          have secondStillAvailable :
              (Function.update source firstLocation firstRest) secondLocation =
                secondAtom ::ₘ secondRest := by
            simpa [Function.update_apply, different.symm] using secondAt
          have firstStillAvailable :
              (Function.update source secondLocation secondRest) firstLocation =
                firstAtom ::ₘ firstRest := by
            simpa [Function.update_apply, different] using firstAt
          refine ⟨joined, .consume secondRest secondStillAvailable, ?_⟩
          have reverseStep :
              LocatedStep .consume firstLocation firstAtom
                (Function.update source secondLocation secondRest)
                (Function.update
                  (Function.update source secondLocation secondRest)
                  firstLocation firstRest) :=
            .consume firstRest firstStillAvailable
          simpa [joined, Function.update_comm different] using reverseStep

end LocatedStep

namespace Request

variable [DecidableEq Location]

/-- Execute the request through the shared located protocol. -/
def Steps (request : Request Location Atom)
    (source target : Network Location Atom) : Prop :=
  LocatedStep request.mode request.location request.atom source target

/-- Disjoint location footprints are the conservative independence test. -/
def Independent (first second : Request Location Atom) : Prop :=
  first.location ≠ second.location

/-- Request-level form of the parallelization theorem.  This is the interface
a scheduler or staged plan needs: independent requests may be reordered, and
both orders have a common residual. -/
theorem independent_commute
    {first second : Request Location Atom}
    {source afterFirst afterSecond : Network Location Atom}
    (independent : Independent first second)
    (firstStep : first.Steps source afterFirst)
    (secondStep : second.Steps source afterSecond) :
    ∃ joined,
      second.Steps afterFirst joined ∧ first.Steps afterSecond joined :=
  LocatedStep.distinct_locations_commute independent firstStep secondStep

end Request

/-! ## Positive and negative located examples -/

variable [DecidableEq Location]

/-- A network with one occurrence at one location. -/
def singletonNetwork (location : Location) (atom : Atom) :
    Network Location Atom :=
  Function.update (fun _ => 0) location ({atom} : Store Atom)

theorem singletonNetwork_at (location : Location) (atom : Atom) :
    singletonNetwork location atom location = ({atom} : Store Atom) := by
  simp [singletonNetwork]

/-- Positive space example: the same located occurrence is persistently
observable twice. -/
theorem located_observe_singleton_twice (location : Location) (atom : Atom) :
    ∃ middle target,
      LocatedStep .observe location atom (singletonNetwork location atom) middle ∧
      LocatedStep .observe location atom middle target := by
  refine ⟨singletonNetwork location atom, singletonNetwork location atom, ?_, ?_⟩
  · exact .observe (by simp [singletonNetwork])
  · exact .observe (by simp [singletonNetwork])

/-- Negative channel example: two consumes compete for one occurrence at the
same location. -/
theorem located_consume_singleton_not_twice (location : Location) (atom : Atom) :
    ¬ ∃ middle target,
      LocatedStep .consume location atom (singletonNetwork location atom) middle ∧
      LocatedStep .consume location atom middle target := by
  rintro ⟨middle, target, first, second⟩
  have firstProjection := LocatedStep.consume_projects_to_linearTake first
  have secondProjection := LocatedStep.consume_projects_to_linearTake second
  apply linearTake_singleton_not_twice atom
  refine ⟨target location, middle location, ?_, secondProjection⟩
  simpa [singletonNetwork] using firstProjection

/-! ## Guarded transactional interaction

The single located requests above isolate access to one occurrence.  A useful
interaction step needs one further layer: several patterned guards share one
binding environment, their occurrence accesses happen atomically, and an
authored continuation publishes the residual work.  Keeping those three
parts separate prevents matching, persistence, and control from being hidden
inside one overloaded instruction.

The matcher remains a parameter.  It may be first-order matching,
unification, a typed relation, or a capability-mediated predicate.  The same
environment is presented to every guard, so repeated-variable consistency is
part of the matching relation rather than an accident of execution order.
-/

namespace GuardedTransaction

universe w x

variable {Pattern : Type w} {Environment : Type x}

/-- A patterned access to one located occurrence. -/
structure Guard (Location : Type u) (Pattern : Type w) where
  mode : AccessMode
  location : Location
  pattern : Pattern

/-- One atom selected as the witness for a guard. -/
def Guard.request (guard : Guard Location Pattern) (atom : Atom) :
    Request Location Atom :=
  ⟨guard.mode, guard.location, atom⟩

/-- One occurrence published by a continuation. -/
structure Emission (Location : Type u) (Atom : Type v) where
  location : Location
  atom : Atom

/-- Publish one occurrence at its selected location. -/
def publish
    (emission : Emission Location Atom) (state : Network Location Atom) :
    Network Location Atom :=
  Function.update state emission.location
    (emission.atom ::ₘ state emission.location)

/-- Publish a finite continuation delta.  The carrier remains a multiset, so
duplicate emissions remain distinct occurrences. -/
def publishAll :
    List (Emission Location Atom) → Network Location Atom →
      Network Location Atom
  | [], state => state
  | emission :: rest, state => publishAll rest (publish emission state)

@[simp] theorem publishAll_nil
    (state : Network Location Atom) :
    publishAll ([] : List (Emission Location Atom)) state = state :=
  rfl

@[simp] theorem publishAll_cons
    (emission : Emission Location Atom)
    (rest : List (Emission Location Atom))
    (state : Network Location Atom) :
    publishAll (emission :: rest) state =
      publishAll rest (publish emission state) :=
  rfl

/-- A list of guards and selected atoms all agree with one shared binding
environment. -/
inductive MatchesAll
    (matchRel : Pattern → Atom → Environment → Prop) :
    List (Guard Location Pattern) → List Atom → Environment → Prop where
  | nil : MatchesAll matchRel [] [] environment
  | cons {guard : Guard Location Pattern} {atom : Atom}
      {guards : List (Guard Location Pattern)} {atoms : List Atom}
      (head : matchRel guard.pattern atom environment)
      (tail : MatchesAll matchRel guards atoms environment) :
      MatchesAll matchRel (guard :: guards) (atom :: atoms) environment

/-- The collective matching interface of a transaction.  Componentwise
matching is available as `MatchesAll`, while symmetric unification, joins,
typed premises, and external predicates may inspect the whole guard vector. -/
abbrev Selection (Location : Type u) (Atom : Type v)
    (Pattern : Type w) (Environment : Type x) :=
  List (Guard Location Pattern) → List Atom → Environment → Prop

/-- Every persistent guard is checked against the same pre-transaction
snapshot.  Consume guards are validated separately by `Consumes`, so guard
order cannot make an earlier claim hide data from a later observation. -/
inductive ObservesSnapshot :
    List (Guard Location Pattern) → List Atom →
      Network Location Atom → Prop where
  | nil {source : Network Location Atom} : ObservesSnapshot [] [] source
  | observe {location : Location} {pattern : Pattern} {atom : Atom}
      {guards : List (Guard Location Pattern)} {atoms : List Atom}
      {source : Network Location Atom}
      (present : atom ∈ source location)
      (tail : ObservesSnapshot guards atoms source) :
      ObservesSnapshot
        (⟨.observe, location, pattern⟩ :: guards) (atom :: atoms) source
  | consume {location : Location} {pattern : Pattern} {atom : Atom}
      {guards : List (Guard Location Pattern)} {atoms : List Atom}
      {source : Network Location Atom}
      (tail : ObservesSnapshot guards atoms source) :
      ObservesSnapshot
        (⟨.consume, location, pattern⟩ :: guards) (atom :: atoms) source

/-- Atomically claim every linear occurrence selected by the consume guards.
Persistent observations do not alter the residual.  Sequential removal is a
proof of availability with multiplicity; it is not the query snapshot. -/
inductive Consumes :
    List (Guard Location Pattern) → List Atom →
      Network Location Atom → Network Location Atom → Prop where
  | nil {source : Network Location Atom} : Consumes [] [] source source
  | observe {location : Location} {pattern : Pattern} {atom : Atom}
      {guards : List (Guard Location Pattern)} {atoms : List Atom}
      {source target : Network Location Atom}
      (tail : Consumes guards atoms source target) :
      Consumes (⟨.observe, location, pattern⟩ :: guards)
        (atom :: atoms) source target
  | consume {location : Location} {pattern : Pattern} {atom : Atom}
      {guards : List (Guard Location Pattern)} {atoms : List Atom}
      {source middle target : Network Location Atom}
      (head : LocatedStep .consume location atom source middle)
      (tail : Consumes guards atoms middle target) :
      Consumes (⟨.consume, location, pattern⟩ :: guards)
        (atom :: atoms) source target

/-- A guarded transaction contains no scheduler.  It says which patterned
occurrences are required and which finite delta its continuation emits for a
successful shared environment. -/
structure Command (Location : Type u) (Atom : Type v)
    (Pattern : Type w) (Environment : Type x) where
  guards : List (Guard Location Pattern)
  continuation : Environment → List (Emission Location Atom)

/-- The core interaction rule:

`guards match with environment; claim their occurrences; publish K(environment)`.

The residual access modes determine which inputs persist.  An unmatched
command has no transition and therefore remains inert at the surrounding
language level. -/
inductive Fires
    (selects : Selection Location Atom Pattern Environment)
    (command : Command Location Atom Pattern Environment) :
    Network Location Atom → Network Location Atom → Prop where
  | fire {atoms : List Atom} {environment : Environment}
      {residual : Network Location Atom}
      (selected : selects command.guards atoms environment)
      (observed : ObservesSnapshot command.guards atoms source)
      (consumed : Consumes command.guards atoms source residual) :
      Fires selects command source
        (publishAll (command.continuation environment) residual)

/-- Exact rule inversion for guarded transactional interaction. -/
theorem fires_iff
    (selects : Selection Location Atom Pattern Environment)
    (command : Command Location Atom Pattern Environment)
    (source target : Network Location Atom) :
    Fires selects command source target ↔
      ∃ atoms environment residual,
        selects command.guards atoms environment ∧
        ObservesSnapshot command.guards atoms source ∧
        Consumes command.guards atoms source residual ∧
        target = publishAll (command.continuation environment) residual := by
  constructor
  · intro step
    cases step with
    | @fire atoms environment residual selected observed consumed =>
        exact ⟨atoms, environment, residual, selected, observed, consumed, rfl⟩
  · rintro ⟨atoms, environment, residual, selected, observed, consumed, rfl⟩
    exact .fire selected observed consumed

/-- A family of enabled commands induces a genuine behavioral GSLT.  Command
selection is left relational: priority, fairness, exhaustive collection, and
bounded execution are profiles over this theory, not silently fixed here. -/
def theory
    (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop) :
    Mettapedia.GSLT.GSLT where
  Term := Network Location Atom
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target :=
    ∃ command, enabled command ∧ Fires selects command source target
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

@[simp] theorem theory_step_iff
    (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (source target : Network Location Atom) :
    (theory selects enabled).Step source target ↔
      ∃ command, enabled command ∧ Fires selects command source target :=
  Iff.rfl

/-- Quiescence is absence of an enabled transaction, not a distinguished
fallback answer. -/
theorem theory_normalForm_iff
    (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (source : Network Location Atom) :
    (theory selects enabled).IsNormalForm source ↔
      ∀ command, enabled command →
        ¬ ∃ target, Fires selects command source target := by
  constructor
  · intro normal command commandEnabled ⟨target, fires⟩
    exact normal ⟨target, command, commandEnabled, fires⟩
  · intro noCommand ⟨target, command, commandEnabled, fires⟩
    exact noCommand command commandEnabled ⟨target, fires⟩

/-! ### Concrete controls

These examples are intentionally not interpretations of a developing MeTTa
dialect.  They isolate two stable machine shapes.  Symmetric communication
uses two consuming guards.  An MM2-shaped transaction consumes its work
directive, observes data persistently, and emits both an answer and later
work.
-/

namespace Canary

inductive CanaryLocation where
  | control
  | data
  | output
deriving DecidableEq, Repr

inductive CanaryAtom where
  | exec
  | fact
  | answer
  | nextExec
  | done
  | leftParty
  | rightParty
  | leftResidual
  | rightResidual
deriving DecidableEq, Repr

/-- Exact matching is the smallest executable instance of the abstract
matcher. -/
def exactMatch (pattern atom : CanaryAtom) (_environment : Unit) : Prop :=
  pattern = atom

def exactSelection :
    Selection CanaryLocation CanaryAtom CanaryAtom Unit :=
  MatchesAll exactMatch

def source : Network CanaryLocation CanaryAtom
  | .control => {.exec}
  | .data => {.fact}
  | .output => 0

def afterExec : Network CanaryLocation CanaryAtom :=
  Function.update source .control 0

def mixedCommand : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards :=
    [⟨.consume, .control, .exec⟩,
      ⟨.observe, .data, .fact⟩]
  continuation _ :=
    [⟨.output, .answer⟩, ⟨.control, .nextExec⟩]

def mixedTarget : Network CanaryLocation CanaryAtom :=
  publishAll (mixedCommand.continuation ()) afterExec

/-- MM2-shaped positive control: the directive is consumed, the fact is
observed without consumption, and the continuation publishes an answer and a
new directive. -/
theorem mixed_command_fires :
    Fires exactSelection mixedCommand source mixedTarget := by
  apply Fires.fire (atoms := [.exec, .fact]) (environment := ())
      (residual := afterExec)
  · exact .cons rfl (.cons rfl .nil)
  · exact .consume (.observe (by simp [source]) .nil)
  · apply Consumes.consume
    · exact LocatedStep.consume (location := .control) (atom := .exec)
        (state := source) 0 rfl
    · exact .observe .nil

@[simp] theorem mixedTarget_control :
    mixedTarget .control = ({.nextExec} : Store CanaryAtom) := by
  simp [mixedTarget, mixedCommand, publishAll, publish, afterExec, source]

@[simp] theorem mixedTarget_data :
    mixedTarget .data = ({.fact} : Store CanaryAtom) := by
  simp [mixedTarget, mixedCommand, publishAll, publish, afterExec, source]

@[simp] theorem mixedTarget_output :
    mixedTarget .output = ({.answer} : Store CanaryAtom) := by
  simp [mixedTarget, mixedCommand, publishAll, publish, afterExec, source]

def followupResidual : Network CanaryLocation CanaryAtom :=
  Function.update mixedTarget .control 0

def followupCommand : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards :=
    [⟨.consume, .control, .nextExec⟩,
      ⟨.observe, .output, .answer⟩]
  continuation _ := [⟨.output, .done⟩]

def followupTarget : Network CanaryLocation CanaryAtom :=
  publishAll (followupCommand.continuation ()) followupResidual

/-- Generated work is genuinely available to a later internal interaction. -/
theorem followup_command_fires :
    Fires exactSelection followupCommand mixedTarget followupTarget := by
  apply Fires.fire (atoms := [.nextExec, .answer]) (environment := ())
      (residual := followupResidual)
  · exact .cons rfl (.cons rfl .nil)
  · exact .consume (.observe (by simp) .nil)
  · apply Consumes.consume
    · exact LocatedStep.consume (location := .control) (atom := .nextExec)
        (state := mixedTarget) 0 mixedTarget_control
    · exact .observe .nil

def enabled
    (command : Command CanaryLocation CanaryAtom CanaryAtom Unit) : Prop :=
  command = mixedCommand ∨ command = followupCommand

/-- The neutral GSLT has a two-step execution because the first continuation
emits the control occurrence selected by the second transaction. -/
theorem continuation_closes_the_loop :
    (theory exactSelection enabled).MultiStep source followupTarget := by
  apply Mettapedia.GSLT.GSLT.MultiStep.step
  · exact ⟨mixedCommand, Or.inl rfl, mixed_command_fires⟩
  · apply Mettapedia.GSLT.GSLT.MultiStep.step
    · exact ⟨followupCommand, Or.inr rfl, followup_command_fires⟩
    · exact Mettapedia.GSLT.GSLT.MultiStep.refl
        (S := theory exactSelection enabled) followupTarget

def empty : Network CanaryLocation CanaryAtom := fun _ => 0

def observingCommand : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards := [⟨.observe, .data, .fact⟩]
  continuation _ := [⟨.output, .answer⟩]

/-- Negative control: an unmatched patterned transaction has no step.  No
special error or fallback value is needed to make it inert. -/
theorem unmatched_is_inert (target : Network CanaryLocation CanaryAtom) :
    ¬ Fires exactSelection observingCommand empty target := by
  intro step
  cases step with
  | fire matched observed consumed =>
      cases observed with
      | observe present tail => simp [empty] at present

def singleFactSource : Network CanaryLocation CanaryAtom :=
  singletonNetwork .data .fact

def snapshotResidual : Network CanaryLocation CanaryAtom :=
  Function.update singleFactSource .data 0

def snapshotTarget : Network CanaryLocation CanaryAtom :=
  publishAll [⟨.output, .answer⟩] snapshotResidual

def consumeThenObserve : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards :=
    [⟨.consume, .data, .fact⟩,
      ⟨.observe, .data, .fact⟩]
  continuation _ := [⟨.output, .answer⟩]

def observeThenConsume : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards :=
    [⟨.observe, .data, .fact⟩,
      ⟨.consume, .data, .fact⟩]
  continuation _ := [⟨.output, .answer⟩]

/-- Observation is evaluated against the pre-transaction snapshot even when
the consuming claim is written first. -/
theorem consume_then_observe_fires :
    Fires exactSelection consumeThenObserve singleFactSource snapshotTarget := by
  apply Fires.fire (atoms := [.fact, .fact]) (environment := ())
      (residual := snapshotResidual)
  · exact .cons rfl (.cons rfl .nil)
  · exact .consume (.observe (by simp [singleFactSource, singletonNetwork]) .nil)
  · apply Consumes.consume
    · exact LocatedStep.consume (location := .data) (atom := .fact)
        (state := singleFactSource) 0
        (by simp [singleFactSource, singletonNetwork])
    · exact .observe .nil

/-- Reversing the written guard order reaches the same transaction target:
snapshot observation and linear claim are distinct phases. -/
theorem observe_then_consume_fires :
    Fires exactSelection observeThenConsume singleFactSource snapshotTarget := by
  apply Fires.fire (atoms := [.fact, .fact]) (environment := ())
      (residual := snapshotResidual)
  · exact .cons rfl (.cons rfl .nil)
  · exact .observe (by simp [singleFactSource, singletonNetwork]) (.consume .nil)
  · exact .observe (.consume
      (LocatedStep.consume (location := .data) (atom := .fact)
        (state := singleFactSource) 0
        (by simp [singleFactSource, singletonNetwork])) .nil)

def consumeTwice : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards :=
    [⟨.consume, .data, .fact⟩,
      ⟨.consume, .data, .fact⟩]
  continuation _ := []

/-- Negative multiplicity control: two linear claims cannot share one stored
occurrence, even though persistent observations may do so. -/
theorem consume_twice_singleton_cannot_fire
    (target : Network CanaryLocation CanaryAtom) :
    ¬ Fires exactSelection consumeTwice singleFactSource target := by
  intro step
  cases step with
  | fire matched observed consumed =>
      cases matched with
      | cons firstMatch matchedTail =>
          cases matchedTail with
          | cons secondMatch matchedNil =>
              cases firstMatch
              cases secondMatch
              cases consumed with
              | consume first tail =>
                  cases tail with
                  | consume second tail =>
                      apply located_consume_singleton_not_twice
                        CanaryLocation.data CanaryAtom.fact
                      exact ⟨_, _, first, second⟩

def contactSource : Network CanaryLocation CanaryAtom
  | .control => {.leftParty, .rightParty}
  | _ => 0

def afterLeft : Network CanaryLocation CanaryAtom :=
  Function.update contactSource .control ({.rightParty} : Store CanaryAtom)

def afterBoth : Network CanaryLocation CanaryAtom :=
  Function.update afterLeft .control 0

def symmetricCommand :
    Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards :=
    [⟨.consume, .control, .leftParty⟩,
      ⟨.consume, .control, .rightParty⟩]
  continuation _ :=
    [⟨.output, .leftResidual⟩, ⟨.output, .rightResidual⟩]

def contactTarget : Network CanaryLocation CanaryAtom :=
  publishAll (symmetricCommand.continuation ()) afterBoth

/-- MeTTa-calculus/rho-shaped positive control: both guarded parties are
linear claims and both residual continuations are published. -/
theorem symmetric_command_fires :
    Fires exactSelection symmetricCommand contactSource contactTarget := by
  apply Fires.fire (atoms := [.leftParty, .rightParty]) (environment := ())
      (residual := afterBoth)
  · exact .cons rfl (.cons rfl .nil)
  · exact .consume (.consume .nil)
  · apply Consumes.consume
    · exact LocatedStep.consume (location := .control) (atom := .leftParty)
        (state := contactSource) ({.rightParty} : Store CanaryAtom) rfl
    · apply Consumes.consume
      · exact LocatedStep.consume (location := .control) (atom := .rightParty)
          (state := afterLeft) 0 (by simp [afterLeft])
      · exact .nil

@[simp] theorem contactTarget_control : contactTarget .control = 0 := by
  simp [contactTarget, symmetricCommand, publishAll, publish, afterBoth,
    afterLeft, contactSource]

@[simp] theorem contactTarget_output :
    contactTarget .output =
      ({.rightResidual, .leftResidual} : Store CanaryAtom) := by
  simp [contactTarget, symmetricCommand, publishAll, publish, afterBoth,
    afterLeft, contactSource]

end Canary

end GuardedTransaction

/-! ## Direct MeTTa-calculus contact -/

/-- One guarded party in a symmetric MeTTa-calculus contact. -/
structure GuardedParty where
  term : Term
  continuation : Proc
deriving DecidableEq, Repr

def guardedProcess (location : Name) (party : GuardedParty) : Proc :=
  pFor party.term location party.continuation

def contactFootprint (left right : GuardedParty) : Store GuardedParty :=
  left ::ₘ right ::ₘ 0

/-- The direct `COMM` rule, before contextual and structural closure.  The
unification witness determines both residual continuations. -/
inductive DirectComm : Proc → Proc → Prop where
  | contact {location : Name} {left right : GuardedParty}
      {substitution : Bindings}
      (unifies : unifyPattern? left.term right.term = some substitution) :
      DirectComm
        (pPar [guardedProcess location left, guardedProcess location right])
        (pPar [applyDot substitution left.continuation,
          applyDot substitution right.continuation])

/-- Every direct `COMM` redex has a two-occurrence linear footprint. -/
theorem directComm_has_linear_footprint
    {source target : Proc} (step : DirectComm source target) :
    ∃ location left right substitution,
      unifyPattern? left.term right.term = some substitution ∧
      source = pPar [guardedProcess location left, guardedProcess location right] ∧
      target = pPar [applyDot substitution left.continuation,
        applyDot substitution right.continuation] ∧
      Sequential (LinearTake left) (LinearTake right)
        (contactFootprint left right) 0 := by
  cases step with
  | @contact location left right substitution unifies =>
      exact ⟨location, left, right, substitution, unifies, rfl, rfl,
        two_party_linear_footprint left right⟩

/-- A direct contact cannot be interpreted as two persistent observations
that consume their participants. -/
theorem directComm_footprint_not_persistent
    {source target : Proc} (step : DirectComm source target) :
    ∃ left right,
      ¬ Sequential (PersistentRead left) (PersistentRead right)
        (contactFootprint left right) 0 := by
  obtain ⟨_location, left, right, _substitution, _unifies,
      _source, _target, _linear⟩ := directComm_has_linear_footprint step
  exact ⟨left, right, two_persistent_reads_do_not_consume left right⟩

/-- Positive direct-contact example requiring no executable proof shortcut. -/
theorem identical_zero_guards_contact (location : Name) :
    DirectComm
      (pPar [pFor pZero location pZero, pFor pZero location pZero])
      (pPar [pZero, pZero]) := by
  let party : GuardedParty := ⟨pZero, pZero⟩
  have unifies : unifyPattern? party.term party.term = some [] := by
    exact unifyPattern_self party.term
  simpa [party, guardedProcess, applyDot, dotBindings, pZero, applyBindings] using
    (DirectComm.contact (location := location) (left := party) (right := party)
      unifies)

/-! ## Direct COMM through the guarded transactional waist -/

namespace DirectCommBridge

open GuardedTransaction

/-- The transaction carrier distinguishes guarded parties from the residual
processes published by their continuations. -/
inductive ContactOccurrence where
  | party : GuardedParty → ContactOccurrence
  | residual : Proc → ContactOccurrence
deriving DecidableEq, Repr

/-- `none` is the surrounding process pool; `some channel` is a selected
contact location. -/
abbrev ContactLocation := Option Name

/-- Collective selection for symmetric COMM.  Unlike componentwise matching,
the unification premise relates the two selected parties. -/
def directSelection :
    Selection ContactLocation ContactOccurrence GuardedParty Bindings :=
  fun guards atoms substitution =>
    ∃ location left right,
      guards =
        [⟨.consume, some location, left⟩,
          ⟨.consume, some location, right⟩] ∧
      atoms = [.party left, .party right] ∧
      unifyPattern? left.term right.term = some substitution

def directCommand (location : Name) (left right : GuardedParty) :
    Command ContactLocation ContactOccurrence GuardedParty Bindings where
  guards :=
    [⟨.consume, some location, left⟩,
      ⟨.consume, some location, right⟩]
  continuation substitution :=
    [⟨none, .residual (applyDot substitution left.continuation)⟩,
      ⟨none, .residual (applyDot substitution right.continuation)⟩]

def directSource (location : Name) (left right : GuardedParty) :
    Network ContactLocation ContactOccurrence :=
  Function.update (fun _ => 0) (some location)
    ({.party left, .party right} : Store ContactOccurrence)

def directAfterLeft (location : Name) (left right : GuardedParty) :
    Network ContactLocation ContactOccurrence :=
  Function.update (directSource location left right) (some location)
    ({.party right} : Store ContactOccurrence)

def directAfterBoth (location : Name) (left right : GuardedParty) :
    Network ContactLocation ContactOccurrence :=
  Function.update (directAfterLeft location left right) (some location) 0

def directTarget (location : Name) (left right : GuardedParty)
    (substitution : Bindings) : Network ContactLocation ContactOccurrence :=
  publishAll ((directCommand location left right).continuation substitution)
    (directAfterBoth location left right)

/-- The manuscript's unification premise is sufficient to execute the exact
two-party contact through the neutral transaction rule. -/
theorem direct_contact_fires
    {location : Name} {left right : GuardedParty}
    {substitution : Bindings}
    (unifies : unifyPattern? left.term right.term = some substitution) :
    Fires directSelection (directCommand location left right)
      (directSource location left right)
      (directTarget location left right substitution) := by
  apply Fires.fire
      (atoms := [.party left, .party right])
      (environment := substitution)
      (residual := directAfterBoth location left right)
  · exact ⟨location, left, right, rfl, rfl, unifies⟩
  · exact .consume (.consume .nil)
  · apply Consumes.consume
    · exact LocatedStep.consume
        (location := some location) (atom := .party left)
        (state := directSource location left right)
        ({.party right} : Store ContactOccurrence)
        (by simp [directSource])
    · apply Consumes.consume
      · exact LocatedStep.consume
          (location := some location) (atom := .party right)
          (state := directAfterLeft location left right) 0
          (by simp [directAfterLeft])
      · exact .nil

/-- Every direct manuscript COMM step therefore has a corresponding guarded
transaction with the same unification witness and residual continuations. -/
theorem directComm_factors_through_guarded_transaction
    {source target : Proc} (step : DirectComm source target) :
    ∃ location left right substitution,
      unifyPattern? left.term right.term = some substitution ∧
      source = pPar [guardedProcess location left,
        guardedProcess location right] ∧
      target = pPar [applyDot substitution left.continuation,
        applyDot substitution right.continuation] ∧
      Fires directSelection (directCommand location left right)
        (directSource location left right)
        (directTarget location left right substitution) := by
  cases step with
  | @contact location left right substitution unifies =>
      exact ⟨location, left, right, substitution, unifies, rfl, rfl,
        direct_contact_fires unifies⟩

end DirectCommBridge

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
