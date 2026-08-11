import Mettapedia.GSLT.Core.GSLT

/-!
# Queryable revision theories

A queryable revision theory separates three pieces that are often hidden in
one host loop:

* a relation saying which revision events may change a world;
* proof-relevant histories and snapshots;
* observations of a world after those events.

The event relation is intentionally relational rather than a fixed strategy.
`StrongSquare` records literal agreement of the two event orders, while
`ObservedSquare` only requires agreement at one declared observer.  This is a
small common interface for world-model revision, reflective-space updates,
and later certified parallel realizations.
-/

namespace Mettapedia.GSLT.Dynamics.QueryRevision

universe uWorld uRevision uQuery uObservation uObserved

/-- A relational world-revision theory equipped with read-only queries. -/
structure Theory where
  World : Type uWorld
  Revision : Type uRevision
  Query : Type uQuery
  Observation : Type uObservation
  Step : Revision → World → World → Prop
  query : World → Query → Observation

namespace Theory

/-- A chronological sequence of named revision events. -/
inductive HistoryStep (theory : Theory) :
    List theory.Revision → theory.World → theory.World → Prop where
  | nil (world : theory.World) : HistoryStep theory [] world world
  | cons {revision : theory.Revision} {revisions : List theory.Revision}
      {source middle target : theory.World} :
      theory.Step revision source middle →
      HistoryStep theory revisions middle target →
      HistoryStep theory (revision :: revisions) source target

namespace HistoryStep

/-- One revision is a singleton history. -/
theorem single {theory : Theory} {revision : theory.Revision}
    {source target : theory.World}
    (step : theory.Step revision source target) :
    theory.HistoryStep [revision] source target :=
  .cons step (.nil target)

/-- Concatenating chronological histories composes their executions. -/
theorem append {theory : Theory}
    {first second : List theory.Revision}
    {source middle target : theory.World}
    (firstSteps : theory.HistoryStep first source middle)
    (secondSteps : theory.HistoryStep second middle target) :
    theory.HistoryStep (first ++ second) source target := by
  induction firstSteps with
  | nil => simpa using secondSteps
  | cons step rest inductionHypothesis =>
      exact .cons step (inductionHypothesis secondSteps)

end HistoryStep

/-- A snapshot retains its origin, chronological revision identity, current
world, and the derivation connecting them. -/
structure Snapshot (theory : Theory) where
  origin : theory.World
  revisions : List theory.Revision
  world : theory.World
  reaches : theory.HistoryStep revisions origin world

namespace Snapshot

/-- Every world has an initial, history-free snapshot. -/
def initial (theory : Theory) (world : theory.World) : theory.Snapshot where
  origin := world
  revisions := []
  world := world
  reaches := .nil world

/-- Extend a snapshot by one checked revision event. -/
def extend {theory : Theory} (snapshot : theory.Snapshot)
    (revision : theory.Revision) (target : theory.World)
    (step : theory.Step revision snapshot.world target) : theory.Snapshot where
  origin := snapshot.origin
  revisions := snapshot.revisions ++ [revision]
  world := target
  reaches := snapshot.reaches.append (.single step)

/-- Querying a snapshot is read-only by construction. -/
def query {theory : Theory} (snapshot : theory.Snapshot)
    (request : theory.Query) : theory.Observation :=
  theory.query snapshot.world request

end Snapshot

/-- A revision is enabled when it has at least one successor. -/
def Enabled (theory : Theory) (revision : theory.Revision)
    (source : theory.World) : Prop :=
  ∃ target, theory.Step revision source target

/-- A literal commuting square: both revision orders reach one common world. -/
structure StrongSquare (theory : Theory)
    (first second : theory.Revision) (source : theory.World) where
  afterFirst : theory.World
  afterSecond : theory.World
  joined : theory.World
  firstFromSource : theory.Step first source afterFirst
  secondFromSource : theory.Step second source afterSecond
  secondAfterFirst : theory.Step second afterFirst joined
  firstAfterSecond : theory.Step first afterSecond joined

/-- An observer-relative square: the two orders may retain different internal
world representations, but the explicitly named value observer cannot
distinguish their endpoints.  The complete query profile is one such value. -/
structure ObservedSquare (theory : Theory)
    (first second : theory.Revision) (source : theory.World)
    {Value : Type uObserved} (observe : theory.World → Value) where
  afterFirst : theory.World
  afterSecond : theory.World
  firstThenSecond : theory.World
  secondThenFirst : theory.World
  firstFromSource : theory.Step first source afterFirst
  secondFromSource : theory.Step second source afterSecond
  secondAfterFirst : theory.Step second afterFirst firstThenSecond
  firstAfterSecond : theory.Step first afterSecond secondThenFirst
  observationAgrees : observe firstThenSecond = observe secondThenFirst

namespace StrongSquare

/-- Literal state commutation implies commutation for every named value
observer. -/
def toObservedValue {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (square : theory.StrongSquare first second source)
    {Value : Type uObserved} (observe : theory.World → Value) :
    theory.ObservedSquare first second source observe where
  afterFirst := square.afterFirst
  afterSecond := square.afterSecond
  firstThenSecond := square.joined
  secondThenFirst := square.joined
  firstFromSource := square.firstFromSource
  secondFromSource := square.secondFromSource
  secondAfterFirst := square.secondAfterFirst
  firstAfterSecond := square.firstAfterSecond
  observationAgrees := rfl

/-- Literal state commutation preserves the complete query profile. -/
def toQuerySquare {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (square : theory.StrongSquare first second source) :
    theory.ObservedSquare first second source theory.query :=
  square.toObservedValue theory.query

end StrongSquare

/-- Strong coexecutibility retains a literal common residual. -/
def StronglyCoexecutible (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  Nonempty (theory.StrongSquare first second source)

/-- Query coexecutibility permits representation differences invisible to the
complete declared query profile. -/
def QueryCoexecutible (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  Nonempty (theory.ObservedSquare first second source theory.query)

/-- Conflict means joint initial enablement without a literal commuting
square.  Observer-relative conflict remains a separate, weaker notion. -/
def Conflict (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  theory.Enabled first source ∧ theory.Enabled second source ∧
    ¬ theory.StronglyCoexecutible first second source

/-- Literal coexecution always gives query-relative coexecution. -/
theorem stronglyCoexecutible_implies_queryCoexecutible
    {theory : Theory} {first second : theory.Revision}
    {source : theory.World}
    (coexecutible : theory.StronglyCoexecutible first second source) :
    theory.QueryCoexecutible first second source := by
  rcases coexecutible with ⟨square⟩
  exact ⟨square.toQuerySquare⟩

end Theory

end Mettapedia.GSLT.Dynamics.QueryRevision
