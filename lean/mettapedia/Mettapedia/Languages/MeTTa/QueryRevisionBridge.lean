import Mettapedia.GSLT.Dynamics.EventValuation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CausalInteraction
import Mettapedia.PLN.WorldModel.BinaryWorldModel

/-!
# Query/revision instances for world models and MeTTa interaction

This module connects two existing theories through the generic relational
query/revision interface:

* WM-PLN revision is additive, so arbitrary revision events commute and query
  evidence distributes over their composition;
* located MeTTa access has a finer boundary: persistent reads can commute,
  while two consumes of one occurrence conflict.

The comparison is deliberately semantic.  It does not choose a scheduler,
thread representation, or abstract-machine plan.
-/

namespace Mettapedia.Languages.MeTTa.QueryRevisionBridge

open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CausalInteraction

universe uState uQuery uLocation uAtom

/-! ## Additive WM-PLN revision -/

/-- A binary world model as a relational query/revision theory.  A revision
event contributes another evidence state by addition. -/
def binaryWorldTheory
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query] : Theory where
  World := State
  Revision := State
  Query := Query
  Observation := BinaryEvidence
  Step := fun revision source target => target = source + revision
  query := fun world request =>
    BinaryWorldModel.evidence (State := State) (Query := Query) world request

/-- Adding one evidence revision is a revision event. -/
theorem binaryWorld_step
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (world revision : State) :
    (binaryWorldTheory (State := State) (Query := Query)).Step
      revision world (world + revision) :=
  rfl

/-- Commutativity and associativity of evidence revision produce a literal
commuting square for every pair of revisions. -/
def binaryWorld_square
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (world first second : State) :
    (binaryWorldTheory (State := State) (Query := Query)).StrongSquare
      first second world where
  afterFirst := world + first
  afterSecond := world + second
  joined := world + first + second
  firstFromSource := rfl
  secondFromSource := rfl
  secondAfterFirst := rfl
  firstAfterSecond := by
    change world + first + second = world + second + first
    ac_rfl

/-- Query evidence after two revisions is the sum of the original and both
revision contributions. -/
theorem binaryWorld_query_after_two
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (world first second : State) (request : Query) :
    (binaryWorldTheory (State := State) (Query := Query)).query
        (world + first + second) request =
      BinaryWorldModel.evidence (State := State) (Query := Query) world request +
        BinaryWorldModel.evidence (State := State) (Query := Query) first request +
        BinaryWorldModel.evidence (State := State) (Query := Query) second request := by
  change BinaryWorldModel.evidence (State := State) (Query := Query)
      (world + first + second) request = _
  rw [BinaryWorldModel.evidence_add', BinaryWorldModel.evidence_add']

/-- Additive world-model revisions preserve the entire query profile under
reordering, not merely one selected query. -/
theorem binaryWorld_queryCoexecutible
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (world first second : State) :
    Theory.QueryCoexecutible
      (binaryWorldTheory (State := State) (Query := Query))
      first second world :=
  Theory.stronglyCoexecutible_implies_queryCoexecutible
    ⟨binaryWorld_square world first second⟩

/-- Observe each world revision through one selected evidence query.  This is
an evidential valuation of events, distinct from execution work or latency. -/
noncomputable def binaryEvidenceValuation
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (request : Query) :
    Valuation (binaryWorldTheory (State := State) (Query := Query)) :=
  additive fun revision =>
    BinaryWorldModel.evidence (State := State) (Query := Query)
      revision request

/-- The grade of two world revisions is their additive evidence contribution
at the selected query. -/
@[simp] theorem binaryEvidence_history_two
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (request : Query) (first second : State) :
    (binaryEvidenceValuation (State := State) request).historyGrade
        [first, second] =
      some
        (BinaryWorldModel.evidence (State := State) (Query := Query)
            first request +
          BinaryWorldModel.evidence (State := State) (Query := Query)
            second request) :=
  by
    simp [binaryEvidenceValuation, Valuation.historyGrade,
      Mettapedia.GSLT.PartialMonoid.foldOption, additive,
      additivePartialMonoid]

/-- Additive evidence revisions are both behaviorally commuting and compatible
in the selected evidence valuation. -/
theorem binaryWorld_evidence_stronglyParallelizable
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (request : Query) (world first second : State) :
    (binaryEvidenceValuation (State := State) request).StronglyParallelizable
      first second world := by
  exact
    ⟨⟨binaryWorld_square world first second⟩,
      additive_compatible
        (theory := binaryWorldTheory (State := State) (Query := Query))
        (Grade := BinaryEvidence)
        (fun revision =>
          BinaryWorldModel.evidence (State := State) (Query := Query)
            revision request)
        first second⟩

/-- Retain evidence contribution and abstract execution work as two separate
coordinates over the same revision history. -/
noncomputable def binaryEvidenceAndWorkValuation
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (request : Query) :
    Valuation (binaryWorldTheory (State := State) (Query := Query)) :=
  (binaryEvidenceValuation (State := State) request).prod
    (eventCount (binaryWorldTheory (State := State) (Query := Query)))

/-- The joint valuation does not conflate its coordinates: evidence adds as
evidence and work counts events. -/
@[simp] theorem binaryEvidenceAndWork_history_two
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (request : Query) (first second : State) :
    (binaryEvidenceAndWorkValuation (State := State) request).historyGrade
        [first, second] =
      some
        (BinaryWorldModel.evidence (State := State) (Query := Query)
            first request +
          BinaryWorldModel.evidence (State := State) (Query := Query)
            second request,
          (2 : Nat)) := by
  simp [binaryEvidenceAndWorkValuation, binaryEvidenceValuation, eventCount,
    Valuation.historyGrade, Mettapedia.GSLT.PartialMonoid.foldOption,
    Valuation.prod, Mettapedia.GSLT.PartialMonoid.prod, additive,
    additivePartialMonoid]

/-- A pair may be admitted simultaneously by the evidential and execution-work
coordinates without identifying their algebras. -/
theorem binaryWorld_evidenceAndWork_stronglyParallelizable
    {State : Type uState} {Query : Type uQuery}
    [EvidenceType State] [BinaryWorldModel State Query]
    (request : Query) (world first second : State) :
    (binaryEvidenceAndWorkValuation (State := State) request).StronglyParallelizable
      first second world := by
  refine ⟨⟨binaryWorld_square world first second⟩, ?_⟩
  apply Valuation.prod_compatible
  · exact additive_compatible
      (theory := binaryWorldTheory (State := State) (Query := Query))
      (Grade := BinaryEvidence)
      (fun revision =>
        BinaryWorldModel.evidence (State := State) (Query := Query)
          revision request)
      first second
  · exact additive_compatible
      (theory := binaryWorldTheory (State := State) (Query := Query))
      (Grade := Nat) (fun _ => 1) first second

/-! ## Located MeTTa space/channel revision -/

/-- Located persistent/linear access as a query/revision theory.  The query
profile exposes occurrence membership at every location. -/
def locatedAccessTheory
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom] : Theory where
  World := Network Location Atom
  Revision := Request Location Atom
  Query := Location × Atom
  Observation := Bool
  Step := fun revision source target => revision.Steps source target
  query := fun state request => decide (request.2 ∈ state request.1)

/-- The existing MeTTa protocol square is exactly a strong revision square. -/
def protocolSquareToRevisionSquare
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    {first second : Request Location Atom}
    {source : Network Location Atom}
    (square : CommutingSquare first second source) :
    (locatedAccessTheory (Location := Location) (Atom := Atom)).StrongSquare
      first second source where
  afterFirst := square.afterFirst
  afterSecond := square.afterSecond
  joined := square.joined
  firstFromSource := square.firstFromSource
  secondFromSource := square.secondFromSource
  secondAfterFirst := square.secondAfterFirst
  firstAfterSecond := square.firstAfterSecond

/-- Strong revision squares recover the existing protocol-square witness. -/
def revisionSquareToProtocolSquare
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    {first second : Request Location Atom}
    {source : Network Location Atom}
    (square :
      (locatedAccessTheory (Location := Location) (Atom := Atom)).StrongSquare
        first second source) :
    CommutingSquare first second source where
  afterFirst := square.afterFirst
  afterSecond := square.afterSecond
  joined := square.joined
  firstFromSource := square.firstFromSource
  secondFromSource := square.secondFromSource
  secondAfterFirst := square.secondAfterFirst
  firstAfterSecond := square.firstAfterSecond

/-- The current conservative different-location test supplies a strong
revision square whenever both events are initially enabled. -/
theorem located_independent_stronglyCoexecutible
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    {first second : Request Location Atom}
    {source : Network Location Atom}
    (independent : first.Independent second)
    (firstEnabled :
      Theory.Enabled
        (locatedAccessTheory (Location := Location) (Atom := Atom))
        first source)
    (secondEnabled :
      Theory.Enabled
        (locatedAccessTheory (Location := Location) (Atom := Atom))
        second source) :
    Theory.StronglyCoexecutible
      (locatedAccessTheory (Location := Location) (Atom := Atom))
      first second source := by
  rcases firstEnabled with ⟨afterFirst, firstStep⟩
  rcases secondEnabled with ⟨afterSecond, secondStep⟩
  exact Nonempty.map protocolSquareToRevisionSquare
    (Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CausalInteraction.Request.independent_coexecutible
      independent firstStep secondStep)

/-- The same independence certificate preserves the complete located query
profile. -/
theorem located_independent_queryCoexecutible
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    {first second : Request Location Atom}
    {source : Network Location Atom}
    (independent : first.Independent second)
    (firstEnabled :
      Theory.Enabled
        (locatedAccessTheory (Location := Location) (Atom := Atom))
        first source)
    (secondEnabled :
      Theory.Enabled
        (locatedAccessTheory (Location := Location) (Atom := Atom))
        second source) :
    Theory.QueryCoexecutible
      (locatedAccessTheory (Location := Location) (Atom := Atom))
      first second source :=
  Theory.stronglyCoexecutible_implies_queryCoexecutible
    (located_independent_stronglyCoexecutible independent
      firstEnabled secondEnabled)

/-- Count one unit of abstract execution work per located request.  This says
nothing about a concrete backend's wall time, allocation, or merge cost. -/
def locatedWorkValuation
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom] :
    Valuation (locatedAccessTheory (Location := Location) (Atom := Atom)) :=
  eventCount (locatedAccessTheory (Location := Location) (Atom := Atom))

@[simp] theorem locatedWork_history_two
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    (first second : Request Location Atom) :
    (locatedWorkValuation (Location := Location) (Atom := Atom)).historyGrade
        [first, second] = some (2 : Nat) :=
  rfl

/-- Initially enabled, location-independent requests satisfy both the strong
semantic square and additive work compatibility. -/
theorem located_independent_stronglyParallelizable
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    {first second : Request Location Atom}
    {source : Network Location Atom}
    (independent : first.Independent second)
    (firstEnabled :
      Theory.Enabled
        (locatedAccessTheory (Location := Location) (Atom := Atom))
        first source)
    (secondEnabled :
      Theory.Enabled
        (locatedAccessTheory (Location := Location) (Atom := Atom))
        second source) :
    (locatedWorkValuation (Location := Location) (Atom := Atom)).StronglyParallelizable
      first second source := by
  exact
    ⟨located_independent_stronglyCoexecutible independent
        firstEnabled secondEnabled,
      additive_compatible
        (theory := locatedAccessTheory (Location := Location) (Atom := Atom))
        (Grade := Nat) (fun _ => 1) first second⟩

/-- Positive boundary: two persistent observations of one occurrence are
strongly coexecutible, even though the locations are not disjoint. -/
theorem located_observe_singleton_stronglyCoexecutible
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    (location : Location) (atom : Atom) :
    Theory.StronglyCoexecutible
      (locatedAccessTheory (Location := Location) (Atom := Atom))
      (observeRequest location atom)
        (observeRequest location atom) (singletonNetwork location atom) := by
  exact Nonempty.map protocolSquareToRevisionSquare
    (observeRequest_singleton_coexecutible location atom)

/-- Same-location persistent observations remain parallelizable under additive
work accounting; syntactic location disjointness is not necessary. -/
theorem located_observe_singleton_stronglyParallelizable
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    (location : Location) (atom : Atom) :
    (locatedWorkValuation (Location := Location) (Atom := Atom)).StronglyParallelizable
        (observeRequest location atom) (observeRequest location atom)
        (singletonNetwork location atom) := by
  exact
    ⟨located_observe_singleton_stronglyCoexecutible location atom,
      additive_compatible
        (theory := locatedAccessTheory (Location := Location) (Atom := Atom))
        (Grade := Nat) (fun _ => 1)
        (observeRequest location atom) (observeRequest location atom)⟩

/-- Location disjointness is sufficient but not necessary: same-location
persistent reads commute. -/
theorem located_location_disjointness_not_necessary
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    (location : Location) (atom : Atom) :
    ¬ (observeRequest location atom).Independent
        (observeRequest location atom) ∧
      Theory.StronglyCoexecutible
        (locatedAccessTheory (Location := Location) (Atom := Atom))
        (observeRequest location atom)
          (observeRequest location atom) (singletonNetwork location atom) := by
  constructor
  · simp [Request.Independent, observeRequest]
  · exact located_observe_singleton_stronglyCoexecutible location atom

/-- Negative boundary: two consumptions of one singleton occurrence are both
enabled initially but have no strong revision square. -/
theorem located_consume_singleton_conflict
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    (location : Location) (atom : Atom) :
    Theory.Conflict
      (locatedAccessTheory (Location := Location) (Atom := Atom))
      (consumeRequest location atom) (consumeRequest location atom)
      (singletonNetwork location atom) := by
  rcases consumeRequest_singleton_conflict location atom with
    ⟨firstEnabled, secondEnabled, notProtocolSquare⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases firstEnabled with ⟨target, step⟩
    exact ⟨target, step⟩
  · rcases secondEnabled with ⟨target, step⟩
    exact ⟨target, step⟩
  · rintro ⟨square⟩
    exact notProtocolSquare ⟨revisionSquareToProtocolSquare square⟩

/-- Additive resource availability cannot rescue a pair with no semantic
commuting square. -/
theorem located_consume_singleton_not_stronglyParallelizable
    {Location : Type uLocation} {Atom : Type uAtom}
    [DecidableEq Location] [DecidableEq Atom]
    (location : Location) (atom : Atom) :
    ¬ (locatedWorkValuation (Location := Location) (Atom := Atom)).StronglyParallelizable
        (consumeRequest location atom) (consumeRequest location atom)
        (singletonNetwork location atom) := by
  intro parallelizable
  exact (located_consume_singleton_conflict location atom).2.2
    parallelizable.1

end Mettapedia.Languages.MeTTa.QueryRevisionBridge
