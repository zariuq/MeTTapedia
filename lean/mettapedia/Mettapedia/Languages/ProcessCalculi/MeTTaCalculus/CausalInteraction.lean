import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
import Mettapedia.Machines.ConeDuality

/-!
# Causal interaction beyond forward reachability

A forward cone records which network states are reachable.  That is necessary
for causal analysis, but it does not say whether two enabled interaction
occurrences can coexist.  This module adds the missing two-dimensional test:
a pair is coexecutible when its two orders form a commuting square.

The square is deliberately stated over the small located access protocol.  It
is a semantic interface for later schedulers and realizations, not a final
syntax or a fixed execution plan.

Positive and negative controls establish the boundary:

* independent locations produce a commuting square;
* two persistent observations of one occurrence produce a commuting square;
* two linear consumptions of one occurrence are individually enabled and lie
  in the same forward cone, but do not produce a commuting square.

Thus forward reachability alone cannot recover conflict or parallel safety.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CausalInteraction

open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceChannelBoundary
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

universe u v

variable {Location : Type u} {Atom : Type v}

/-- The unlabeled network transition obtained by forgetting which request
occurrence caused a step. -/
def ProtocolStep [DecidableEq Location]
    (source target : Network Location Atom) : Prop :=
  ∃ request : Request Location Atom, request.Steps source target

/-- Reachable network states after forgetting request-occurrence identity. -/
def Future [DecidableEq Location] (source : Network Location Atom) :
    Set (Network Location Atom) :=
  forwardCone (ProtocolStep (Location := Location) (Atom := Atom)) {source}

/-- A commuting square is the proof-relevant witness that both interaction
occurrences can happen, in either order, with one common residual. -/
structure CommutingSquare [DecidableEq Location]
    (first second : Request Location Atom)
    (source : Network Location Atom) where
  afterFirst : Network Location Atom
  afterSecond : Network Location Atom
  joined : Network Location Atom
  firstFromSource : first.Steps source afterFirst
  secondFromSource : second.Steps source afterSecond
  secondAfterFirst : second.Steps afterFirst joined
  firstAfterSecond : first.Steps afterSecond joined

namespace Request

variable [DecidableEq Location]

/-- A request is enabled when it has at least one protocol successor. -/
def Enabled (request : Request Location Atom)
    (source : Network Location Atom) : Prop :=
  ∃ target, request.Steps source target

/-- Two request occurrences are coexecutible when they have a commuting
square from the current network. -/
def Coexecutible (first second : Request Location Atom)
    (source : Network Location Atom) : Prop :=
  Nonempty (CommutingSquare first second source)

/-- Conflict is joint initial enablement without a commuting execution
square. -/
def Conflict (first second : Request Location Atom)
    (source : Network Location Atom) : Prop :=
  Enabled first source ∧ Enabled second source ∧
    ¬ Coexecutible first second source

/-- A single request step places its endpoint in the source's ordinary
forward cone. -/
theorem step_mem_future
    {request : Request Location Atom}
    {source target : Network Location Atom}
    (step : request.Steps source target) :
    target ∈ Future source := by
  exact ⟨source, by simp,
    Relation.ReflTransGen.single ⟨request, step⟩⟩

/-- Independent request footprints give a coexecution witness, not merely
two unrelated reachability facts. -/
theorem independent_coexecutible
    {first second : Request Location Atom}
    {source afterFirst afterSecond : Network Location Atom}
    (independent : first.Independent second)
    (firstStep : first.Steps source afterFirst)
    (secondStep : second.Steps source afterSecond) :
    Coexecutible first second source := by
  obtain ⟨joined, secondAfterFirst, firstAfterSecond⟩ :=
    first.independent_commute independent firstStep secondStep
  exact ⟨⟨afterFirst, afterSecond, joined, firstStep, secondStep,
    secondAfterFirst, firstAfterSecond⟩⟩

/-- Disjoint request footprints cannot be conflicts in this protocol.  This
is the theorem a parallel realization may use as its static admission rule. -/
theorem independent_not_conflict
    {first second : Request Location Atom}
    {source : Network Location Atom}
    (independent : first.Independent second) :
    ¬ Conflict first second source := by
  rintro ⟨⟨afterFirst, firstStep⟩, ⟨afterSecond, secondStep⟩,
    notCoexecutible⟩
  exact notCoexecutible
    (independent_coexecutible independent firstStep secondStep)

/-- The common residual of a commuting square also lies in the source's
forward cone. -/
theorem joined_mem_future
    {first second : Request Location Atom}
    {source : Network Location Atom}
    (square : CommutingSquare first second source) :
    square.joined ∈ Future source := by
  refine ⟨source, by simp, ?_⟩
  exact (Relation.ReflTransGen.single
    ⟨first, square.firstFromSource⟩).tail
      ⟨second, square.secondAfterFirst⟩

end Request

/-! ## Separating examples -/

variable [DecidableEq Location]

/-- The persistent-space request used by the positive control. -/
def observeRequest (location : Location) (atom : Atom) :
    Request Location Atom :=
  ⟨.observe, location, atom⟩

/-- The linear-channel request used by the conflict control. -/
def consumeRequest (location : Location) (atom : Atom) :
    Request Location Atom :=
  ⟨.consume, location, atom⟩

theorem observeRequest_singleton_step (location : Location) (atom : Atom) :
    (observeRequest location atom).Steps
      (singletonNetwork location atom)
      (singletonNetwork location atom) := by
  change LocatedStep .observe location atom
    (singletonNetwork location atom) (singletonNetwork location atom)
  exact .observe (by simp [singletonNetwork])

theorem consumeRequest_singleton_step (location : Location) (atom : Atom) :
    (consumeRequest location atom).Steps
      (singletonNetwork location atom)
      (Function.update (singletonNetwork location atom) location 0) := by
  change LocatedStep .consume location atom
    (singletonNetwork location atom)
    (Function.update (singletonNetwork location atom) location 0)
  exact .consume 0 (by simp [singletonNetwork])

/-- Persistent observation of one occurrence is coexecutible with itself:
both occurrences leave the network unchanged. -/
theorem observeRequest_singleton_coexecutible
    (location : Location) (atom : Atom) :
    Request.Coexecutible (observeRequest location atom)
      (observeRequest location atom)
      (singletonNetwork location atom) := by
  have step := observeRequest_singleton_step location atom
  exact ⟨⟨_, _, _, step, step, step, step⟩⟩

/-- Consequently, repeated persistent observation is not a conflict. -/
theorem observeRequest_singleton_not_conflict
    (location : Location) (atom : Atom) :
    ¬ Request.Conflict (observeRequest location atom)
      (observeRequest location atom)
      (singletonNetwork location atom) := by
  intro conflict
  exact conflict.2.2 (observeRequest_singleton_coexecutible location atom)

/-- Two linear consumptions of one occurrence cannot form a commuting
square. -/
theorem consumeRequest_singleton_not_coexecutible
    (location : Location) (atom : Atom) :
    ¬ Request.Coexecutible (consumeRequest location atom)
      (consumeRequest location atom)
      (singletonNetwork location atom) := by
  rintro ⟨square⟩
  apply located_consume_singleton_not_twice location atom
  exact ⟨square.afterFirst, square.joined,
    square.firstFromSource, square.secondAfterFirst⟩

/-- The same linear request is nevertheless enabled twice when occurrences
are considered separately at the initial state. -/
theorem consumeRequest_singleton_conflict
    (location : Location) (atom : Atom) :
    Request.Conflict (consumeRequest location atom)
      (consumeRequest location atom)
      (singletonNetwork location atom) := by
  refine ⟨⟨_, consumeRequest_singleton_step location atom⟩,
    ⟨_, consumeRequest_singleton_step location atom⟩, ?_⟩
  exact consumeRequest_singleton_not_coexecutible location atom

/-- **Forward-cone insufficiency.** Both individually enabled consume
occurrences have endpoints in the same forward cone, yet the occurrences
conflict.  Reachability support therefore does not determine safe
parallelism. -/
theorem forward_cone_does_not_determine_coexecution
    (location : Location) (atom : Atom) :
    ∃ firstTarget secondTarget,
      (consumeRequest location atom).Steps
        (singletonNetwork location atom) firstTarget ∧
      (consumeRequest location atom).Steps
        (singletonNetwork location atom) secondTarget ∧
      firstTarget ∈ Future (singletonNetwork location atom) ∧
      secondTarget ∈ Future (singletonNetwork location atom) ∧
      Request.Conflict (consumeRequest location atom)
        (consumeRequest location atom)
        (singletonNetwork location atom) := by
  let target := Function.update (singletonNetwork location atom) location 0
  have step : (consumeRequest location atom).Steps
      (singletonNetwork location atom) target :=
    consumeRequest_singleton_step location atom
  exact ⟨target, target, step, step,
    Request.step_mem_future step, Request.step_mem_future step,
    consumeRequest_singleton_conflict location atom⟩

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CausalInteraction
