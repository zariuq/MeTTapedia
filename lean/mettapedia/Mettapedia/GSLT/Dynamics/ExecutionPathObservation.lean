import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.GSLT.Dynamics.ObservationDiscipline

/-!
# Observation disciplines on complete execution paths

This module connects the four-dial observation interface to the free execution
paths used by GSLT-IL realizations.  A path retains its ordered primitive
steps; a discipline first collects that history and then reads its value.

The connection is deliberately one way.  Observing a path may forget
occurrence, order, span, or provenance, but the underlying path remains
available to other disciplines.
-/

namespace Mettapedia.GSLT.Dynamics.ExecutionPathObservation

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational

universe uTerm uValue

/-- Extract the ordered primitive-step history from a proof-relevant execution
path. -/
def events {system : GSLT.{uTerm}} :
    {source target : system.Term} → ExecutionPath system source target →
      List system.LabeledStep
  | _, _, .refl _ => []
  | _, _, .cons step rest =>
      ⟨_, _, step.down⟩ :: events rest

@[simp] theorem events_refl {system : GSLT.{uTerm}}
    (term : system.Term) :
    events (.refl term : ExecutionPath system term term) = [] :=
  rfl

@[simp] theorem events_cons {system : GSLT.{uTerm}}
    {source middle target : system.Term}
    (step : PLift (system.Step source middle))
    (rest : ExecutionPath system middle target) :
    events (.cons step rest) = ⟨source, middle, step.down⟩ :: events rest :=
  rfl

@[simp] theorem events_append {system : GSLT.{uTerm}}
    {source middle target : system.Term}
    (earlier : ExecutionPath system source middle)
    (later : ExecutionPath system middle target) :
    events (earlier.append later) = events earlier ++ events later := by
  induction earlier with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      change
        ⟨_, _, step.down⟩ :: events (rest.append later) =
          ⟨_, _, step.down⟩ :: (events rest ++ events later)
      rw [inductionHypothesis]

/-- A common-value observation on every finite execution path of one GSLT. -/
abbrev PathObservation (system : GSLT.{uTerm}) (Value : Type uValue) :=
  {source target : system.Term} → ExecutionPath system source target →
    Option Value

/-- Every discipline over primitive labeled steps induces a path observation
without replacing or truncating the path. -/
def ofDiscipline {system : GSLT.{uTerm}}
    (discipline : GSLTObservation system) :
    PathObservation system discipline.Value :=
  fun path => discipline.observe (events path)

@[simp] theorem ofDiscipline_apply {system : GSLT.{uTerm}}
    (discipline : GSLTObservation system)
    {source target : system.Term}
    (path : ExecutionPath system source target) :
    ofDiscipline discipline path = discipline.observe (events path) :=
  rfl

/-- Chronological collector composition computes observation of concatenated
paths by combining their retained containers. -/
theorem collect_events_append {system : GSLT.{uTerm}}
    (discipline : GSLTObservation system)
    (chronological : ChronologicalCapability discipline.collection)
    {source middle target : system.Term}
    (earlier : ExecutionPath system source middle)
    (later : ExecutionPath system middle target) :
    discipline.collection.collect (events (earlier.append later)) =
      (discipline.collection.collect (events earlier)).bind fun left =>
        (discipline.collection.collect (events later)).bind fun right =>
          chronological.algebra.op left right := by
  rw [events_append, chronological.collect_append]

/-! ## Lossy observation canary -/

namespace Canary

@[reducible] def system : GSLT := GSLT.discrete Bool

def provenance : GSLTObservation system where
  collection :=
    { Container := List system.LabeledStep
      collect := some }
  Value := Nat
  readout := List.length

/-- The readout forgets every zero-step endpoint distinction. -/
theorem distinct_empty_paths_same_observation :
    ofDiscipline provenance
        (.refl false : ExecutionPath system false false) =
      ofDiscipline provenance
        (.refl true : ExecutionPath system true true) :=
  rfl

end Canary

#print axioms events_append
#print axioms collect_events_append
#print axioms Canary.distinct_empty_paths_same_observation

end Mettapedia.GSLT.Dynamics.ExecutionPathObservation
