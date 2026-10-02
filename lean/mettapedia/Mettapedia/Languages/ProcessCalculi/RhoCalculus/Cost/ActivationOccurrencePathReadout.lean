import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationPaths

/-!
# Source-bearing readout of existing finite cost paths

The readout records the actual event identifier, entire source trace and
selected runtime candidate at each existing path constructor. Its projections
are the established candidate sequence and chronological receipt emission.
It adds no execution relation or enabledness rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostPath

open ActivationGenerated.SerializationAdmission

def firingEntries {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    List (Nat × List RawTraceComponent × RawRuntimeStep) :=
  match path with
  | .done _ _ => []
  | .fire _ _ step _ rest => (nextId, components, step) :: rest.firingEntries

theorem firingEntries_length {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.firingEntries.length = path.depth := by
  induction path with
  | done supported bounded => rfl
  | fire supported bounded step enabled rest ih =>
      simp only [firingEntries, List.length_cons, depth]
      omega

theorem firingEntries_steps {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.firingEntries.map (fun entry => entry.2.2) = path.steps := by
  induction path with
  | done supported bounded => rfl
  | fire supported bounded step enabled rest ih =>
      simp only [firingEntries, List.map_cons, steps, ih]

theorem firingEntries_emission {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.firingEntries.map (fun entry => eventFor entry.2.1 entry.2.2 entry.1) = path.rawEmission := by
  induction path with
  | done supported bounded => rfl
  | fire supported bounded step enabled rest ih =>
      simp only [firingEntries, List.map_cons, rawEmission, ih]

theorem firingEntries_ids_eq_emission {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.firingEntries.map Prod.fst = path.emission.map (fun event => event.id) := by
  induction path with
  | done supported bounded => rfl
  | fire supported bounded step enabled rest ih =>
      simp only [firingEntries, emission, List.map_cons, ih]

/-- Chronology is inherited from the established receipt IDs. Equal literal
candidates are retained as distinct entries at their actual event IDs. -/
theorem firingEntries_ids {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.firingEntries.map Prod.fst = List.range' nextId path.depth :=
  path.firingEntries_ids_eq_emission.trans path.emission_ids

/-- Every entry retains the actual source occurrence bounds and candidate
membership supplied by its original execution constructor. -/
theorem firingEntries_enabled {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    ∀ entry ∈ path.firingEntries,
      TraceComponentsWellFormed entry.2.1 ∧ TraceComponentsBefore entry.1 entry.2.1 ∧
        entry.2.2 ∈ runtimeCostCandidatesFromConfig (entry.2.1.map RawTraceComponent.term) := by
  induction path with
  | done supported bounded => simp only [firingEntries, List.not_mem_nil, false_implies, implies_true]
  | fire supported bounded step enabled rest ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨supported, bounded, enabled⟩
      · exact ih entry member

/-- The admitted canonical source invariant reaches every actual firing,
including later firings created by previous receiver substitution. -/
theorem firingEntries_canonical_admitted {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {location : RawCostName} (canonical : TraceComponentsCanonical components)
    (images : (components.map RawTraceComponent.term).Forall (ConfigAdmitted location)) :
    ∀ entry ∈ path.firingEntries,
      TraceComponentsCanonical entry.2.1 ∧
        (entry.2.1.map RawTraceComponent.term).Forall (ConfigAdmitted location) := by
  induction path with
  | done supported bounded => simp only [firingEntries, List.not_mem_nil, false_implies, implies_true]
  | @fire nextId components finalId finalComponents supported bounded step enabled rest ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨canonical, images⟩
      · exact ih (applyTracedStep_canonical canonical enabled nextId)
          (applyTracedStep_admitted images enabled nextId) entry member

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostPath
