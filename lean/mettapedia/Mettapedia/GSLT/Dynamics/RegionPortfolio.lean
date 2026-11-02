import Mettapedia.GSLT.Dynamics.RegionObservations
import Mettapedia.GSLT.Dynamics.PartialRegionPlan
import Mathlib.Data.List.MinMax
import Mathlib.Data.Prod.Lex

/-!
# Observer-qualified portfolios of independently certified regions

The boundary fixes source semantics and the summary which all its future
observers can use. Each worker has its own artifact type and must prove its
commit and refusal laws. Neither a cost estimate nor a registry tag supplies
such a proof. Gathering keeps every successful classifier; selection minimizes
predicted work, then retained bytes, then stable registry ordinal.

The source and profile index the boundary before classification. Runtime
dependency validation belongs to the prepared-region adapter. This layer is
not a frontend, and no constructor here certifies arbitrary C code.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified

open PartialRegionPlan
open RegionObservations

universe u v

/-- The result may include stores, faults, traces and suspended computation.
Only the separately proved sufficient summary may cross this boundary. -/
structure Boundary (Input Result Summary : Type u) where
  source : Input → Result
  summarize : Result → Summary
  future : Family.{u, u, u} Result
  sufficient : future.Sufficient summarize

namespace Boundary

variable {Input Result Summary : Type u} (boundary : Boundary Input Result Summary)

def reference (input : Input) : Summary := boundary.summarize (boundary.source input)

/-- A client is admitted exactly by its ability to use the boundary summary.
The law below is used only for an already specified client, not to silently
coarsen the client's observation. -/
theorem continuation (result other : Result)
    (same : boundary.summarize result = boundary.summarize other)
    (question : boundary.future.Question) :
    boundary.future.read question result = boundary.future.read question other :=
  boundary.sufficient result other same question

end Boundary

structure CertifiedRegion {Input Result Summary : Type u}
    (boundary : Boundary Input Result Summary) (Regime : Type v) where
  regime : Regime
  Artifact : Type u
  attempt : Input → Attempt Input Artifact
  decode : Artifact → Summary
  restores : RestoresOnDecline attempt
  exact : ∀ input artifact, attempt input = .committed artifact →
    decode artifact = boundary.reference input

namespace CertifiedRegion

variable {Input Result Summary : Type u} {Regime : Type v}
variable {boundary : Boundary Input Result Summary}

def observationAttempt (region : CertifiedRegion boundary Regime) (input : Input) :
    Attempt Input Summary :=
  match region.attempt input with
  | .committed artifact => .committed (region.decode artifact)
  | .declined restored => .declined restored

theorem observation_restores (region : CertifiedRegion boundary Regime) :
    RestoresOnDecline region.observationAttempt := by
  intro input restored declined
  cases step : region.attempt input with
  | committed artifact => simp [observationAttempt, step] at declined
  | declined prior =>
      have equal : prior = restored := by simpa [observationAttempt, step] using declined
      subst restored
      exact region.restores input prior step

theorem observation_exact (region : CertifiedRegion boundary Regime) :
    ExactOnCommit region.observationAttempt boundary.reference := by
  intro input observation committed
  cases step : region.attempt input with
  | declined prior => simp [observationAttempt, step] at committed
  | committed artifact =>
      have equal : region.decode artifact = observation := by
        simpa [observationAttempt, step] using committed
      exact equal.symm.trans (region.exact input artifact step)

def execute (region : CertifiedRegion boundary Regime) : Input → Summary :=
  realize region.observationAttempt boundary.reference

theorem execute_eq_reference (region : CertifiedRegion boundary Regime) :
    region.execute = boundary.reference :=
  realize_exact _ _ region.observation_restores region.observation_exact

theorem continue_execute {Answer : Type*} (region : CertifiedRegion boundary Regime)
    (continuation : Summary → Answer) (input : Input) :
    continuation (region.execute input) = continuation (boundary.reference input) := by
  rw [execute_eq_reference]

/-- Any finite conjunction of live admission checks may disable a worker.
It cannot create a new source outcome or damage the fallback input. -/
def restrict (region : CertifiedRegion boundary Regime) (enabled : Input → Bool) :
    CertifiedRegion boundary Regime where
  regime := region.regime
  Artifact := region.Artifact
  attempt input := if enabled input then region.attempt input else .declined input
  decode := region.decode
  restores input restored declined := by
    dsimp only at declined
    split at declined
    · exact region.restores _ _ declined
    · exact (Attempt.declined.inj declined).symm
  exact input artifact committed := by
    split at committed
    · exact region.exact _ _ committed
    · cases committed

theorem restrict_refusal (region : CertifiedRegion boundary Regime) (enabled : Input → Bool)
    (input : Input) (rejected : enabled input = false) :
    (region.restrict enabled).attempt input = .declined input := by
  simp [restrict, rejected]

end CertifiedRegion

/-- Work estimates include preparation and conversion when instantiated.
Nothing in this record asserts that an estimate equals physical work. -/
structure Estimate where
  work : Nat
  retainedBytes : Nat
  deriving DecidableEq, Repr

abbrev Score := Nat ×ₗ (Nat ×ₗ Nat)

def Estimate.score (estimate : Estimate) (registryOrdinal : Nat) : Score :=
  toLex (estimate.work, toLex (estimate.retainedBytes, registryOrdinal))

structure Candidate {Input Result Summary : Type u}
    (boundary : Boundary Input Result Summary) (Regime : Type v) where
  region : CertifiedRegion boundary Regime
  estimate : Input → Estimate
  ordinal : Nat

namespace Candidate

variable {Input Result Summary : Type u} {Regime : Type v}
variable {boundary : Boundary Input Result Summary}

def score (input : Input) (candidate : Candidate boundary Regime) : Score :=
  (candidate.estimate input).score candidate.ordinal

end Candidate

/-- The family is indexed by the exact profile and source occurrence.
Source semantics is not recovered from a regime name or cost annotation. -/
abbrev RegionClassifier (Profile Source Input Result Summary : Type u) (Regime : Type v)
    (boundary : Profile → Source → Boundary Input Result Summary) :=
  (profile : Profile) → (source : Source) → Option (Candidate (boundary profile source) Regime)

namespace RegionPortfolio

variable {Input Result Summary : Type u} {Regime : Type v}
variable {boundary : Boundary Input Result Summary}

/-- Keep every admitted proposal, including multiple physical realizations
of the same source. No proof is synthesized by this collection operation. -/
def gather (proposals : List (Option (Candidate boundary Regime))) :
    List (Candidate boundary Regime) := proposals.filterMap id

theorem mem_gather (proposals : List (Option (Candidate boundary Regime)))
    (candidate : Candidate boundary Regime) :
    candidate ∈ gather proposals ↔ some candidate ∈ proposals := by
  simp [gather]

theorem gather_append (first later : List (Option (Candidate boundary Regime))) :
    gather (first ++ later) = gather first ++ gather later := by
  simp [gather]

def select (input : Input) (candidates : List (Candidate boundary Regime)) :
    Option (Candidate boundary Regime) := candidates.argmin (Candidate.score input)

theorem selected_mem (input : Input) (candidates : List (Candidate boundary Regime))
    (candidate : Candidate boundary Regime) (chosen : select input candidates = some candidate) :
    candidate ∈ candidates := List.argmin_mem chosen

theorem selected_minimal (input : Input) (candidates : List (Candidate boundary Regime))
    (candidate : Candidate boundary Regime) (chosen : select input candidates = some candidate)
    (other : Candidate boundary Regime) (present : other ∈ candidates) :
    candidate.score input ≤ other.score input := List.le_of_mem_argmin present chosen

theorem no_selection_iff_empty (input : Input) (candidates : List (Candidate boundary Regime)) :
    select input candidates = none ↔ candidates = [] := List.argmin_eq_none

def execute (input : Input) (candidates : List (Candidate boundary Regime)) : Summary :=
  match select input candidates with
  | none => boundary.reference input
  | some candidate => candidate.region.execute input

theorem execute_exact (input : Input) (candidates : List (Candidate boundary Regime)) :
    execute input candidates = boundary.reference input := by
  unfold execute
  split
  · rfl
  · exact congrFun (CertifiedRegion.execute_eq_reference _) input

/-- Even inaccurate costs or a reordered registry cannot change meaning.
Equal candidate sets are not needed: every member has its own certificate. -/
theorem selection_independent (input : Input)
    (first later : List (Candidate boundary Regime)) :
    execute input first = execute input later := by rw [execute_exact, execute_exact]

theorem continue_exact {Answer : Type*} (input : Input)
    (candidates : List (Candidate boundary Regime)) (continuation : Summary → Answer) :
    continuation (execute input candidates) = continuation (boundary.reference input) := by
  rw [execute_exact]

end RegionPortfolio

namespace Controls

theorem rank_work_before_memory :
    (Estimate.score ⟨2, 1000000⟩ 9) < (Estimate.score ⟨3, 0⟩ 0) := by decide

theorem rank_memory_before_ordinal :
    (Estimate.score ⟨2, 4⟩ 9) < (Estimate.score ⟨2, 5⟩ 0) := by decide

theorem rank_stable_registry_tie :
    (Estimate.score ⟨2, 4⟩ 3) < (Estimate.score ⟨2, 4⟩ 7) := by decide

/-- A private attempt that writes before declining is not an admissible
region. The existing generic fallback theorem cannot certify it. -/
theorem changed_input_on_decline_is_rejected :
    ¬ RestoresOnDecline (fun input : Nat => (Attempt.declined (input + 1) : Attempt Nat Nat)) := by
  intro restores
  have impossible := restores 0 1 rfl
  exact (by decide : (1 : Nat) ≠ 0) impossible

end Controls

#print axioms CertifiedRegion.execute_eq_reference
#print axioms CertifiedRegion.restrict
#print axioms RegionPortfolio.selected_minimal
#print axioms RegionPortfolio.selection_independent

end Mettapedia.GSLT.Dynamics.ObservationQualified
