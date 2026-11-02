import Mettapedia.GSLT.Dynamics.CollectedReadRegion
import Mettapedia.Machines.RegionReadCensus

/-!
# Exact information normal forms for retained-handle clients

For a fixed pending/fallback/returned-handle interface, the collected heap's
lookup function is an exact summary of all admitted complete path questions.
Every sufficient summary determines it on reachable codes. The worker's
minimal allocation and cell-weight results remain representation-relative.

This does not grant clients arbitrary access to unrooted addresses, recover
freed identities, or claim a globally shortest physical representation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.CollectedReadInformation

open Mettapedia.Machines ResourceOwnership RegionReadCollection RegionReadInformation
open RegionObservations

variable {Address Value : Type} [DecidableEq Address]

def future (state : State Address Value) : Family (Heap Address Value) where
  Question := {address : Address // address ∈ state.roots} × List Address
  Answer _ := Answer Address Value
  read question heap := walk heap question.1.val question.2

theorem equivalent_iff_agrees (state : State Address Value) (before after : Heap Address Value) :
    (future state).Equivalent before after ↔ AgreesAt before after state := by
  constructor
  · intro equivalent address member path
    exact (equivalent (⟨address, member⟩, path)).symm
  · intro agree ⟨address, path⟩
    exact (agree address.val address.property path).symm

noncomputable def normal (state : State Address Value) (heap : Heap Address Value) :
    Address → Option (Cell Address Value) := (collect heap state.registry).lookup

theorem normal_exact (state : State Address Value) : (future state).Exact (normal state) := by
  intro before after
  rw [equivalent_iff_agrees, ← collected_lookup_exact]
  exact eq_comm

theorem normal_sufficient (state : State Address Value) : (future state).Sufficient (normal state) :=
  fun before after => (normal_exact state before after).mp

/-- Sufficient does not mean minimal: a richer code can retain extra data.
The exact normal form is recoverable from every sufficient reachable code. -/
theorem every_sufficient_summary_determines_normal (state : State Address Value) {Code : Type}
    (summary : Heap Address Value → Code) (sufficient : (future state).Sufficient summary) :
    Core.NonFactorization.Factors (Set.rangeFactorization summary) (normal state) := by
  apply (Core.NonFactorization.factors_iff_constantOnFibers
    Set.rangeFactorization_surjective (normal state)).mpr
  intro before after same
  apply (normal_exact state before after).mpr
  exact sufficient before after (congrArg Subtype.val same)

noncomputable def reachable_normal_classes (state : State Address Value) :
    Set.range (normal state) ≃ (future state).Classes :=
  (future state).exactEquiv (normal state) (normal_exact state)

theorem collection_attains_normal (state : State Address Value) (heap : Heap Address Value) :
    normal state (collect heap state.registry) = normal state heap := by
  funext address
  exact collect_lookup_idempotent heap state.registry address

theorem any_faithful_heap_keeps_live_allocations (state : State Address Value)
    (before after : Heap Address Value) (same : (future state).Equivalent before after) :
    (collect before state.registry).allocated ⊆ after.allocated :=
  collected_allocation_minimal before after state ((equivalent_iff_agrees state before after).mp same)

theorem any_faithful_heap_keeps_live_weight (state : State Address Value)
    (before after : Heap Address Value) (same : (future state).Equivalent before after) :
    allocatedBytes (collect before state.registry) ≤ allocatedBytes after :=
  collected_weight_minimal before after state ((equivalent_iff_agrees state before after).mp same)

/-- The finite-census worker realizes the existing page boundary without
using the noncomputable semantic collector as its implementation. -/
def censusRegion (policy : Nat → Bool) (budget rootSlots : Nat) :
    CertifiedRegion (CollectedRead.boundary (Address := Address) (Value := Value) budget) Nat where
  regime := rootSlots
  Artifact := CollectedRead.Input Address Value
  attempt input := if input.2.roots.length ≤ rootSlots then
    .committed (RegionReadCensus.run policy input.1 budget input.2) else .declined input
  decode := CollectedRead.observe
  restores input restored declined := by
    dsimp only at declined
    split at declined
    · cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact input result accepted := by
    split at accepted
    · cases accepted
      rw [RegionReadCensus.run_eq_semantic]
      exact CollectedRead.collected_observation_exact policy budget input
    · cases accepted

theorem census_capacity_refusal (policy : Nat → Bool) (budget rootSlots : Nat)
    (input : CollectedRead.Input Address Value) (tooSmall : rootSlots < input.2.roots.length) :
    (censusRegion policy budget rootSlots).attempt input = .declined input := by
  simp [censusRegion, Nat.not_le.mpr tooSmall]

theorem census_attempt_exact (policy : Nat → Bool) (budget rootSlots : Nat)
    (input : CollectedRead.Input Address Value) :
    (censusRegion policy budget rootSlots).attempt input =
      (CollectedRead.region policy budget rootSlots).attempt input := by
  simp only [censusRegion, CollectedRead.region, RegionReadCensus.run_eq_semantic]

theorem accepted_root_capacity_preserved (policy : Nat → Bool) (budget rootSlots : Nat)
    (input result : CollectedRead.Input Address Value)
    (accepted : (censusRegion policy budget rootSlots).attempt input = .committed result) :
    result.2.roots.length ≤ rootSlots := by
  unfold censusRegion at accepted
  dsimp only at accepted
  split at accepted
  next fits =>
    cases accepted
    exact (RegionReadCensus.run_root_slots_nonincreasing policy input.1 budget input.2).trans fits
  next => cases accepted

end Mettapedia.GSLT.Dynamics.ObservationQualified.CollectedReadInformation
