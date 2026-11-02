import Mettapedia.Machines.RegionReadCollection
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Root-derived operation collection as an observation-qualified route

Admission checks available root-entry slots before doing any collection.
Refusal preserves the exact entrance heap and pending computation. Accepted
pages return the actual collected heap plus their exact ordered result and
residual. Future reads through returned or fallback handles remain valid.

The capacity is a logical root-entry budget, not an allocator byte estimate.
Collection itself uses the finite-heap model; native tracing, allocation and
concurrency require their own refinements.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.CollectedRead

open Mettapedia.Machines ResourceOwnership RegionReadCollection

variable {Address Value : Type} [DecidableEq Address]

abbrev Input (Address Value : Type) := Heap Address Value × RegionReadCollection.State Address Value

/-- The public page includes its exact residual and every permitted future
path from a retained handle. It does not grant inspection of arbitrary garbage. -/
structure Observation (Address Value : Type) where
  state : RegionReadCollection.State Address Value
  path : Address → List Address → Answer Address Value

def observe (result : Input Address Value) : Observation Address Value where
  state := result.2
  path address route := if address ∈ result.2.roots then walk result.1 address route else none

def boundary (budget : Nat) : Boundary (Input Address Value)
    (Input Address Value) (Observation Address Value) where
  source input := (input.1, RegionReadCollection.run input.1 budget input.2)
  summarize := observe
  future := {
    Question := Observation Address Value → Bool
    Answer _ := Bool
    read question result := question (observe result) }
  sufficient _ _ same question := congrArg question same

theorem observe_agrees (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : observe (after, state) = observe (before, state) := by
  unfold observe
  apply congrArg (Observation.mk state)
  funext address route
  by_cases member : address ∈ state.roots
  · simp only [member, ↓reduceIte, agree address member route]
  · simp only [member, ↓reduceIte]

theorem collected_observation_exact (policy : Nat → Bool) (budget : Nat) (input : Input Address Value) :
    observe (runHeap policy input.1 budget input.2) = (boundary budget).reference input := by
  have receipt := heap_run_preserves_future policy input.1 budget input.2
  calc
    observe (runHeap policy input.1 budget input.2) =
        observe (input.1, (runHeap policy input.1 budget input.2).2) :=
      observe_agrees input.1 _ _ receipt.2
    _ = (boundary budget).reference input :=
      congrArg (fun state => observe (input.1, state)) receipt.1

noncomputable def region (policy : Nat → Bool) (budget rootSlots : Nat) :
    CertifiedRegion (boundary (Address := Address) (Value := Value) budget) Nat where
  regime := rootSlots
  Artifact := Input Address Value
  attempt input := if input.2.roots.length ≤ rootSlots then
    .committed (runHeap policy input.1 budget input.2) else .declined input
  decode := observe
  restores input restored declined := by
    dsimp only at declined
    split at declined
    · cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact input result accepted := by
    split at accepted
    · cases accepted
      exact collected_observation_exact policy budget input
    · cases accepted

theorem capacity_refusal_keeps_heap_and_residual (policy : Nat → Bool) (budget rootSlots : Nat)
    (input : Input Address Value) (tooSmall : rootSlots < input.2.roots.length) :
    (region policy budget rootSlots).attempt input = .declined input := by
  simp [region, Nat.not_le.mpr tooSmall]

theorem accepted_heap_keeps_future (policy : Nat → Bool) (budget rootSlots : Nat)
    (input result : Input Address Value)
    (accepted : (region policy budget rootSlots).attempt input = .committed result) :
    AgreesAt input.1 result.1 result.2 := by
  unfold region at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
    exact (heap_run_preserves_future policy input.1 budget input.2).2
  · cases accepted

end Mettapedia.GSLT.Dynamics.ObservationQualified.CollectedRead
