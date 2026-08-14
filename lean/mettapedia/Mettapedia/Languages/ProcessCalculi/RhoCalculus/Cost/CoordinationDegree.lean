import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.BinaryCoordinationBoundary

/-!
# Coordination degree of exact-cover cost events

A concrete cost event atomically consumes its communication endpoint group and
every selected purse-head occurrence.  Exact covers can contain arbitrarily
many purse heads, so this atomic coordination degree is unbounded even for the
whole-redex communication shape.

Core rho remains binary: every primitive `COMM` claim owns two endpoints.
Consequently no uniform finite bound on the number of binary claims can cover
the consumed-occurrence capacity of every cost event.  This does not rule out
event-dependent administrative protocols; it states the coordination cost
that any such protocol must expose.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

namespace CoordinationDegree

abbrev Ground := Unit

def authority : CostSig Ground := {()}

theorem authority_valid : authority.RuntimeValid := by
  simp [CostSig.RuntimeValid, authority]

def location : CostName Ground := .signature authority

def selectedHead : SelectedPurseHead Ground where
  head := authority
  tail := .empty
  head_valid := authority_valid

/-- An exact demand assembled from `n + 1` independently selected purse-head
occurrences. -/
def demand (n : Nat) : CostSig Ground :=
  ((Multiset.replicate (n + 1) selectedHead).map
    SelectedPurseHead.head).sum

theorem demand_valid (n : Nat) : (demand n).RuntimeValid := by
  simp [CostSig.RuntimeValid, demand, selectedHead, authority]

def selection (n : Nat) : FundingSelection Ground location (demand n) where
  chosen := Multiset.replicate (n + 1) selectedHead
  demand_eq := rfl

/-- A single whole-redex event funded by `n + 1` purse occurrences. -/
def event (n : Nat) : CostedEvent Ground :=
  .wholeRecvSend location .nil .nil (demand n) (demand_valid n) (selection n)

/-- The event owns one whole-redex endpoint component and `n + 1` selected
purse occurrences. -/
theorem event_consumed_card (n : Nat) :
    (event n).consumed.card = n + 2 := by
  simp [event, CostedEvent.consumed, CostedEvent.endpoints,
    CostedEvent.fundingBefore, FundingSelection.before,
    LocatedPurse.configComponents, selection]

/-- Atomic coordination degree in the concrete cost relation is unbounded. -/
theorem event_coordination_unbounded (bound : Nat) :
    ∃ candidate : CostedEvent Ground, bound < candidate.consumed.card := by
  refine ⟨event bound, ?_⟩
  rw [event_consumed_card]
  omega

/-- A uniform binary-plan bound would assign every cost event a plan no longer
than the same fixed number of primitive binary claims while covering all of
the event's consumed occurrences. -/
def UniformBinaryPlanBound : Prop :=
  ∃ bound : Nat, ∀ candidate : CostedEvent Ground,
    ∃ claims : List CommClaim,
      claims.length ≤ bound ∧
        candidate.consumed.card ≤ binaryPlanEndpointCount claims

/-- No such uniform bound exists.  An event funded by `2 * bound + 1` purse
occurrences consumes strictly more occurrences than `bound` binary claims can
cover. -/
theorem no_uniform_binary_plan_bound : ¬UniformBinaryPlanBound := by
  rintro ⟨bound, covers⟩
  obtain ⟨claims, claims_le, capacity⟩ := covers (event (2 * bound))
  rw [event_consumed_card, binaryPlanEndpointCount_eq_twice_length] at capacity
  omega

/-- The negative result is not caused by an empty family: the smallest member
is an ordinary two-occurrence event, matching one binary claim's capacity. -/
theorem smallest_event_has_binary_capacity :
    (event 0).consumed.card = 2 := by
  simpa using event_consumed_card 0

end CoordinationDegree

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
