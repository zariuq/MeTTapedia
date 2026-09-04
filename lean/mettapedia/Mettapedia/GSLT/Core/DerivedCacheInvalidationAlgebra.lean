import Mathlib.Data.Finset.Card

/-!
# Exact invalidation of semantically erased binding caches

A binding cache is a derived representation: its entries may accelerate an
observer, but the authoritative logical substitution does not depend on them.
This module isolates the rollback law for such caches and the conditional
cost theorem used by an explicit per-entry invalidator.

The theorem does not claim that support logging is the only possible cache
design.  It says that, among mechanisms which explicitly touch entries to
invalidate them, touching exactly the valid cache support is cardinality
minimal.  Scanning an allocated table is strictly more expensive whenever
that table contains an unused slot.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.DerivedCacheInvalidationAlgebra

universe uLogical uKey

variable {Logical : Type uLogical} {Key : Type uKey}
variable [DecidableEq Key]

/-- A semantic state paired with the support of a derived cache.  Cache
values are irrelevant to rollback validity; only which entries currently
carry derived information matters for invalidation cost. -/
structure State (Logical : Type uLogical) (Key : Type uKey)
    [DecidableEq Key] where
  logical : Logical
  validCacheKeys : Finset Key

/-- The authoritative meaning erases the cache component. -/
def denote (state : State Logical Key) : Logical := state.logical

/-- Invalidate exactly the entries named by the cache support. -/
def invalidateSupport (state : State Logical Key) : State Logical Key :=
  { state with validCacheKeys := ∅ }

/-- Cache invalidation cannot change the logical substitution. -/
@[simp] theorem invalidateSupport_exact (state : State Logical Key) :
    denote (invalidateSupport state) = denote state := rfl

/-- An explicit invalidation set is sufficient when it touches every valid
cache entry. -/
def Clears (state : State Logical Key) (touched : Finset Key) : Prop :=
  state.validCacheKeys ⊆ touched

/-- Exact support invalidation is sufficient. -/
theorem support_clears (state : State Logical Key) :
    Clears state state.validCacheKeys :=
  Finset.Subset.rfl

/-- Unit-cost model for an invalidator which explicitly visits entries. -/
def invalidationCost (touched : Finset Key) : Nat := touched.card

/-- Any sufficient explicit invalidator must visit at least as many distinct
entries as exact support invalidation. -/
theorem support_invalidation_minimal
    (state : State Logical Key) (touched : Finset Key)
    (clears : Clears state touched) :
    invalidationCost state.validCacheKeys ≤ invalidationCost touched :=
  Finset.card_le_card clears

/-- Scanning the whole allocated table is strictly more expensive whenever
the table contains an unused entry. -/
theorem support_cost_lt_capacity_scan
    (state : State Logical Key) (allocated : Finset Key)
    (contained : state.validCacheKeys ⊆ allocated)
    (unused : ∃ key ∈ allocated, key ∉ state.validCacheKeys) :
    invalidationCost state.validCacheKeys < invalidationCost allocated := by
  rw [invalidationCost, invalidationCost]
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset contained).2 unused)

namespace Canaries

def state : State Nat Nat where
  logical := 42
  validCacheKeys := {1, 3}

/-- Positive: invalidating the derived cache retains the logical meaning. -/
example : denote (invalidateSupport state) = 42 := rfl

/-- Positive: exact support invalidation visits two entries. -/
example : invalidationCost state.validCacheKeys = 2 := by decide

/-- Negative control: touching one cached key cannot clear a two-key cache. -/
example : ¬ Clears state {1} := by
  intro clears
  have member : (3 : Nat) ∈ ({1} : Finset Nat) :=
    clears (by simp [state])
  simp at member

/-- A four-slot capacity scan is strictly costlier than clearing the two live
cache entries. -/
example :
    invalidationCost state.validCacheKeys <
      invalidationCost ({0, 1, 2, 3} : Finset Nat) := by decide

end Canaries

namespace AuthorityIndexed

universe uAuthority uValue

variable {Authority : Type uAuthority} {Value : Type uValue}
variable [DecidableEq Authority]

/-- One derived classification together with the exact semantic authority and
source key under which it was computed. -/
structure Entry (Authority : Type uAuthority) (Key : Type uKey)
    (Value : Type uValue) where
  authority : Authority
  key : Key
  value : Value

/-- Reuse a derived classification only when both its authority and source
key agree with the live request.  Every mismatch recomputes from the
authoritative classifier. -/
def reuseOrRecompute
    (derive : Authority → Key → Value)
    (liveAuthority : Authority) (liveKey : Key)
    (entry : Entry Authority Key Value) : Value :=
  if entry.authority = liveAuthority ∧ entry.key = liveKey then
    entry.value
  else
    derive liveAuthority liveKey

/-- An authority-indexed cache is observationally exact when its stored value
was derived at its stored authority and key.  A changed authority or changed
source can never authorize the old result. -/
theorem reuseOrRecompute_exact
    (derive : Authority → Key → Value)
    (liveAuthority : Authority) (liveKey : Key)
    (entry : Entry Authority Key Value)
    (sound : entry.value = derive entry.authority entry.key) :
    reuseOrRecompute derive liveAuthority liveKey entry =
      derive liveAuthority liveKey := by
  unfold reuseOrRecompute
  split_ifs with hMatch
  · obtain ⟨authorityEq, keyEq⟩ := hMatch
    simpa [authorityEq, keyEq] using sound
  · rfl

namespace Canaries

def classify (authority key : Nat) : Nat := authority * 100 + key

def cached : Entry Nat Nat Nat where
  authority := 2
  key := 7
  value := classify 2 7

/-- Positive: an exactly matching authority and key reuse the cached result. -/
example : reuseOrRecompute classify 2 7 cached = 207 := by decide

/-- Negative authority control: changing mutable authority recomputes rather
than reusing the old classification. -/
example : reuseOrRecompute classify 3 7 cached = 307 := by decide

/-- Negative source control: a different authored occurrence also
recomputes. -/
example : reuseOrRecompute classify 2 8 cached = 208 := by decide

end Canaries

#print axioms reuseOrRecompute_exact

end AuthorityIndexed

#print axioms invalidateSupport_exact
#print axioms support_invalidation_minimal
#print axioms support_cost_lt_capacity_scan

end Mettapedia.GSLT.Core.DerivedCacheInvalidationAlgebra
