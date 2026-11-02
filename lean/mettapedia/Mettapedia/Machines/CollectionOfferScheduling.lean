import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Collection opportunities for interleaved execution owners

The source lists eligible visits to a known universe. The implementation
accumulates offers during an iterative traversal. Source-step permission is
independent of a visit's collection eligibility: a suspended caller can still
present a safe, quiescent collection opportunity.

A second algorithm implements the former thread-wide countdown. Repeating
an actual 64-visit alternating-owner block indefinitely starves its first
owner. Per-visit offers preserve source order and offer to both owners.
These are scheduling laws, not a proof of the collector's root traversal or
of the C implementation. Heap safety retains its own ownership obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CollectionOfferScheduling

structure Visit (Owner : Type) where
  owner : Owner
  safe : Bool
  quiescent : Bool
  due : Bool
  sourcePermitted : Bool
  deriving DecidableEq, Repr

def eligible {Owner : Type} (visit : Visit Owner) : Bool :=
  visit.safe && visit.quiescent && visit.due

def reference {Owner : Type} (visits : List (Visit Owner)) : List Owner :=
  visits.filterMap fun visit => if eligible visit then some visit.owner else none

def loop {Owner : Type} : List Owner → List (Visit Owner) → List Owner
  | pending, [] => pending.reverse
  | pending, visit :: rest =>
      if eligible visit then loop (visit.owner :: pending) rest
      else loop pending rest

theorem loop_refines {Owner : Type} (pending : List Owner) (visits : List (Visit Owner)) :
    loop pending visits = pending.reverse ++ reference visits := by
  induction visits generalizing pending with
  | nil => simp [loop, reference]
  | cons visit rest ih =>
      cases yes : eligible visit <;>
        simp [loop, reference, yes, ih, List.reverse_cons, List.append_assoc]

def offers {Owner : Type} (visits : List (Visit Owner)) : List Owner := loop [] visits

theorem offers_exact {Owner : Type} (visits : List (Visit Owner)) :
    offers visits = reference visits := by
  simp [offers, loop_refines]

theorem reference_append {Owner : Type} (first later : List (Visit Owner)) :
    reference (first ++ later) = reference first ++ reference later := by
  simp [reference]

theorem eligible_visit_offered {Owner : Type} (visits : List (Visit Owner))
    (visit : Visit Owner) (present : visit ∈ visits) (ready : eligible visit = true) :
    visit.owner ∈ offers visits := by
  rw [offers_exact, reference]
  exact List.mem_filterMap.mpr ⟨visit, present, by simp [ready]⟩

theorem prefix_offer_exact {Owner : Type} (first later : List (Visit Owner))
    (visit : Visit Owner) (ready : eligible visit = true) :
    offers (first ++ visit :: later) = reference first ++ visit.owner :: reference later := by
  simp [offers_exact, reference, ready]

theorem source_permission_independent {Owner : Type} (visits : List (Visit Owner))
    (allow : Bool) :
    offers (visits.map fun visit => {visit with sourcePermitted := allow}) = offers visits := by
  simp only [offers_exact]
  induction visits with
  | nil => rfl
  | cons visit rest ih => simp_all [reference, eligible]

theorem unsafe_visit_omitted {Owner : Type} (visit : Visit Owner) (blocked : visit.safe = false) :
    offers [visit] = [] := by
  simp [offers_exact, reference, eligible, blocked]

structure Cadence (Owner : Type) where
  remaining : Nat
  pending : List Owner
  deriving DecidableEq, Repr

def legacyTick {Owner : Type} (period : Nat) (state : Cadence Owner)
    (visit : Visit Owner) : Cadence Owner :=
  if visit.safe then
    if state.remaining ≤ 1 then
      ⟨period, if visit.quiescent && visit.due then visit.owner :: state.pending else state.pending⟩
    else {state with remaining := state.remaining - 1}
  else state

def legacyLoop {Owner : Type} (period : Nat) : Cadence Owner → List (Visit Owner) → Cadence Owner
  | state, [] => state
  | state, visit :: rest => legacyLoop period (legacyTick period state visit) rest

theorem legacy_append {Owner : Type} (period : Nat) (state : Cadence Owner)
    (first later : List (Visit Owner)) :
    legacyLoop period state (first ++ later) =
      legacyLoop period (legacyLoop period state first) later := by
  induction first generalizing state with
  | nil => rfl
  | cons visit rest ih => simpa [legacyLoop] using ih (legacyTick period state visit)

theorem legacy_prefix_countdown {Owner : Type} (period : Nat) (pending : List Owner)
    (visits : List (Visit Owner)) (safe : ∀ visit ∈ visits, visit.safe = true) :
    legacyLoop period ⟨visits.length + 1, pending⟩ visits = ⟨1, pending⟩ := by
  induction visits with
  | nil => rfl
  | cons visit rest ih =>
      have here := safe visit (by simp)
      have later : ∀ item ∈ rest, item.safe = true := fun item member =>
        safe item (by simp [member])
      have positive : ¬rest.length + 1 + 1 ≤ 1 := by omega
      simpa [legacyLoop, legacyTick, here, positive] using ih later

def paused (owner : Nat) : Visit Nat := ⟨owner, true, true, true, false⟩
def blockPrefix : List (Visit Nat) :=
  ((List.replicate 31 [0, 1]).flatten ++ [0]).map paused
def block : List (Visit Nat) := blockPrefix ++ [paused 1]

theorem block_prefix_length : blockPrefix.length = 63 := by decide

theorem block_prefix_safe : ∀ visit ∈ blockPrefix, visit.safe = true := by
  intro visit member
  obtain ⟨owner, _, rfl⟩ := List.mem_map.mp member
  rfl

def rounds : Nat → List (Visit Nat)
  | 0 => []
  | n + 1 => block ++ rounds n

/-- Apply the generic countdown law to all 64 alternating visits. -/
theorem legacy_block (pending : List Nat) :
    legacyLoop 64 ⟨64, pending⟩ block = ⟨64, 1 :: pending⟩ := by
  have afterPrefix : legacyLoop 64 ⟨64, pending⟩ blockPrefix = ⟨1, pending⟩ := by
    simpa [block_prefix_length] using
      legacy_prefix_countdown 64 pending blockPrefix block_prefix_safe
  rw [block, legacy_append, afterPrefix]
  rfl

theorem legacy_rounds (n : Nat) (pending : List Nat) :
    legacyLoop 64 ⟨64, pending⟩ (rounds n) = ⟨64, List.replicate n 1 ++ pending⟩ := by
  induction n generalizing pending with
  | zero => rfl
  | succ n ih =>
      rw [rounds, legacy_append, legacy_block, ih]
      simp [List.replicate_add, List.append_assoc]

theorem legacy_starves_first (n : Nat) :
    0 ∉ (legacyLoop 64 ⟨64, []⟩ (rounds n)).pending := by
  rw [legacy_rounds]
  simp

theorem both_owners_offered (n : Nat) :
    0 ∈ offers (rounds (n + 1)) ∧ 1 ∈ offers (rounds (n + 1)) := by
  constructor
  · apply eligible_visit_offered _ (paused 0)
    · exact List.mem_append_left _ (by decide : paused 0 ∈ block)
    · rfl
  · apply eligible_visit_offered _ (paused 1)
    · exact List.mem_append_left _ (by decide : paused 1 ∈ block)
    · rfl

end Mettapedia.Machines.CollectionOfferScheduling
