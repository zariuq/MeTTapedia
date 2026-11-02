import Mettapedia.Machines.CMemory.Borrowing

/-!
# Spatial views with attenuated permissions

A view keeps an object's identity while restricting its byte range and rights.
Virtual addresses are computed separately from allocation identity. Restricting
a view twice is the same operation as restricting the original range once;
disjoint source ranges remain disjoint after restriction.

This is the general range/permission layer, independent of mask encodings,
hardware keys, grant validity checks and the C implementation. A view record is
not a release authority or a live loan. Overlapping authorized views need the
separate borrowing discipline; the final control makes that boundary explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.RegionViews

open Borrowing (Region)

universe u

structure Grant (Right : Type u) where
  region : Region
  virtualBase : Nat
  rights : List Right
  deriving DecidableEq

structure Request (Right : Type u) where
  offset : Nat
  count : Nat
  rights : List Right
  deriving DecidableEq

structure View (Right : Type u) where
  region : Region
  virtualAddress : Nat
  rights : List Right
  deriving DecidableEq

variable {Right : Type u}

def part (g : Grant Right) (q : Request Right) : Region :=
  ⟨g.region.root, g.region.first + q.offset, q.count⟩

def Allowed (g : Grant Right) (q : Request Right) : Prop :=
  0 < q.count ∧ q.offset + q.count ≤ g.region.count ∧
    ∀ right ∈ q.rights, right ∈ g.rights

instance [DecidableEq Right] (g : Grant Right) (q : Request Right) :
    Decidable (Allowed g q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def resolve [DecidableEq Right] (g : Grant Right) (q : Request Right) : Option (View Right) :=
  if Allowed g q then some ⟨part g q, g.virtualBase + q.offset, q.rights⟩ else none

theorem resolve_eq_some_iff [DecidableEq Right] {g : Grant Right} {q : Request Right}
    {v : View Right} :
    resolve g q = some v ↔
      Allowed g q ∧ v = ⟨part g q, g.virtualBase + q.offset, q.rights⟩ := by
  by_cases h : Allowed g q <;> simp [resolve, h, eq_comm]

theorem resolve_sound [DecidableEq Right] {g : Grant Right} {q : Request Right}
    {v : View Right} (h : resolve g q = some v) :
    g.region.Contains v.region ∧ 0 < v.region.count ∧
      ∀ right ∈ v.rights, right ∈ g.rights := by
  obtain ⟨allowed, rfl⟩ := resolve_eq_some_iff.mp h
  refine ⟨⟨rfl, ?_, ?_⟩, allowed.1, allowed.2.2⟩
  · simp [part]
  · dsimp [Region.finish, part]
    have bound := allowed.2.1
    omega

theorem address_end_le [DecidableEq Right] {g : Grant Right} {q : Request Right}
    {v : View Right} (h : resolve g q = some v) :
    v.virtualAddress + v.region.count ≤ g.virtualBase + g.region.count := by
  obtain ⟨allowed, rfl⟩ := resolve_eq_some_iff.mp h
  have bound := allowed.2.1
  dsimp [part]
  omega

theorem address_within_limit [DecidableEq Right] {g : Grant Right} {q : Request Right}
    {v : View Right} {limit : Nat} (h : resolve g q = some v)
    (bounded : g.virtualBase + g.region.count ≤ limit) :
    v.virtualAddress + v.region.count ≤ limit :=
  (address_end_le h).trans bounded

def View.asGrant (v : View Right) : Grant Right :=
  ⟨v.region, v.virtualAddress, v.rights⟩

theorem restrict_twice [DecidableEq Right] {g : Grant Right}
    {q₁ q₂ : Request Right} {v₁ v₂ : View Right}
    (first : resolve g q₁ = some v₁) (second : resolve v₁.asGrant q₂ = some v₂) :
    resolve g ⟨q₁.offset + q₂.offset, q₂.count, q₂.rights⟩ = some v₂ := by
  obtain ⟨a₁, rfl⟩ := resolve_eq_some_iff.mp first
  obtain ⟨a₂, rfl⟩ := resolve_eq_some_iff.mp second
  have small : q₂.offset + q₂.count ≤ q₁.count := by
    simpa [View.asGrant, part] using a₂.2.1
  have combined : Allowed g ⟨q₁.offset + q₂.offset, q₂.count, q₂.rights⟩ := by
    refine ⟨a₂.1, ?_, ?_⟩
    · have large := a₁.2.1
      dsimp
      omega
    · intro right member
      exact a₁.2.2 right (a₂.2.2 right member)
  apply resolve_eq_some_iff.mpr
  exact ⟨combined, by simp [part, View.asGrant, Nat.add_assoc]⟩

theorem disjoint_views [DecidableEq Right] {g₁ g₂ : Grant Right}
    {q₁ q₂ : Request Right} {v₁ v₂ : View Right}
    (apart : g₁.region.Disjoint g₂.region)
    (first : resolve g₁ q₁ = some v₁) (second : resolve g₂ q₂ = some v₂) :
    v₁.region.Disjoint v₂.region :=
  Region.disjoint_subregions apart (resolve_sound first).1 (resolve_sound second).1

def resolveHeld [DecidableEq Right] {Holder Slot : Type}
    (table : Holder → Slot → Option (Grant Right)) (holder : Holder) (slot : Slot)
    (q : Request Right) : Option (View Right) :=
  (table holder slot).bind fun grant => resolve grant q

/-- Unrelated table edits preserve the result; the complete looked-up grant,
including its rights and bounds, is the dependency of this policy query. -/
theorem unchanged_lookup [DecidableEq Right] {Holder Slot : Type}
    {before after : Holder → Slot → Option (Grant Right)} {holder : Holder} {slot : Slot}
    (same : before holder slot = after holder slot) (q : Request Right) :
    resolveHeld before holder slot q = resolveHeld after holder slot q := by
  simp only [resolveHeld, same]

theorem held_origin [DecidableEq Right] {Holder Slot : Type}
    {table : Holder → Slot → Option (Grant Right)} {holder : Holder} {slot : Slot}
    {q : Request Right} {v : View Right} (h : resolveHeld table holder slot q = some v) :
    ∃ grant, table holder slot = some grant ∧ grant.region.Contains v.region ∧
      ∀ right ∈ v.rights, right ∈ grant.rights := by
  cases lookup : table holder slot with
  | none => simp [resolveHeld, lookup] at h
  | some grant =>
    have result : resolve grant q = some v := by simpa [resolveHeld, lookup] using h
    exact ⟨grant, rfl, (resolve_sound result).1, (resolve_sound result).2.2⟩

namespace Controls

def readable : Grant Nat := ⟨⟨7, 0, 16⟩, 4096, [0, 1]⟩

theorem nonzero_offset : resolve readable ⟨3, 5, [1]⟩ =
    some ⟨⟨7, 3, 5⟩, 4099, [1]⟩ := by decide

theorem end_exceeds_parent : resolve readable ⟨15, 2, [1]⟩ = none := by decide

theorem rights_escalation : resolve readable ⟨0, 1, [2]⟩ = none := by decide

theorem zero_count : resolve readable ⟨0, 0, [1]⟩ = none := by decide

/-- Permission to form views alone does not establish exclusive access. -/
theorem authorized_views_may_overlap :
    resolve readable ⟨0, 4, [1]⟩ = some ⟨⟨7, 0, 4⟩, 4096, [1]⟩ ∧
    resolve readable ⟨2, 4, [1]⟩ = some ⟨⟨7, 2, 4⟩, 4098, [1]⟩ ∧
    ¬Region.Disjoint ⟨7, 0, 4⟩ ⟨7, 2, 4⟩ := by decide

def beforeRevocation : Nat → Nat → Option (Grant Nat) :=
  fun holder slot => if holder = 3 ∧ slot = 1024 then some readable else none

def afterRevocation : Nat → Nat → Option (Grant Nat) := fun _ _ => none

theorem revoked_lookup_refuses_old_view :
    resolveHeld beforeRevocation 3 1024 ⟨3, 5, [1]⟩ =
      some ⟨⟨7, 3, 5⟩, 4099, [1]⟩ ∧
    resolveHeld afterRevocation 3 1024 ⟨3, 5, [1]⟩ = none := by decide

end Controls

#print axioms resolve_sound
#print axioms restrict_twice
#print axioms disjoint_views
#print axioms held_origin
#print axioms unchanged_lookup
#print axioms Controls.revoked_lookup_refuses_old_view

end Mettapedia.Machines.CMemory.RegionViews
