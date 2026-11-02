import Mathlib.Tactic

/-!
# Open addressing with a probe bound: exact membership in at most `L` probes

A table of `cap` slots places each key at the first free slot from its home,
`home k`, onward.  With homes nobody can predict, chains stay short; with a
fixed, public placement, crafted keys can share one home and make every probe
walk the whole chain.  A guard keeps every key within `L` slots of its home:
an insertion that finds no free slot there rebuilds the table (larger, or with
a fresh placement key) instead.

Under that invariant a lookup reads at most `L` slots, and stops after them
even when it finds no empty slot: a key not within `L` of its home is in no
slot.  The answers depend only on the keys stored, never on the placement:
keying the homes moves where keys sit, not what the table answers.

This file proves:
* `lookup_iff`: under the invariant, a lookup of `L` probes finds a key exactly
  when some slot holds it;
* `lookup_placement_free`: two tables holding the same keys, each under its
  own placement and invariant, answer every lookup alike;
* `insert_within`: placing a key at a free slot within `L` of its home keeps
  the invariant;
* `insert_found`: after such a placement, the lookup finds the key.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BoundedProbeTable

variable {Key : Type} [DecidableEq Key]

/-- `cap` slots, read at an index modulo `cap`. -/
structure Table (Key : Type) where
  cap : Nat
  cap_pos : 0 < cap
  slots : Nat → Option Key

/-- The slot `i` steps from `k`'s home. -/
def at_ (t : Table Key) (home : Key → Nat) (k : Key) (i : Nat) : Nat :=
  (home k + i) % t.cap

/-- Some slot below `cap` holds `k`. -/
def Holds (t : Table Key) (k : Key) : Prop := ∃ p < t.cap, t.slots p = some k

/-- The guard's invariant: every key a slot holds sits within `L` of its home. -/
def Within (t : Table Key) (home : Key → Nat) (L : Nat) : Prop :=
  ∀ p < t.cap, ∀ k, t.slots p = some k → ∃ i < L, at_ t home k i = p

/-- A lookup reads the `L` slots from the key's home. -/
def lookup (t : Table Key) (home : Key → Nat) (L : Nat) (k : Key) : Bool :=
  (List.range L).any (fun i => t.slots (at_ t home k i) == some k)

theorem lookup_iff (t : Table Key) (home : Key → Nat) (L : Nat)
    (inv : Within t home L) (k : Key) :
    lookup t home L k = true ↔ Holds t k := by
  unfold lookup Holds
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨at_ t home k i, Nat.mod_lt _ t.cap_pos, hi⟩
  · rintro ⟨p, hp, hk⟩
    obtain ⟨i, hi, hat⟩ := inv p hp k hk
    exact ⟨i, hi, by rw [hat]; exact hk⟩

/-- The answers do not depend on the placement: tables holding the same keys,
each under its own homes and invariant, answer alike. -/
theorem lookup_placement_free (t₁ t₂ : Table Key) (home₁ home₂ : Key → Nat)
    (L₁ L₂ : Nat) (inv₁ : Within t₁ home₁ L₁) (inv₂ : Within t₂ home₂ L₂)
    (same : ∀ k, Holds t₁ k ↔ Holds t₂ k) (k : Key) :
    lookup t₁ home₁ L₁ k = lookup t₂ home₂ L₂ k := by
  have h₁ := lookup_iff t₁ home₁ L₁ inv₁ k
  have h₂ := lookup_iff t₂ home₂ L₂ inv₂ k
  cases e₁ : lookup t₁ home₁ L₁ k <;> cases e₂ : lookup t₂ home₂ L₂ k <;>
    simp_all

/-- Place `k` at slot `p`. -/
def place (t : Table Key) (p : Nat) (k : Key) : Table Key :=
  { t with slots := fun q => if q = p then some k else t.slots q }

omit [DecidableEq Key] in
/-- Placing a key at a free slot within `L` of its home keeps the invariant. -/
theorem insert_within (t : Table Key) (home : Key → Nat) (L : Nat)
    (inv : Within t home L) (k : Key) (i : Nat) (hi : i < L) :
    Within (place t (at_ t home k i) k) home L := by
  intro p hp k' hk'
  simp only [place] at hk' hp
  by_cases hpe : p = at_ t home k i
  · simp only [hpe, if_true, Option.some.injEq] at hk'
    subst hk'
    exact ⟨i, hi, by simp [at_, place, hpe]⟩
  · simp only [hpe, if_false] at hk'
    obtain ⟨j, hj, hat⟩ := inv p hp k' hk'
    exact ⟨j, hj, by simpa [at_, place] using hat⟩

/-- After the placement, the lookup finds the key. -/
theorem insert_found (t : Table Key) (home : Key → Nat) (L : Nat)
    (inv : Within t home L) (k : Key) (i : Nat) (hi : i < L) :
    lookup (place t (at_ t home k i) k) home L k = true := by
  rw [lookup_iff _ home L (insert_within t home L inv k i hi)]
  refine ⟨at_ t home k i, Nat.mod_lt _ t.cap_pos, ?_⟩
  simp [place]

end Mettapedia.Machines.BoundedProbeTable
