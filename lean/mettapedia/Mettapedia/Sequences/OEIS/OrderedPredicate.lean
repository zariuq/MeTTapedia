import Mathlib.Data.Nat.Nth
import Mettapedia.Sequences.OEIS.Basic

/-!
# Ordered enumerations of decidable or mathematical predicates

Many OEIS entries enumerate the natural numbers satisfying a predicate rather
than giving a closed formula for the value at each index.  `Nat.nth` supplies
the ordered enumeration, but returns zero after the end of a finite predicate.
The `Available` domain below records exactly when that fallback is not used.
This lets finite and infinite enumerations share one honest `SequenceSpec`.
-/

namespace Mettapedia.Sequences.OEIS.OrderedPredicate

open Set

/-- Position `position` exists in the ordered enumeration of `p`.

For an infinite predicate this is automatic.  For a finite predicate it says
that the position lies strictly below the number of satisfying naturals. -/
def Available (p : Nat → Prop) (position : Nat) : Prop :=
  ∀ finite : (setOf p).Finite, position < finite.toFinset.card

/-- The integer-sequence specification that enumerates the naturals satisfying
`p` in increasing order.  Its domain excludes `Nat.nth`'s out-of-range zero. -/
noncomputable def spec (offset : Int) (p : Nat → Prop) : SequenceSpec where
  offset := offset
  Domain := fun index =>
    offset ≤ index ∧ Available p (index - offset).toNat
  value := fun index => Int.ofNat (Nat.nth p (index - offset).toNat)

theorem available_of_infinite {p : Nat → Prop} (infinite : (setOf p).Infinite)
    (position : Nat) : Available p position := by
  intro finite
  exact (infinite finite).elim

@[simp]
theorem domain_index_iff (offset : Int) (p : Nat → Prop) (position : Nat) :
    (spec offset p).Domain ((spec offset p).index position) ↔ Available p position := by
  simp [spec, SequenceSpec.index]

@[simp]
theorem value_index (offset : Int) (p : Nat → Prop) (position : Nat) :
    (spec offset p).value ((spec offset p).index position) =
      Int.ofNat (Nat.nth p position) := by
  simp [spec, SequenceSpec.index]

/-- Every in-domain value of the ordered specification satisfies its defining
predicate. -/
theorem value_satisfies (offset : Int) (p : Nat → Prop) (position : Nat)
    (available : (spec offset p).Domain ((spec offset p).index position)) :
    p (Nat.nth p position) := by
  exact Nat.nth_mem (p := p) position
    ((domain_index_iff offset p position).mp available)

/-- In-domain positions are enumerated strictly increasingly. -/
theorem value_strictly_increases (offset : Int) (p : Nat → Prop)
    {earlier later : Nat} (order : earlier < later)
    (available : (spec offset p).Domain ((spec offset p).index later)) :
    (spec offset p).value ((spec offset p).index earlier) <
      (spec offset p).value ((spec offset p).index later) := by
  rw [value_index, value_index]
  exact Int.ofNat_lt.mpr <|
    Nat.nth_lt_nth' (p := p) order
      ((domain_index_iff offset p later).mp available)

/-- For an infinite predicate the ordered specification is defined at every
enumeration position. -/
theorem domain_all_of_infinite (offset : Int) {p : Nat → Prop}
    (infinite : (setOf p).Infinite) (position : Nat) :
    (spec offset p).Domain ((spec offset p).index position) := by
  exact (domain_index_iff offset p position).mpr
    (available_of_infinite infinite position)

/-! Small boundary fixtures: the universal predicate gives the identity
enumeration, while the empty predicate has no available first element. -/

theorem universal_value (offset : Int) (position : Nat) :
    (spec offset (fun _ : Nat => True)).value
        ((spec offset (fun _ : Nat => True)).index position) = Int.ofNat position := by
  simp

theorem empty_has_no_first : ¬ Available (fun _ : Nat => False) 0 := by
  intro available
  have finite : (setOf (fun _ : Nat => False)).Finite := by
    simpa only [setOf_false] using (Set.finite_empty : (∅ : Set Nat).Finite)
  have := available finite
  simp at this

theorem empty_domain_is_empty (offset : Int) (position : Nat) :
    ¬ (spec offset (fun _ : Nat => False)).Domain
      ((spec offset (fun _ : Nat => False)).index position) := by
  intro inDomain
  have available := (domain_index_iff offset (fun _ : Nat => False) position).mp inDomain
  have finite : (setOf (fun _ : Nat => False)).Finite := by
    simpa only [setOf_false] using (Set.finite_empty : (∅ : Set Nat).Finite)
  have below := available finite
  simp at below

#print axioms value_satisfies
#print axioms value_strictly_increases
#print axioms empty_has_no_first

end Mettapedia.Sequences.OEIS.OrderedPredicate
