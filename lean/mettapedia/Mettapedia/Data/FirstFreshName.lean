import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# The first unoccupied name in an injective ordinal family

Some generated names are observable, so choosing any fresh string is too weak:
the allocator must pick the first available ordinal at or beyond its cursor.
Finite support and injectivity earn termination and the exact choice. No name
is reserved merely because a different spelling decodes to the same number.
-/

set_option autoImplicit false

namespace Mettapedia.FirstFreshName

variable {Name : Type} [DecidableEq Name]

theorem exists_fresh_bounded (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start : Nat) :
    ∃ next, start ≤ next ∧ next ≤ start + occupied.card ∧ encode next ∉ occupied := by
  by_contra absent
  have all : ∀ offset ∈ Finset.range (occupied.card + 1), encode (start + offset) ∈ occupied := by
    intro offset present
    by_contra fresh
    apply absent
    exact ⟨start + offset,by omega,by have := Finset.mem_range.mp present; omega,fresh⟩
  have bounded : (Finset.range (occupied.card + 1)).card ≤ occupied.card :=
    Finset.card_le_card_of_injOn (fun offset => encode (start + offset)) all
      (fun _ _ _ _ same => Nat.add_left_cancel (injective same))
  simp only [Finset.card_range] at bounded
  omega

theorem exists_fresh (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start : Nat) :
    ∃ next, start ≤ next ∧ encode next ∉ occupied := by
  obtain ⟨next,lower,_,fresh⟩ := exists_fresh_bounded encode injective occupied start
  exact ⟨next,lower,fresh⟩

/-- The computed first available ordinal; injectivity is proof-only evidence
that the search cannot exhaust its finite occupied support. -/
def choose (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start : Nat) : Nat :=
  Nat.find (exists_fresh encode injective occupied start)

theorem choose_spec (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start : Nat) :
    start ≤ choose encode injective occupied start ∧
      encode (choose encode injective occupied start) ∉ occupied :=
  Nat.find_spec (exists_fresh encode injective occupied start)

theorem choose_minimal (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start candidate : Nat)
    (lower : start ≤ candidate) (earlier : candidate < choose encode injective occupied start) :
    encode candidate ∈ occupied := by
  by_contra fresh
  have bound : choose encode injective occupied start ≤ candidate :=
    Nat.find_min' (exists_fresh encode injective occupied start) ⟨lower,fresh⟩
  omega

theorem choose_bound (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start : Nat) :
    choose encode injective occupied start ≤ start + occupied.card := by
  obtain ⟨next,lower,upper,fresh⟩ := exists_fresh_bounded encode injective occupied start
  have bound := Nat.find_min' (exists_fresh encode injective occupied start) ⟨lower,fresh⟩
  exact bound.trans upper

theorem choose_eq_iff (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start next : Nat) :
    choose encode injective occupied start = next ↔
      start ≤ next ∧ encode next ∉ occupied ∧
        ∀ earlier, start ≤ earlier → earlier < next → encode earlier ∈ occupied := by
  constructor
  · rintro rfl
    exact ⟨(choose_spec encode injective occupied start).1,
      (choose_spec encode injective occupied start).2,
      choose_minimal encode injective occupied start⟩
  · rintro ⟨lower,fresh,minimal⟩
    have upper : choose encode injective occupied start ≤ next :=
      Nat.find_min' (exists_fresh encode injective occupied start) ⟨lower,fresh⟩
    have notEarlier : ¬choose encode injective occupied start < next := by
      intro earlier
      exact (choose_spec encode injective occupied start).2
        (minimal _ (choose_spec encode injective occupied start).1 earlier)
    omega

/-- Recording the allocated name prevents its immediate reuse. -/
theorem after_recording_is_later (encode : Nat → Name) (injective : Function.Injective encode)
    (occupied : Finset Name) (start : Nat) :
    let first := choose encode injective occupied start
    first < choose encode injective (insert (encode first) occupied) first := by
  dsimp only
  have next := choose_spec encode injective
    (insert (encode (choose encode injective occupied start)) occupied)
    (choose encode injective occupied start)
  have different : choose encode injective (insert (encode (choose encode injective occupied start)) occupied)
      (choose encode injective occupied start) ≠ choose encode injective occupied start := by
    intro same
    apply next.2
    simp [same]
  omega

omit [DecidableEq Name] in
theorem constant_family_has_no_fresh_name (name : Name) :
    ¬∃ ordinal : Nat, (fun _ => name) ordinal ∉ ({name} : Finset Name) := by simp

end Mettapedia.FirstFreshName
