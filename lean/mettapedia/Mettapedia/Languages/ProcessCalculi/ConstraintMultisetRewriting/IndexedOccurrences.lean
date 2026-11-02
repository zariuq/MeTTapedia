import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# An inexhaustible occurrence supply with exact multiset observations

Occurrence identities pair a fresh natural index with their immutable value.
Every finite bag can be represented, including duplicate equal values, and
every finite store has a fresh occurrence of each value. This is a semantic
supply for occurrence-complete simulations, not a physical storage layout.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {T : Type*} [DecidableEq T]

abbrev Occurrence (T : Type*) := Nat × T

def label (occurrence : Occurrence T) : T := occurrence.2

omit [DecidableEq T] in
theorem supply (world : Finset (Occurrence T)) (value : T) :
    ∃ occurrence, occurrence ∉ world ∧ label occurrence = value := by
  let next := (world.image Prod.fst).sup id + 1
  refine ⟨(next, value), ?_, rfl⟩
  intro member
  have seen : next ∈ world.image Prod.fst := Finset.mem_image.mpr ⟨(next, value), member, rfl⟩
  have bounded := Finset.le_sup (f := id) seen
  dsimp [next] at bounded
  omega

theorem realize (bag : Multiset T) :
    ∃ world : Finset (Occurrence T), labels label world = bag := by
  induction bag using Multiset.induction_on with
  | empty => exact ⟨∅, rfl⟩
  | cons value bag earlier =>
      obtain ⟨world, reconstructed⟩ := earlier
      obtain ⟨occurrence, fresh, atValue⟩ := supply world value
      refine ⟨insert occurrence world, ?_⟩
      change (insert occurrence world).val.map label = value ::ₘ bag
      rw [Finset.insert_val_of_notMem fresh, Multiset.map_cons, atValue]
      exact congrArg (Multiset.cons value) reconstructed

omit [DecidableEq T] in
theorem duplicate_values_need_distinct_occurrences (value : T)
    {world : Finset (Occurrence T)} (represented : labels label world = {value, value}) :
    world.card = 2 := by
  have cardinalities := congrArg Multiset.card represented
  simpa [labels] using cardinalities

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences
