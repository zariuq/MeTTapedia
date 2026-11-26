import Mettapedia.GSLT.Equations.ReadoutDeltas
import Mathlib.Data.Finset.Card

/-! # Count the occurrences, not the classes or proof paths

The weights in a readout can be taken from the actual raw posting
fibres. Identities, not payload equality, distinguish copies. Adding or
removing one identity has a single-key effect on the histogram. The
capture of a current occurrence set and the authorization to edit it
are separate from this algebra.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.OccurrenceReadouts

open ReadoutDeltas
open scoped BigOperators

variable {Id Key : Type*} [DecidableEq Key]

def counts (live : Finset Id) (key : Id → Key) (k : Key) : Int :=
  mass live (fun r => decide (key r = k)) (fun _ => 1)

theorem counts_eq_histogram (live : Finset Id) (key : Id → Key) (k : Key) :
    counts live key k = histogram live key (fun _ => (1 : Int)) k := by
  rw [counts, mass, histogram, Finset.sum_filter]
  simp only [contribution, decide_eq_true_eq]

/-- Count on an entry list of distinct identities is the sum of raw
posting counts. Copies with identical payloads contribute independently.
The key domain can include additional (currently empty) postings. -/
theorem exact_count [DecidableEq Id] (xs : List Id) (distinct : xs.Nodup)
    (key : Id → Key) (domain : Finset Key) (covers : xs.toFinset.image key ⊆ domain)
    (accept : Key → Bool) :
    mass domain accept (counts xs.toFinset key) = ((xs.filter (accept ∘ key)).length : Int) := by
  have sameTotal :
      mass (xs.toFinset.image key) accept (counts xs.toFinset key) =
        mass domain accept (counts xs.toFinset key) := by
    apply Finset.sum_subset covers
    intro k _ empty
    have absent : xs.toFinset.filter (fun r => key r = k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r found
      obtain ⟨mem, equal⟩ := Finset.mem_filter.mp found
      exact empty (equal ▸ Finset.mem_image_of_mem key mem)
    simp [contribution, counts_eq_histogram, histogram, absent]
  have fibre : counts xs.toFinset key = histogram xs.toFinset key (fun _ => (1 : Int)) :=
    funext (counts_eq_histogram xs.toFinset key)
  rw [← sameTotal, fibre, ← regroup]
  simp only [mass, contribution, ← Finset.sum_filter, ← List.toFinset_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, List.toFinset_card_of_nodup (distinct.filter _)]

theorem count_insert [DecidableEq Id] (live : Finset Id) (key : Id → Key) (r : Id)
    (fresh : r ∉ live) (k : Key) :
    counts (insert r live) key k = counts live key k + (if key r = k then 1 else 0) := by
  simp only [counts, mass, Finset.sum_insert fresh, contribution, decide_eq_true_eq]
  exact add_comm _ _

theorem count_erase [DecidableEq Id] (live : Finset Id) (key : Id → Key) (r : Id)
    (present : r ∈ live) (k : Key) :
    counts (live.erase r) key k = counts live key k - (if key r = k then 1 else 0) := by
  have restore := count_insert (live.erase r) key r (Finset.notMem_erase r live) k
  rw [Finset.insert_erase present] at restore
  exact eq_sub_of_add_eq restore.symm

/-- A materialized count after row and equation changes agrees with a
new occurrence read. The supplied deltas are not themselves authority to
insert or remove an occurrence. -/
theorem refresh_exact [DecidableEq Id] (before after : List Id)
    (beforeDistinct : before.Nodup) (afterDistinct : after.Nodup)
    (key : Id → Key) (domain changedMask changedRows : Finset Key)
    (coversBefore : before.toFinset.image key ⊆ domain)
    (coversAfter : after.toFinset.image key ⊆ domain)
    (old new : Key → Bool)
    (maskIn : changedMask ⊆ domain) (rowsIn : changedRows ⊆ domain)
    (maskFrame : ∀ k ∈ domain, k ∉ changedMask → old k = new k)
    (rowFrame : ∀ k ∈ domain, k ∉ changedRows →
      counts before.toFinset key k = counts after.toFinset key k) :
    ((after.filter (new ∘ key)).length : Int) =
      ((before.filter (old ∘ key)).length : Int) +
        maskDelta changedMask old new (counts before.toFinset key) +
        rowDelta changedRows new (counts before.toFinset key) (counts after.toFinset key) := by
  rw [← exact_count before beforeDistinct key domain coversBefore old,
    ← exact_count after afterDistinct key domain coversAfter new]
  exact sparse_delta domain changedMask changedRows old new _ _
    maskIn rowsIn maskFrame rowFrame

namespace Examples

/-- Removing the first of two equal-payload occurrences decrements the
count by one, not by the size of its equivalence class. -/
theorem two_occurrences_one_key :
    counts ({10, 11} : Finset Nat) (fun _ => false) false = 2 ∧
    counts (({10, 11} : Finset Nat).erase 10) (fun _ => false) false = 1 := by
  have two : counts ({10, 11} : Finset Nat) (fun _ => false) false = 2 := by
    simp [counts, mass, contribution]
  refine ⟨two, ?_⟩
  rw [count_erase _ _ _ (by simp) _, two]
  decide

end Examples

end Mettapedia.GSLT.Equations.OccurrenceReadouts
