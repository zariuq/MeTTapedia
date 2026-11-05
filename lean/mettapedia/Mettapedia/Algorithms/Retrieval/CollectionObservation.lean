import Mettapedia.Algebra.Collections.Folds
import Mettapedia.Algorithms.Retrieval.OrderedGroupedFold

/-!
# Occurrence observations and indexed lookup

An index changes how occurrences are found, not whether occurrences count.
The reference carrier here is a list: callers may observe its sequence, its
permutation class, or only membership. The existing `Collections.Folds.Model`
laws characterize which reductions may forget order or multiplicity.

Keyed lookup retains every matching occurrence. A functional map requires an
additional uniqueness contract; it is not implied by the use of a hash index.
Snapshots are values of the observation, not authority to mutate a source.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.CollectionObservation

variable {Row Key Bucket : Type*}

/-- Exact matching remains the authority even inside an indexed bucket. -/
def lookup (accepts : Key → Row → Bool) (key : Key) (rows : List Row) : List Row :=
  rows.filter (accepts key)

def indexedLookup [DecidableEq Bucket] (accepts : Key → Row → Bool)
    (keyHash : Key → Bucket) (rowHash : Row → Bucket)
    (key : Key) (rows : List Row) : List Row :=
  (rows.filter (fun row => decide (rowHash row = keyHash key))).filter (accepts key)

/-- Collisions are harmless: exact matching rejects them. Completeness needs
every matching occurrence in the selected bucket, not collision-free hashing.
The equality is of complete ordered occurrence lists, including duplicates. -/
theorem indexedLookup_eq_lookup [DecidableEq Bucket]
    (accepts : Key → Row → Bool) (keyHash : Key → Bucket) (rowHash : Row → Bucket)
    (compatible : ∀ key row, accepts key row = true → rowHash row = keyHash key)
    (key : Key) (rows : List Row) :
    indexedLookup accepts keyHash rowHash key rows = lookup accepts key rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      by_cases selected : accepts key row = true
      · simp [indexedLookup, lookup, selected, compatible key row selected] at *
        exact ih
      · have miss : accepts key row = false := Bool.eq_false_iff.mpr selected
        by_cases bucket : rowHash row = keyHash key <;>
          simpa [indexedLookup, lookup, miss, bucket] using ih

theorem lookup_insert (accepts : Key → Row → Bool) (key : Key)
    (rows : List Row) (row : Row) :
    lookup accepts key (rows ++ [row]) =
      lookup accepts key rows ++ (if accepts key row then [row] else []) := by
  cases observed : accepts key row <;> simp [lookup, observed]

/-- A changed source still admits an old key index only when its matching
rows remain in that bucket. The counterexample below shows why a revision
or another lifetime-validity mechanism is required for mutable keys. -/
example : indexedLookup (fun key row : Nat => decide (key = row))
    (fun _ => 0) (fun _ => 0) 1 [1, 2, 1] = [1, 1] := by decide +kernel

example : indexedLookup (fun key row : Nat => decide (key = row))
    (fun _ => 0) (fun _ => 1) 1 [1, 2, 1] ≠
      lookup (fun key row : Nat => decide (key = row)) 1 [1, 2, 1] := by
  decide +kernel

example : lookup (fun key row : Nat × Nat => decide (key.1 = row.1))
    (1, 0) [(1, 7), (1, 9)] = [(1, 7), (1, 9)] := by decide +kernel

/-- Deduplication preserves membership, but not the occurrence count used as
evidence. This distinction precedes any choice of physical storage. -/
theorem dedup_membership [DecidableEq Row] (rows : List Row) (row : Row) :
    row ∈ rows.dedup ↔ row ∈ rows := List.mem_dedup

example : ([1, 1] : List Nat).dedup.length ≠ ([1, 1] : List Nat).length := by
  decide +kernel

example : ([1, 2] : List Nat).Perm [2, 1] ∧ ([1, 2] : List Nat) ≠ [2, 1] := by
  constructor
  · exact List.Perm.swap _ _ []
  · decide +kernel

/-- A snapshot's lookup is unchanged by later insertion into a different
source value; re-observing the updated source includes the new occurrence. -/
theorem snapshot_vs_insert (accepts : Key → Row → Bool) (key : Key)
    (rows : List Row) (row : Row) (hit : accepts key row = true) :
    (lookup accepts key (rows ++ [row])).length =
      (lookup accepts key rows).length + 1 := by
  simp [lookup_insert, hit]

open Mettapedia.Algebra.Collections.Folds in
/-- The reused algebraic boundary: forgetting multiplicity additionally
requires idempotence; commutativity alone licenses only forgetting order. -/
theorem set_fold_conditions {A : Type*} (algebra : Model A) :
    algebra.MembershipInvariant ↔ algebra.PermutationInvariant ∧
      ∀ value, algebra.fold [value, value] = value :=
  algebra.membershipInvariant_iff

#print axioms indexedLookup_eq_lookup
#print axioms lookup_insert
#print axioms snapshot_vs_insert

end Mettapedia.Algorithms.Retrieval.CollectionObservation
