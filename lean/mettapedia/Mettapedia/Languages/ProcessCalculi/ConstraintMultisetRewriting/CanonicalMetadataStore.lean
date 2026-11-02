import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataRegistry
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Canonical finite private rows follow actual registry creation and lookup

The finite physical row set is updated by the same executable lookup/intern
operation as the registry. A repeated key creates no row. New identities use
the finite registry's actual prior length, and old identities and rows survive.
Every successful metadata query therefore has exactly one physical witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStore

open CanonicalMetadataRegistry

variable {K : Type*} [DecidableEq K]

private theorem find_append_other (key other : K) (different : other ≠ key) (keys : List K) :
    find other (keys ++ [key]) = find other keys := by
  induction keys with
  | nil => simp [find, Ne.symm different]
  | cons head tail earlier =>
      by_cases same : head = other
      · simp [find, same]
      · simp [find, same, earlier]

theorem lookup_other_after_intern (registry : Registry K) (key other : K) (different : other ≠ key) :
    (registry.intern key).1.lookup other = registry.lookup other := by
  cases known : registry.lookup key with
  | some index => rw [registry.intern_existing key index known]
  | none =>
      simp only [Registry.intern, dif_pos known]
      exact find_append_other key other different registry.keys

def Represents (registry : Registry K) (rows : Finset (Nat × K)) : Prop :=
  ∀ index key, (index, key) ∈ rows ↔ registry.lookup key = some index

private theorem rows_after_correct (registry : Registry K) (rows : Finset (Nat × K))
    (represented : Represents registry rows) (key : K) :
    Represents (registry.intern key).1
      (if registry.lookup key = none then insert (registry.keys.length, key) rows else rows) := by
  cases known : registry.lookup key with
  | some index =>
      rw [registry.intern_existing key index known]
      simp only [reduceCtorEq, if_false]
      exact represented
  | none =>
      change Represents (registry.intern key).1 (insert (registry.keys.length, key) rows)
      have freshResult := registry.new_identity_is_actual_length key known
      have keyLookup : (registry.intern key).1.lookup key = some registry.keys.length := by
        have found := registry.intern_lookup key
        rw [freshResult.1] at found
        exact found
      intro index other
      by_cases same : other = key
      · subst other
        rw [keyLookup]
        simp [represented index key, known, eq_comm]
      · rw [lookup_other_after_intern registry key other same]
        have different : (index, other) ≠ (registry.keys.length, key) :=
          fun equal => same (congrArg Prod.snd equal)
        simpa only [Finset.mem_insert, different, false_or] using represented index other

structure Store (K : Type*) [DecidableEq K] where
  registry : Registry K
  rows : Finset (Nat × K)
  represented : Represents registry rows

namespace Store

def empty : Store K where
  registry := Registry.empty
  rows := ∅
  represented := by intro index key; simp [Registry.lookup, Registry.empty, find]

def lookup (store : Store K) (key : K) : Option Nat := store.registry.lookup key

/-- A completed operation returns the updated actual store, canonical ID,
and whether the single new physical row was inserted. -/
def intern (store : Store K) (key : K) : Store K × Nat × Bool :=
  let result := store.registry.intern key
  (⟨result.1,
      if store.registry.lookup key = none then insert (store.registry.keys.length, key) store.rows else store.rows,
      rows_after_correct store.registry store.rows store.represented key⟩,
    result.2)

theorem after_lookup (store : Store K) (key : K) :
    (store.intern key).1.lookup key = some (store.intern key).2.1 := store.registry.intern_lookup key

theorem retained_lookup (store : Store K) (key other : K) (index : Nat)
    (known : store.lookup other = some index) : (store.intern key).1.lookup other = some index :=
  store.registry.old_lookup_retained key other index known

theorem old_rows_retained (store : Store K) (key : K) : store.rows ⊆ (store.intern key).1.rows := by
  change store.rows ⊆ if store.registry.lookup key = none then insert (store.registry.keys.length, key) store.rows else store.rows
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem repeated_lookup_creates_no_row (store : Store K) (key : K) (index : Nat)
    (known : store.lookup key = some index) :
    (store.intern key).1.rows = store.rows ∧ (store.intern key).2 = (index, false) := by
  change (if store.registry.lookup key = none then insert (store.registry.keys.length, key) store.rows else store.rows) = store.rows ∧ _
  simp [show store.registry.lookup key = some index from known,
    intern, store.registry.intern_existing key index known]

theorem actual_fresh_row (store : Store K) (key : K) (fresh : store.lookup key = none) :
    (store.intern key).1.rows = insert (store.registry.keys.length, key) store.rows ∧
      (store.intern key).2 = (store.registry.keys.length, true) := by
  constructor
  · change (if store.registry.lookup key = none then _ else _) = _
    rw [if_pos (show store.registry.lookup key = none from fresh)]
  · exact (store.registry.new_identity_is_actual_length key fresh).1

theorem canonical_row_unique (store : Store K) {key : K} {first second : Nat}
    (left : (first, key) ∈ store.rows) (right : (second, key) ∈ store.rows) : first = second :=
  Option.some.inj (((store.represented first key).mp left).symm.trans ((store.represented second key).mp right))

def query (store : Store K) (key : K) : Finset (Nat × K) := store.rows.filter (fun row => row.2 = key)

theorem query_of_present (store : Store K) (key : K) (index : Nat) (known : store.lookup key = some index) :
    store.query key = {(index, key)} := by
  ext row
  obtain ⟨otherIndex, otherKey⟩ := row
  by_cases same : otherKey = key
  · subst otherKey
    simp only [query, Finset.mem_filter, and_true, Finset.mem_singleton, Prod.mk.injEq]
    rw [store.represented, show store.registry.lookup key = some index from known]
    simp [eq_comm]
  · simp [query, same]

theorem query_of_absent (store : Store K) (key : K) (absent : store.lookup key = none) : store.query key = ∅ := by
  ext row
  obtain ⟨index, other⟩ := row
  by_cases same : other = key
  · subst other
    simp [query, store.represented index key, show store.registry.lookup key = none from absent]
  · simp [query, same]

theorem successful_read_has_one_witness (store : Store K) (key : K) (index : Nat) (known : store.lookup key = some index) :
    (store.query key).card = 1 := by rw [store.query_of_present key index known]; rfl

end Store
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStore
