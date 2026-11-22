import Mathlib.Data.List.Basic

/-!
# Executable canonical metadata creation and stable lookup

Creation consults the actual registry. An existing key reuses its stored
index; a missing key appends exactly one entry at the old length. The fresh
identity is calculated from the finite state, not supplied by an oracle.
The representation is a verified reference implementation, with no claim
about a particular native index or its asymptotic lookup cost.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataRegistry

variable {K : Type*} [DecidableEq K]

def find (key : K) : List K → Option Nat
  | [] => none
  | head :: tail => if head = key then some 0 else (find key tail).map Nat.succ

theorem find_none_iff (key : K) (keys : List K) : find key keys = none ↔ key ∉ keys := by
  induction keys with
  | nil => simp [find]
  | cons head tail earlier =>
      by_cases same : head = key
      · simp [find, same]
      · have different : key ≠ head := Ne.symm same
        simp [find, same, earlier, different]

theorem find_get {key : K} {keys : List K} {index : Nat} (found : find key keys = some index) :
    keys[index]? = some key := by
  induction keys generalizing index with
  | nil => simp [find] at found
  | cons head tail earlier =>
      by_cases same : head = key
      · simp only [find, if_pos same, Option.some.injEq] at found
        subst index
        simpa using congrArg some same
      · simp only [find, if_neg same] at found
        obtain ⟨prior, known, rfl⟩ := Option.map_eq_some_iff.mp found
        simpa using earlier known

theorem find_bound {key : K} {keys : List K} {index : Nat} (found : find key keys = some index) :
    index < keys.length := (List.getElem?_eq_some_iff.mp (find_get found)).1

theorem find_append_retained (suffix : List K) {key : K} {keys : List K} {index : Nat}
    (found : find key keys = some index) : find key (keys ++ suffix) = some index := by
  induction keys generalizing index with
  | nil => simp [find] at found
  | cons head tail earlier =>
      by_cases same : head = key
      · simpa [find, same] using found
      · simp only [find, if_neg same] at found
        obtain ⟨prior, known, rfl⟩ := Option.map_eq_some_iff.mp found
        simp [find, same, earlier known]

theorem find_new_append (key : K) (keys : List K) (fresh : key ∉ keys) :
    find key (keys ++ [key]) = some keys.length := by
  induction keys with
  | nil => simp [find]
  | cons head tail earlier =>
      have different : head ≠ key := by intro same; exact fresh (List.mem_cons.mpr (Or.inl same.symm))
      have absent : key ∉ tail := fun member => fresh (List.mem_cons_of_mem _ member)
      simp [find, different, earlier absent]

structure Registry (K : Type*) where
  keys : List K
  unique : keys.Nodup

namespace Registry

def empty : Registry K := ⟨[], by simp⟩
def lookup (registry : Registry K) (key : K) : Option Nat := find key registry.keys

omit [DecidableEq K] in
private theorem appended_unique (registry : Registry K) (key : K) (fresh : key ∉ registry.keys) :
    (registry.keys ++ [key]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨registry.unique, by simp, ?_⟩
  intro first member second singleton same
  have equal : second = key := List.mem_singleton.mp singleton
  exact fresh ((same.trans equal) ▸ member)

/-- The result is the new actual registry, canonical ID, and whether one row
was created. A repeated lookup creates no extra metadata occurrence. -/
def intern (registry : Registry K) (key : K) : Registry K × Nat × Bool :=
  if fresh : registry.lookup key = none then
    (⟨registry.keys ++ [key], appended_unique registry key ((find_none_iff key _).mp fresh)⟩,
      registry.keys.length, true)
  else (registry, (registry.lookup key).getD registry.keys.length, false)

theorem intern_existing (registry : Registry K) (key : K) (index : Nat)
    (known : registry.lookup key = some index) : registry.intern key = (registry, index, false) := by
  simp [intern, known]

theorem intern_lookup (registry : Registry K) (key : K) :
    (registry.intern key).1.lookup key = some (registry.intern key).2.1 := by
  cases known : registry.lookup key with
  | some index => simp [intern, known]
  | none =>
      simp only [intern, dif_pos known]
      exact find_new_append key registry.keys ((find_none_iff key _).mp known)

theorem old_lookup_retained (registry : Registry K) (key other : K) (index : Nat)
    (known : registry.lookup other = some index) : (registry.intern key).1.lookup other = some index := by
  cases atKey : registry.lookup key with
  | some existing => simpa [intern, atKey] using known
  | none =>
      simp only [intern, dif_pos atKey]
      exact find_append_retained [key] known

theorem new_identity_is_actual_length (registry : Registry K) (key : K) (fresh : registry.lookup key = none) :
    (registry.intern key).2 = (registry.keys.length, true) ∧
      (registry.intern key).1.keys = registry.keys ++ [key] := by simp [intern, fresh]

theorem duplicate_creation_is_lookup (registry : Registry K) (key : K) :
    (registry.intern key).1.intern key = ((registry.intern key).1, (registry.intern key).2.1, false) :=
  intern_existing _ _ _ (registry.intern_lookup key)

theorem lookup_injective (registry : Registry K) {first second : K} {index : Nat}
    (left : registry.lookup first = some index) (right : registry.lookup second = some index) : first = second :=
  Option.some.inj ((find_get left).symm.trans (find_get right))

end Registry
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataRegistry
