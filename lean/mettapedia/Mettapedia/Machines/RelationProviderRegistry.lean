import Mettapedia.Machines.RegistryIndexCost
import Mettapedia.Machines.RelationCapturedRoots

/-!
# Semantic root census over the indexed provider registry

Reuse the existing append/swap-removal carrier and its index-coherence laws.
Enumeration is supplied at collection time, not cached at registration time.
Provider keys denote complete callback/context identities in one universe;
the native encoding and completeness of the external owner census remain
representation obligations. The registry's cost model alone does not prove
that every live snapshot has enrolled its provider.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationProviderRegistry

open RegistryIndexCost RelationCapturedRoots ResourceOwnership
variable {Id Value : Type} [DecidableEq Id]

def Present (registry : Reg) (key : Nat) : Prop := registry.idx key ≠ none

def census (registry : Reg) (enumerate : Nat → Finset Id) : Finset Id :=
  (Finset.range registry.len).biUnion (fun position => enumerate (registry.slot position))

theorem mem_census (registry : Reg) (valid : Valid registry)
    (enumerate : Nat → Finset Id) (id : Id) :
    id ∈ census registry enumerate ↔ ∃ key, Present registry key ∧ id ∈ enumerate key := by
  constructor
  · intro member
    obtain ⟨position, bounded, member⟩ := Finset.mem_biUnion.mp member
    refine ⟨registry.slot position, ?_, member⟩
    have found := valid.1 position (Finset.mem_range.mp bounded)
    simp [Present, found]
  · rintro ⟨key, present, member⟩
    cases found : registry.idx key with
    | none => exact (present found).elim
    | some position =>
        obtain ⟨bounded, same⟩ := valid.2 key position found
        apply Finset.mem_biUnion.mpr
        exact ⟨position, Finset.mem_range.mpr bounded, by simpa [same] using member⟩

theorem add_present (registry : Reg) (key other : Nat) :
    Present (indexAdd registry key).1 other ↔ other = key ∨ Present registry other := by
  unfold indexAdd
  cases found : registry.idx key with
  | none =>
      by_cases same : other = key
      · subst other; simp [append, Present]
      · simp [append, Present, same]
  | some position =>
      by_cases same : other = key
      · subst other; simp [Present, found]
      · simp [same]

theorem remove_present (registry : Reg) (valid : Valid registry) (key other : Nat) :
    Present (indexRemove registry key).1 other ↔ other ≠ key ∧ Present registry other := by
  unfold indexRemove
  cases found : registry.idx key with
  | none =>
      by_cases same : other = key
      · subst other; simp [Present, found]
      · simp [same]
  | some position =>
      obtain ⟨bounded, selected⟩ := valid.2 key position found
      have lastBound : registry.len - 1 < registry.len := by omega
      have lastPresent := valid.1 (registry.len - 1) lastBound
      have lastDistinct (different : position ≠ registry.len - 1) :
          registry.slot (registry.len - 1) ≠ key := by
        intro same
        rw [same, found] at lastPresent
        exact different (Option.some.inj lastPresent)
      by_cases last : position = registry.len - 1
      · have selectedLast : registry.slot (registry.len - 1) = key := by simpa [last] using selected
        by_cases same : other = key
        · subst other; simp [Present, swapRemove, last, selectedLast]
        · simp [Present, swapRemove, last, selectedLast, same]
      · by_cases moved : other = registry.slot (registry.len - 1)
        · subst other
          simp [Present, swapRemove, last, lastPresent, lastDistinct last]
        · by_cases same : other = key
          · subst other; simp [Present, swapRemove, last, selected,
              Function.update_of_ne moved]
          · simp [Present, swapRemove, last, selected, Function.update_of_ne moved, same]

theorem census_add (registry : Reg) (valid : Valid registry) (key : Nat)
    (enumerate : Nat → Finset Id) :
    census (indexAdd registry key).1 enumerate = enumerate key ∪ census registry enumerate := by
  ext id
  rw [mem_census _ (valid_indexAdd registry valid key), Finset.mem_union,
    mem_census registry valid]
  simp only [add_present]
  constructor
  · rintro ⟨other, same | present, member⟩
    · subst other; exact Or.inl member
    · exact Or.inr ⟨other, present, member⟩
  · rintro (member | ⟨other, present, member⟩)
    · exact ⟨key, Or.inl rfl, member⟩
    · exact ⟨other, Or.inr present, member⟩

theorem census_remove (registry : Reg) (valid : Valid registry) (key : Nat)
    (enumerate : Nat → Finset Id) :
    census (indexRemove registry key).1 enumerate =
      census registry (fun other => if other = key then ∅ else enumerate other) := by
  ext id
  rw [mem_census _ (valid_indexRemove registry valid key), mem_census registry valid]
  simp only [remove_present registry valid]
  constructor
  · rintro ⟨other, ⟨different, present⟩, member⟩
    exact ⟨other, present, by simpa [different] using member⟩
  · rintro ⟨other, present, member⟩
    by_cases same : other = key
    · simp [same] at member
    · exact ⟨other, ⟨same, present⟩, by simpa [same] using member⟩

def roots (registry : Reg) (enumerate : Nat → Finset Id) : Roots Unit Id :=
  (census registry enumerate).image (fun id => ((), id))

theorem registered_snapshot_survives (registry : Reg) (valid : Valid registry)
    (views : Nat → Snapshot Id) (key : Nat) (present : Present registry key)
    (layout : (views key).Valid) (heap : Heap Id Value) (outside : Roots Unit Id)
    (allocated : ValidRoots heap (RelationCapturedRoots.roots (views key))) :
    readFields (views key) (RelationRootOwners.heapLookup
        (collect heap (roots registry (fun k => (listed (views k)).toFinset) ∪ outside))) =
      readFields (views key) (RelationRootOwners.heapLookup heap) := by
  apply collection_preserves_fields (views key) layout heap _ _ allocated
  intro address member
  obtain ⟨id, needed, same⟩ := Finset.mem_image.mp member
  subst address
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨id, ?_, rfl⟩
  exact (mem_census registry valid _ id).mpr ⟨key, present, needed⟩

namespace Controls

def two : Reg := (indexAdd (indexAdd empty 10).1 20).1
def shared : Nat → Finset Nat := fun key => if key = 10 then {7} else {7, 9}

theorem duplicate_registration_has_no_extra_slot :
    (indexAdd two 10).1.len = 2 := by decide

theorem last_slot_moves_without_losing_its_roots :
    (indexRemove two 10).1.idx 20 = some 0 ∧
      census (indexRemove two 10).1 shared = {7, 9} := by decide

theorem removing_one_owner_is_not_set_subtraction :
    census (indexRemove two 10).1 shared ≠ census two shared \ shared 10 := by decide

theorem stale_callback_results_miss_new_roots :
    let later := Function.update shared 20 {7, 9, 11}
    11 ∉ census two shared ∧ 11 ∈ census two later := by decide

end Controls
end Mettapedia.Machines.RelationProviderRegistry
