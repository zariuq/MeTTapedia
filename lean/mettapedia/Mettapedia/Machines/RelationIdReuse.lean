import Mettapedia.Machines.RelationColumnOwnership
import Mathlib.Data.List.Nodup

/-!
# Dead numbering entries and current identifier meaning

A numbering dictionary stores raw IDs, not cached payloads. A dead entry may
remain in it without retaining that ID. Lookup after revival must use the
current universe meaning. Changing only unprotected IDs preserves every live
relation row, and the protected set must include other owners and snapshots,
not merely this relation's own holds.

Missing IDs remain explicit `none` values in the denotation; they are never
silently filtered out. Native number arrays, side indexes, finite-word bounds
and the discovery of the complete protected set are implementation duties.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationIdReuse

open RelationColumnOwnership

variable {Id Value : Type} [DecidableEq Id]

abbrev Lookup (Id Value : Type) := Id → Option Value

def denote (lookup : Lookup Id Value) (rows : List (List Id)) : List (List (Option Value)) :=
  rows.map (List.map lookup)

omit [DecidableEq Id] in
theorem denote_agrees (before after : Lookup Id Value) (rows : List (List Id))
    (agree : ∀ row ∈ rows, ∀ id ∈ row, before id = after id) :
    denote before rows = denote after rows := by
  apply List.map_congr_left
  intro row member
  exact List.map_congr_left (agree row member)

def Preserves (protectedIds : Finset Id) (before after : Lookup Id Value) : Prop :=
  ∀ id ∈ protectedIds, before id = after id

theorem protected_change_preserves_rows (state : State Id) (valid : state.Valid)
    (protectedIds : Finset Id) (covered : state.counters.owned ⊆ protectedIds)
    (before after : Lookup Id Value) (stable : Preserves protectedIds before after) :
    denote before state.rows = denote after state.rows := by
  apply denote_agrees
  intro row member id column
  exact stable id (covered ((owned_iff_live_column state valid id).mpr ⟨row, member, column⟩))

def reuse (protectedIds : Finset Id) (lookup : Lookup Id Value) (id : Id) (value : Value) : Option (Lookup Id Value) :=
  if id ∈ protectedIds then none else some (Function.update lookup id (some value))

theorem reuse_preserves (protectedIds : Finset Id) (before : Lookup Id Value) (id : Id) (value : Value)
    (after : Lookup Id Value) (accepted : reuse protectedIds before id value = some after) :
    Preserves protectedIds before after := by
  by_cases held : id ∈ protectedIds
  · simp [reuse, held] at accepted
  · have same : Function.update before id (some value) = after := by simpa [reuse, held] using accepted
    subst after
    intro observed member
    have apart : observed ≠ id := by intro equality; subst observed; exact held member
    simp [apart]

theorem reuse_preserves_rows (state : State Id) (valid : state.Valid)
    (protectedIds : Finset Id) (covered : state.counters.owned ⊆ protectedIds)
    (before after : Lookup Id Value) (id : Id) (value : Value)
    (accepted : reuse protectedIds before id value = some after) :
    denote before state.rows = denote after state.rows :=
  protected_change_preserves_rows state valid protectedIds covered before after
    (reuse_preserves protectedIds before id value after accepted)

theorem dead_id_has_no_live_column (state : State Id) (valid : state.Valid) (id : Id)
    (dead : state.counters.uses id = 0) : ∀ row ∈ state.rows, id ∉ row := by
  intro row member contains
  have held := (owned_iff_live_column state valid id).mpr ⟨row, member, contains⟩
  have positive := (valid.1 id).mp held
  omega

theorem change_dead_id_preserves_rows (state : State Id) (valid : state.Valid)
    (lookup : Lookup Id Value) (id : Id) (value : Value) (dead : state.counters.uses id = 0) :
    denote lookup state.rows = denote (Function.update lookup id (some value)) state.rows := by
  apply denote_agrees
  intro row member observed column
  have apart : observed ≠ id := by
    intro same
    subst observed
    exact dead_id_has_no_live_column state valid id dead row member column
  simp [apart]

/-- Pure numbering reservation may leave an unused dictionary entry after a
later refusal. It acquires no ownership by itself. -/
def reserve (dictionary : List Id) (id : Id) : List Id × Nat :=
  if id ∈ dictionary then (dictionary, dictionary.idxOf id)
  else (dictionary ++ [id], dictionary.length)

theorem reserve_names_id (dictionary : List Id) (id : Id) :
    (reserve dictionary id).1[(reserve dictionary id).2]? = some id := by
  by_cases present : id ∈ dictionary
  · simp [reserve, present, List.getElem?_idxOf]
  · simp [reserve, present]

theorem reserve_keeps_prefix (dictionary : List Id) (id : Id) :
    dictionary <+: (reserve dictionary id).1 := by
  by_cases present : id ∈ dictionary <;> simp [reserve, present]

theorem reserve_nodup (dictionary : List Id) (distinct : dictionary.Nodup) (id : Id) :
    (reserve dictionary id).1.Nodup := by
  by_cases present : id ∈ dictionary
  · simpa [reserve, present] using distinct
  · simpa [reserve, present] using List.Nodup.concat present distinct

theorem reserved_read_is_current (dictionary : List Id) (lookup : Lookup Id Value) (id : Id) :
    ((reserve dictionary id).1[(reserve dictionary id).2]?).bind lookup = lookup id := by
  rw [reserve_names_id]
  rfl

/-- Existing live indices survive appending an unused number. -/
theorem reserve_preserves_old_index (dictionary : List Id) (id : Id) (index : Nat)
    (bounded : index < dictionary.length) :
    (reserve dictionary id).1[index]? = dictionary[index]? := by
  by_cases present : id ∈ dictionary <;> simp [reserve, present, List.getElem?_append, bounded]

theorem revived_count_uses_new_columns (state : State Id) (row : List Id) (id : Id)
    (dead : state.counters.uses id = 0) :
    (insertRow state row).counters.uses id = row.count id := by
  simp [insertRow, holdColumns_uses, dead]

namespace Controls

def oldMeaning : Lookup Nat String := fun id => if id = 7 then some "old" else some "other"
def newMeaning : Lookup Nat String := Function.update oldMeaning 7 (some "new")
def oldRelation : State Nat := insertRow empty [7, 7]
def emptied : State Nat := (removeRow oldRelation [7, 7]).2

theorem dead_number_can_remain_without_a_hold :
    (reserve [7] 7).1 = [7] ∧ emptied.counters.uses 7 = 0 ∧ 7 ∉ emptied.counters.owned := by decide

theorem revival_reads_new_payload :
    ((reserve [7] 7).1[(reserve [7] 7).2]?).bind newMeaning = some "new" ∧
    denote newMeaning (insertRow emptied [7, 7]).rows = [[some "new", some "new"]] := by decide

theorem stale_payload_cache_is_wrong :
    oldMeaning 7 = some "old" ∧ newMeaning 7 = some "new" ∧ oldMeaning 7 ≠ newMeaning 7 := by decide

theorem this_relation_being_dead_does_not_release_a_snapshot :
    emptied.counters.owned = ∅ ∧
    (reuse ({7} : Finset Nat) oldMeaning 7 "new").isNone = true ∧
    denote oldMeaning [[7]] ≠ denote newMeaning [[7]] := by decide

theorem dead_side_entry_would_invent_a_new_fact :
    denote newMeaning emptied.rows = [] ∧ denote newMeaning [[7]] = [[some "new"]] := by decide

end Controls
end Mettapedia.Machines.RelationIdReuse
