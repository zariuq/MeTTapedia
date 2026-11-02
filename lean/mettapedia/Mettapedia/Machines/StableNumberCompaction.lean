import Mettapedia.Machines.RelationIdReuse

/-!
# Stable compaction of numbered entries

The worker scans a Boolean live mask and a dictionary together, retaining live
entries in their old order. Its relocation map is the number of live entries
strictly before the old coordinate. Lookup is proved against the original
dictionary, rather than defined by decoding the output. The map preserves
strict order on live coordinates and never moves a coordinate to the right.

Masks must cover the dictionary and callers must not relocate dead entries.
This is a finite-list correspondence, not a proof of an in-place C bit loop.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StableNumberCompaction

variable {Id : Type}

def pack : List Bool → List Id → List Id
  | [], _ => []
  | _, [] => []
  | live :: mask, id :: ids =>
      if live then id :: pack mask ids else pack mask ids

def rank (mask : List Bool) (index : Nat) : Nat := (mask.take index).count true

@[simp] theorem rank_zero (mask : List Bool) : rank mask 0 = 0 := rfl

@[simp] theorem rank_cons (live : Bool) (mask : List Bool) (index : Nat) :
    rank (live :: mask) (index + 1) = (if live then 1 else 0) + rank mask index := by
  cases live <;> simp [rank, Nat.add_comm]

theorem rank_le (mask : List Bool) (index : Nat) : rank mask index ≤ index := by
  exact List.count_le_length.trans (by simp [List.length_take])

theorem rank_strict (mask : List Bool) (first later : Nat)
    (live : mask[first]? = some true) (before : first < later) :
    rank mask first < rank mask later := by
  induction mask generalizing first later with
  | nil => simp at live
  | cons head mask ih =>
      cases first with
      | zero =>
          have head_live : head = true := by simpa using live
          subst head
          cases later with
          | zero => omega
          | succ later => simp
      | succ first =>
          cases later with
          | zero => omega
          | succ later =>
              have strict := ih first later (by simpa using live) (by omega)
              simp only [rank_cons]
              omega

/-- The compact coordinates have no gaps. -/
theorem rank_surjective (mask : List Bool) (index : Nat) (bounded : index < mask.count true) :
    ∃ old : Nat, mask[old]? = some true ∧ rank mask old = index := by
  induction mask generalizing index with
  | nil => simp at bounded
  | cons head mask ih =>
      cases head
      · obtain ⟨old, live, same⟩ := ih index (by simpa using bounded)
        exact ⟨old + 1, by simpa using live, by simpa using same⟩
      · cases index with
        | zero => exact ⟨0, rfl, rfl⟩
        | succ index =>
            obtain ⟨old, live, same⟩ := ih index (by simpa using bounded)
            exact ⟨old + 1, by simpa using live, by simp [same, Nat.add_comm]⟩

theorem pack_length (mask : List Bool) (ids : List Id) (size : mask.length = ids.length) :
    (pack mask ids).length = mask.count true := by
  induction mask generalizing ids with
  | nil => simp [pack]
  | cons live mask ih =>
      cases ids with
      | nil => simp at size
      | cons id ids =>
          have tail := ih ids (by simpa using size)
          cases live <;> simp [pack, tail]

theorem pack_sublist (mask : List Bool) (ids : List Id) : (pack mask ids).Sublist ids := by
  induction mask generalizing ids with
  | nil => simp [pack]
  | cons live mask ih =>
      cases ids with
      | nil => simp [pack]
      | cons id ids =>
          cases live
          · exact (ih ids).cons id
          · exact (ih ids).cons_cons id

theorem pack_nodup (mask : List Bool) (ids : List Id) (distinct : ids.Nodup) :
    (pack mask ids).Nodup := distinct.sublist (pack_sublist mask ids)

theorem relocated_lookup (mask : List Bool) (ids : List Id)
    (size : mask.length = ids.length) (index : Nat) (live : mask[index]? = some true) :
    (pack mask ids)[rank mask index]? = ids[index]? := by
  induction mask generalizing ids index with
  | nil => simp at live
  | cons head mask ih =>
      cases ids with
      | nil => simp at size
      | cons id ids =>
          have size_tail : mask.length = ids.length := by simpa using size
          cases index with
          | zero =>
              have head_live : head = true := by simpa using live
              simp [pack, head_live]
          | succ index =>
              have tail := ih ids size_tail index (by simpa using live)
              cases head <;>
                simpa only [pack, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
                  rank_cons, Nat.zero_add, Nat.one_add, List.getElem?_cons_succ] using tail

/-- Every output entry comes from a live original coordinate. -/
theorem pack_mem (mask : List Bool) (ids : List Id) (id : Id) :
    id ∈ pack mask ids ↔ ∃ index : Nat, mask[index]? = some true ∧ ids[index]? = some id := by
  induction mask generalizing ids with
  | nil => simp [pack]
  | cons live mask ih =>
      cases ids with
      | nil => simp [pack]
      | cons first ids =>
          constructor
          · intro member
            cases live
            · obtain ⟨index, kept, found⟩ := (ih ids).mp member
              exact ⟨index + 1, by simpa using kept, by simpa using found⟩
            · have choice : id = first ∨ id ∈ pack mask ids := by simpa [pack] using member
              rcases choice with rfl | member
              · exact ⟨0, rfl, rfl⟩
              · obtain ⟨index, kept, found⟩ := (ih ids).mp member
                exact ⟨index + 1, by simpa using kept, by simpa using found⟩
          · rintro ⟨index, kept, found⟩
            cases index with
            | zero =>
                have live_true : live = true := by simpa using kept
                have same : first = id := by simpa using found
                simp [pack, live_true, same]
            | succ index =>
                have member := (ih ids).mpr ⟨index, by simpa using kept, by simpa using found⟩
                cases live <;> simp [pack, member]

theorem rank_preserves_sorted (mask : List Bool) (indices : List Nat)
    (sorted : indices.Pairwise (· < ·)) (live : ∀ index ∈ indices, mask[index]? = some true) :
    (indices.map (rank mask)).Pairwise (· < ·) := by
  induction indices with
  | nil => simp
  | cons first rest ih =>
      rw [List.pairwise_cons] at sorted
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro later member
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        exact rank_strict mask first old (live first (by simp)) (sorted.1 old oldMember)
      · exact ih sorted.2 (fun index member => live index (by simp [member]))

/-- A destination bit is never written into an unread later source word.
The current source word still needs to be captured before clearing it. -/
theorem destination_word_not_future (mask : List Bool) (index width : Nat) :
    rank mask index / width ≤ index / width := Nat.div_le_div_right (rank_le mask index)

namespace Controls

theorem gaps_move_left_without_changing_meaning :
    pack [false, true, false, true] [8, 7, 6, 9] = [7, 9] ∧
    rank [false, true, false, true] 1 = 0 ∧
    rank [false, true, false, true] 3 = 1 := by decide

theorem old_coordinates_cannot_read_new_dictionary :
    ([8, 7, 6, 9] : List Nat)[1]? = some 7 ∧
    (pack [false, true, false, true] [8, 7, 6, 9])[1]? = some 9 := by decide

theorem dead_coordinate_requires_refusal :
    ([false, true] : List Bool)[0]? = some false ∧
    (pack [false, true] [8, 7])[rank [false, true] 0]? = some 7 := by decide

end Controls
end Mettapedia.Machines.StableNumberCompaction
