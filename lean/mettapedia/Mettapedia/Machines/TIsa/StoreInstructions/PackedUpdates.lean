import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences

/-!
# The prepared word-array effects of TAKE and MAKE

TAKE compares identities, not value codes, and keeps surviving
occurrences in order. MAKE appends the next identity and refuses
when either header would overflow. These are array effects for a
private destination; a separate publication can install the complete
result. They do not authorize reads of a partially prepared array.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences

open Derivation (Store)

variable {V : Type*} (codes : Codes V)

def take (memory : Layout) (identity : ℕ) : Layout :=
  let remaining := memory.occurrences.filter fun row => row.1.toNat != identity
  ⟨BitVec.ofNat 64 remaining.size, remaining, memory.nextIdentity⟩

def make? (memory : Layout) (value : V) : Option Layout :=
  let next := memory.nextIdentity.toNat
  if memory.occurrences.size + 1 < 2 ^ 64 ∧ next + 1 < 2 ^ 64 then
    (packRow codes (next, value)).map fun row =>
      ⟨BitVec.ofNat 64 (memory.occurrences.size + 1), memory.occurrences.push row, BitVec.ofNat 64 (next + 1)⟩
  else none

private theorem same_identity {source : ℕ × V} {row : Row} (recorded : packRow codes source = some row) :
    row.1.toNat = source.1 := by
  have read := row_roundtrip codes recorded
  obtain ⟨value, _, same⟩ := Option.map_eq_some_iff.mp read
  exact congrArg Prod.fst same

private theorem packed_filter (records : List (ℕ × V)) {packed : List Row}
    (done : records.mapM (packRow codes) = some packed) (identity : ℕ) :
    (records.filter (fun item => item.1 != identity)).mapM (packRow codes) =
      some (packed.filter (fun row => row.1.toNat != identity)) := by
  induction records generalizing packed with
  | nil =>
    have empty : ([] : List Row) = packed := Option.some.inj done
    rw [← empty]
    rfl
  | cons first rest ih =>
    simp only [List.mapM_cons] at done
    obtain ⟨head, written, pending⟩ := Option.bind_eq_some_iff.mp done
    obtain ⟨tail, encoded, result⟩ := Option.bind_eq_some_iff.mp pending
    obtain rfl := (Option.some.inj result).symm
    have id := same_identity codes written
    cases keep : (first.1 != identity) <;>
      simp [id, keep, List.mapM_cons, written, ih encoded]

theorem pack_take {s : Store V} {memory : Layout}
    (formed : pack codes s = some memory) (identity : ℕ) :
    pack codes (s.remove identity) = some (take memory identity) := by
  unfold pack at formed
  split at formed
  next bounds =>
    obtain ⟨rows, packed, rfl⟩ := Option.map_eq_some_iff.mp formed
    have kept := packed_filter codes s.occurrences packed identity
    have available : (s.remove identity).occurrences.length < 2 ^ 64 ∧ (s.remove identity).fresh < 2 ^ 64 := by
      refine ⟨?_, bounds.2⟩
      exact (List.length_filter_le _ _).trans_lt bounds.1
    rw [pack, if_pos available]
    change (List.mapM (packRow codes) (s.occurrences.filter (fun row => row.1 != identity))).map _ = _
    rw [kept]
    let remaining := rows.filter fun row => row.1.toNat != identity
    have arrays : remaining.toArray = rows.toArray.filter (fun row => row.1.toNat != identity) := by
      apply Array.toList_inj.mp
      simp only [remaining, Array.toList_filter]
    change some (Layout.mk (BitVec.ofNat 64 remaining.toArray.size) remaining.toArray (BitVec.ofNat 64 s.fresh)) = _
    rw [arrays]
    rfl
  next => cases formed

theorem pack_make {s : Store V} {memory : Layout} (formed : pack codes s = some memory) (value : V) :
    pack codes (s.add value) = make? codes memory value := by
  unfold pack at formed
  split at formed
  next bounds =>
    obtain ⟨rows, packed, rfl⟩ := Option.map_eq_some_iff.mp formed
    have width := (rows_roundtrip codes s.occurrences packed).2
    have next : (BitVec.ofNat 64 s.fresh).toNat = s.fresh := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounds.2]
    have arrayWidth : rows.toArray.size = s.occurrences.length := width
    unfold pack make?
    dsimp only
    simp only [Store.add, List.length_append, List.length_singleton, next, arrayWidth]
    by_cases room : s.occurrences.length + 1 < 2 ^ 64 ∧ s.fresh + 1 < 2 ^ 64
    · simp only [if_pos room]
      rw [List.mapM_append, packed]
      cases encoded : packRow codes (s.fresh, value) with
      | none => simp [encoded]
      | some row =>
        have pushed : (rows ++ [row]).toArray = rows.toArray.push row := by
          apply Array.toList_inj.mp
          simp
        simp only [List.mapM_cons, List.mapM_nil, encoded, bind, Option.bind_some, pure, Option.map_some,
          List.length_append, List.length_singleton, width, pushed]
    · simp only [if_neg room]
  next => cases formed

namespace Examples

private def words : Codes Word := ⟨some, some, fun same => by cases same; rfl⟩
private def original : Store Word := ⟨[(7, 42), (9, 42)], 12⟩

theorem take_then_make_preserves_the_other_equal_value :
    ((pack words original).bind (fun memory => make? words (take memory 7) 42)).map
      (fun memory => memory.occurrences.toList) = some [(9, 42), (12, 42)] := by
  decide +kernel

theorem make_refuses_counter_wrap :
    make? words ⟨0, #[], 0xffffffffffffffff#64⟩ 42 = none := by
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences
