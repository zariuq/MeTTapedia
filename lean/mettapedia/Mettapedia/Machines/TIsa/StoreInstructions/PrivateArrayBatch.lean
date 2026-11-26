import Mettapedia.Machines.TIsa.StoreInstructions.PrivateArrayPlan

/-!
# One private successor for a batch of takes and makes

Take tests use occurrence identities. Each survivor is copied
from its original coordinates, once, and newly made values
retain their order. The index is computed on the final snapshot,
never on a partially updated store.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PrivateArrayBatch

open Derivation (Store)
open PackedOccurrences (Codes Row Layout pack packRow)
open StorePublication (Snapshot)
open PrivateArrayPlan (Write Slot Operand evaluate copyRows rows dataContents contents literals)

def survivors (old : Layout) (taken : List ℕ) : List (Row × ℕ) :=
  old.occurrences.toList.zipIdx.filter (fun entry => !taken.contains entry.1.1.toNat)

def born {V : Type*} (start : ℕ) (made : List V) : List (ℕ × V) :=
  made.zipIdx.map (fun (value, offset) => (start + offset, value))

def allocate {V : Type*} (codes : Codes V) (old : Layout) (taken : List ℕ) (made : List V) :
    Option (Layout × List Write) :=
  let kept := survivors old taken
  let size := kept.length + made.length
  let fresh := old.nextIdentity.toNat + made.length
  if size < 2 ^ 64 ∧ fresh < 2 ^ 64 then do
    let inserted ← (born old.nextIdentity.toNat made).mapM (packRow codes)
    let data : Layout := ⟨BitVec.ofNat 64 size, ((kept.map Prod.fst) ++ inserted).toArray, BitVec.ofNat 64 fresh⟩
    let plan := [(.size, .literal data.sizeWord), (.nextIdentity, .literal data.nextIdentity)] ++
      copyRows kept 0 ++ literals (rows inserted kept.length)
    some (data, plan)
  else none

theorem keyed_survivors (old : Layout) (taken : List ℕ) :
    (survivors old taken).map Prod.fst =
      old.occurrences.toList.filter (fun entry => !taken.contains entry.1.toNat) := by
  have filtered := List.filter_map (l := old.occurrences.toList.zipIdx) (f := Prod.fst)
    (p := fun (entry : Row) => !taken.contains entry.1.toNat)
  rw [List.zipIdx_map_fst] at filtered
  exact filtered.symm

theorem resident_source (before : Snapshot) (taken : List ℕ) (entry : Row × ℕ)
    (found : entry ∈ survivors before.data taken) : before.data.occurrences[entry.2]? = some entry.1 := by
  have known := List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp found).1
  simpa only [Array.getElem?_toList] using known

private theorem packed_filter {V : Type*} (codes : Codes V) (atoms : List (ℕ × V)) (packed : List Row)
    (read : atoms.mapM (packRow codes) = some packed) (taken : List ℕ) :
    (atoms.filter (fun o => !taken.contains o.1)).mapM (packRow codes) =
      some (packed.filter (fun r => !taken.contains r.1.toNat)) := by
  induction atoms generalizing packed with
  | nil =>
    have same : [] = packed := Option.some.inj read
    subst packed
    rfl
  | cons head rest ih =>
    rw [List.mapM_cons] at read
    obtain ⟨row, packedHead, tail⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨more, packedTail, returns⟩ := Option.bind_eq_some_iff.mp tail
    have same : row :: more = packed := Option.some.inj returns
    subst packed
    obtain ⟨_, _, decoded⟩ := Option.map_eq_some_iff.mp (PackedOccurrences.row_roundtrip codes packedHead)
    have identity : row.1.toNat = head.1 := congrArg Prod.fst decoded
    cases chosen : !taken.contains head.1
    · simp only [List.filter_cons, identity, chosen, Bool.false_eq_true, if_false, ih _ packedTail]
    · simp only [List.filter_cons, identity, chosen, if_true, List.mapM_cons, packedHead, ih _ packedTail,
        bind, pure, Option.bind_some]

/-- The one-batch preparation computes the same ordered
store as the language's scalar take and make instructions. -/
theorem allocate_exact {V : Type*} (codes : Codes V) {old : Layout} {source : Store V}
    (held : pack codes source = some old) (taken : List ℕ) (made : List V) :
    (allocate codes old taken made).map Prod.fst = pack codes ((source.takeAll taken).makeAll made) := by
  unfold pack at held
  split at held
  next beforeFits =>
    obtain ⟨raw, packed, rfl⟩ := Option.map_eq_some_iff.mp held
    let old : Layout := ⟨BitVec.ofNat 64 raw.length, raw.toArray, BitVec.ofNat 64 source.fresh⟩
    let kept := survivors old taken
    let live := source.occurrences.filter (fun o => !taken.contains o.1)
    have livePacked : live.mapM (packRow codes) = some (kept.map Prod.fst) := by
      rw [keyed_survivors]
      exact packed_filter codes source.occurrences raw packed taken
    have width : (survivors old taken).length = live.length := by
      simpa only [List.length_map] using (PackedOccurrences.rows_roundtrip codes live livePacked).2
    have fresh : old.nextIdentity.toNat = source.fresh := by
      simp only [old, BitVec.toNat_ofNat, Nat.mod_eq_of_lt beforeFits.2]
    have middle := Store.takeAll_occurrences source taken
    have target := Store.makeAll_occurrences (source.takeAll taken) made
    have labels : ((source.takeAll taken).makeAll made).occurrences = live ++ born source.fresh made := by
      rw [target.1, middle.1, middle.2]
      rfl
    have high : ((source.takeAll taken).makeAll made).fresh = source.fresh + made.length := target.2.trans (by rw [middle.2])
    have appended : ((live ++ born source.fresh made).mapM (packRow codes)) =
        ((born source.fresh made).mapM (packRow codes)).map ((kept.map Prod.fst) ++ ·) := by
      rw [List.mapM_append, livePacked]
      cases (born source.fresh made).mapM (packRow codes) <;> rfl
    change (allocate codes old taken made).map Prod.fst = _
    unfold pack
    rw [labels, high, appended]
    simp only [allocate, fresh, List.length_append, born, List.length_map, List.length_zipIdx, width]
    by_cases fits : live.length + made.length < 2 ^ 64 ∧ source.fresh + made.length < 2 ^ 64
    · simp only [if_pos fits]
      cases ready : ((made.zipIdx.map (fun o => (source.fresh + o.2, o.1))).mapM (packRow codes)) with
      | none => rfl
      | some new =>
        have newSize : new.length = made.length := by
          simpa only [born, List.length_map, List.length_zipIdx] using (PackedOccurrences.rows_roundtrip codes _ ready).2
        simp only [bind, Option.bind_some, Option.map_some, List.length_append, List.length_map, newSize,
          show kept.length = live.length from width]
        rfl
    · simp only [if_neg fits, Option.map_none]
  next => cases held

theorem evaluate_allocate {V : Type*} (codes : Codes V) (before : Snapshot) (taken : List ℕ) (made : List V)
    {after : Layout} {plan : List Write} (ready : allocate codes before.data taken made = some (after, plan)) :
    evaluate before plan = some (dataContents after) := by
  simp only [allocate] at ready
  split at ready
  · obtain ⟨new, _, produced⟩ := Option.bind_eq_some_iff.mp ready
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj produced)
    have copied := PrivateArrayPlan.evaluate_copyRows before (survivors before.data taken) 0 (resident_source before taken)
    rw [PrivateArrayPlan.evaluate_append, PrivateArrayPlan.evaluate_append, copied, PrivateArrayPlan.evaluate_literals]
    simp only [dataContents, PrivateArrayPlan.rows_append, List.length_map, Nat.zero_add]
    rfl
  · cases ready

def assemble {V : Type*} {keys : ℕ} (codes : Codes V) (classify : V → Fin keys) (before : Snapshot)
    (taken : List ℕ) (made : List V) : Option (Snapshot × List Write) := do
  let (data, moves) ← allocate codes before.data taken made
  let target ← StorePublication.indexPrepared codes classify data
  some (target, moves ++ literals (PrivateArrayPlan.indexContents target.index))

theorem assembled {V : Type*} {keys : ℕ} (codes : Codes V) (classify : V → Fin keys)
    {source : Store V} {before target : Snapshot} {taken : List ℕ} {made : List V} {plan : List Write}
    (packed : StorePublication.encode codes classify source = some before)
    (ready : assemble codes classify before taken made = some (target, plan)) :
    StorePublication.encode codes classify ((source.takeAll taken).makeAll made) = some target ∧
      evaluate before plan = some (contents target) := by
  obtain ⟨⟨data, moves⟩, allocated, later⟩ := Option.bind_eq_some_iff.mp ready
  obtain ⟨complete, indexed, final⟩ := Option.bind_eq_some_iff.mp later
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj final)
  have packedNext := allocate_exact codes (StorePublication.encode_views codes classify packed).1 taken made
  rw [allocated, Option.map_some] at packedNext
  have packedNext' := packedNext.symm
  have read := (PackedOccurrences.pack_roundtrip codes packedNext').1
  simp only [StorePublication.indexPrepared, read] at indexed
  obtain ⟨index, built, rfl⟩ := Option.map_eq_some_iff.mp indexed
  exact ⟨by simp only [StorePublication.encode, packedNext', bind, Option.bind_some, built, pure],
    by rw [PrivateArrayPlan.evaluate_append, evaluate_allocate codes before taken made allocated,
      PrivateArrayPlan.evaluate_literals]; rfl⟩

namespace Examples

private def old : Layout := ⟨3, #[(5, 20), (6, 30), (7, 20)], 8⟩

theorem an_equal_successor_keeps_its_own_source :
    (survivors old [5, 6]).map Prod.snd = [2] ∧
      (survivors old [5, 6]).map (fun s => s.1.1) = [7] := by decide +kernel

theorem taking_an_equal_value_is_not_taking_its_other_occurrence :
    (survivors old [5]).length ≠ 1 := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PrivateArrayBatch
