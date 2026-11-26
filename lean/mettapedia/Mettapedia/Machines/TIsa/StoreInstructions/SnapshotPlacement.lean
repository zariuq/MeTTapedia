import Mettapedia.Machines.TIsa.StoreInstructions.NativePreparation
import Mettapedia.Machines.TIsa.StoreInstructions.WordRegion

/-!
# Contiguous placement of a store snapshot

The header precedes the occurrence array, the key directory, and
the posting array. Valid fields have distinct whole-word homes.
Offsets are nonnegative signed dwords, while a bank can lie in
either canonical half of the native address space.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SnapshotPlacement

open PrivateArrayPlan (Slot read)
open StorePublication (Snapshot)
open NativePreparation (AddressMap)
open X86PlacedMemory (Cell footprint)
open X86CanonicalSpan (Area)

def count (snapshot : Snapshot) : ℕ :=
  2 + 2 * snapshot.data.occurrences.size + 2 * snapshot.index.directory.size + snapshot.index.postings.size

def Available (snapshot : Snapshot) : Slot → Prop
  | .size | .nextIdentity => True
  | .identity i | .value i => i < snapshot.data.occurrences.size
  | .start i | .length i => i < snapshot.index.directory.size
  | .posting i => i < snapshot.index.postings.size

instance (snapshot : Snapshot) (field : Slot) : Decidable (Available snapshot field) := by
  cases field <;> unfold Available <;> infer_instance

def position (snapshot : Snapshot) : Slot → ℕ
  | .size => 0
  | .nextIdentity => 1
  | .identity i => 2 + 2 * i
  | .value i => 2 + 2 * i + 1
  | .start i => 2 + 2 * snapshot.data.occurrences.size + 2 * i
  | .length i => 2 + 2 * snapshot.data.occurrences.size + 2 * i + 1
  | .posting i => 2 + 2 * snapshot.data.occurrences.size + 2 * snapshot.index.directory.size + i

theorem packed_fields {snapshot : Snapshot} {field : Slot} {word : Word}
    (present : read snapshot field = some word) : Available snapshot field := by
  cases field <;> unfold Available
  case size => trivial
  case nextIdentity => trivial
  all_goals
    first
    | exact (Array.getElem?_eq_some_iff.mp present).choose
    | obtain ⟨_, selected, _⟩ := Option.map_eq_some_iff.mp present
      exact (Array.getElem?_eq_some_iff.mp selected).choose

theorem position_bound {snapshot : Snapshot} {field : Slot} (available : Available snapshot field) :
    position snapshot field < count snapshot := by
  cases field <;> simp only [position, Available, count] at available ⊢ <;> omega

theorem position_inj {snapshot : Snapshot} {left right : Slot}
    (l : Available snapshot left) (r : Available snapshot right)
    (same : position snapshot left = position snapshot right) : left = right := by
  cases left <;> cases right <;> simp only [Available, position] at *
  all_goals first | rfl | (congr 1; omega)

def safePosition (snapshot : Snapshot) (field : Slot) : Fin (count snapshot) :=
  if available : Available snapshot field then ⟨position snapshot field, position_bound available⟩
  else ⟨0, by unfold count; omega⟩

theorem safe_exact {snapshot : Snapshot} {field : Slot} (available : Available snapshot field) :
    (safePosition snapshot field).val = position snapshot field := by
  rw [safePosition, dif_pos available]

structure Bank (snapshot : Snapshot) where
  pointer : Word
  aligned : pointer.toNat % 8 = 0
  area : Area pointer (8 * count snapshot)
  shortOffset : 8 * count snapshot ≤ 2 ^ 31

def Bank.atLow (snapshot : Snapshot) (base : ℕ)
    (aligned : base % 8 = 0) (bounds : base + 8 * count snapshot ≤ 2 ^ 47)
    (shortOffset : 8 * count snapshot ≤ 2 ^ 31) : Bank snapshot := by
  let ptr := BitVec.ofNat 64 base
  have address : ptr.toNat = base := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : base < 2 ^ 64)]
  refine ⟨ptr, address.symm ▸ aligned, ⟨?_, ?_⟩, shortOffset⟩
  · rw [address]; omega
  · intro shift inside
    apply Or.inl
    rw [X86CanonicalSpan.add_toNat _ _ (by rw [address]; omega), address]
    omega

variable {snapshot : Snapshot}

def byteOffset (snapshot : Snapshot) (field : Slot) : ℕ :=
  WordRegion.offset (safePosition snapshot field)

def Bank.region (bank : Bank snapshot) : WordRegion.Region (count snapshot) :=
  ⟨bank.pointer, bank.aligned, bank.area, bank.shortOffset⟩

def Bank.cell (bank : Bank snapshot) (field : Slot) :
    Cell bank.pointer (BitVec.ofNat 32 (byteOffset snapshot field)) :=
  bank.region.cell (safePosition snapshot field)

def Bank.addressMap (bank : Bank snapshot) : AddressMap bank.pointer :=
  ⟨fun field => BitVec.ofNat 32 (byteOffset snapshot field), bank.cell⟩

/-- Two available fields of a snapshot cannot share a byte. -/
theorem Bank.disjoint_fields (bank : Bank snapshot) {left right : Slot}
    (l : Available snapshot left) (r : Available snapshot right) (distinct : left ≠ right) :
    Disjoint (footprint (bank.addressMap.addr left)) (footprint (bank.addressMap.addr right)) := by
  apply bank.region.separate_words
  intro same
  have equal := congrArg Fin.val same
  rw [safe_exact l, safe_exact r] at equal
  exact distinct (position_inj l r equal)

theorem Bank.disjoint_banks (old : Bank snapshot) {newSnapshot : Snapshot} (next : Bank newSnapshot)
    (before : old.pointer.toNat + 8 * count snapshot ≤ next.pointer.toNat)
    (left right : Slot) : Disjoint (footprint (old.addressMap.addr left)) (footprint (next.addressMap.addr right)) :=
  old.region.separate_banks next.region before (safePosition snapshot left) (safePosition newSnapshot right)

private theorem paired_range {A : Type*} (xs : List A) (base first : ℕ) :
    (xs.zipIdx first).flatMap (fun p => [base + 2 * p.2, base + 2 * p.2 + 1]) =
      List.range' (base + 2 * first) (2 * xs.length) := by
  induction xs generalizing first with
  | nil => rfl
  | cons x tail ih =>
    rw [List.zipIdx_cons, List.flatMap_cons, ih]
    change [base + 2 * first, base + 2 * first + 1] ++ List.range' (base + 2 * (first + 1)) (2 * tail.length) =
      List.range' (base + 2 * first) (2 * (tail.length + 1))
    rw [show base + 2 * (first + 1) = (base + 2 * first) + 2 by omega,
      show 2 * (tail.length + 1) = 2 + 2 * tail.length by omega]
    exact List.range'_append_1 (s := base + 2 * first) (m := 2) (n := 2 * tail.length)

private theorem occurrence_range (snapshot : Snapshot) (rows : List PackedOccurrences.Row) (first : ℕ) :
    (PrivateArrayPlan.rows rows first).map (fun p => position snapshot p.1) = List.range' (2 + 2 * first) (2 * rows.length) := by
  induction rows generalizing first with
  | nil => rfl
  | cons row later ih =>
    change [2 + 2 * first, 2 + 2 * first + 1] ++
      (PrivateArrayPlan.rows later (first + 1)).map (fun p => position snapshot p.1) =
        List.range' (2 + 2 * first) (2 * (later.length + 1))
    rw [ih, show 2 + 2 * (first + 1) = (2 + 2 * first) + 2 by omega,
      show 2 * (later.length + 1) = 2 + 2 * later.length by omega]
    exact List.range'_append_1 (s := 2 + 2 * first) (m := 2) (n := 2 * later.length)

/-- The physical sequence covers the bank without a gap or repeated word. -/
theorem content_positions (snapshot : Snapshot) :
    (PrivateArrayPlan.contents snapshot).map (fun p => position snapshot p.1) = List.range (count snapshot) := by
  unfold PrivateArrayPlan.contents PrivateArrayPlan.dataContents PrivateArrayPlan.indexContents
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_flatMap, List.map_map, Function.comp_def]
  rw [occurrence_range]
  simp only [position, Nat.mul_zero, Nat.add_zero, Array.length_toList]
  rw [paired_range]
  have postingRange :
      snapshot.index.postings.toList.zipIdx.map
        (fun x => 2 + 2 * snapshot.data.occurrences.size + 2 * snapshot.index.directory.size + x.2) =
        List.range'
          (2 + 2 * snapshot.data.occurrences.size + 2 * snapshot.index.directory.size) snapshot.index.postings.size := by
    rw [show (fun x : Word × ℕ => 2 + 2 * snapshot.data.occurrences.size + 2 * snapshot.index.directory.size + x.2) =
      ((2 + 2 * snapshot.data.occurrences.size + 2 * snapshot.index.directory.size) + ·) ∘ Prod.snd from rfl]
    rw [← List.map_map, List.zipIdx_map_snd, List.map_add_range']
    simp
  simp only [postingRange, Nat.mul_zero, Nat.add_zero, Array.length_toList]
  change List.range' 0 2 ++ List.range' (0 + 2) (2 * snapshot.data.occurrences.size) ++
    (List.range' (2 + 2 * snapshot.data.occurrences.size) (2 * snapshot.index.directory.size) ++
      List.range' (2 + 2 * snapshot.data.occurrences.size + 2 * snapshot.index.directory.size) snapshot.index.postings.size) = _
  rw [List.range'_append_1, ← List.append_assoc]
  let n := 2 + 2 * snapshot.data.occurrences.size
  let d := 2 * snapshot.index.directory.size
  let b := snapshot.index.postings.size
  have joinDirectory : List.range' 0 n ++ List.range' n d = List.range' 0 (n + d) := by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s := 0) (m := n) (n := d))
  have joinPostings : List.range' 0 (n + d) ++ List.range' (n + d) b = List.range' 0 (n + d + b) := by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s := 0) (m := n + d) (n := b))
  change (List.range' 0 n ++ List.range' n d) ++ List.range' (n + d) b = List.range (count snapshot)
  rw [joinDirectory, joinPostings, List.range_eq_range']
  rfl

private theorem rows_available (rows : List PackedOccurrences.Row) (first : ℕ) (entry : Slot × Word)
    (member : entry ∈ PrivateArrayPlan.rows rows first) :
    ∃ i < first + rows.length, entry.1 = .identity i ∨ entry.1 = .value i := by
  induction rows generalizing first with
  | nil => cases member
  | cons head later ih =>
    simp only [PrivateArrayPlan.rows, List.mem_cons] at member
    rcases member with firstMember | secondMember | laterMember
    · exact ⟨first, by simp, Or.inl (congrArg Prod.fst firstMember)⟩
    · exact ⟨first, by simp, Or.inr (congrArg Prod.fst secondMember)⟩
    · obtain ⟨i, within, shape⟩ := ih (first + 1) laterMember
      exact ⟨i, by simp only [List.length_cons]; omega, shape⟩

theorem content_available {entry : Slot × Word} (inside : entry ∈ PrivateArrayPlan.contents snapshot) :
    Available snapshot entry.1 := by
  unfold PrivateArrayPlan.contents at inside
  rcases List.mem_append.mp inside with inData | inIndex
  · unfold PrivateArrayPlan.dataContents at inData
    rcases List.mem_append.mp inData with header | data
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at header
      rcases header with rfl | rfl <;> trivial
    · obtain ⟨i, within, h | h⟩ := rows_available _ 0 entry data <;>
        simpa only [h, Available, zero_add, Array.length_toList] using within
  · unfold PrivateArrayPlan.indexContents at inIndex
    rcases List.mem_append.mp inIndex with directory | posting
    · obtain ⟨⟨word, k⟩, counted, field⟩ := List.mem_flatMap.mp directory
      have within := List.snd_lt_of_mem_zipIdx counted
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at field
      rcases field with rfl | rfl <;>
        simpa only [Available, Array.length_toList, Nat.add_zero] using within
    · obtain ⟨⟨word, k⟩, counted, rfl⟩ := List.mem_map.mp posting
      simpa only [Available, Array.length_toList, Nat.add_zero] using List.snd_lt_of_mem_zipIdx counted

theorem content_distinct (snapshot : Snapshot) : ((PrivateArrayPlan.contents snapshot).map Prod.fst).Nodup := by
  apply List.Nodup.of_map (position snapshot)
  rw [List.map_map]
  change ((PrivateArrayPlan.contents snapshot).map (fun p => position snapshot p.1)).Nodup
  rw [content_positions]
  exact List.nodup_range

theorem planned_words {before target : Snapshot} {plan : List PrivateArrayPlan.Write}
    (computed : PrivateArrayPlan.evaluate before plan = some (PrivateArrayPlan.contents target)) :
    plan.length = count target := by
  have destinations := congrArg List.length (PrivateArrayPlan.evaluate_destinations computed)
  have extent := congrArg List.length (content_positions target)
  simp only [List.length_map, List.length_range] at destinations extent
  exact destinations.symm.trans extent

open NativePreparation (Geometry skeleton place source)
open X86PlacedMemory (CodeApart)

/-- The data geometry follows from two disjoint banks and the computed
word plan. Only separation from the independently placed code remains
to check at this boundary. -/
theorem geometry_of_banks {before target : Snapshot} (old : Bank before) (next : Bank target)
    (disjointBanks : old.pointer.toNat + 8 * count before ≤ next.pointer.toNat ∨
      next.pointer.toNat + 8 * count target ≤ old.pointer.toNat)
    (w : NativeWords.Wiring) (image : NativeImage.View) (base : BitVec 48)
    {plan : List PrivateArrayPlan.Write} (computed : PrivateArrayPlan.evaluate before plan = some (PrivateArrayPlan.contents target))
    (codeApart : CodeApart image base (NativeWords.written (skeleton old.addressMap next.addressMap plan))) :
    Geometry w image base old.addressMap next.addressMap plan := by
  have same := PrivateArrayPlan.evaluate_destinations computed
  have distinct : (plan.map Prod.fst).Nodup := same ▸ content_distinct target
  have available (entry : PrivateArrayPlan.Write) (member : entry ∈ plan) : Available target entry.1 := by
    have listed : entry.1 ∈ plan.map Prod.fst := List.mem_map_of_mem member
    rw [← same] at listed
    obtain ⟨pair, inside, sameField⟩ := List.mem_map.mp listed
    exact sameField ▸ content_available inside
  refine ⟨?_, ?_, codeApart⟩
  · unfold NativeWords.Separate skeleton
    rw [List.pairwise_map]
    have different : plan.Pairwise (fun l r => l.1 ≠ r.1) := List.pairwise_map.mp distinct
    exact different.imp_of_mem (fun {l r} lm rm ne =>
      next.disjoint_fields (available l lm) (available r rm) ne)
  · intro m member
    obtain ⟨⟨slot, operation⟩, _, rfl⟩ := List.mem_map.mp member
    cases operation with
    | literal value => simp [place, source, NativeWords.Source.uses]
    | copy readSlot =>
      apply NativeWords.apart_written
      intro later within
      obtain ⟨future, _, rfl⟩ := List.mem_map.mp within
      rcases disjointBanks with before | after
      · exact Bank.disjoint_banks old next before readSlot future.1
      · exact (Bank.disjoint_banks next old after future.1 readSlot).symm

namespace Examples

private def demo : Snapshot :=
  ⟨⟨2, #[(7, 42), (9, 42)], 10⟩, ⟨#[(0, 2)], #[0, 1]⟩⟩

theorem positions_read_header_data_directory_then_postings :
    (PrivateArrayPlan.contents demo).map (fun p => position demo p.1) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  rw [content_positions]
  decide +kernel

theorem a_missing_word_cannot_be_placed_as_an_occurrence :
    ¬ Available demo (.value 2) := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.SnapshotPlacement
