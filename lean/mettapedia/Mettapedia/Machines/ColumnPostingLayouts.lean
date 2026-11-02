import Mathlib.Tactic
import Mathlib.Data.Finset.Sort

/-!
# Constructed column postings and three logical directory layouts

Posting directories are built by insertion, independently of the scan
specification. Sorted key directories, packed offset blocks and collision-
checked hash buckets recover the same row IDs. Physical array access, hashing
costs, word encodings and C ownership remain separate refinements.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ColumnPostingLayouts

variable {Id Key : Type} [DecidableEq Id] [DecidableEq Key]

abbrev Directory (Key Id : Type) := Key → List Id

def insertPosting (key : Id → Key) (row : Id) (index : Directory Key Id) : Directory Key Id :=
  Function.update index (key row) (row :: index (key row))

def buildPostings (key : Id → Key) : List Id → Directory Key Id
  | [] => fun _ => []
  | row :: rows => insertPosting key row (buildPostings key rows)

omit [DecidableEq Id] in
theorem mem_buildPostings (key : Id → Key) (rows : List Id) (q : Key) (i : Id) :
    i ∈ buildPostings key rows q ↔ i ∈ rows ∧ key i = q := by
  induction rows with
  | nil => simp [buildPostings]
  | cons row rows ih =>
    by_cases hq : q = key row
    · subst q
      simp only [buildPostings, insertPosting, Function.update_self,
        ih, List.mem_cons]
      aesop
    · simp only [buildPostings, insertPosting, Function.update_of_ne hq, ih, List.mem_cons]
      aesop

def scan (table : List Id) (key : Id → Key) (q : Key) : Finset Id :=
  table.toFinset.filter (fun i => key i = q)

theorem postings_eq_scan (table : List Id) (key : Id → Key) (q : Key) :
    (buildPostings key table q).toFinset = scan table key q := by
  ext i
  simp [mem_buildPostings, scan]

structure SortedColumn (Key Id : Type) where
  entries : List (Key × List Id)

def buildSorted [LinearOrder Key] (table : List Id) (key : Id → Key) : SortedColumn Key Id :=
  ⟨((table.map key).toFinset.sort (· ≤ ·)).map (fun q => (q, buildPostings key table q))⟩

def lookupSorted (index : SortedColumn Key Id) (q : Key) : Finset Id :=
  ((index.entries.lookup q).getD []).toFinset

omit [DecidableEq Id] in
theorem lookup_mapped (keys : List Key) (values : Key → List Id) (q : Key) :
    ((keys.map (fun k => (k, values k))).lookup q).getD [] =
      if q ∈ keys then values q else [] := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    by_cases h : q = key
    · subst key; simp
    · have hb : (q == key) = false := by simpa only [beq_eq_false_iff_ne] using h
      simp [List.lookup, hb, h, ih]

omit [DecidableEq Id] in
theorem buildSorted_ordered [LinearOrder Key] (table : List Id) (key : Id → Key) :
    ((buildSorted table key).entries.map Prod.fst).Pairwise (· ≤ ·) := by
  simp [buildSorted, List.map_map, Function.comp_def]

theorem lookupSorted_exact [LinearOrder Key] (table : List Id) (key : Id → Key) (q : Key) :
    lookupSorted (buildSorted table key) q = scan table key q := by
  rw [lookupSorted, buildSorted, lookup_mapped]
  by_cases h : q ∈ table.map key
  · simpa [h] using postings_eq_scan table key q
  · have empty : scan table key q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨member, equal⟩ := Finset.mem_filter.mp hi
      exact h (List.mem_map.mpr ⟨i, List.mem_toFinset.mp member, equal⟩)
    simp [h, empty]

/-- A packed posting array and its offset/length descriptors. -/
structure PackedBlocks (Id : Type) where
  data : List Id
  spans : List (Nat × Nat)

def packBlocks : List (List Id) → PackedBlocks Id
  | [] => ⟨[], []⟩
  | block :: blocks =>
    let later := packBlocks blocks
    ⟨block ++ later.data,
      (0, block.length) :: later.spans.map (fun span => (block.length + span.1, span.2))⟩

def lookupBlock (packed : PackedBlocks Id) (i : Nat) : List Id :=
  match packed.spans[i]? with
  | none => []
  | some (start, length) => (packed.data.drop start).take length

omit [DecidableEq Id] in
/-- Offsets retrieve their actual packed block, including empty blocks. -/
theorem lookupBlock_pack (blocks : List (List Id)) (i : Nat) :
    lookupBlock (packBlocks blocks) i = blocks[i]?.getD [] := by
  induction blocks generalizing i with
  | nil => simp [packBlocks, lookupBlock]
  | cons block blocks ih =>
    cases i with
    | zero => simp [packBlocks, lookupBlock]
    | succ i =>
      have hi := ih i
      cases hs : (packBlocks blocks).spans[i]? with
      | none => simpa [packBlocks, lookupBlock, List.getElem?_map, hs] using hi
      | some span =>
        rcases span with ⟨start, length⟩
        simpa [packBlocks, lookupBlock, List.getElem?_map, hs] using hi

structure OffsetColumn (Key Id : Type) where
  keys : List Key
  packed : PackedBlocks Id

def buildOffset (table : List Id) (key : Id → Key) : OffsetColumn Key Id :=
  let keys := (table.map key).eraseDups
  ⟨keys, packBlocks (keys.map (fun q => buildPostings key table q))⟩

def lookupOffset (index : OffsetColumn Key Id) (q : Key) : Finset Id :=
  if q ∈ index.keys then (lookupBlock index.packed (index.keys.idxOf q)).toFinset else ∅

theorem lookupOffset_exact (table : List Id) (key : Id → Key) (q : Key) :
    lookupOffset (buildOffset table key) q = scan table key q := by
  unfold lookupOffset buildOffset
  dsimp only
  split
  · rename_i present
    rw [lookupBlock_pack]
    have hq : ((table.map key).eraseDups)[(table.map key).eraseDups.idxOf q]? = some q :=
      List.getElem?_idxOf present
    simp [List.getElem?_map, hq, postings_eq_scan]
  · rename_i absent
    symm
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨member, equal⟩ := Finset.mem_filter.mp hi
    exact absent (List.mem_eraseDups.mpr (List.mem_map.mpr ⟨i, List.mem_toFinset.mp member, equal⟩))

structure HashedColumn (Id : Type) where
  buckets : Nat → List Id

def buildHashed (table : List Id) (key : Id → Key) (hash : Key → Nat) : HashedColumn Id :=
  ⟨buildPostings (hash ∘ key) table⟩

def lookupHashed (index : HashedColumn Id) (key : Id → Key) (hash : Key → Nat) (q : Key) : Finset Id :=
  (index.buckets (hash q)).toFinset.filter (fun i => key i = q)

theorem lookupHashed_exact (table : List Id) (key : Id → Key) (hash : Key → Nat) (q : Key) :
    lookupHashed (buildHashed table key hash) key hash q = scan table key q := by
  ext i
  simp only [lookupHashed, buildHashed, Finset.mem_filter, List.mem_toFinset,
    mem_buildPostings, Function.comp_apply, scan]
  constructor
  · rintro ⟨⟨member, _⟩, equal⟩; exact ⟨member, equal⟩
  · rintro ⟨member, equal⟩; exact ⟨⟨member, congrArg hash equal⟩, equal⟩

example : lookupBlock (packBlocks ([[4, 5], [], [9]] : List (List Nat))) 2 = [9] := by decide

/-- Identical packed values with a wrong descriptor give a different answer. -/
example : lookupBlock (⟨[7, 8], [(0, 1), (0, 1)]⟩ : PackedBlocks Nat) 1 ≠
    lookupBlock (packBlocks [[7], [8]]) 1 := by decide

/-- Bucket equality alone admits a wrong row under a forced collision. -/
example :
    (buildHashed ([0, 1] : List Nat) id (fun _ => 0)).buckets 0 = [0, 1] ∧
    lookupHashed (buildHashed [0, 1] id (fun _ => 0)) id (fun _ => 0) 0 = {0} := by decide

#print axioms postings_eq_scan
#print axioms lookupSorted_exact
#print axioms lookupBlock_pack
#print axioms lookupOffset_exact
#print axioms lookupHashed_exact

end Mettapedia.Machines.ColumnPostingLayouts
