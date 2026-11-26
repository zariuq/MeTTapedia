import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences
import Mettapedia.Machines.TIsa.Derivation.OccurrenceIndex

/-!
# A directory and shared array for ordered postings

One directory entry gives a start and a length in the posting array.
Postings hold store ordinals, not copied values or quotient
representatives. Thus two equal values may be returned at different
occurrence identities. Empty buckets and absent directory keys differ;
an invalid range is refused instead of silently truncating it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedIndex

private def segments (start : ℕ) : List (List ℕ) → List (ℕ × ℕ)
  | [] => []
  | block :: rest => (start, block.length) :: segments (start + block.length) rest

private theorem segment_bound (blocks : List (List ℕ)) (start : ℕ) {entry : ℕ × ℕ}
    (included : entry ∈ segments start blocks) : entry.1 + entry.2 ≤ start + blocks.flatten.length := by
  induction blocks generalizing start with
  | nil => cases included
  | cons block rest ih =>
    rcases List.mem_cons.mp included with rfl | later
    · simp only [List.flatten_cons, List.length_append]
      omega
    · have bound := ih (start + block.length) later
      simp only [List.flatten_cons, List.length_append]
      omega

private theorem slice_exact (blocks : List (List ℕ)) (earlier : List ℕ) (i : ℕ) :
    (segments earlier.length blocks)[i]?.map (fun entry =>
      ((earlier ++ blocks.flatten).drop entry.1).take entry.2) = blocks[i]? := by
  induction blocks generalizing earlier i with
  | nil => simp [segments]
  | cons block rest ih =>
    cases i with
    | zero =>
      simp only [segments, List.getElem?_cons_zero, Option.map_some, List.flatten_cons, List.drop_append_length,
        List.take_append_length]
    | succ i =>
      simpa only [segments, List.getElem?_cons_succ, List.length_append, List.flatten_cons,
        List.append_assoc] using ih (earlier ++ block) i

structure Layout where
  directory : Array (Word × Word)
  postings : Array Word
  deriving Repr

private def encodeEntry (entry : ℕ × ℕ) : Word × Word :=
  (BitVec.ofNat 64 entry.1, BitVec.ofNat 64 entry.2)

def pack (blocks : List (List ℕ)) : Option Layout :=
  if blocks.flatten.length < 2 ^ 64 && blocks.flatten.all (fun slot => decide (slot < 2 ^ 64)) then
    some ⟨((segments 0 blocks).map encodeEntry).toArray, (blocks.flatten.map (BitVec.ofNat 64)).toArray⟩
  else none

def get? (index : Layout) (key : ℕ) : Option (List ℕ) := do
  let (first, length) ← index.directory[key]?
  if first.toNat + length.toNat ≤ index.postings.size then
    some ((index.postings.extract first.toNat (first.toNat + length.toNat)).toList.map BitVec.toNat)
  else none

def lengthWord? (index : Layout) (key : ℕ) : Option Word :=
  (index.directory[key]?).map Prod.snd

/-- The length header already carries the count when the whole
posting interval is valid. An invalid interval cannot justify it. -/
theorem length_word {index : Layout} {key : ℕ} {slots : List ℕ}
    (selected : get? index key = some slots) :
    lengthWord? index key = some (BitVec.ofNat 64 slots.length) := by
  unfold get? at selected
  cases entry : index.directory[key]? with
  | none => simp [entry] at selected
  | some interval =>
    obtain ⟨first, length⟩ := interval
    by_cases valid : first.toNat + length.toNat ≤ index.postings.size
    · simp only [entry, bind, Option.bind_some, if_pos valid] at selected
      have size := congrArg List.length (Option.some.inj selected)
      simp only [List.length_map, Array.length_toList, Array.size_extract_of_le valid, Nat.add_sub_cancel_left] at size
      simp only [lengthWord?, entry, Option.map_some, ← size, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp [entry, valid] at selected

theorem get_exact {blocks : List (List ℕ)} {index : Layout} (formed : pack blocks = some index) (key : ℕ) :
    get? index key = blocks[key]? := by
  unfold pack at formed
  split at formed
  next valid =>
    obtain rfl := (Option.some.inj formed).symm
    have bounds : blocks.flatten.length < 2 ^ 64 ∧ ∀ slot ∈ blocks.flatten, slot < 2 ^ 64 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using valid
    have decode : (blocks.flatten.map (fun slot => slot % 2 ^ 64)) = blocks.flatten := by
      conv_rhs => rw [← List.map_id blocks.flatten]
      apply List.map_congr_left
      intro slot inside
      exact Nat.mod_eq_of_lt (bounds.2 slot inside)
    have slices := slice_exact blocks [] key
    simp only [List.length_nil, List.nil_append] at slices
    unfold get?
    simp only [List.getElem?_toArray, List.getElem?_map]
    cases selected : (segments 0 blocks)[key]? with
    | none => simpa only [selected, Option.map_none, bind, Option.bind_none] using slices
    | some entry =>
      obtain ⟨first, length⟩ := entry
      have bound := segment_bound blocks 0 (List.mem_of_getElem? selected)
      change first + length ≤ 0 + blocks.flatten.length at bound
      have firstFits : first < 2 ^ 64 := by have := bounds.1; omega
      have lengthFits : length < 2 ^ 64 := by have := bounds.1; omega
      have endFits : first + length ≤ blocks.flatten.length := by omega
      simp only [selected, Option.map_some, bind, Option.bind_some, encodeEntry, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt firstFits, Nat.mod_eq_of_lt lengthFits, List.size_toArray, List.length_map,
        if_pos endFits, Array.toList_extract, List.extract, List.map_take, List.map_drop, List.map_map,
        Function.comp_def, decode, Nat.add_sub_cancel_left] at *
      exact slices
  next invalid => cases formed

/-! ## Restoring occurrences from an index of positions -/

open Derivation (Store)

variable {V : Type*}

def candidates (codes : PackedOccurrences.Codes V) (store : PackedOccurrences.Layout)
    (index : Layout) (key : ℕ) : Option (List (ℕ × V)) :=
  match get? index key with
  | none => none
  | some slots => slots.mapM (PackedOccurrences.at? codes store)

private theorem decoded_length {A B : Type*} (f : A → Option B) (input : List A)
    {output : List B} (found : input.mapM f = some output) : output.length = input.length := by
  induction input generalizing output with
  | nil =>
    cases (Option.some.inj found).symm
    rfl
  | cons first rest ih =>
    rw [List.mapM_cons] at found
    obtain ⟨head, _, tail⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨more, decoded, produced⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := (Option.some.inj produced).symm
    exact congrArg Nat.succ (ih decoded)

theorem candidates_length (codes : PackedOccurrences.Codes V) (store : PackedOccurrences.Layout)
    (index : Layout) (key : ℕ) {values : List (ℕ × V)} (found : candidates codes store index key = some values) :
    lengthWord? index key = some (BitVec.ofNat 64 values.length) := by
  unfold candidates at found
  cases atKey : get? index key with
  | none => simp [atKey] at found
  | some slots =>
    rw [atKey] at found
    rw [decoded_length _ _ found]
    exact length_word atKey

theorem candidates_exact (codes : PackedOccurrences.Codes V)
    {s : Store V} {store : PackedOccurrences.Layout} (storePacked : PackedOccurrences.pack codes s = some store)
    {blocks : List (List ℕ)} {index : Layout} (indexPacked : pack blocks = some index) (key : ℕ) :
    candidates codes store index key = (match blocks[key]? with
      | none => none
      | some slots => slots.mapM (fun slot => s.occurrences[slot]?)) := by
  unfold candidates
  rw [get_exact indexPacked]
  have access : PackedOccurrences.at? codes store = fun slot => s.occurrences[slot]? := by
    funext slot
    exact PackedOccurrences.at_exact codes storePacked slot
  rw [access]

open Derivation.OccurrencePostings (group bucket bucket_group)

variable {n : ℕ}

/-- Group store positions once by an encoded finite key. The same
construction accepts head keys or the key of an argument coordinate. -/
def fromKeys (classify : V → Fin n) (s : Store V) : List (List ℕ) :=
  let groups := group (fun entry : (ℕ × V) × ℕ => classify entry.1.2) s.occurrences.zipIdx
  (List.finRange n).map fun key => (bucket groups key).map Prod.snd

private theorem access_zip {A : Type*} (values : List A) (selected : List (A × ℕ))
    (indices : ∀ entry ∈ selected, entry ∈ values.zipIdx) :
    (selected.map Prod.snd).mapM (fun i => values[i]?) = some (selected.map Prod.fst) := by
  induction selected with
  | nil => rfl
  | cons first rest ih =>
    have entry := List.mem_zipIdx_iff_getElem?.mp (indices first List.mem_cons_self)
    have tail := ih (fun chosen inside => indices chosen (List.mem_cons_of_mem _ inside))
    simp only [List.map_cons, List.mapM_cons, entry, tail]
    rfl

theorem candidates_fromKeys (codes : PackedOccurrences.Codes V) (classify : V → Fin n)
    {s : Store V} {store : PackedOccurrences.Layout} (storePacked : PackedOccurrences.pack codes s = some store)
    {index : Layout} (indexPacked : pack (fromKeys classify s) = some index) (key : Fin n) :
    candidates codes store index key.val = some (s.occurrences.filter (fun entry => classify entry.2 == key)) := by
  rw [candidates_exact codes storePacked indexPacked]
  have ordinal : key.val < (List.finRange n).length := by simp
  have selected : (List.finRange n)[key.val]? = some key := by
    rw [List.getElem?_eq_getElem ordinal, List.getElem_finRange]
    rfl
  simp only [fromKeys, List.getElem?_map, selected, Option.map_some, bucket_group]
  rw [access_zip s.occurrences _ (fun entry inside => (List.mem_filter.mp inside).1)]
  have same := List.filter_map
    (l := s.occurrences.zipIdx) (f := Prod.fst) (p := fun entry => classify entry.2 == key)
  rw [List.zipIdx_map_fst] at same
  exact congrArg some same.symm

namespace Examples

private def blocks : List (List ℕ) := [[0, 2], [], [1, 3]]

theorem directory_preserves_posting_order :
    (pack blocks).bind (fun memory => get? memory 2) = some [1, 3] := by
  decide +kernel

theorem empty_bucket_is_not_missing_key :
    (pack blocks).bind (fun memory => get? memory 1) = some [] ∧
    (pack blocks).bind (fun memory => get? memory 3) = none := by
  decide +kernel

theorem bad_endpoint_does_not_truncate :
    get? ⟨#[(1, 3)], #[0, 4]⟩ 0 = none := by
  decide +kernel

private def wordCodes : PackedOccurrences.Codes Word := ⟨some, some, fun equal => by cases equal; rfl⟩
private def store : Store Word := ⟨[(7, 42), (9, 42), (12, 13)], 13⟩

private def valueGroup (word : Word) : Fin 2 := if word = 42 then 1 else 0

theorem same_key_keeps_both_occurrences {memory : PackedOccurrences.Layout} {index : Layout}
    (stored : PackedOccurrences.pack wordCodes store = some memory)
    (indexed : pack (fromKeys valueGroup store) = some index) :
    candidates wordCodes memory index 1 = some [(7, 42), (9, 42)] := by
  refine (candidates_fromKeys wordCodes valueGroup stored indexed (1 : Fin 2)).trans ?_
  decide +kernel

theorem same_key_counts_both_occurrences {memory : PackedOccurrences.Layout} {index : Layout}
    (stored : PackedOccurrences.pack wordCodes store = some memory)
    (indexed : pack (fromKeys valueGroup store) = some index) :
    lengthWord? index 1 = some 2 :=
  candidates_length wordCodes memory index 1 (same_key_keeps_both_occurrences stored indexed)

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedIndex
