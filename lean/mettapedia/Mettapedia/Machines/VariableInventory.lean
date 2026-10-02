import Mettapedia.Machines.VariableIndex

/-!
# Indexed inventories preserve the first payload and occurrence order

`VariableIndex` validates proposed positions against a key list. This module
connects that mechanism to an independently linear `List.find?` over entries,
and to an executable inventory which retains each key's first payload.

Keys identify variables; payloads may contain spelling, source presentation,
or a reference to the mapped variable. Neither payload equality nor spelling
determines key identity. Hash tables propose positions only; the ordered
entry array remains authoritative for the payload.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VariableInventory

universe u v
variable {Key : Type u} {Payload : Type v} [DecidableEq Key]

abbrev Entry (Key : Type u) (Payload : Type v) := Key × Payload

def scan (entries : List (Entry Key Payload)) (key : Key) : Option (Entry Key Payload) :=
  entries.find? (fun entry => decide (entry.1 = key))

def indexed (entries : List (Entry Key Payload)) (proposal : Key → Option Nat)
    (key : Key) : Option (Entry Key Payload) :=
  (VariableIndex.lookup (entries.map Prod.fst) proposal key).bind (entries[·]?)

theorem scan_none_iff (entries : List (Entry Key Payload)) (key : Key) :
    scan entries key = none ↔ key ∉ entries.map Prod.fst := by
  unfold scan
  rw [List.find?_eq_none]
  constructor
  · intro absent present
    obtain ⟨entry, member, sameKey⟩ := List.mem_map.mp present
    exact absent entry member (by simp [sameKey])
  · intro absent entry member matchesKey
    exact absent (List.mem_map.mpr ⟨entry, member, of_decide_eq_true matchesKey⟩)

theorem scan_some {entries : List (Entry Key Payload)} {key : Key}
    {entry : Entry Key Payload} (found : scan entries key = some entry) :
    entry ∈ entries ∧ entry.1 = key := by
  exact ⟨List.mem_of_find?_eq_some found,
    of_decide_eq_true (List.find?_some
      (p := fun item : Entry Key Payload => decide (item.1 = key)) found)⟩

/-- Confirming a key position and then reading that position returns the
current array's payload, even when the proposal originated before a reset. -/
theorem indexed_sound {entries : List (Entry Key Payload)} {proposal : Key → Option Nat}
    {key : Key} {entry : Entry Key Payload} (found : indexed entries proposal key = some entry) :
    entry ∈ entries ∧ entry.1 = key := by
  unfold indexed at found
  cases atPosition : VariableIndex.lookup (entries.map Prod.fst) proposal key with
  | none => simp [atPosition] at found
  | some position =>
      simp [atPosition] at found
      have keyFound := VariableIndex.lookup_sound atPosition
      simp [List.getElem?_map, found] at keyFound
      exact ⟨List.mem_of_getElem? found, keyFound⟩

theorem indexed_complete {entries : List (Entry Key Payload)} {proposal : Key → Option Nat}
    {key : Key} (complete : VariableIndex.Complete (entries.map Prod.fst) proposal)
    (present : key ∈ entries.map Prod.fst) :
    ∃ entry, indexed entries proposal key = some entry := by
  obtain ⟨position, proposed⟩ := VariableIndex.lookup_complete complete present
  have keyFound := VariableIndex.lookup_sound proposed
  cases entryAt : entries[position]? with
  | none => simp [List.getElem?_map, entryAt] at keyFound
  | some entry => exact ⟨entry, by simp [indexed, proposed, entryAt]⟩

theorem indexed_none {entries : List (Entry Key Payload)} {proposal : Key → Option Nat}
    {key : Key} (absent : key ∉ entries.map Prod.fst) :
    indexed entries proposal key = none := by
  simp [indexed, VariableIndex.lookup_none absent]

/-- Under unique keys and a complete position table, the entire returned
entry agrees with the linear first-match oracle, including its payload. -/
theorem indexed_eq_scan (entries : List (Entry Key Payload)) (proposal : Key → Option Nat)
    (unique : (entries.map Prod.fst).Nodup)
    (complete : VariableIndex.Complete (entries.map Prod.fst) proposal) (key : Key) :
    indexed entries proposal key = scan entries key := by
  by_cases present : key ∈ entries.map Prod.fst
  · obtain ⟨entry, found⟩ := indexed_complete complete present
    obtain ⟨member, sameKey⟩ := indexed_sound found
    cases scanned : scan entries key with
    | none => exact (((scan_none_iff entries key).mp scanned) present).elim
    | some first =>
        obtain ⟨firstMember, firstKey⟩ := scan_some scanned
        have same : entry = first :=
          List.inj_on_of_nodup_map unique member firstMember (sameKey.trans firstKey.symm)
        simpa [same] using found
  · rw [indexed_none present, (scan_none_iff entries key).mpr present]

structure State (Key : Type u) (Payload : Type v) where
  entries : List (Entry Key Payload)
  proposal : Key → Option Nat

def State.Valid (state : State Key Payload) : Prop :=
  (state.entries.map Prod.fst).Nodup ∧
    VariableIndex.Complete (state.entries.map Prod.fst) state.proposal

/-- Appending records the new key at its current position. The payload is
copied as a whole; no spelling-based identity test is performed. -/
def append (state : State Key Payload) (entry : Entry Key Payload) : State Key Payload :=
  ⟨state.entries ++ [entry], Function.update state.proposal entry.1 (some state.entries.length)⟩

def insert (state : State Key Payload) (entry : Entry Key Payload) : State Key Payload :=
  match indexed state.entries state.proposal entry.1 with
  | some _ => state
  | none => append state entry

/-- The independent linear first-occurrence reference. -/
def referenceInsert (entries : List (Entry Key Payload)) (entry : Entry Key Payload) :
    List (Entry Key Payload) :=
  match scan entries entry.1 with
  | some _ => entries
  | none => entries ++ [entry]

theorem insert_entries_eq_reference (state : State Key Payload) (entry : Entry Key Payload)
    (valid : state.Valid) :
    (insert state entry).entries = referenceInsert state.entries entry := by
  simp only [insert, indexed_eq_scan _ _ valid.1 valid.2, referenceInsert]
  cases scan state.entries entry.1 <;> rfl

theorem append_valid (state : State Key Payload) (entry : Entry Key Payload)
    (valid : state.Valid) (absent : entry.1 ∉ state.entries.map Prod.fst) :
    (append state entry).Valid := by
  constructor
  · simp only [append, List.map_append, List.map_singleton]
    rw [List.nodup_append_comm]
    exact List.nodup_cons.mpr ⟨absent, valid.1⟩
  · have appended := VariableIndex.complete_append entry.1 valid.2
    simpa [append] using appended

theorem insert_valid (state : State Key Payload) (entry : Entry Key Payload)
    (valid : state.Valid) : (insert state entry).Valid := by
  unfold insert
  cases found : indexed state.entries state.proposal entry.1 with
  | some _ => exact valid
  | none =>
      apply append_valid state entry valid
      intro present
      obtain ⟨old, oldFound⟩ := indexed_complete valid.2 present
      rw [found] at oldFound
      cases oldFound

def build (input : List (Entry Key Payload)) (state : State Key Payload) : State Key Payload :=
  input.foldl insert state

def referenceBuild (input : List (Entry Key Payload)) (entries : List (Entry Key Payload)) :
    List (Entry Key Payload) := input.foldl referenceInsert entries

theorem build_valid (input : List (Entry Key Payload)) (state : State Key Payload)
    (valid : state.Valid) : (build input state).Valid := by
  induction input generalizing state with
  | nil => exact valid
  | cons entry rest ih => exact ih (insert state entry) (insert_valid state entry valid)

theorem build_entries_eq_reference (input : List (Entry Key Payload)) (state : State Key Payload)
    (valid : state.Valid) : (build input state).entries = referenceBuild input state.entries := by
  induction input generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      simp only [build, referenceBuild, List.foldl_cons]
      change (build rest (insert state entry)).entries =
        referenceBuild rest (referenceInsert state.entries entry)
      rw [ih (insert state entry) (insert_valid state entry valid),
        insert_entries_eq_reference state entry valid]

/-- First appearances in source order. The whole original entry is retained
when its key is fresh, including spelling and alias/reference payload. -/
def firstOccurrences (seen : List Key) : List (Entry Key Payload) → List (Entry Key Payload)
  | [] => []
  | entry :: rest =>
      if entry.1 ∈ seen then firstOccurrences seen rest
      else entry :: firstOccurrences (seen ++ [entry.1]) rest

theorem referenceBuild_eq_firstOccurrences (input : List (Entry Key Payload))
    (entries : List (Entry Key Payload)) :
    referenceBuild input entries = entries ++ firstOccurrences (entries.map Prod.fst) input := by
  induction input generalizing entries with
  | nil => simp [referenceBuild, firstOccurrences]
  | cons entry rest ih =>
      by_cases present : entry.1 ∈ entries.map Prod.fst
      · have found : scan entries entry.1 ≠ none := by
          intro absent
          exact (scan_none_iff entries entry.1).mp absent present
        cases scanned : scan entries entry.1 with
        | none => exact (found scanned).elim
        | some previous =>
            simpa [referenceBuild, referenceInsert, scanned, firstOccurrences, present] using ih entries
      · have absent := (scan_none_iff entries entry.1).mpr present
        simpa [referenceBuild, referenceInsert, absent, firstOccurrences, present,
          List.map_append, List.append_assoc] using ih (entries ++ [entry])

/-- Exact sequence equality proves both first payload retention and first
appearance order. It is stronger than equality of sets of keys. -/
theorem build_firstOccurrences (input : List (Entry Key Payload)) (state : State Key Payload)
    (valid : state.Valid) :
    (build input state).entries =
      state.entries ++ firstOccurrences (state.entries.map Prod.fst) input := by
  rw [build_entries_eq_reference input state valid, referenceBuild_eq_firstOccurrences]

def reset (proposal : Key → Option Nat) : State Key Payload := ⟨[], proposal⟩

omit [DecidableEq Key] in
theorem reset_valid (proposal : Key → Option Nat) : (reset (Payload := Payload) proposal).Valid :=
  ⟨by simp [reset], VariableIndex.complete_nil proposal⟩

theorem build_from_reset (input : List (Entry Key Payload)) (proposal : Key → Option Nat) :
    (build input (reset proposal)).entries = firstOccurrences [] input := by
  simpa [reset] using build_firstOccurrences input (reset proposal) (reset_valid proposal)

theorem scan_cons (entry : Entry Key Payload) (rest : List (Entry Key Payload)) (key : Key) :
    scan (entry :: rest) key = if entry.1 = key then some entry else scan rest key := by
  by_cases same : entry.1 = key <;> simp [scan, same]

theorem scan_append (left right : List (Entry Key Payload)) (key : Key) :
    scan (left ++ right) key = (scan left key).or (scan right key) := by
  simp [scan]

/-- The retained payload is precisely the first source entry for the key.
Keys already supplied by the initial inventory are excluded from new rows. -/
theorem scan_firstOccurrences (input : List (Entry Key Payload)) (seen : List Key) (key : Key) :
    scan (firstOccurrences seen input) key = if key ∈ seen then none else scan input key := by
  induction input generalizing seen with
  | nil => simp [firstOccurrences, scan]
  | cons entry rest ih =>
      by_cases old : entry.1 ∈ seen
      · by_cases keyOld : key ∈ seen
        · simp [firstOccurrences, old, ih, keyOld]
        · have different : entry.1 ≠ key := by intro same; exact keyOld (same ▸ old)
          simp [firstOccurrences, old, ih, keyOld, scan_cons, different]
      · by_cases same : entry.1 = key
        · subst key
          simp [firstOccurrences, old, scan_cons]
        · have reverseDifferent : key ≠ entry.1 := Ne.symm same
          simp [firstOccurrences, old, scan_cons, same, ih, reverseDifferent]

theorem build_lookup_first (input : List (Entry Key Payload)) (state : State Key Payload)
    (valid : state.Valid) (key : Key) :
    indexed (build input state).entries (build input state).proposal key =
      scan (state.entries ++ input) key := by
  have builtValid := build_valid input state valid
  rw [indexed_eq_scan _ _ builtValid.1 builtValid.2, build_firstOccurrences input state valid,
    scan_append, scan_firstOccurrences, scan_append]
  by_cases old : key ∈ state.entries.map Prod.fst
  · cases found : scan state.entries key with
    | none => exact (((scan_none_iff state.entries key).mp found) old).elim
    | some entry => simp [old]
  · rw [(scan_none_iff state.entries key).mpr old]
    simp [old]

theorem firstOccurrences_sublist (input : List (Entry Key Payload)) (seen : List Key) :
    List.Sublist (firstOccurrences seen input) input := by
  induction input generalizing seen with
  | nil => exact List.Sublist.refl []
  | cons entry rest ih =>
      rw [firstOccurrences]
      split
      · exact List.Sublist.cons entry (ih seen)
      · exact List.Sublist.cons_cons entry (ih (seen ++ [entry.1]))

/-- A retained key was present in the input and was not already seen.
This characterizes the inventory independently of its insertion algorithm. -/
theorem mem_firstOccurrences_keys (input : List (Entry Key Payload))
    (seen : List Key) (key : Key) :
    key ∈ (firstOccurrences seen input).map Prod.fst ↔
      key ∈ input.map Prod.fst ∧ key ∉ seen := by
  have selected := scan_none_iff (firstOccurrences seen input) key
  rw [scan_firstOccurrences] at selected
  by_cases old : key ∈ seen
  · rw [if_pos old] at selected
    have missing := selected.mp rfl
    exact ⟨fun present => False.elim (missing present),
      fun present => False.elim (present.2 old)⟩
  · simp only [if_neg old] at selected
    exact ⟨fun present => ⟨by
      by_contra absent
      exact (selected.mp ((scan_none_iff input key).mpr absent)) present, old⟩,
      fun present => by
        by_contra absent
        exact ((scan_none_iff input key).mp (selected.mpr absent)) present.1⟩

/-- First appearances have unique keys even when input payloads disagree.
The discarded duplicates do not impose any equality on those payloads. -/
theorem firstOccurrences_keys_nodup (input : List (Entry Key Payload)) (seen : List Key) :
    ((firstOccurrences seen input).map Prod.fst).Nodup := by
  induction input generalizing seen with
  | nil => exact List.nodup_nil
  | cons entry rest ih =>
    rw [firstOccurrences]
    split
    · exact ih seen
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun present =>
        ((mem_firstOccurrences_keys rest (seen ++ [entry.1]) entry.1).mp present).2
          (by simp), ih (seen ++ [entry.1])⟩

/-- Payload copying/transformation keeps the same position authority when
keys and order are unchanged. The returned value is transformed from the
current entry, not retained in the proposal cache. -/
theorem indexed_map_payload {Other : Type*} (f : Payload → Other)
    (entries : List (Entry Key Payload)) (proposal : Key → Option Nat) (key : Key) :
    indexed (entries.map (fun entry => (entry.1, f entry.2))) proposal key =
      (indexed entries proposal key).map (fun entry => (entry.1, f entry.2)) := by
  have sameKeys :
      (entries.map (fun entry => (entry.1, f entry.2))).map Prod.fst = entries.map Prod.fst := by
    simp [List.map_map, Function.comp_def]
  simp only [indexed, sameKeys]
  cases VariableIndex.lookup (entries.map Prod.fst) proposal key <;>
    simp [List.getElem?_map]

/-- Explicit mapping insertion may reject a conflicting payload, while an
inventory/get-or-add operation retains the first one. Keeping those two
operations separate preserves pointer-consistency checks. -/
def addChecked [DecidableEq Payload] (state : State Key Payload) (entry : Entry Key Payload) :
    Option (State Key Payload) :=
  match indexed state.entries state.proposal entry.1 with
  | none => some (append state entry)
  | some existing => if existing.2 = entry.2 then some state else none

theorem addChecked_conflict [DecidableEq Payload] (state : State Key Payload)
    (entry old : Entry Key Payload) (found : indexed state.entries state.proposal entry.1 = some old)
    (different : old.2 ≠ entry.2) : addChecked state entry = none := by
  simp [addChecked, found, different]

theorem addChecked_same [DecidableEq Payload] (state : State Key Payload)
    (entry old : Entry Key Payload) (found : indexed state.entries state.proposal entry.1 = some old)
    (same : old.2 = entry.2) : addChecked state entry = some state := by
  simp [addChecked, found, same]

namespace Controls

/-- Distinct variable identities retain their own references despite equal
printed spellings. Repeated identity retains its first spelling/reference. -/
def appearances : List (Entry Nat (String × Nat)) :=
  [(7, ("x", 41)), (8, ("x", 42)), (7, ("renamed", 99)), (9, ("z", 43))]

theorem spelling_does_not_merge_ids :
    (build appearances (reset (fun _ => none))).entries =
      [(7, ("x", 41)), (8, ("x", 42)), (9, ("z", 43))] := by decide

theorem repeated_id_keeps_original_reference :
    indexed (build appearances (reset (fun _ => none))).entries
      (build appearances (reset (fun _ => none))).proposal 7 = some (7, ("x", 41)) := by decide

theorem stale_position_cannot_forge_key :
    indexed [(3, "new"), (4, "other")] (fun key => if key = 7 then some 1 else none) 7 = none := by
  decide

theorem reset_discards_all_payloads :
    indexed ([] : List (Entry Nat String)) (fun key => if key = 7 then some 0 else none) 7 = none := by
  decide

/-- If a recycled position again contains the same key, its current payload
is returned. No old payload was cached in the proposal table. -/
theorem refill_reads_current_payload :
    indexed [(7, "new")] (fun key => if key = 7 then some 0 else none) 7 = some (7, "new") := by
  decide

/-- Sound key confirmation alone is insufficient without unique keys: a
later confirmed occurrence can carry a different payload than the first. -/
theorem duplicate_key_payload_counterexample :
    indexed [(7, "first"), (7, "later")] (fun _ => some 1) 7 = some (7, "later") ∧
    scan [(7, "first"), (7, "later")] 7 = some (7, "first") := by decide

theorem duplicate_key_table_still_complete :
    VariableIndex.Complete ([7, 7] : List Nat) (fun _ => some 1) := by
  intro key member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst key
  exact ⟨1, rfl, rfl⟩

/-- A stale table remains sound but can be incomplete. Rebuilding/recording
the live keys is necessary for exact agreement with linear search. -/
theorem missing_record_is_not_complete :
    indexed [(7, "present")] (fun _ => none) 7 = none ∧
    scan [(7, "present")] 7 = some (7, "present") := by decide

theorem missing_record_incomplete :
    ¬VariableIndex.Complete ([7] : List Nat) (fun _ => none) := by
  intro complete
  obtain ⟨position, found, _⟩ := complete 7 (by simp)
  cases found

theorem checked_mapping_rejects_pointer_conflict :
    (addChecked (Payload := Nat) ⟨[(7, 41)], fun _ => some 0⟩ (7, 99)).isNone = true ∧
    (insert (Payload := Nat) ⟨[(7, 41)], fun _ => some 0⟩ (7, 99)).entries = [(7, 41)] := by
  decide

end Controls

end Mettapedia.Machines.VariableInventory
