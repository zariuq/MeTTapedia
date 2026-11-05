import Mathlib.Tactic

/-!
# A space file's laws: reading back gives the same bag, and lookups agree

A space's facts can be kept in a read-only file: a dictionary of the
symbols the facts use, each fact as the tuple of its symbols' positions in
the dictionary, and a side listing the facts by their first column, so a
lookup on a bound first column reads only the facts it selects.  The file
must answer as the facts it was made from do:

* `decode_encode`: reading the file back gives the facts it was made from,
  in their order and multiplicity, so the same bag;
* `lookup_side_perm`, `lookup_side`: a lookup through the sorted side
  answers the facts of that first column: the scan's answers in the side's
  order, so the same bag;
* `lookup_absent_symbol`: a key the dictionary does not hold answers
  nothing, as the scan does, without reading a fact.

Facts are lists of symbols (natural numbers); a fact with no fields has no
first column and no lookup selects it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SpaceFileLaws

abbrev Fact := List Nat

/-- The dictionary: the symbols the facts use, each once. -/
def dictionary (facts : List Fact) : List Nat := (facts.flatten).dedup

/-- A symbol's position in the dictionary. -/
def code (dict : List Nat) (s : Nat) : Nat := dict.idxOf s

/-- The symbol at a position. -/
def symbol (dict : List Nat) (i : Nat) : Nat := dict.getD i 0

/-- The file: the dictionary, the facts as positions, and the side: the same
records sorted by their first column's position, so a lookup on a bound
first column reads one run of it. -/
structure File where
  dict : List Nat
  records : List (List Nat)
  side : List (List Nat)

def encodeFact (dict : List Nat) (f : Fact) : List Nat := f.map (code dict)
def decodeFact (dict : List Nat) (r : List Nat) : Fact := r.map (symbol dict)

/-- A record's first column's position (a record with no fields sorts
first). -/
def firstCode (r : List Nat) : Nat := r.head?.getD 0

def encode (facts : List Fact) : File :=
  let dict := dictionary facts
  let records := facts.map (encodeFact dict)
  { dict := dict, records := records,
    side := records.mergeSort (fun a b => decide (firstCode a ≤ firstCode b)) }

def decode (file : File) : List Fact := file.records.map (decodeFact file.dict)

theorem symbol_code (dict : List Nat) (s : Nat) (h : s ∈ dict) :
    symbol dict (code dict s) = s := by
  unfold symbol code
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr h)]
  simp [List.getElem_idxOf]

theorem decodeFact_encodeFact (dict : List Nat) (f : Fact)
    (h : ∀ s ∈ f, s ∈ dict) : decodeFact dict (encodeFact dict f) = f := by
  unfold decodeFact encodeFact
  rw [List.map_map]
  conv_rhs => rw [← List.map_id f]
  apply List.map_congr_left
  intro s hs
  exact symbol_code dict s (h s hs)

theorem mem_dictionary (facts : List Fact) (f : Fact) (hf : f ∈ facts)
    (s : Nat) (hs : s ∈ f) : s ∈ dictionary facts := by
  unfold dictionary
  rw [List.mem_dedup, List.mem_flatten]
  exact ⟨f, hf, hs⟩

/-- Reading the file back gives the facts it was made from. -/
theorem decode_encode (facts : List Fact) : decode (encode facts) = facts := by
  unfold decode encode
  simp only [List.map_map]
  conv_rhs => rw [← List.map_id facts]
  apply List.map_congr_left
  intro f hf
  exact decodeFact_encodeFact _ f (fun s hs => mem_dictionary facts f hf s hs)

/-! ## Lookups on a bound first column -/

/-- The scan: the facts whose first column is `key`. -/
def scanLookup (facts : List Fact) (key : Nat) : List Fact :=
  facts.filter (fun f => f.head? == some key)

/-- The file's lookup: the key's position in the dictionary, then the
records of the side at that position, decoded.  A key the dictionary lacks
answers nothing. -/
def fileLookup (file : File) (key : Nat) : List Fact :=
  if key ∈ file.dict then
    (file.side.filter (fun r => r.head? == some (code file.dict key))).map
      (decodeFact file.dict)
  else []

theorem lookup_absent_symbol (facts : List Fact) (key : Nat)
    (h : key ∉ dictionary facts) :
    fileLookup (encode facts) key = [] ∧ scanLookup facts key = [] := by
  refine ⟨by simp [fileLookup, encode, h], ?_⟩
  unfold scanLookup
  rw [List.filter_eq_nil_iff]
  intro f hf
  cases hfh : f with
  | nil => simp
  | cons s rest =>
      have hs : s ∈ dictionary facts := mem_dictionary facts f hf s (by simp [hfh])
      have hne : s ≠ key := fun e => h (e ▸ hs)
      simp [hne]

/-- Positions are injective on the dictionary's symbols. -/
theorem code_inj (dict : List Nat) (a b : Nat) (ha : a ∈ dict) (hb : b ∈ dict)
    (h : code dict a = code dict b) : a = b := by
  have := congrArg (symbol dict) h
  rwa [symbol_code dict a ha, symbol_code dict b hb] at this

/-- On a fact the dictionary covers, testing its encoded first column
against the key's position tests its first column against the key. -/
theorem first_test_encode (dict : List Nat) (key : Nat) (hk : key ∈ dict)
    (f : Fact) (hf : ∀ s ∈ f, s ∈ dict) :
    ((encodeFact dict f).head? == some (code dict key)) = (f.head? == some key) := by
  cases f with
  | nil => simp [encodeFact]
  | cons s rest =>
      have hs : s ∈ dict := hf s (by simp)
      simp only [encodeFact, List.map_cons, List.head?_cons]
      by_cases e : s = key
      · simp [e]
      · have : code dict s ≠ code dict key := fun c => e (code_inj dict s key hs hk c)
        simp [e, this]

/-- A lookup through the sorted side answers the facts of that first
column: the scan's answers, in the side's order. -/
theorem lookup_side_perm (facts : List Fact) (key : Nat) :
    (fileLookup (encode facts) key).Perm (scanLookup facts key) := by
  by_cases hk : key ∈ dictionary facts
  · set dict := dictionary facts with hdict
    have cover : ∀ f ∈ facts, ∀ s ∈ f, s ∈ dict :=
      fun f hf s hs => mem_dictionary facts f hf s hs
    have side_perm : (encode facts).side.Perm (facts.map (encodeFact dict)) :=
      List.mergeSort_perm _ _
    have exact_on_records :
        ((facts.map (encodeFact dict)).filter
            (fun r => r.head? == some (code dict key))).map (decodeFact dict) =
          scanLookup facts key := by
      rw [List.filter_map, List.map_map]
      unfold scanLookup
      have hfilter : facts.filter ((fun r => r.head? == some (code dict key)) ∘ encodeFact dict)
          = facts.filter (fun f => f.head? == some key) := by
        apply List.filter_congr
        intro f hf
        exact first_test_encode dict key hk f (cover f hf)
      rw [hfilter]
      conv_rhs => rw [← List.map_id (facts.filter (fun f => f.head? == some key))]
      apply List.map_congr_left
      intro f hf
      exact decodeFact_encodeFact dict f (cover f (List.mem_of_mem_filter hf))
    have hlook : fileLookup (encode facts) key =
        ((encode facts).side.filter (fun r => r.head? == some (code dict key))).map
          (decodeFact dict) := by
      have hk' : key ∈ dictionary facts := hk
      simp [fileLookup, encode, hk', hdict]
    rw [hlook, ← exact_on_records]
    exact (side_perm.filter _).map _
  · rw [(lookup_absent_symbol facts key hk).1, (lookup_absent_symbol facts key hk).2]

/-- The same bag, as multisets. -/
theorem lookup_side (facts : List Fact) (key : Nat) :
    (fileLookup (encode facts) key : Multiset Fact) = scanLookup facts key :=
  Multiset.coe_eq_coe.mpr (lookup_side_perm facts key)

end Mettapedia.Machines.SpaceFileLaws
