import Mettapedia.Algebra.TensorExternalLease

/-!
# Validation of borrowed sparse tensor components

The reference describes globally strict bounded keys and complete compressed
pointer windows. The implementation scans adjacent keys and consecutive
pointer pairs. Equal component lengths prevent truncation of explicit support.
SupportTensor and SupportTensorLayout separately specify Option-valued support
and constructed compressed layouts; no new joined decoder theorem is claimed.

Major/minor axes describe CSR or CSC physical admission. CSC's canonical to
physical permutation, stable duplicate normalization, value byte decoding,
native binary lookup, allocation and pointer lifetime remain separate native
or existing-model obligations. One aggregate owner uses TensorExternalLease;
there is no new ownership core or implicit absent-to-zero interpretation.
-/

set_option autoImplicit false
namespace Mettapedia.Algebra.TensorSparseIngress

variable {Value Context Handle : Type}

namespace Reference

def Keys (bound : Nat) (previous : Option Nat) (keys : List Nat) : Prop :=
  keys.Pairwise (· < ·) ∧ ∀ key ∈ keys, key < bound ∧
    match previous with | none => True | some old => old < key

def COO (bound : Nat) (keys : List Nat) (values : List Value) : Prop :=
  keys.length = values.length ∧ Keys bound none keys

def Segment (minorCount nnz : Nat) (keys : List Nat) (first last : Nat) : Prop :=
  first ≤ last ∧ last ≤ nnz ∧ Keys minorCount none ((keys.drop first).take (last - first))

def Pointers (minorCount nnz : Nat) (keys pointers : List Nat) : Prop :=
  pointers.getLast? = some nnz ∧
    ∀ edge ∈ pointers.zip pointers.tail, Segment minorCount nnz keys edge.1 edge.2

def Compressed (majorCount minorCount : Nat) (pointers keys : List Nat) (values : List Value) : Prop :=
  keys.length = values.length ∧ pointers.length = majorCount + 1 ∧
    pointers.head? = some 0 ∧ Pointers minorCount keys.length keys pointers

end Reference

namespace Native

def scanKeys (bound : Nat) : Option Nat → List Nat → Bool
  | _, [] => true
  | previous, key :: rest =>
      decide (key < bound) &&
        (match previous with | none => true | some old => decide (old < key)) &&
          scanKeys bound (some key) rest

def coo (bound : Nat) (keys : List Nat) (values : List Value) : Bool :=
  decide (keys.length = values.length) && scanKeys bound none keys

def scanPointers (minorCount nnz : Nat) (keys : List Nat) : List Nat → Bool
  | [] => false
  | [last] => decide (last = nnz)
  | first :: last :: rest =>
      decide (first ≤ last) && decide (last ≤ nnz) &&
        scanKeys minorCount none ((keys.drop first).take (last - first)) &&
          scanPointers minorCount nnz keys (last :: rest)

def compressed (majorCount minorCount : Nat) (pointers keys : List Nat) (values : List Value) : Bool :=
  decide (keys.length = values.length) && decide (pointers.length = majorCount + 1) &&
    decide (pointers.head? = some 0) && scanPointers minorCount keys.length keys pointers

end Native

theorem key_contract_cons (bound : Nat) (previous : Option Nat) (key : Nat) (rest : List Nat) :
    Reference.Keys bound previous (key :: rest) ↔
      key < bound ∧ (match previous with | none => True | some old => old < key) ∧
        Reference.Keys bound (some key) rest := by
  constructor
  · rintro ⟨pairwise, bounded⟩
    obtain ⟨headRelations, tailPairwise⟩ := List.pairwise_cons.mp pairwise
    obtain ⟨headBound, headPrevious⟩ := bounded key List.mem_cons_self
    refine ⟨headBound, headPrevious, tailPairwise, ?_⟩
    intro current member
    exact ⟨(bounded current (List.mem_cons_of_mem _ member)).1, headRelations current member⟩
  · rintro ⟨headBound, headPrevious, tailPairwise, bounded⟩
    constructor
    · apply List.pairwise_cons.mpr
      exact ⟨fun current member => (bounded current member).2, tailPairwise⟩
    · intro current member
      rcases List.mem_cons.mp member with same | remaining
      · subst current
        exact ⟨headBound, headPrevious⟩
      · obtain ⟨currentBound, later⟩ := bounded current remaining
        refine ⟨currentBound, ?_⟩
        cases previous with
        | none => trivial
        | some old => exact Nat.lt_trans headPrevious later

theorem key_scan_refines (bound : Nat) (previous : Option Nat) (keys : List Nat) :
    Native.scanKeys bound previous keys = true ↔ Reference.Keys bound previous keys := by
  induction keys generalizing previous with
  | nil => simp [Native.scanKeys, Reference.Keys]
  | cons key rest ih =>
      rw [key_contract_cons]
      cases previous <;> simp [Native.scanKeys, ih, and_assoc]

theorem coo_boundary_refines (bound : Nat) (keys : List Nat) (values : List Value) :
    Native.coo bound keys values = true ↔ Reference.COO bound keys values := by
  simp [Native.coo, Reference.COO, key_scan_refines]

theorem pointer_contract_cons (minorCount nnz : Nat) (keys : List Nat) (first last : Nat)
    (rest : List Nat) :
    Reference.Pointers minorCount nnz keys (first :: last :: rest) ↔
      Reference.Segment minorCount nnz keys first last ∧
        Reference.Pointers minorCount nnz keys (last :: rest) := by
  simp [Reference.Pointers, and_left_comm]

theorem pointer_scan_refines (minorCount nnz : Nat) (keys pointers : List Nat) :
    Native.scanPointers minorCount nnz keys pointers = true ↔
      Reference.Pointers minorCount nnz keys pointers := by
  induction pointers with
  | nil => simp [Native.scanPointers, Reference.Pointers]
  | cons first rest ih =>
      cases rest with
      | nil => simp [Native.scanPointers, Reference.Pointers]
      | cons last remaining =>
          rw [pointer_contract_cons]
          simp [Native.scanPointers, Reference.Segment, key_scan_refines, ih, and_assoc]

theorem compressed_boundary_refines (majorCount minorCount : Nat)
    (pointers keys : List Nat) (values : List Value) :
    Native.compressed majorCount minorCount pointers keys values = true ↔
      Reference.Compressed majorCount minorCount pointers keys values := by
  simp [Native.compressed, Reference.Compressed, pointer_scan_refines, and_assoc]

/-- Component length admission prevents the zip interpretation from silently
discarding entries in either externally supplied component. -/
theorem admitted_coo_retains_component_counts (bound : Nat) (keys : List Nat) (values : List Value)
    (admitted : Native.coo bound keys values = true) :
    (keys.zip values).length = keys.length ∧ (keys.zip values).length = values.length := by
  have same := ((coo_boundary_refines bound keys values).mp admitted).1
  simp [same]

/-- The actual sparse validator supplies the existing lease admission gate.
Value-format/content checks and allocation remain independent gates. -/
theorem coo_lease_admission (bound : Nat) (keys : List Nat) (values : List Value)
    (allocation valueReady : Bool) (context : Context) (seed : Handle) :
    (TensorExternalLease.Native.step .fresh (.construct context seed
      ⟨allocation, Native.coo bound keys values, valueReady⟩)).events =
        [.retained context, .published seed] ↔
      allocation = true ∧ Reference.COO bound keys values ∧ valueReady = true := by
  rw [← coo_boundary_refines]
  cases allocation <;> cases valueReady <;> cases Native.coo bound keys values <;>
    simp [TensorExternalLease.Native.step]

theorem compressed_lease_admission (majorCount minorCount : Nat)
    (pointers keys : List Nat) (values : List Value)
    (allocation valueReady : Bool) (context : Context) (seed : Handle) :
    (TensorExternalLease.Native.step .fresh (.construct context seed
      ⟨allocation, Native.compressed majorCount minorCount pointers keys values, valueReady⟩)).events =
        [.retained context, .published seed] ↔
      allocation = true ∧ Reference.Compressed majorCount minorCount pointers keys values ∧ valueReady = true := by
  rw [← compressed_boundary_refines]
  cases allocation <;> cases valueReady <;>
    cases Native.compressed majorCount minorCount pointers keys values <;>
      simp [TensorExternalLease.Native.step]

namespace Controls

theorem explicit_zero_is_present_and_missing_is_absent :
    List.lookup 1 [(1, 0), (3, 7)] = some 0 ∧
      List.lookup 2 [(1, 0), (3, 7)] = none := by decide

theorem coo_rejects_duplicate_unsorted_and_out_of_bounds :
    Native.coo 4 [1, 1] [0, 7] = false ∧ Native.coo 4 [3, 1] [0, 7] = false ∧
      Native.coo 4 [1, 4] [0, 7] = false := by decide

theorem mismatched_components_cannot_silently_truncate :
    Native.coo 4 [1, 3] [0] = false ∧ Native.coo 4 [1] [0, 7] = false := by decide

theorem compressed_empty_segments_and_stored_zero_are_valid :
    Native.compressed 3 4 [0, 0, 2, 2] [1, 3] [0, 7] = true ∧
      List.lookup 1 ([1, 3].zip [0, 7]) = some 0 := by decide

theorem skipped_and_shifted_pointers_are_rejected :
    Native.compressed 2 4 [1, 1, 2] [1, 3] [0, 7] = false ∧
      Native.compressed 2 4 [0, 1, 1] [1, 3] [0, 7] = false ∧
      Native.compressed 2 4 [0, 3, 2] [1, 3] [0, 7] = false := by decide

theorem minor_order_resets_at_each_segment :
    Native.compressed 2 4 [0, 1, 2] [3, 1] [0, 7] = true ∧
      Native.compressed 2 4 [0, 0, 2] [3, 1] [0, 7] = false := by decide

theorem duplicate_minor_is_allowed_only_across_segments :
    Native.compressed 2 4 [0, 1, 2] [1, 1] [0, 7] = true ∧
      Native.compressed 1 4 [0, 2] [1, 1] [0, 7] = false := by decide

theorem exact_compressed_component_lengths_are_required :
    Native.compressed 2 4 [0, 2] [1, 3] [0, 7] = false ∧
      Native.compressed 1 4 [0, 2] [1, 3] [0] = false := by decide

theorem empty_axes_and_minor_bounds_are_distinct :
    Native.compressed 0 0 [0] [] ([] : List Nat) = true ∧
      Native.compressed 1 0 [0, 0] [] ([] : List Nat) = true ∧
      Native.compressed 1 0 [0, 1] [0] [0] = false ∧
      Native.compressed 1 4 [0, 1] [4] [0] = false := by decide

theorem shifted_value_slice_changes_support_observation :
    List.lookup 1 ([1, 3].zip [0, 7]) = some 0 ∧ List.lookup 1 ([1, 3].zip [7]) = some 7 := by decide

theorem shifted_segment_is_observable :
    List.lookup 1 (([(1, 0), (3, 7)].drop 0).take 0) = none ∧
      List.lookup 1 (([(1, 0), (3, 7)].drop 0).take 1) = some 0 := by
  decide

theorem invalid_components_acquire_no_owner_lease :
    (TensorExternalLease.Native.step .fresh
      (.construct (1, 2, 3) (0 : Nat) ⟨true, Native.coo 4 [1, 1] [0, 7], true⟩)).events = [.refused] := by
  decide

theorem invalid_final_pointer_acquires_no_owner_lease :
    (TensorExternalLease.Native.step .fresh
      (.construct (1, 2, 3) (0 : Nat)
        ⟨true, Native.compressed 2 4 [0, 1, 1] [1, 3] [0, 7], true⟩)).events = [.refused] := by
  decide

theorem exported_components_share_one_aggregate_lease :
    (TensorExternalLease.run TensorExternalLease.Native.step .fresh
      [.construct (1, 2, 3) (0 : Nat) ⟨true, Native.coo 4 [1, 3] [0, 7], true⟩,
       .share 0 1 true, .drop 0, .drop 1]).events =
      [.retained (1, 2, 3), .published 0, .published 1, .dropped 0, .dropped 1, .released (1, 2, 3)] := by
  decide

end Controls
end Mettapedia.Algebra.TensorSparseIngress
