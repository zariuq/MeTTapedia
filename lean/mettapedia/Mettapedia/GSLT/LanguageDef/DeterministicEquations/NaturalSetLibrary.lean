import Mathlib.Data.Finset.Sort

/-! # Canonical finite-natural-set library lowering

Insertion retains increasing order and removes duplicates. Its list union
agrees with the canonical `Finset.sort` encoding, including overlapping sets.
These are standard-library operations, independent of any guest calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

def insertNatural (index : Nat) : List Nat → List Nat
  | [] => [index]
  | first :: rest =>
      if index = first then first :: rest
      else if index < first then index :: first :: rest
      else first :: insertNatural index rest

def unionNaturals : List Nat → List Nat → List Nat
  | [], right => right
  | first :: rest, right => unionNaturals rest (insertNatural first right)

def natSetUnion (left right : Finset Nat) : Finset Nat := left ∪ right

def natSetEmpty : Finset Nat := ∅

def natSetSingleton (index : Nat) : Finset Nat := {index}

def natSetMember (index : Nat) (values : Finset Nat) : Bool := decide (index ∈ values)

theorem insertNatural_mem (index value : Nat) (values : List Nat) :
    value ∈ insertNatural index values ↔ value = index ∨ value ∈ values := by
  induction values with
  | nil => simp [insertNatural]
  | cons first rest ih =>
      by_cases same : index = first
      · simp [insertNatural, same]
      · by_cases before : index < first
        · simp [insertNatural, same, before]
        · simp only [insertNatural, same, ↓reduceIte, before, List.mem_cons, ih]
          tauto

theorem insertNatural_toFinset (index : Nat) (values : List Nat) :
    (insertNatural index values).toFinset = insert index values.toFinset := by
  ext value
  simp only [List.mem_toFinset, insertNatural_mem, Finset.mem_insert]

theorem insertNatural_sorted (index : Nat) {values : List Nat}
    (sorted : values.Pairwise (· < ·)) :
    (insertNatural index values).Pairwise (· < ·) := by
  induction values with
  | nil => simp [insertNatural]
  | cons first rest ih =>
      rcases List.pairwise_cons.mp sorted with ⟨least, tail⟩
      by_cases same : index = first
      · simpa [insertNatural, same] using sorted
      · by_cases before : index < first
        · rw [insertNatural, if_neg same, if_pos before]
          apply List.pairwise_cons.mpr
          refine ⟨?_, sorted⟩
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact before
          · exact Nat.lt_trans before (least value member)
        · rw [insertNatural, if_neg same, if_neg before]
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih tail⟩
          intro value member
          rcases (insertNatural_mem index value rest).mp member with rfl | member
          · omega
          · exact least value member

theorem unionNaturals_toFinset (left right : List Nat) :
    (unionNaturals left right).toFinset = left.toFinset ∪ right.toFinset := by
  induction left generalizing right with
  | nil => simp [unionNaturals]
  | cons first rest ih =>
      rw [unionNaturals, ih, insertNatural_toFinset]
      ext value
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto

theorem unionNaturals_sorted (left : List Nat) {right : List Nat}
    (sorted : right.Pairwise (· < ·)) :
    (unionNaturals left right).Pairwise (· < ·) := by
  induction left generalizing right with
  | nil => exact sorted
  | cons first rest ih => exact ih (insertNatural_sorted first sorted)

theorem unionNaturals_canonical (left right : Finset Nat) :
    unionNaturals (left.sort (· ≤ ·)) (right.sort (· ≤ ·)) =
      (natSetUnion left right).sort (· ≤ ·) := by
  apply (unionNaturals_sorted _ right.sortedLT_sort.pairwise).eq_of_mem_iff
    (natSetUnion left right).sortedLT_sort.pairwise
  intro index
  rw [← List.mem_toFinset, unionNaturals_toFinset]
  simp [natSetUnion]

theorem natSetMember_sorted (index : Nat) (values : Finset Nat) :
    decide (index ∈ values.sort (· ≤ ·)) = natSetMember index values := by
  simp [natSetMember]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
