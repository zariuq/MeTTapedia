import Mettapedia.Machines.CMemory.Borrowing
import Mathlib.Data.Fin.Basic

/-!
# Pointwise reference contracts and array ranges

The C type supplies count and stride. Element contracts use the existing
allocation-region geometry. Unknown-index borrows retain the whole array
footprint; distinct constant indices give disjoint element ranges. Pointwise
replacement preserves a uniform field contract only when the replacement
establishes that same contract.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.ReferenceArrays

open Mettapedia.Machines.CMemory.Borrowing

structure Layout where
  root : Nat
  first : Nat
  count : Nat
  stride : Nat

def Layout.region (layout : Layout) : Region :=
  ⟨layout.root, layout.first, layout.count * layout.stride⟩

def Layout.element (layout : Layout) (index : Fin layout.count) : Region :=
  ⟨layout.root, layout.first + index.val * layout.stride, layout.stride⟩

theorem element_within_array (layout : Layout) (index : Fin layout.count) :
    layout.region.Contains (layout.element index) := by
  refine ⟨rfl, Nat.le_add_right _ _, ?_⟩
  have bounded := Nat.mul_le_mul_right layout.stride (Nat.succ_le_of_lt index.isLt)
  rw [Nat.succ_mul] at bounded
  dsimp [Layout.region, Layout.element, Region.finish]
  omega

theorem distinct_elements_disjoint (layout : Layout) (a b : Fin layout.count)
    (different : a ≠ b) : (layout.element a).Disjoint (layout.element b) := by
  have values : a.val ≠ b.val := fun same => different (Fin.ext same)
  rcases Nat.lt_or_gt_of_ne values with before | after
  · have ordered := Nat.mul_le_mul_right layout.stride (Nat.succ_le_of_lt before)
    rw [Nat.succ_mul] at ordered
    exact Or.inr (Or.inl (by dsimp [Layout.element, Region.finish]; omega))
  · have ordered := Nat.mul_le_mul_right layout.stride (Nat.succ_le_of_lt after)
    rw [Nat.succ_mul] at ordered
    exact Or.inr (Or.inr (by dsimp [Layout.element, Region.finish]; omega))

/-- A whole-array loan is conservative: every possible element it might name
is contained in that footprint. No independence follows from unequal runtime
index variable names. -/
theorem unknown_index_loan_covers_element (layout : Layout) (index : Fin layout.count)
    (part : Region) (inside : (layout.element index).Contains part) :
    layout.region.Contains part := Region.contains_trans (element_within_array layout index) inside

theorem exclusive_unknown_index_conflicts {loans : List Loan} (ordered : Ordered loans)
    (layout : Layout) (a b : Nat) (index : Fin layout.count) (write : Bool)
    (different : a ≠ b) (whole : Access loans a layout.region true)
    (element : Access loans b (layout.element index) write) :
    layout.region.Disjoint (layout.element index) :=
  exclusive_access_disjoint ordered different whole element

variable {Value : Type} {count : Nat}

def Pointwise (contract : Value → Prop) (values : Fin count → Value) : Prop :=
  ∀ index, contract (values index)

theorem replace_preserves_contract (contract : Value → Prop) (values : Fin count → Value)
    (valid : Pointwise contract values) (index : Fin count) (value : Value)
    (establishes : contract value) : Pointwise contract (Function.update values index value) := by
  intro observed
  by_cases same : observed = index
  · subst observed; simpa using establishes
  · simpa [same] using valid observed

theorem copied_nonstatic_origin_refused (origins : Fin count → Nat) (index : Fin count)
    (nonstatic : origins index ≠ 0) : ¬ Pointwise (· = 0) origins := by
  intro declared
  exact nonstatic (declared index)

#print axioms element_within_array
#print axioms distinct_elements_disjoint
#print axioms exclusive_unknown_index_conflicts

end Mettapedia.Machines.Resources.ReferenceArrays
