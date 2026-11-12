import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Work of immediate and prepared ordered deletion

The algorithms count predicate invocations, row-equality tests and constructed
list cells while computing their actual results. The immediate algorithm
produces survivors and the changed flag in one traversal. The prepared
algorithm constructs a selected list, validates it against the current input,
and contracts by those selected values.

Predicates here are pure, total Boolean functions. An invocation is not assumed
to be one machine instruction. These meters omit control, allocator and native
layout costs; a natural-valued tariff describes only the named operations.
Validation across an intervening change is explicit and may refuse.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List.PublicationWork

structure Work where
  predicates : Nat
  comparisons : Nat
  cells : Nat
  deriving DecidableEq, Repr

def Work.plus (first second : Work) : Work :=
  ⟨first.predicates + second.predicates, first.comparisons + second.comparisons,
    first.cells + second.cells⟩

def Work.price (predicate equality cell : Nat) (work : Work) : Nat :=
  predicate * work.predicates + equality * work.comparisons + cell * work.cells

structure Measured (Value : Type*) where
  value : Value
  work : Work
  deriving DecidableEq, Repr

universe u
variable {Row : Type u}

def immediate (select : Row → Bool) : List Row → Measured (List Row × Bool)
  | [] => ⟨([], false), ⟨0, 0, 0⟩⟩
  | row :: rest =>
      let matched := select row
      let later := immediate select rest
      if matched then
        ⟨(later.value.1, true), later.work.plus ⟨1, 0, 0⟩⟩
      else
        ⟨(row :: later.value.1, later.value.2), later.work.plus ⟨1, 0, 1⟩⟩

def gather (select : Row → Bool) : List Row → Measured (List Row)
  | [] => ⟨[], ⟨0, 0, 0⟩⟩
  | row :: rest =>
      let matched := select row
      let later := gather select rest
      if matched then ⟨row :: later.value, later.work.plus ⟨1, 0, 1⟩⟩
      else ⟨later.value, later.work.plus ⟨1, 0, 0⟩⟩

variable [DecidableEq Row]

def member (row : Row) : List Row → Measured Bool
  | [] => ⟨false, ⟨0, 0, 0⟩⟩
  | candidate :: rest =>
      if row = candidate then ⟨true, ⟨0, 1, 0⟩⟩
      else
        let later := member row rest
        ⟨later.value, later.work.plus ⟨0, 1, 0⟩⟩

def equalRows : List Row → List Row → Measured Bool
  | [], [] => ⟨true, ⟨0, 0, 0⟩⟩
  | first :: left, second :: right =>
      if first = second then
        let later := equalRows left right
        ⟨later.value, later.work.plus ⟨0, 1, 0⟩⟩
      else ⟨false, ⟨0, 1, 0⟩⟩
  | _, _ => ⟨false, ⟨0, 0, 0⟩⟩

def contract (selected : List Row) : List Row → Measured (List Row)
  | [] => ⟨[], ⟨0, 0, 0⟩⟩
  | row :: rest =>
      let chosen := member row selected
      let later := contract selected rest
      if chosen.value then ⟨later.value, chosen.work.plus later.work⟩
      else ⟨row :: later.value, (chosen.work.plus later.work).plus ⟨0, 0, 1⟩⟩

def publishSelected (selected current : List Row) : Measured (List Row × Bool) :=
  let published := contract selected current
  ⟨(published.value, !selected.isEmpty), published.work⟩

/-- Revalidation can reject a stale selection without returning a proposed
new store. No contraction is executed in that branch. -/
def checked (select : Row → Bool) (selected current : List Row) :
    Measured (Option (List Row × Bool)) :=
  let found := gather select current
  let same := equalRows selected found.value
  if same.value then
    let published := publishSelected selected current
    ⟨some published.value, (found.work.plus same.work).plus published.work⟩
  else ⟨none, found.work.plus same.work⟩

/-- Preparation and publication in one stable interval, implemented as the
two actual algorithm calls rather than defined through the immediate result. -/
def prepared (select : Row → Bool) (rows : List Row) :
    Measured (Option (List Row × Bool)) :=
  let selected := gather select rows
  let published := checked select selected.value rows
  ⟨published.value, selected.work.plus published.work⟩

omit [DecidableEq Row] in
theorem immediate_value (select : Row → Bool) (rows : List Row) :
    (immediate select rows).value = (rows.filter (fun row => !select row), rows.any select) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [immediate, matched, ih]

omit [DecidableEq Row] in
theorem gather_value (select : Row → Bool) (rows : List Row) :
    (gather select rows).value = rows.filter select := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [gather, matched, ih]

omit [DecidableEq Row] in
theorem immediate_work (select : Row → Bool) (rows : List Row) :
    (immediate select rows).work = ⟨rows.length, 0, (rows.filter (fun row => !select row)).length⟩ := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [immediate, Work.plus, matched, ih]

omit [DecidableEq Row] in
theorem gather_work (select : Row → Bool) (rows : List Row) :
    (gather select rows).work = ⟨rows.length, 0, (rows.filter select).length⟩ := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [gather, Work.plus, matched, ih]

theorem member_value (row : Row) (rows : List Row) :
    (member row rows).value = decide (row ∈ rows) := by
  induction rows with
  | nil => rfl
  | cons candidate rest ih => by_cases same : row = candidate <;> simp [member, same, ih]

theorem member_work (row : Row) (rows : List Row) :
    (member row rows).work.predicates = 0 ∧ (member row rows).work.cells = 0 := by
  induction rows with
  | nil => exact ⟨rfl, rfl⟩
  | cons candidate rest ih => by_cases same : row = candidate <;> simp [member, same, Work.plus, ih]

theorem equal_self (rows : List Row) : equalRows rows rows = ⟨true, ⟨0, rows.length, 0⟩⟩ := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [equalRows, ih, Work.plus]

theorem contract_value (selected rows : List Row) :
    (contract selected rows).value = rows.filter (fun row => decide (row ∉ selected)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      by_cases chosen : row ∈ selected <;> simp [contract, member_value, chosen, ih]

theorem contract_work (selected rows : List Row) :
    (contract selected rows).work.predicates = 0 ∧
      (contract selected rows).work.cells = (contract selected rows).value.length := by
  induction rows with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rest ih =>
      have noWork := member_work row selected
      cases chosen : (member row selected).value <;>
        simp [contract, chosen, Work.plus, ih, noWork]

theorem contract_gathered (select : Row → Bool) (rows : List Row) :
    (contract (gather select rows).value rows).value = rows.filter (fun row => !select row) := by
  rw [contract_value, gather_value]
  apply List.filter_congr
  intro row present
  cases matched : select row <;> simp [present, matched]

omit [DecidableEq Row] in
theorem changed_iff_selected (select : Row → Bool) (rows : List Row) :
    Bool.not (rows.filter select).isEmpty = rows.any select := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [matched, ih]

theorem prepared_value (select : Row → Bool) (rows : List Row) :
    (prepared select rows).value = some (immediate select rows).value := by
  simp only [prepared, checked, equal_self, if_true, publishSelected]
  rw [contract_gathered, gather_value, changed_iff_selected, immediate_value]

theorem prepared_work (select : Row → Bool) (rows : List Row) :
    (prepared select rows).work =
      ⟨2 * rows.length,
        (rows.filter select).length + (contract (gather select rows).value rows).work.comparisons,
        2 * (rows.filter select).length + (rows.filter (fun row => !select row)).length⟩ := by
  have publication := contract_work (gather select rows).value rows
  rw [contract_gathered] at publication
  simp only [gather_value] at publication
  simp [prepared, checked, publishSelected, equal_self, gather_work, Work.plus,
    publication, gather_value, two_mul, Nat.add_assoc]

theorem immediate_price_le_prepared (select : Row → Bool) (rows : List Row)
    (predicate equality cell : Nat) :
    (immediate select rows).work.price predicate equality cell ≤
      (prepared select rows).work.price predicate equality cell := by
  rw [immediate_work, prepared_work]
  simp only [Work.price, Nat.mul_zero, Nat.add_zero]
  apply Nat.add_le_add
  · exact (Nat.mul_le_mul_left predicate (by omega : rows.length ≤ 2 * rows.length)).trans
      (Nat.le_add_right _ _)
  · exact Nat.mul_le_mul_left cell (Nat.le_add_left _ _)

theorem price_overhead_exact (select : Row → Bool) (rows : List Row)
    (predicate equality cell : Nat) :
    (prepared select rows).work.price predicate equality cell =
      (immediate select rows).work.price predicate equality cell +
        predicate * rows.length +
        equality * ((rows.filter select).length +
          (contract (gather select rows).value rows).work.comparisons) +
        cell * (2 * (rows.filter select).length) := by
  rw [immediate_work, prepared_work]
  simp only [Work.price]
  ring

theorem strictly_less_when_predicates_cost (select : Row → Bool) (rows : List Row)
    (predicate equality cell : Nat) (positive : 0 < predicate) (nonempty : rows ≠ []) :
    (immediate select rows).work.price predicate equality cell <
      (prepared select rows).work.price predicate equality cell := by
  have paid := Nat.mul_pos positive (List.length_pos_iff.mpr nonempty)
  rw [price_overhead_exact]
  omega

/-- Existing stable selection licenses the actual publication function,
without rerunning the predicate or constructing another selected list. -/
theorem checked_of_stable (select : Row → Bool) (selected current : List Row)
    (stable : (gather select current).value = selected) :
    (checked select selected current).value = some (publishSelected selected current).value := by
  simp [checked, stable, equal_self]

theorem stable_publication_price_le (select : Row → Bool) (selected current : List Row)
    (stable : (gather select current).value = selected) (predicate equality cell : Nat) :
    (publishSelected selected current).work.price predicate equality cell ≤
      (checked select selected current).work.price predicate equality cell := by
  simp only [checked, stable, equal_self, if_true, Work.plus, Work.price]
  nlinarith

omit [DecidableEq Row] in
/-- An independently established nonmatching extension preserves the complete
selection; a whole-store revision change alone would be too conservative. -/
theorem nonmatching_append_preserves_selection (select : Row → Bool) (before added : List Row)
    (irrelevant : ∀ row ∈ added, select row = false) :
    (gather select (before ++ added)).value = (gather select before).value := by
  rw [gather_value, gather_value, List.filter_append]
  have empty : added.filter select = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row present
    simp [irrelevant row present]
  rw [empty, List.append_nil]

namespace Controls

theorem selected_copies_retain_their_multiplicity :
    (immediate (· == 7) [7, 8, 7]).value = ([8], true) ∧
      (prepared (· == 7) [7, 8, 7]).value = some ([8], true) := by decide

theorem concrete_work_is_not_erased_by_equal_results :
    (immediate (· == 7) [7, 8, 7]).work = ⟨3, 0, 1⟩ ∧
      (prepared (· == 7) [7, 8, 7]).work = ⟨6, 6, 5⟩ := by decide

theorem a_changed_region_refuses_the_old_selection :
    (checked (· == 7) [7] [7, 7]).value = none ∧
      (checked (· == 7) [7] [7, 7]).work.cells = 2 := by decide

end Controls

end Mettapedia.Data.List.PublicationWork
