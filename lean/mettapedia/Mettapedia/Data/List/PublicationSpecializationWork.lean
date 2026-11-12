import Mettapedia.Data.List.PublicationWork
import Mettapedia.Data.List.CountedErase

/-!
# Append and first-occurrence publication work

These are explicit immutable-list implementations and the work coordinates
from PublicationWork. First deletion stops testing at the first match and
shares the unused tail. Its prepared counterpart selects, checks that first
selection, then contracts physical identities. Agreement requires distinct
physical identities; payload equality is not that condition.

The append comparison isolates an implementation that runs an empty-take
contraction before append. It does not assert that CeTTa's scalar addition
performs such a traversal or that these counts measure its record overhead.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List.PublicationSpecializationWork

open PublicationWork
universe u
variable {Row : Type u}

def append : List Row → List Row → Measured (List Row)
  | [], made => ⟨made, ⟨0, 0, 0⟩⟩
  | row :: rest, made =>
      let later := append rest made
      ⟨row :: later.value, later.work.plus ⟨0, 0, 1⟩⟩

theorem append_value (rows made : List Row) : (append rows made).value = rows ++ made := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [append, ih]

theorem append_work (rows made : List Row) : (append rows made).work = ⟨0, 0, rows.length⟩ := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [append, Work.plus, ih]

def first (select : Row → Bool) : List Row → Measured (List Row × Bool)
  | [] => ⟨([], false), ⟨0, 0, 0⟩⟩
  | row :: rest =>
      if select row then ⟨(rest, true), ⟨1, 0, 0⟩⟩
      else
        let later := first select rest
        ⟨(row :: later.value.1, later.value.2), later.work.plus ⟨1, 0, 1⟩⟩

def gatherFirst (select : Row → Bool) : List Row → Measured (List Row)
  | [] => ⟨[], ⟨0, 0, 0⟩⟩
  | row :: rest =>
      if select row then ⟨[row], ⟨1, 0, 1⟩⟩
      else
        let later := gatherFirst select rest
        ⟨later.value, later.work.plus ⟨1, 0, 0⟩⟩

theorem first_value (select : Row → Bool) (rows : List Row) :
    (first select rows).value = (rows.eraseP select, rows.any select) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [first, List.eraseP, matched, ih]

theorem first_as_counted (select : Row → Bool) (rows : List Row) :
    (first select rows).value.1 = CountedErase.eraseUpTo select 1 rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [first, CountedErase.eraseUpTo, matched, ih]

theorem gatherFirst_as_counted (select : Row → Bool) (rows : List Row) :
    (gatherFirst select rows).value = (CountedErase.scan select 1 rows).1 := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [gatherFirst, CountedErase.scan, matched, ih]

theorem first_work (select : Row → Bool) (rows : List Row) :
    (first select rows).work.predicates = (CountedErase.scan select 1 rows).2 ∧
      (first select rows).work.comparisons = 0 ∧
      (first select rows).work.cells ≤ (first select rows).value.1.length := by
  induction rows with
  | nil => simp [first, CountedErase.scan]
  | cons row rest ih =>
      cases matched : select row <;> simp [first, CountedErase.scan, matched, Work.plus, ih]

theorem gatherFirst_work (select : Row → Bool) (rows : List Row) :
    (gatherFirst select rows).work =
      ⟨(CountedErase.scan select 1 rows).2, 0, (gatherFirst select rows).value.length⟩ := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;>
      simp [gatherFirst, CountedErase.scan, matched, Work.plus, ih]

theorem gatherFirst_changed (select : Row → Bool) (rows : List Row) :
    Bool.not (gatherFirst select rows).value.isEmpty = rows.any select := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases matched : select row <;> simp [gatherFirst, matched, ih]

variable [DecidableEq Row]

def appendAfterEmptyTake (rows made : List Row) : Measured (List Row) :=
  let unchanged := contract [] rows
  let result := append unchanged.value made
  ⟨result.value, unchanged.work.plus result.work⟩

def checkedFirst (select : Row → Bool) (selected current : List Row) :
    Measured (Option (List Row × Bool)) :=
  let found := gatherFirst select current
  let same := equalRows selected found.value
  if same.value then
    let published := publishSelected selected current
    ⟨some published.value, (found.work.plus same.work).plus published.work⟩
  else ⟨none, found.work.plus same.work⟩

def preparedFirst (select : Row → Bool) (rows : List Row) :
    Measured (Option (List Row × Bool)) :=
  let selected := gatherFirst select rows
  let published := checkedFirst select selected.value rows
  ⟨published.value, selected.work.plus published.work⟩

theorem empty_take_work (rows : List Row) : (contract [] rows).work = ⟨0, 0, rows.length⟩ := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [contract, member, ih, Work.plus]

theorem empty_take_append_value (rows made : List Row) :
    (appendAfterEmptyTake rows made).value = (append rows made).value := by
  simp [appendAfterEmptyTake, contract_value]

theorem empty_take_append_work (rows made : List Row) :
    (appendAfterEmptyTake rows made).work = ⟨0, 0, 2 * rows.length⟩ := by
  simp [appendAfterEmptyTake, empty_take_work, append_work, contract_value, Work.plus, two_mul]

theorem append_price_le (rows made : List Row) (predicate equality cell : Nat) :
    (append rows made).work.price predicate equality cell ≤
      (appendAfterEmptyTake rows made).work.price predicate equality cell := by
  rw [append_work, empty_take_append_work]
  simp only [Work.price, Nat.mul_zero, Nat.zero_add]
  exact Nat.mul_le_mul_left cell (by omega)

theorem contract_first (select : Row → Bool) (rows : List Row) (unique : rows.Nodup) :
    (contract (gatherFirst select rows).value rows).value = (first select rows).value.1 := by
  rw [contract_value, gatherFirst_as_counted, CountedErase.filter_selected _ _ _ unique, first_as_counted]

theorem preparedFirst_value (select : Row → Bool) (rows : List Row) (unique : rows.Nodup) :
    (preparedFirst select rows).value = some (first select rows).value := by
  simp only [preparedFirst, checkedFirst, equal_self, if_true, publishSelected]
  rw [contract_first select rows unique, gatherFirst_changed, first_value]

theorem preparedFirst_work (select : Row → Bool) (rows : List Row) (unique : rows.Nodup) :
    (preparedFirst select rows).work =
      ⟨2 * (CountedErase.scan select 1 rows).2,
        (gatherFirst select rows).value.length + (contract (gatherFirst select rows).value rows).work.comparisons,
        2 * (gatherFirst select rows).value.length + (first select rows).value.1.length⟩ := by
  have publication := contract_work (gatherFirst select rows).value rows
  rw [contract_first select rows unique] at publication
  simp [preparedFirst, checkedFirst, publishSelected, equal_self, gatherFirst_work,
    Work.plus, publication, two_mul, Nat.add_assoc]

theorem first_price_le (select : Row → Bool) (rows : List Row) (unique : rows.Nodup)
    (predicate equality cell : Nat) :
    (first select rows).work.price predicate equality cell ≤
      (preparedFirst select rows).work.price predicate equality cell := by
  have direct := first_work select rows
  rw [preparedFirst_work select rows unique]
  simp only [Work.price, direct.1, direct.2.1, Nat.mul_zero, Nat.add_zero]
  apply Nat.add_le_add
  · exact (Nat.mul_le_mul_left predicate (by omega :
      (CountedErase.scan select 1 rows).2 ≤ 2 * (CountedErase.scan select 1 rows).2)).trans
      (Nat.le_add_right _ _)
  · exact Nat.mul_le_mul_left cell (direct.2.2.trans (Nat.le_add_left _ _))

namespace Controls

theorem first_retains_the_unused_tail :
    (first (fun n : Nat => n % 2 == 0) [1, 2, 4, 6]).value = ([1, 4, 6], true) ∧
      (first (fun n : Nat => n % 2 == 0) [1, 2, 4, 6]).work = ⟨2, 0, 1⟩ := by decide

theorem value_aliases_cannot_replace_occurrence_ids :
    (first (· == 7) [7, 7]).value = ([7], true) ∧
      (preparedFirst (· == 7) [7, 7]).value = some ([], true) := by decide

theorem append_contraction_is_extra_work :
    (append [1, 2, 3] [4]).value = (appendAfterEmptyTake [1, 2, 3] [4]).value ∧
      (append [1, 2, 3] [4]).work.cells = 3 ∧
      (appendAfterEmptyTake [1, 2, 3] [4]).work.cells = 6 := by decide

end Controls

end Mettapedia.Data.List.PublicationSpecializationWork
