import Mettapedia.GSLT.LanguageDef.NativeOpsAllocationGuards

/-!
Ordered reserve-slot planning for the compact native allocation table. Counter
additions retain unsigned wraparound; the capacity-doubling and table-extent
checks are distinct. A successful plan either retains the existing table or
requests a new table. Allocation callbacks and rehashing have subsequent
stateful effects. The cell width is a positive parameter of the declared ABI.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsAllocationTableGuards

open NativeWord64

abbrev CellWidth := { width : Word // 0 < width.val }

def sourceDouble (capacity : Word) : Except Fault Word :=
  if (bound - 1) / 2 < capacity.val then .error .lengthOverflow
  else .ok (bounded 64 (capacity.val * 2))

def targetDouble (capacity : BitVec 64) : Except Fault (BitVec 64) :=
  if BitVec.allOnes 64 / 2 < capacity then .error .lengthOverflow
  else .ok (capacity * 2)

theorem doubling_correspondence (capacity : Word) :
    (targetDouble (encode capacity)).map BitVec.toFin = sourceDouble capacity := by
  have two : (2 : BitVec 64).toNat = 2 := rfl
  unfold targetDouble sourceDouble
  simp only [BitVec.lt_def, BitVec.toNat_udiv, BitVec.toNat_allOnes,
    two, encode_toNat, bound]
  by_cases overflow : (2 ^ 64 - 1) / 2 < capacity.val
  · simp only [overflow, if_true, Except.map]
  · simp only [overflow, if_false, Except.map]
    apply congrArg Except.ok
    apply Fin.ext
    simp only [BitVec.val_toFin, BitVec.toNat_mul, encode_toNat, bounded, two]

def sourceNext (capacity occupied : Word) : Except Fault Word :=
  if capacity.val ≠ 0 ∧ capacity.val / 2 < (occupied.val + 1) % bound then
    sourceDouble capacity
  else .ok (if capacity.val = 0 then 16 else capacity)

def targetNext (capacity occupied : BitVec 64) : Except Fault (BitVec 64) :=
  if capacity ≠ 0 ∧ capacity / 2 < occupied + 1 then targetDouble capacity
  else .ok (if capacity = 0 then 16 else capacity)

theorem next_capacity_correspondence (capacity occupied : Word) :
    (targetNext (encode capacity) (encode occupied)).map BitVec.toFin =
      sourceNext capacity occupied := by
  have one : (1 : BitVec 64).toNat = 1 := rfl
  have two : (2 : BitVec 64).toNat = 2 := rfl
  unfold sourceNext targetNext
  simp only [ne_eq, encode_eq_zero, BitVec.lt_def, BitVec.toNat_udiv, encode_toNat,
    BitVec.toNat_add, one, two, bound]
  by_cases grow : ¬ capacity.val = 0 ∧ capacity.val / 2 < (occupied.val + 1) % (2 ^ 64)
  · simp only [grow]
    exact doubling_correspondence capacity
  · simp only [grow, if_false]
    by_cases zero : capacity.val = 0
    · simp only [zero, if_true, Except.map]
      rfl
    · simp only [zero, if_false, Except.map]
      rfl

def sourcePlan (capacity occupied deleted : Word) (width : CellWidth) :
    Except Fault (Option Word) :=
  if capacity.val ≠ 0 ∧ (occupied.val + deleted.val + 1) % bound ≤ capacity.val / 2 then
    .ok none
  else match sourceNext capacity occupied with
    | .error fault => .error fault
    | .ok next =>
        if (bound - 1) / width.val.val < next.val then .error .lengthOverflow
        else .ok (some next)

def targetPlan (capacity occupied deleted width : BitVec 64) :
    Except Fault (Option (BitVec 64)) :=
  if capacity ≠ 0 ∧ occupied + deleted + 1 ≤ capacity / 2 then .ok none
  else match targetNext capacity occupied with
    | .error fault => .error fault
    | .ok next =>
        if BitVec.allOnes 64 / width < next then .error .lengthOverflow
        else .ok (some next)

def observePlan (result : Except Fault (Option (BitVec 64))) : Except Fault (Option Word) :=
  result.map (Option.map BitVec.toFin)

theorem reservation_correspondence (capacity occupied deleted : Word) (width : CellWidth) :
    observePlan (targetPlan (encode capacity) (encode occupied) (encode deleted)
      (encode width.val)) = sourcePlan capacity occupied deleted width := by
  have one : (1 : BitVec 64).toNat = 1 := rfl
  have two : (2 : BitVec 64).toNat = 2 := rfl
  unfold sourcePlan targetPlan
  have wrapped : ((occupied.val + deleted.val) % (2 ^ 64) + 1) % (2 ^ 64) =
      (occupied.val + deleted.val + 1) % (2 ^ 64) := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  simp only [ne_eq, encode_eq_zero, BitVec.le_def, BitVec.toNat_add, encode_toNat,
    BitVec.toNat_udiv, one, two, bound, wrapped]
  by_cases keep : ¬ capacity.val = 0 ∧
      (occupied.val + deleted.val + 1) % (2 ^ 64) ≤ capacity.val / 2
  · simp only [keep]
    rfl
  · simp only [keep, if_false]
    cases next : targetNext (encode capacity) (encode occupied) with
    | error fault =>
        have source := next_capacity_correspondence capacity occupied
        simp only [next, Except.map] at source
        simp only [← source, observePlan, Except.map]
    | ok value =>
        have source := next_capacity_correspondence capacity occupied
        simp only [next, Except.map] at source
        simp only [← source, BitVec.lt_def, BitVec.toNat_udiv,
          BitVec.toNat_allOnes, encode_toNat, BitVec.val_toFin]
        by_cases overflow : (2 ^ 64 - 1) / width.val.val < value.toNat
        · simp only [overflow, if_true]
          rfl
        · simp only [overflow, if_false]
          rfl

theorem doubling_success_exact {capacity next : Word}
    (success : sourceDouble capacity = .ok next) :
    next.val = capacity.val * 2 ∧ capacity.val * 2 < bound := by
  unfold sourceDouble at success
  by_cases overflow : (bound - 1) / 2 < capacity.val
  · rw [if_pos overflow] at success
    cases success
  · rw [if_neg overflow] at success
    have same : bounded 64 (capacity.val * 2) = next := Except.ok.inj success
    have capacityBound := capacity.isLt
    change capacity.val < bound at capacityBound
    have safe : capacity.val * 2 < bound := by
      have maxHalf : (bound - 1) / 2 = 2 ^ 63 - 1 := by decide +kernel
      rw [maxHalf] at overflow
      have size : bound = 2 * 2 ^ 63 := by decide +kernel
      rw [size]
      omega
    constructor
    · rw [← same]
      exact Nat.mod_eq_of_lt safe
    · exact safe

private def word (value : Nat) : Word := bounded 64 value
private def cellWidth : CellWidth := ⟨word 16, by decide +kernel⟩

theorem first_table_has_sixteen_cells : sourcePlan 0 0 0 cellWidth = .ok (some 16) :=
  by decide +kernel

theorem below_half_capacity_reuses_table : sourcePlan 16 6 0 cellWidth = .ok none :=
  by decide +kernel

theorem tombstones_at_half_capacity_require_compaction :
    sourcePlan 16 6 2 cellWidth = .ok (some 16) := by decide +kernel

theorem live_cells_at_half_capacity_require_doubling :
    sourcePlan 16 8 0 cellWidth = .ok (some 32) := by decide +kernel

theorem maximal_doubling_refuses :
    sourceDouble (word (bound - 1)) = .error .lengthOverflow := by decide +kernel

theorem table_byte_extent_refuses :
    sourcePlan (word (2 ^ 63)) 0 (word (2 ^ 63)) cellWidth = .error .lengthOverflow :=
  by decide +kernel

theorem counter_wrap_is_retained :
    sourcePlan 16 (word (bound - 1)) 0 cellWidth = .ok none := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOpsAllocationTableGuards
