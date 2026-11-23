import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-! A read-only list index built from shared suffixes at a fixed stride. -/

set_option autoImplicit false

namespace Mettapedia.Data.List.BlockIndex

variable {A : Type*}

def suffixes (width : Nat) : Nat → List A → List (List A)
  | 0, _ => []
  | count + 1, source => source :: suffixes width count (source.drop width)

theorem length_suffixes (width count : Nat) (source : List A) :
    (suffixes width count source).length = count := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih => simp [suffixes, ih]

theorem suffixes_at (width count index : Nat) (source : List A)
    (inside : index < count) :
    (suffixes width count source)[index]? = some (source.drop (index * width)) := by
  induction index generalizing count source with
  | zero =>
      cases count with
      | zero => simp at inside
      | succ count => simp [suffixes]
  | succ index ih =>
      cases count with
      | zero => simp at inside
      | succ remaining =>
          have earlier : index < remaining := Nat.lt_of_succ_lt_succ inside
          simp only [suffixes, List.getElem?_cons_succ, ih _ (source.drop width) earlier,
            List.drop_drop, Nat.succ_mul, Nat.add_comm]

def fromList (width : Nat) (source : List A) : List (List A) :=
  suffixes width (source.length / width + 1) source

def read (width : Nat) (table : List (List A)) (index : Nat) : Option A :=
  (table[index / width]?).bind (fun block => block[index % width]?)

theorem read_fromList (width : Nat) (source : List A) (index : Nat) :
    read width (fromList width source) index = source[index]? := by
  by_cases bounded : index / width < source.length / width + 1
  · rw [read, fromList, suffixes_at _ _ _ _ bounded]
    simp only [Option.bind, List.getElem?_drop]
    congr 1
    rw [Nat.mul_comm (index / width) width, Nat.add_comm, Nat.mod_add_div]
  · have past : source.length ≤ index := by
      by_contra h
      exact bounded (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt (Nat.lt_of_not_ge h))))
    have outside : (fromList width source).length ≤ index / width := by
      rw [fromList, length_suffixes]
      exact Nat.le_of_not_gt bounded
    simp [read, List.getElem?_eq_none_iff.mpr outside, List.getElem?_eq_none_iff.mpr past]

end Mettapedia.Data.List.BlockIndex
