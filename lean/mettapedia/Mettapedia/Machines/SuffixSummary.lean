import Mathlib.Data.List.Basic

/-!
# A suffix's summary from its list's, bit by bit

An expression carries a summary folded from its elements' summaries.  Some
bits are held when any element holds them: whether it has variables, whether
it may hold a list carrier.  Others are held when every element holds them:
whether its hash is stable.  A walk by `(cons $x $xs)` over a flat list takes
the rest of the list as a suffix view, which needs the suffix's summary.

Refolding the suffix costs its length at every step, a quadratic walk.  This
file justifies deriving the suffix's summary from the list's, one bit at a
time, where `take k` departs and `drop k` remains:
* A bit any element must hold: if no departed element held it, the suffix
  holds it exactly when the list does (`any_drop_of_take`); if the list does
  not hold it, neither does the suffix (`any_drop_of_not`).  Otherwise the
  suffix holds it exactly when some remaining element does, which a scan of
  the suffix finds (`any_drop_scan`).
* A bit every element must hold: if every departed element held it, the
  suffix holds it exactly when the list does (`all_drop_of_take`); if the list
  holds it, so does the suffix (`all_drop_of_all`).  Otherwise the suffix
  holds it exactly when no remaining element lacks it (`all_drop_scan`).
* The single variable: when every variable of the list is `x` and the suffix
  has a variable, every variable of the suffix is `x` (`single_drop`).

A scan for a bit starts only where a departed element held it (or lacked it,
for a bit every element must hold), and stops at the next element that does.
Over a walk by one element at a time the scans for one bit cover the gaps
between its holders once each, so the whole walk costs linear time per bit.

`Controls.inheritance_wrong`: a list whose first element alone has a variable
has one, and its tail has none.  Keeping the list's summary for the suffix
would be wrong, and the scan is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SuffixSummary

universe u v

variable {α : Type u} (p : α → Bool)

/-! ## Bits any element must hold -/

/-- If no departed element holds the bit, the suffix holds it exactly when
the list does. -/
theorem any_drop_of_take (l : List α) (k : ℕ) (h : (l.take k).any p = false) :
    (l.drop k).any p = l.any p := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [List.any_append, h, Bool.false_or]

/-- If the list does not hold the bit, neither does the suffix. -/
theorem any_drop_of_not (l : List α) (k : ℕ) (h : l.any p = false) :
    (l.drop k).any p = false := by
  rw [← List.take_append_drop k l, List.any_append, Bool.or_eq_false_iff] at h
  exact h.2

/-- Otherwise the suffix holds it exactly when a scan of the suffix finds a
holder. -/
theorem any_drop_scan (l : List α) (k : ℕ) :
    (l.drop k).any p = true ↔ ∃ x ∈ l.drop k, p x = true :=
  List.any_eq_true

/-! ## Bits every element must hold -/

/-- If every departed element holds the bit, the suffix holds it exactly when
the list does. -/
theorem all_drop_of_take (l : List α) (k : ℕ) (h : (l.take k).all p = true) :
    (l.drop k).all p = l.all p := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [List.all_append, h, Bool.true_and]

/-- If the list holds the bit, so does the suffix. -/
theorem all_drop_of_all (l : List α) (k : ℕ) (h : l.all p = true) :
    (l.drop k).all p = true := by
  rw [← List.take_append_drop k l, List.all_append, Bool.and_eq_true] at h
  exact h.2

/-- Otherwise the suffix holds it exactly when a scan of the suffix finds no
element that lacks it. -/
theorem all_drop_scan (l : List α) (k : ℕ) :
    (l.drop k).all p = true ↔ ∀ x ∈ l.drop k, p x = true :=
  List.all_eq_true

/-! ## The single variable -/

variable {V : Type v}

/-- When every variable of the list's elements is `x`, every variable of the
suffix's is: the suffix's single variable is the list's whenever the suffix
has one. -/
theorem single_drop (vars : α → List V) (l : List α) (k : ℕ) (x : V)
    (h : ∀ e ∈ l, ∀ y ∈ vars e, y = x) :
    ∀ e ∈ l.drop k, ∀ y ∈ vars e, y = x :=
  fun e he => h e (List.mem_of_mem_drop he)

namespace Controls

/-- The first element alone has a variable: the list has one, its tail none.
The departed element held the bit, so the scan decides, and finds no holder. -/
theorem inheritance_wrong :
    ([true, false, false].take 1).any id = true ∧
      [true, false, false].any id = true ∧
      ([true, false, false].drop 1).any id = false :=
  ⟨rfl, rfl, rfl⟩

/-- Every element has a variable: the scan stops at the first element of the
suffix, a constant cost per step. -/
theorem holder_first :
    ([true, true, true].drop 1).head? = some true := rfl

end Controls

end Mettapedia.Machines.SuffixSummary
