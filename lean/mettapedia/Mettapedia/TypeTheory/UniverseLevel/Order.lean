import Mathlib.Order.Nat

/-!
# Orders of universe levels

A universe level lives in a well-founded linear order with a least element and
a successor that is the least strict upper bound. The natural numbers are one
such order; ordinal notations below ε₀ are another.

The interpretation of a type at level `l` is built from the interpretations at
the levels below `l`. The *table* of those interpretations is defined here once,
by well-founded recursion, for any level order: at level `l` it reads each lower
level `k` by the interpretation at `k` given the table below `k`, and every other
level by a fixed empty value. The table unfolds by an equation rather than by
definition, which is all its consumers need.

Positive examples: the natural numbers, and a table over them. Negative
examples: doubling plus one is not a least strict upper bound, and the integers
have no least element.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

/-- A well-founded linear order of universe levels, with a least level and a
successor that is the least level strictly above a given one. -/
class LevelOrder (L : Type) extends LinearOrder L where
  wf : WellFounded (fun a b : L => a < b)
  bot : L
  bot_le : ∀ l, bot ≤ l
  succ : L → L
  lt_succ : ∀ l, l < succ l
  succ_le_of_lt : ∀ {a b : L}, a < b → succ a ≤ b

namespace LevelOrder

variable {L : Type} [LevelOrder L]

/-- A level is below its successor. -/
theorem le_succ (l : L) : l ≤ succ l := le_of_lt (lt_succ l)

/-- Nothing lies strictly between a level and its successor. -/
theorem not_lt_of_lt_succ {a b : L} (h : a < b) : ¬ b < succ a :=
  not_lt_of_ge (succ_le_of_lt h)

/-- Strict order is reflected by the successor. -/
theorem lt_of_succ_le {a b : L} (h : succ a ≤ b) : a < b := lt_of_lt_of_le (lt_succ a) h

/-- `succ a ≤ b` exactly when `a < b`. -/
theorem succ_le_iff {a b : L} : succ a ≤ b ↔ a < b := ⟨lt_of_succ_le, succ_le_of_lt⟩

/-- The successor is monotone. -/
theorem succ_le_succ {a b : L} (h : a ≤ b) : succ a ≤ succ b :=
  succ_le_of_lt (lt_of_le_of_lt h (lt_succ b))

/-- Strong induction over levels. -/
theorem induction {motive : L → Prop} (l : L)
    (step : ∀ l, (∀ k, k < l → motive k) → motive l) : motive l :=
  wf.induction l step

end LevelOrder

/-! ## The natural numbers -/

/-- The natural numbers are a level order: zero is least, and `n + 1` is the
least number above `n`. -/
instance : LevelOrder Nat where
  toLinearOrder := inferInstance
  wf := Nat.lt_wfRel.wf
  bot := 0
  bot_le := Nat.zero_le
  succ := Nat.succ
  lt_succ := Nat.lt_succ_self
  succ_le_of_lt := Nat.succ_le_of_lt

@[simp] theorem nat_succ (n : Nat) : LevelOrder.succ n = n + 1 := rfl

@[simp] theorem nat_bot : (LevelOrder.bot : Nat) = 0 := rfl

/-! ## The table of interpretations below a level -/

section Table

variable {L : Type} [LevelOrder L] {β : Sort _}

/-- The table of the interpretations below a level. At level `l`, a lower level
`k` is read by `step k` applied to the table below `k`; every other level by
`empty`. -/
noncomputable def below (step : L → (L → β) → β) (empty : β) : L → L → β :=
  LevelOrder.wf.fix fun l rec k => if h : k < l then step k (rec k h) else empty

/-- The table's equation. -/
theorem below_eq (step : L → (L → β) → β) (empty : β) (l : L) :
    below step empty l = fun k => if k < l then step k (below step empty k) else empty :=
  LevelOrder.wf.fix_eq _ l

/-- A lower level is read by the interpretation at that level. -/
theorem below_of_lt (step : L → (L → β) → β) (empty : β) {l k : L} (h : k < l) :
    below step empty l k = step k (below step empty k) := by
  rw [below_eq]
  exact if_pos h

/-- Any other level is read by the empty value. -/
theorem below_of_not_lt (step : L → (L → β) → β) (empty : β) {l k : L} (h : ¬ k < l) :
    below step empty l k = empty := by
  rw [below_eq]
  exact if_neg h

/-- The interpretation at a level, given the table below it. -/
noncomputable def atLevel (step : L → (L → β) → β) (empty : β) (l : L) : β :=
  step l (below step empty l)

/-- Reading a lower level through the table is the interpretation at that
level. -/
theorem below_iff_atLevel (step : L → (L → β) → β) (empty : β) {l k : L} (h : k < l) :
    below step empty l k = atLevel step empty k :=
  below_of_lt step empty h

end Table

/-! ## Examples -/

section Examples

/-- A table over the natural numbers that counts the levels below: the entry at
`k` is `k`, obtained from the entries below `k`. -/
example : below (L := Nat) (fun k _ => k) 0 5 3 = 3 :=
  below_of_lt _ _ (by decide)

/-- The same table reads a level that is not below as empty. -/
example : below (L := Nat) (fun k _ => k) 0 3 5 = 0 :=
  below_of_not_lt _ _ (by decide)

/-- Doubling plus one is strictly increasing but not the least strict upper
bound: `1 < 2`, while `2 * 1 + 1 = 3` is not below `2`. -/
theorem doubling_not_least :
    ¬ ∀ {a b : Nat}, a < b → 2 * a + 1 ≤ b := fun h =>
  absurd (h (a := 1) (b := 2) (by decide)) (by decide)

/-- The integers have no least element, so they carry no level order that
extends their usual order. -/
theorem int_no_bot : ¬ ∃ bot : Int, ∀ l, bot ≤ l := fun ⟨bot, h⟩ =>
  Int.lt_irrefl bot (Int.lt_of_le_of_lt (h (bot - 1)) (Int.sub_one_lt_iff.mpr (Int.le_refl bot)))

end Examples

end Mettapedia.TypeTheory.UniverseLevel
