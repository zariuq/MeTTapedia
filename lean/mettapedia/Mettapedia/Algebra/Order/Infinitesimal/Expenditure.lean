import Mettapedia.Algebra.Order.Infinitesimal.LevelSeries

/-!
# Expenditure at several scales

Accounting distinguishes two things that are easy to conflate.

**Expenditure** is consumed: it is nonnegative, it accumulates, and no later
step gives it back. Its natural structure is a monoid, not a group — the
absence of inverses is the content, not an oversight.

**Potential** — a credit, a balance, a remaining budget — is signed. It goes up
and down, and it belongs in the state being reasoned about, never in the
accumulated cost.

This file supplies the first of those over `LevelField`, so that expenditure
can be recorded at several scales at once: a safety-relevant cost at level
`-1`, an ordinary resource cost at level `0`, a negligible overhead at level
`1`. The order comes from the field, so the comparison of two expenditures is
ordinary arithmetic.

The fact that makes the multi-scale reading worth anything is
`omega_spend_not_covered`: **an expenditure carrying anything at level `-1`
exceeds every budget expressed in rationals.** So a level is not a large
weight — it cannot be bought off at all, which is exactly the accounting
property a hard constraint should have and a penalty term does not.

`Expenditure` is deliberately *not* given a subtraction. Refunds, rebates and
credit belong to the signed side and must be carried separately.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries

/-- A nonnegative amount in the level field: something spent. -/
def Expenditure : Type := {c : LevelField // 0 ≤ c}

namespace Expenditure

/-- The amount spent, as a field element. -/
def value (e : Expenditure) : LevelField := e.1

theorem nonneg (e : Expenditure) : 0 ≤ e.value := e.2

@[ext] theorem ext {e f : Expenditure} (h : e.value = f.value) : e = f :=
  Subtype.ext h

/-- Spending nothing. -/
instance : Zero Expenditure := ⟨⟨0, le_refl 0⟩⟩

/-- Spending twice. -/
instance : Add Expenditure :=
  ⟨fun e f => ⟨e.value + f.value, add_nonneg e.nonneg f.nonneg⟩⟩

@[simp] theorem value_zero : (0 : Expenditure).value = 0 := rfl
@[simp] theorem value_add (e f : Expenditure) : (e + f).value = e.value + f.value := rfl

instance : AddCommMonoid Expenditure where
  add_assoc e f g := by ext; simp [add_assoc]
  zero_add e := by ext; simp
  add_zero e := by ext; simp
  add_comm e f := by ext; simp [add_comm]
  nsmul n e := ⟨n • e.value, nsmul_nonneg e.nonneg n⟩
  nsmul_zero e := by ext; exact zero_nsmul e.value
  nsmul_succ n e := by ext; exact succ_nsmul e.value n

/-- Expenditures compare by amount.  The order is declared once, inside the
`PartialOrder`, so that there is a single `≤` on the type. -/
instance : PartialOrder Expenditure where
  le e f := e.value ≤ f.value
  lt e f := e.value < f.value
  le_refl e := _root_.le_refl e.value
  le_trans _ _ _ hef hfg := _root_.le_trans hef hfg
  lt_iff_le_not_ge e f := lt_iff_le_not_ge (a := e.value) (b := f.value)
  le_antisymm _ _ hef hfe := ext (_root_.le_antisymm hef hfe)

theorem le_def {e f : Expenditure} : e ≤ f ↔ e.value ≤ f.value := Iff.rfl
theorem lt_def {e f : Expenditure} : e < f ↔ e.value < f.value := Iff.rfl

/-! ## Spending never decreases

This is the whole reason expenditure is a monoid rather than a group. -/

/-- **Spending more never costs less.** -/
theorem le_add_right (e f : Expenditure) : e ≤ e + f := by
  rw [le_def, value_add]
  exact le_add_of_nonneg_right f.nonneg

theorem le_add_left (e f : Expenditure) : f ≤ e + f := by
  rw [le_def, value_add]
  exact le_add_of_nonneg_left e.nonneg

/-- **Nothing is the cheapest.** -/
theorem zero_le (e : Expenditure) : 0 ≤ e := e.nonneg

/-! ## Scales -/

/-- A rational amount, at level `0`. -/
noncomputable def ofRat' (q : ℚ) (hq : 0 ≤ q) : Expenditure := ⟨ofRat q, ofRat_nonneg hq⟩

/-- One unit of level `-1` expenditure: the scale a rational budget cannot
reach. -/
noncomputable def omegaSpend : Expenditure := ⟨Om, le_of_lt Om_pos⟩

@[simp] theorem value_omegaSpend : omegaSpend.value = Om := rfl
@[simp] theorem value_ofRat' (q : ℚ) (hq : 0 ≤ q) : (ofRat' q hq).value = ofRat q := rfl

/-- **A level-`-1` expenditure exceeds every rational budget.**  So it is not a
large price: it is outside the currency the budget is quoted in. -/
theorem omega_spend_not_covered (budget : ℚ) (hb : 0 ≤ budget) :
    ofRat' budget hb < omegaSpend := by
  rw [lt_def, value_ofRat', value_omegaSpend]
  exact ofRat_lt_Om budget

/-- And it stays out of reach however much else is spent alongside it: any
total containing it still exceeds every rational budget. -/
theorem omega_spend_not_covered_in_total (budget : ℚ) (hb : 0 ≤ budget)
    (rest : Expenditure) : ofRat' budget hb < omegaSpend + rest :=
  lt_of_lt_of_le (omega_spend_not_covered budget hb) (le_add_right _ _)

/-! ## Controls -/

namespace ExpenditureControls

/-- A rational budget *does* cover a smaller rational expenditure, so the
previous theorem is about the level and not about budgets being useless. -/
theorem rational_budget_covers {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    ofRat' a ha ≤ ofRat' b hb := by
  rw [le_def, value_ofRat', value_ofRat']
  exact ofRat_le_ofRat hab

/-- Expenditure has no inverses: nothing but `0` can be cancelled back to `0`.
This is the formal content of "spending is not refundable". -/
theorem no_refund {e f : Expenditure} (h : e + f = 0) : e = 0 ∧ f = 0 := by
  have hv : e.value + f.value = 0 := congrArg Expenditure.value h
  have he : e.value ≤ 0 := by
    calc e.value ≤ e.value + f.value := le_add_of_nonneg_right f.nonneg
      _ = 0 := hv
  have hf : f.value ≤ 0 := by
    calc f.value ≤ e.value + f.value := le_add_of_nonneg_left e.nonneg
      _ = 0 := hv
  exact ⟨ext (le_antisymm he e.nonneg), ext (le_antisymm hf f.nonneg)⟩

end ExpenditureControls

end Expenditure

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.Expenditure.le_add_right
#print axioms Mettapedia.Algebra.Order.Infinitesimal.Expenditure.omega_spend_not_covered
#print axioms Mettapedia.Algebra.Order.Infinitesimal.Expenditure.omega_spend_not_covered_in_total
#print axioms Mettapedia.Algebra.Order.Infinitesimal.Expenditure.ExpenditureControls.no_refund
