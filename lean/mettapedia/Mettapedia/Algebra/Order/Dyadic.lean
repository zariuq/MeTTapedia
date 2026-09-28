import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dyadic rationals

The rationals with a power of two as denominator. Mathlib does not define them
and this development needs them in three unrelated places, so they are defined
once here, in their mathematical subject.

The definition is chosen so that nothing has to be rebuilt: dyadics are a
**subring of `ℚ`**, and the ring and order structure are inherited rather than
re-proved. A representation as a pair `(numerator, exponent)` is a *view*
(`ofPair`, `exists_pair`), not the definition — pairs are not unique
(`1/2 = 2/4`), and making them primary forces a normalization discipline on
every later lemma.

* `IsDyadic` — the predicate, `∃ m k, q = m / 2 ^ k`.
* `dyadicSubring` — the subring of `ℚ` they form.
* `Dyadic` — its carrier, with `CommRing` and `LinearOrder` inherited.
* `ofPair` / `exists_pair` — the numerator-and-exponent view, both ways.

What this is *not*: a computational representation. `Dyadic` is a subtype of
`ℚ`, so equality is equality of rationals and `1/2 = 2/4` holds definitionally
rather than up to a normal form. That is the right primitive for stating
theorems; a normalized pair type is the right primitive for computing, and the
two should be related by a theorem rather than conflated.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order

/-- A rational is dyadic when some power of two clears its denominator. -/
def IsDyadic (q : ℚ) : Prop := ∃ (m : ℤ) (k : ℕ), q = (m : ℚ) / 2 ^ k

namespace IsDyadic

theorem of_int (m : ℤ) : IsDyadic (m : ℚ) := ⟨m, 0, by simp⟩

@[simp] theorem zero : IsDyadic 0 := by simpa using of_int 0
@[simp] theorem one : IsDyadic 1 := by simpa using of_int 1

theorem neg {q : ℚ} (h : IsDyadic q) : IsDyadic (-q) := by
  obtain ⟨m, k, rfl⟩ := h
  exact ⟨-m, k, by push_cast; ring⟩

theorem add {p q : ℚ} (hp : IsDyadic p) (hq : IsDyadic q) : IsDyadic (p + q) := by
  obtain ⟨m, j, rfl⟩ := hp
  obtain ⟨n, k, rfl⟩ := hq
  refine ⟨m * 2 ^ k + n * 2 ^ j, j + k, ?_⟩
  have h2 : ((2 : ℚ) ^ j) ≠ 0 := by positivity
  have h3 : ((2 : ℚ) ^ k) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem mul {p q : ℚ} (hp : IsDyadic p) (hq : IsDyadic q) : IsDyadic (p * q) := by
  obtain ⟨m, j, rfl⟩ := hp
  obtain ⟨n, k, rfl⟩ := hq
  refine ⟨m * n, j + k, ?_⟩
  have h2 : ((2 : ℚ) ^ j) ≠ 0 := by positivity
  have h3 : ((2 : ℚ) ^ k) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Halving stays inside.**  This is the property that makes the dyadics the
natural home for sign expansions of finite length. -/
theorem half {q : ℚ} (h : IsDyadic q) : IsDyadic (q / 2) := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨m, k + 1, ?_⟩
  have h2 : ((2 : ℚ) ^ k) ≠ 0 := by positivity
  field_simp
  ring

end IsDyadic

/-- **The dyadic rationals, as a subring of `ℚ`.**  Stating it this way is what
makes the ring structure inherited instead of rebuilt. -/
def dyadicSubring : Subring ℚ where
  carrier := {q | IsDyadic q}
  zero_mem' := IsDyadic.zero
  one_mem' := IsDyadic.one
  add_mem' := IsDyadic.add
  neg_mem' := IsDyadic.neg
  mul_mem' := IsDyadic.mul

/-- The dyadic rationals. -/
abbrev Dyadic : Type := dyadicSubring

namespace Dyadic

/-- The underlying rational. -/
def val (d : Dyadic) : ℚ := d.1

@[simp] theorem val_isDyadic (d : Dyadic) : IsDyadic d.val := d.2

@[ext] theorem ext {d e : Dyadic} (h : d.val = e.val) : d = e := Subtype.ext h

/-! ## The pair view

Every dyadic is `m / 2 ^ k`, and every such quotient is a dyadic.  Neither
direction is the definition, which is why `1/2` and `2/4` are the same dyadic
without any normalization step. -/

/-- Build a dyadic from a numerator and an exponent. -/
def ofPair (m : ℤ) (k : ℕ) : Dyadic := ⟨(m : ℚ) / 2 ^ k, m, k, rfl⟩

@[simp] theorem val_ofPair (m : ℤ) (k : ℕ) : (ofPair m k).val = (m : ℚ) / 2 ^ k := rfl

/-- And every dyadic arises that way. -/
theorem exists_pair (d : Dyadic) : ∃ (m : ℤ) (k : ℕ), d = ofPair m k := by
  obtain ⟨m, k, hk⟩ := d.2
  exact ⟨m, k, Subtype.ext hk⟩

/-- **Distinct pairs can name the same dyadic**, which is why the pair is a
view and not the definition. -/
theorem ofPair_one_two_eq_two_four : ofPair 1 1 = ofPair 2 2 := by
  refine Dyadic.ext ?_
  rw [val_ofPair, val_ofPair]
  norm_num

/-! ## Inherited structure

Nothing below is constructed: the ring comes from `dyadicSubring`, and the
order from `ℚ` through the subtype. -/

instance : CommRing Dyadic := inferInstance
instance : LinearOrder Dyadic := inferInstance

theorem val_injective : Function.Injective val := fun _ _ h => Subtype.ext h

@[simp] theorem val_zero : (0 : Dyadic).val = 0 := rfl
@[simp] theorem val_one : (1 : Dyadic).val = 1 := rfl
@[simp] theorem val_add (d e : Dyadic) : (d + e).val = d.val + e.val := rfl
@[simp] theorem val_neg (d : Dyadic) : (-d).val = -d.val := rfl
@[simp] theorem val_mul (d e : Dyadic) : (d * e).val = d.val * e.val := rfl

theorem lt_iff {d e : Dyadic} : d < e ↔ d.val < e.val := Iff.rfl
theorem le_iff {d e : Dyadic} : d ≤ e ↔ d.val ≤ e.val := Iff.rfl

/-! ## Halving, as an operation -/

/-- Halving a dyadic. -/
def half (d : Dyadic) : Dyadic := ⟨d.val / 2, IsDyadic.half d.2⟩

@[simp] theorem val_half (d : Dyadic) : (half d).val = d.val / 2 := rfl

theorem half_lt_self {d : Dyadic} (h : 0 < d) : half d < d := by
  rw [lt_iff, val_half]
  have : (0 : ℚ) < d.val := h
  linarith

/-! ## Controls -/

namespace DyadicControls

/-- Not every rational is dyadic: `1/3` is not. -/
theorem one_third_not_dyadic : ¬ IsDyadic (1 / 3) := by
  rintro ⟨m, k, hk⟩
  have h2 : ((2 : ℚ) ^ k) ≠ 0 := by positivity
  have h3 : (3 : ℚ) * (m : ℚ) = 2 ^ k := by
    field_simp at hk
    linarith [hk]
  -- Transport `3 * m = 2 ^ k` to the integers, then to the naturals.
  have hint : (3 : ℤ) * m = 2 ^ k := by exact_mod_cast h3
  have hdvd : (3 : ℤ) ∣ 2 ^ k := ⟨m, hint.symm⟩
  have hnat : (3 : ℕ) ∣ 2 ^ k := by
    have : ((3 : ℕ) : ℤ) ∣ ((2 ^ k : ℕ) : ℤ) := by push_cast; exact hdvd
    exact_mod_cast this
  -- But 3 is coprime to every power of 2.
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by decide)
  have hgcd : Nat.gcd 3 (2 ^ k) = 1 := hcop
  have hd1 : (3 : ℕ) ∣ 1 := by
    have h := Nat.dvd_gcd (dvd_refl (3 : ℕ)) hnat
    rwa [hgcd] at h
  norm_num at hd1

/-- The dyadics are closed under halving but the integers are not, which is the
whole reason to have them. -/
theorem half_one_not_int : (Dyadic.half 1).val = 1 / 2 := by
  simp

/-- And the order is the rationals' own. -/
theorem half_one_lt_one : Dyadic.half 1 < 1 := by
  rw [lt_iff, val_half, val_one]
  norm_num

end DyadicControls

end Dyadic

end Mettapedia.Algebra.Order

#print axioms Mettapedia.Algebra.Order.IsDyadic.add
#print axioms Mettapedia.Algebra.Order.IsDyadic.half
#print axioms Mettapedia.Algebra.Order.Dyadic.exists_pair
#print axioms Mettapedia.Algebra.Order.Dyadic.DyadicControls.one_third_not_dyadic
