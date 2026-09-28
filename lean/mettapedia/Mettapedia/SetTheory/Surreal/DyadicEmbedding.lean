import Mettapedia.SetTheory.Surreal.HalvingLadder
import Mettapedia.SetTheory.Surreal.AdditionBirthday
import Mettapedia.Algebra.Order.Dyadic
import Mathlib.Algebra.Order.Group.Basic

/-!
# The executable dyadics inside the surreals

`Mettapedia/Algebra/Order/Dyadic.lean` already carries the executable side:
the dyadic rationals are the subring `ℤ[1/2] ⊆ ℚ`, so their arithmetic
computes and their order and equality decide, through `ℚ`. Nothing is rebuilt
here.

What is built is the map into the surreals and the theorems that make it an
interpretation rather than a coincidence:

```
toSurreal (m / 2^k)  =  m • ladder k
```

an **integer multiple of a rung of the halving ladder**. That choice is what
makes this section short. Additivity is `add_zsmul` and needs no induction;
negation is `neg_zsmul`; well-definedness — that `1/2` and `2/4` land on the
same surreal — is `ladder_add_self` applied `j` times; and order preservation
*and reflection* are `zsmul_lt_zsmul_iff_left`, because a rung is positive and
the surreals are a linearly ordered group.

The alternative, defining the map by recursion on the exponent and proving
additivity against that recursion, needs an induction over `ℤ × ℤ` at fixed
exponent which is well founded in neither direction. Routing through the group
structure avoids it.

## What is proved

* `toSurreal_lt_iff`, `toSurreal_le_iff`, `toSurreal_inj` — order and equality
  both **preserved and reflected**, so nothing is lost and nothing invented;
* `toSurreal_zero`, `toSurreal_one`, `toSurreal_neg`, `toSurreal_add` — the
  structure maps, and `toSurrealHom` packaging them;
* `birthday_toSurreal_lt_omega0` — every represented dyadic has finite
  birthday. That is one inclusion of the characterisation the goal asks for;
  the converse belongs with the finite-birthday analysis and is not claimed
  here.

The type is written out as `Algebra.Order.Dyadic` rather than opened, because
the short name is ambiguous in this namespace.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open Mettapedia.SetTheory.OrdinalArithmetic

/-! ## The pair map -/

/-- `m / 2^k`, read into the surreals as an integer multiple of the `k`-th
rung. -/
noncomputable def ofPairSurreal (m : ℤ) (k : ℕ) : Surreal := m • ladder k

@[simp] theorem ofPairSurreal_zero_num (k : ℕ) : ofPairSurreal 0 k = 0 := by
  rw [ofPairSurreal, zero_zsmul]

theorem ofPairSurreal_one_zero : ofPairSurreal 1 0 = ofNat 1 := by
  rw [ofPairSurreal, one_zsmul, ladder_zero]

/-- A rung is twice the next, in the form the shift lemma consumes. -/
theorem ladder_two_zsmul (k : ℕ) : (2 : ℤ) • ladder (k + 1) = ladder k := by
  rw [two_zsmul, ← add_eq]
  exact ladder_add_self k

theorem ofPairSurreal_succ (m : ℤ) (k : ℕ) :
    ofPairSurreal (m * 2) (k + 1) = ofPairSurreal m k := by
  rw [ofPairSurreal, ofPairSurreal, ← ladder_add_self k, add_eq, zsmul_add,
    show m * 2 = m + m from by omega, add_zsmul]

/-- **Scaling numerator and exponent together changes nothing.**  This is
well-definedness of the pair view, and the only place the halving law is used
more than once. -/
theorem ofPairSurreal_shift (m : ℤ) (k : ℕ) :
    ∀ j : ℕ, ofPairSurreal (m * 2 ^ j) (k + j) = ofPairSurreal m k
  | 0 => by rw [pow_zero, mul_one, Nat.add_zero]
  | (j + 1) => by
      have hpow : m * 2 ^ (j + 1) = m * 2 ^ j * 2 := by ring
      have hidx : k + (j + 1) = (k + j) + 1 := by omega
      rw [hpow, hidx, ofPairSurreal_succ]
      exact ofPairSurreal_shift m k j

/-! ## Well-definedness -/

private theorem congr_of_le {m n : ℤ} {k j : ℕ} (hkj : k ≤ j)
    (h : (m : ℚ) / 2 ^ k = (n : ℚ) / 2 ^ j) :
    ofPairSurreal m k = ofPairSurreal n j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
  have hq : (m : ℚ) * 2 ^ (k + i) = (n : ℚ) * 2 ^ k :=
    (div_eq_div_iff (by positivity) (by positivity)).mp h
  have hz : m * 2 ^ (k + i) = n * 2 ^ k := by exact_mod_cast hq
  have hcancel : m * 2 ^ i = n := by
    refine mul_right_cancel₀ (b := (2 : ℤ) ^ k) (by positivity) ?_
    calc m * 2 ^ i * 2 ^ k = m * 2 ^ (k + i) := by ring
      _ = n * 2 ^ k := hz
  rw [← hcancel]
  exact (ofPairSurreal_shift m k i).symm

/-- **Two pairs naming the same rational name the same surreal.** -/
theorem ofPairSurreal_congr {m n : ℤ} {k j : ℕ}
    (h : (m : ℚ) / 2 ^ k = (n : ℚ) / 2 ^ j) :
    ofPairSurreal m k = ofPairSurreal n j := by
  rcases le_total k j with hkj | hjk
  · exact congr_of_le hkj h
  · exact (congr_of_le hjk h.symm).symm

/-! ## The map on dyadics -/

/-- The interpretation of an executable dyadic. -/
noncomputable def toSurreal (d : Algebra.Order.Dyadic) : Surreal :=
  ofPairSurreal (Classical.choose (Algebra.Order.Dyadic.val_isDyadic d))
    (Classical.choose (Classical.choose_spec (Algebra.Order.Dyadic.val_isDyadic d)))

theorem toSurreal_spec (d : Algebra.Order.Dyadic) {m : ℤ} {k : ℕ}
    (h : d.val = (m : ℚ) / 2 ^ k) : toSurreal d = ofPairSurreal m k := by
  have hchoice := Classical.choose_spec
    (Classical.choose_spec (Algebra.Order.Dyadic.val_isDyadic d))
  exact ofPairSurreal_congr (by rw [← hchoice, h])

@[simp] theorem toSurreal_ofPair (m : ℤ) (k : ℕ) :
    toSurreal (Algebra.Order.Dyadic.ofPair m k) = ofPairSurreal m k :=
  toSurreal_spec _ rfl

/-! ## A common exponent

Two dyadics can always be written over the same power of two, which turns
every statement below into a statement about numerators. -/

theorem exists_common_pair (d e : Algebra.Order.Dyadic) :
    ∃ (M N : ℤ) (K : ℕ), d = Algebra.Order.Dyadic.ofPair M K ∧
      e = Algebra.Order.Dyadic.ofPair N K := by
  obtain ⟨m, k, rfl⟩ := Algebra.Order.Dyadic.exists_pair d
  obtain ⟨n, j, rfl⟩ := Algebra.Order.Dyadic.exists_pair e
  refine ⟨m * 2 ^ j, n * 2 ^ k, k + j,
    Algebra.Order.Dyadic.ext ?_, Algebra.Order.Dyadic.ext ?_⟩ <;>
    rw [Algebra.Order.Dyadic.val_ofPair, Algebra.Order.Dyadic.val_ofPair] <;>
    push_cast <;> rw [pow_add] <;> field_simp

/-! ## Order, preserved and reflected -/

theorem ofPairSurreal_lt_iff {m n : ℤ} {k : ℕ} :
    ofPairSurreal m k < ofPairSurreal n k ↔ m < n :=
  zsmul_lt_zsmul_iff_left (ladder_pos k)

theorem ofPair_lt_iff {m n : ℤ} {k : ℕ} :
    Algebra.Order.Dyadic.ofPair m k < Algebra.Order.Dyadic.ofPair n k ↔ m < n := by
  rw [Algebra.Order.Dyadic.lt_iff, Algebra.Order.Dyadic.val_ofPair,
    Algebra.Order.Dyadic.val_ofPair, div_lt_div_iff_of_pos_right (by positivity)]
  exact Int.cast_lt

/-- **The interpretation preserves and reflects the order.** -/
theorem toSurreal_lt_iff {d e : Algebra.Order.Dyadic} :
    toSurreal d < toSurreal e ↔ d < e := by
  obtain ⟨M, N, K, rfl, rfl⟩ := exists_common_pair d e
  rw [toSurreal_ofPair, toSurreal_ofPair, ofPairSurreal_lt_iff, ofPair_lt_iff]

theorem toSurreal_le_iff {d e : Algebra.Order.Dyadic} :
    toSurreal d ≤ toSurreal e ↔ d ≤ e :=
  ⟨fun h => not_lt.mp fun hlt => absurd (toSurreal_lt_iff.mpr hlt) (not_lt.mpr h),
   fun h => not_lt.mp fun hlt => absurd (toSurreal_lt_iff.mp hlt) (not_lt.mpr h)⟩

/-- **And equality**, so no two distinct dyadics collide. -/
theorem toSurreal_inj {d e : Algebra.Order.Dyadic} :
    toSurreal d = toSurreal e ↔ d = e := by
  refine ⟨fun h => le_antisymm (toSurreal_le_iff.mp (le_of_eq h))
    (toSurreal_le_iff.mp (le_of_eq h.symm)), fun h => by rw [h]⟩

theorem toSurreal_injective : Function.Injective toSurreal :=
  fun _ _ h => toSurreal_inj.mp h

/-! ## The structure maps -/

@[simp] theorem toSurreal_zero : toSurreal 0 = 0 := by
  have h : (0 : Algebra.Order.Dyadic) = Algebra.Order.Dyadic.ofPair 0 0 :=
    Algebra.Order.Dyadic.ext (by rw [Algebra.Order.Dyadic.val_ofPair]; norm_num)
  rw [h, toSurreal_ofPair, ofPairSurreal_zero_num]

@[simp] theorem toSurreal_one : toSurreal 1 = ofNat 1 := by
  have h : (1 : Algebra.Order.Dyadic) = Algebra.Order.Dyadic.ofPair 1 0 :=
    Algebra.Order.Dyadic.ext (by rw [Algebra.Order.Dyadic.val_ofPair]; norm_num)
  rw [h, toSurreal_ofPair, ofPairSurreal_one_zero]

@[simp] theorem toSurreal_neg (d : Algebra.Order.Dyadic) :
    toSurreal (-d) = -(toSurreal d) := by
  obtain ⟨m, k, rfl⟩ := Algebra.Order.Dyadic.exists_pair d
  have h : -Algebra.Order.Dyadic.ofPair m k = Algebra.Order.Dyadic.ofPair (-m) k :=
    Algebra.Order.Dyadic.ext (by
      rw [Algebra.Order.Dyadic.val_neg, Algebra.Order.Dyadic.val_ofPair,
        Algebra.Order.Dyadic.val_ofPair]
      push_cast; ring)
  rw [h, toSurreal_ofPair, toSurreal_ofPair, ofPairSurreal, ofPairSurreal, neg_zsmul]

/-- **Addition is preserved.**  With a common exponent both sides are integer
multiples of one rung, and `add_zsmul` finishes it. -/
@[simp] theorem toSurreal_add (d e : Algebra.Order.Dyadic) :
    toSurreal (d + e) = toSurreal d + toSurreal e := by
  obtain ⟨M, N, K, rfl, rfl⟩ := exists_common_pair d e
  have hsum : Algebra.Order.Dyadic.ofPair M K + Algebra.Order.Dyadic.ofPair N K
      = Algebra.Order.Dyadic.ofPair (M + N) K :=
    Algebra.Order.Dyadic.ext (by
      rw [Algebra.Order.Dyadic.val_add, Algebra.Order.Dyadic.val_ofPair,
        Algebra.Order.Dyadic.val_ofPair, Algebra.Order.Dyadic.val_ofPair]
      push_cast; ring)
  rw [hsum, toSurreal_ofPair, toSurreal_ofPair, toSurreal_ofPair,
    ofPairSurreal, ofPairSurreal, ofPairSurreal, add_zsmul]

/-- The interpretation, packaged as a homomorphism of additive groups. -/
noncomputable def toSurrealHom : Algebra.Order.Dyadic →+ Surreal where
  toFun := toSurreal
  map_zero' := toSurreal_zero
  map_add' := toSurreal_add

@[simp] theorem toSurrealHom_apply (d : Algebra.Order.Dyadic) :
    toSurrealHom d = toSurreal d := rfl

/-- Differences are preserved by the additive homomorphism. -/
theorem toSurreal_sub (d e : Algebra.Order.Dyadic) :
    toSurreal (d - e) = toSurreal d - toSurreal e := map_sub toSurrealHom d e

/-! ## Represented dyadics are born early -/

theorem birthday_ladder (k : ℕ) : birthday (ladder k) = (k : Ordinal) + 1 := by
  rw [ladder_def, birthday_mk, dyadicPre_length]

theorem birthday_ladder_lt_omega0 (k : ℕ) : birthday (ladder k) < Ordinal.omega0 := by
  rw [birthday_ladder]
  calc (k : Ordinal) + 1 = ((k + 1 : ℕ) : Ordinal) := (Nat.cast_succ k).symm
    _ < Ordinal.omega0 := Ordinal.natCast_lt_omega0 _

/-- **Every represented dyadic has finite birthday.**

The induction is over the numerator, and each step adds or subtracts one rung;
the birthday bound from `AdditionBirthday.lean` turns that into a natural sum
of two finite ordinals, which stays finite. -/
theorem birthday_ofPairSurreal_lt_omega0 (m : ℤ) (k : ℕ) :
    birthday (ofPairSurreal m k) < Ordinal.omega0 := by
  have hl := birthday_ladder_lt_omega0 k
  rw [ofPairSurreal]
  refine Int.induction_on m ?_ ?_ ?_
  · rw [zero_zsmul]; exact Ordinal.omega0_pos
  · intro i ih
    rw [show ((i : ℤ) + 1) • ladder k = (i : ℤ) • ladder k + ladder k by
      rw [add_zsmul, one_zsmul]]
    exact lt_of_le_of_lt (birthday_add_le' _ _) (naturalAdd_lt_omega0 ih hl)
  · intro i ih
    rw [show (-(i : ℤ) - 1) • ladder k = (-(i : ℤ)) • ladder k - ladder k by
      rw [sub_zsmul, one_zsmul]; abel]
    exact lt_of_le_of_lt (birthday_sub_le _ _) (naturalAdd_lt_omega0 ih hl)

theorem birthday_toSurreal_lt_omega0 (d : Algebra.Order.Dyadic) :
    birthday (toSurreal d) < Ordinal.omega0 := by
  obtain ⟨m, k, rfl⟩ := Algebra.Order.Dyadic.exists_pair d
  rw [toSurreal_ofPair]
  exact birthday_ofPairSurreal_lt_omega0 m k

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ofPairSurreal_congr
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.toSurreal_lt_iff
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.toSurreal_add
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_toSurreal_lt_omega0
