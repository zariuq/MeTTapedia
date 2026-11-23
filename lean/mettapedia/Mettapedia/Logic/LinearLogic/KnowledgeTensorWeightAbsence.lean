import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mettapedia.GSLT.Logic.GradedSupport

/-!
# Absence needs a complement

A positive query of one pattern over a weighted store weighs the **sum over its matches**
(`presence`), and the sum is additive over disjoint parts of the store (`presence_union`).
Absence of the pattern is a conjunction over the facts, so it is multiplicative over disjoint parts
(`absence_union`): read through a complement `c` of single weights it is the **product of the
complements over the matches** (`absence`).

**When is absence the complement of presence?** Exactly when the complement turns the union in
question into the product (`UnionComplement`). For the semiring sum this is a `SumComplement`:
`c 0 = 1`, `c (x + y) = c x * c y`, `c 1 = 0`.

* `SumComplement.absence_eq`, `of_absence_eq`: absence of every store is the complement of its
  presence exactly for a complement of the sum.
* **Boolean** (`boolean`): negation is a complement of the sum, and it is injective.
* **Rings have none** (`ring_isEmpty`): `0 = 1 + (-1)` forces `1 = 0`. The amplitude algebras
  of interference (`ℤ`, `ℚ`, `ℂ`, ...) cannot express absence through their sum.
* **Weights that do not cancel have only the zero test** (`zeroTest`): it is a complement of the
  sum under `NoCancellation`. On `ℕ` (`nat_eq_zeroTest`, `nat_not_injective`), on the probability
  semiring `ℝ≥0` (`nnreal_crisp`), and on the tropical semiring (`tropical_crisp`) it is the only
  kind there is: absence of counts, of expected counts and of costs sees only whether there is a
  match. A complement of an idempotent sum takes idempotent values (`idempotent_values`).
* **Probability composes absence over the independent union.** `1 - x` turns
  `a + b - a * b` into the product (`independent`); it is injective, so absence keeps the
  weights. But the independent union is not a semiring sum: multiplication does not distribute
  over it (`independentUnion_not_distrib`), and absence is not a function of the sum over matches
  (`absence_not_function_of_presence`).
* **Monus.** `1 ∸ (a + b) = (1 ∸ a) * (1 ∸ b)` holds on `ℕ` (`nat_monus_law`), where the monus is the
  zero test, and fails on `ℝ≥0` (`nnreal_monus_fails`): there `1 ∸ sum` is the absence of
  *exclusive* events, and the product is the absence of independent ones.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight

open Mettapedia.GSLT.GradedSupport (NoCancellation OrBool)
open scoped NNReal

universe u v

/-! ## Presence and absence over a weighted store -/

section Stores

variable {K : Type u} [CommSemiring K] {α : Type v}

/-- **Presence**: a positive query of one pattern weighs the sum over its matches. -/
def presence (w : α → K) (matched : Finset α) : K := ∑ a ∈ matched, w a

/-- **Absence** read through a complement of single weights: the product over the matches. -/
def absence (c : K → K) (w : α → K) (matched : Finset α) : K := ∏ a ∈ matched, c (w a)

/-- Presence is additive over disjoint parts of a store. -/
theorem presence_union [DecidableEq α] (w : α → K) {Γ Δ : Finset α} (apart : Disjoint Γ Δ) :
    presence w (Γ ∪ Δ) = presence w Γ + presence w Δ :=
  Finset.sum_union apart

/-- Absence is multiplicative over disjoint parts of a store, for every complement. -/
theorem absence_union [DecidableEq α] (c : K → K) (w : α → K) {Γ Δ : Finset α}
    (apart : Disjoint Γ Δ) : absence c w (Γ ∪ Δ) = absence c w Γ * absence c w Δ :=
  Finset.prod_union apart

end Stores

/-! ## Complements of a union -/

/-- **A complement of a union**: certainty for the empty union, the product of the complements for
a union, impossibility for a certain event. -/
structure UnionComplement (K : Type u) [CommSemiring K] (union : K → K → K) where
  complement : K → K
  map_zero : complement 0 = 1
  map_union : ∀ x y, complement (union x y) = complement x * complement y
  map_one : complement 1 = 0

/-- **A complement of the sum**: a complement of the semiring's own union. -/
abbrev SumComplement (K : Type u) [CommSemiring K] := UnionComplement K (· + ·)

namespace SumComplement

variable {K : Type u} [CommSemiring K]

theorem map_add (C : SumComplement K) (x y : K) :
    C.complement (x + y) = C.complement x * C.complement y :=
  C.map_union x y

/-- **Absence is the complement of presence**, store by store, for a complement of the sum. -/
theorem absence_eq (C : SumComplement K) {α : Type v} [DecidableEq α] (w : α → K)
    (matched : Finset α) : absence C.complement w matched = C.complement (presence w matched) := by
  induction matched using Finset.induction_on with
  | empty => exact C.map_zero.symm
  | insert a s notMem ih =>
      unfold absence presence at *
      rw [Finset.prod_insert notMem, Finset.sum_insert notMem, ih]
      exact (C.map_add (w a) (∑ x ∈ s, w x)).symm

/-- Conversely, if absence is the complement of presence on the stores of two weighted facts,
the complement sends the empty sum to certainty and a sum to a product. -/
theorem of_absence_eq (c : K → K)
    (every : ∀ (w : Bool → K) (matched : Finset Bool), absence c w matched = c (presence w matched)) :
    c 0 = 1 ∧ ∀ x y, c (x + y) = c x * c y := by
  refine ⟨(every (fun _ => 0) ∅).symm, fun x y => ?_⟩
  have pair := every (fun b => if b then x else y) {true, false}
  unfold absence presence at pair
  rw [Finset.prod_pair (by decide), Finset.sum_pair (by decide)] at pair
  simpa using pair.symm

/-- A complement of the sum kills every positive multiple of one. -/
theorem natCast_succ (C : SumComplement K) (n : ℕ) : C.complement ((n + 1 : ℕ) : K) = 0 := by
  rw [Nat.cast_succ, C.map_add, C.map_one, mul_zero]

/-- **Rings have no complement of the sum.** -/
theorem ring_isEmpty {R : Type u} [CommRing R] [Nontrivial R] : IsEmpty (SumComplement R) := by
  refine ⟨fun C => (one_ne_zero : (1 : R) ≠ 0) ?_⟩
  have split := C.map_add 1 (-1)
  rw [add_neg_cancel, C.map_zero, C.map_one, zero_mul] at split
  exact split

/-- **The zero test** is a complement of the sum when weights do not cancel. -/
def zeroTest [DecidableEq K] (noCancel : NoCancellation K) : SumComplement K where
  complement x := if x = 0 then 1 else 0
  map_zero := if_pos rfl
  map_union x y := by
    show (if x + y = 0 then (1 : K) else 0) = (if x = 0 then (1 : K) else 0) * (if y = 0 then 1 else 0)
    by_cases hx : x = 0
    · subst hx
      simp
    · have sum : x + y ≠ 0 := fun zero => hx (noCancel.add_eq_zero x y zero)
      rw [if_neg sum, if_neg hx, zero_mul]
  map_one := if_neg noCancel.one_ne_zero

/-- **On `ℕ` the only complement of the sum is the zero test.** -/
theorem nat_eq_zeroTest (C : SumComplement ℕ) (n : ℕ) :
    C.complement n = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
      rw [if_pos rfl]
      exact C.map_zero
  | succ k =>
      rw [if_neg (Nat.succ_ne_zero k)]
      have killed := natCast_succ C k
      rwa [Nat.cast_id] at killed

/-- So absence of counts forgets the count: one match and two matches have the same absence. -/
theorem nat_not_injective (C : SumComplement ℕ) : ¬ Function.Injective C.complement := by
  intro injective
  have same : C.complement 1 = C.complement 2 := by
    rw [nat_eq_zeroTest C 1, nat_eq_zeroTest C 2]
    rfl
  exact absurd (injective same) (by decide)

/-- **On the probability semiring every complement of the sum is the zero test**: a positive
weight is a part of some multiple that exceeds one. -/
theorem nnreal_crisp (C : SumComplement ℝ≥0) {x : ℝ≥0} (positive : x ≠ 0) : C.complement x = 0 := by
  obtain ⟨n, big⟩ := Archimedean.arch (1 : ℝ≥0) (pos_iff_ne_zero.mpr positive)
  have power : ∀ k : ℕ, C.complement (k • x) = C.complement x ^ k := by
    intro k
    induction k with
    | zero => rw [zero_nsmul, pow_zero]; exact C.map_zero
    | succ k ih =>
        rw [succ_nsmul, pow_succ, ← ih]
        exact C.map_add (k • x) x
  have split : n • x = 1 + (n • x - 1) := (add_tsub_cancel_of_le big).symm
  have killed : C.complement (n • x) = 0 := by
    rw [split]
    exact (C.map_add 1 (n • x - 1)).trans (by rw [C.map_one, zero_mul])
  rw [power n] at killed
  have nonzero : n ≠ 0 := by
    rintro rfl
    rw [zero_nsmul] at big
    exact absurd big (by norm_num)
  exact (pow_eq_zero_iff nonzero).mp killed

/-- A complement of an idempotent sum takes idempotent values. -/
theorem idempotent_values (C : SumComplement K) (idempotent : ∀ x : K, x + x = x) (x : K) :
    C.complement x * C.complement x = C.complement x := by
  rw [← C.map_add x x, idempotent]

/-- **On the tropical semiring every complement of the sum is crisp**: its values are the
tropical one (cost `0`) and the tropical zero (cost `⊤`). -/
theorem tropical_crisp (C : SumComplement (Tropical (WithTop ℕ))) (x : Tropical (WithTop ℕ)) :
    C.complement x = 1 ∨ C.complement x = 0 := by
  have idempotent := idempotent_values C Tropical.add_self x
  have doubled : Tropical.untrop (C.complement x) + Tropical.untrop (C.complement x) =
      Tropical.untrop (C.complement x) := by
    rw [← Tropical.untrop_mul, idempotent]
  have key : ∀ a : WithTop ℕ, a + a = a → a = 0 ∨ a = ⊤ := by
    intro a same
    induction a using WithTop.recTopCoe with
    | top => exact Or.inr rfl
    | coe n =>
        left
        have value : n + n = n := by exact_mod_cast same
        have zero : n = 0 := by omega
        rw [zero]
        rfl
  rcases key _ doubled with zero | top
  · left
    rw [← Tropical.trop_untrop (C.complement x), zero]
    rfl
  · right
    rw [← Tropical.trop_untrop (C.complement x), top]
    rfl

end SumComplement

/-! ## Instances -/

/-- **Negation is a complement of the Boolean sum.** -/
def boolean : SumComplement OrBool where
  complement b := ⟨!b.val⟩
  map_zero := rfl
  map_union x y := OrBool.ext' (Bool.not_or x.val y.val)
  map_one := rfl

/-- The Boolean complement is injective: absence loses nothing of a Boolean weight. -/
theorem boolean_injective : Function.Injective boolean.complement := by
  intro x y same
  rcases x with ⟨_ | _⟩ <;> rcases y with ⟨_ | _⟩
  all_goals first
    | rfl
    | exact absurd (congrArg OrBool.val same) (by decide)

/-- The zero test of the Boolean semiring is negation. -/
theorem boolean_zeroTest (b : OrBool) :
    (SumComplement.zeroTest OrBool.noCancellation).complement b = boolean.complement b := by
  rcases b with ⟨_ | _⟩ <;> rfl

section Probability

variable {R : Type u} [CommRing R]

/-- **The union of independent events**: `a + b - a * b`. -/
def independentUnion (a b : R) : R := a + b - a * b

/-- **Probability composes absence over the independent union**: `1 - x` is a complement of it. -/
def independent : UnionComplement R independentUnion where
  complement x := 1 - x
  map_zero := sub_zero 1
  map_union x y := by
    show 1 - (x + y - x * y) = (1 - x) * (1 - y)
    ring
  map_one := sub_self 1

/-- The probabilistic complement is injective: absence keeps the weights. -/
theorem independent_injective : Function.Injective (independent (R := R)).complement := by
  intro x y same
  have values : (1 : R) - x = 1 - y := same
  exact sub_right_injective values

/-- **The independent union is not a semiring sum**: multiplication does not distribute over it. -/
theorem independentUnion_not_distrib :
    (1 / 2 : ℚ) * independentUnion (1 / 2) (1 / 2) ≠
      independentUnion ((1 / 2) * (1 / 2)) ((1 / 2) * (1 / 2)) := by
  unfold independentUnion
  norm_num

/-- **Absence is not a function of the sum over matches.** Two stores of two facts whose match
probabilities have the same sum have different probabilities of absence. -/
theorem absence_not_function_of_presence :
    ¬ ∃ C : ℚ → ℚ, ∀ w : Bool → ℚ,
      absence (fun p => 1 - p) w {true, false} = C (presence w {true, false}) := by
  rintro ⟨C, every⟩
  have halves := every (fun _ => 1 / 2)
  have certain := every (fun b => if b then 1 else 0)
  unfold absence presence at halves certain
  rw [Finset.prod_pair (by decide), Finset.sum_pair (by decide)] at halves certain
  norm_num at halves certain
  linarith

end Probability

/-! ## Monus -/

/-- On `ℕ`, `1 ∸ (a + b) = (1 ∸ a) * (1 ∸ b)`: the monus is the zero test. -/
theorem nat_monus_law (a b : ℕ) : 1 - (a + b) = (1 - a) * (1 - b) := by
  have left : 1 - a = if a = 0 then 1 else 0 := by split_ifs <;> omega
  have right : 1 - b = if b = 0 then 1 else 0 := by split_ifs <;> omega
  have both : 1 - (a + b) = if a + b = 0 then 1 else 0 := by split_ifs <;> omega
  rw [left, right, both]
  split_ifs <;> omega

/-- On `ℝ≥0` the monus law fails: `1 ∸ (1/2 + 1/2) = 0`, while the product of the monuses is
`1/4`, the absence of two independent events of probability `1/2`. -/
theorem nnreal_monus_fails : (1 : ℝ≥0) - (1 / 2 + 1 / 2) ≠ (1 - 1 / 2) * (1 - 1 / 2) := by
  have half : (1 / 2 : ℝ≥0) + 1 / 2 = 1 := add_halves 1
  rw [half, tsub_self]
  have positive : (0 : ℝ≥0) < 1 - 1 / 2 := tsub_pos_of_lt one_half_lt_one
  exact (mul_pos positive positive).ne

end Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight
