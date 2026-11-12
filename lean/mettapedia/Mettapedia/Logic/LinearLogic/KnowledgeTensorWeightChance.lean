import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Random surroundings: survival, correlation and counting

A grade is a predicate on surroundings: the extra facts beside which a run still runs. Make the
surrounding random, every fact `a` present independently with probability `p a` (`chance`). The
measure of a grade (`measure`) is then the chance that the run survives being placed there.

* `sum_prod_compl`: the generating identity `∑_T (∏_{a ∈ T} f a) (∏_{a ∉ T} g a) = ∏_a (f a + g a)`.
* `measure_cylinder`: the chance that every fact of `S` is present and no fact of `F` is.
  * `measure_absence`: **survival of absence** is `∏_{a ∈ F} (1 - p a)`.
  * `measure_presence`: presence of `S` is `∏_{a ∈ S} p a`.
  * `measure_presence_absence`: if `S` and `F` meet the chance is `0`, otherwise the product.
* `absence_conjunction`: the conjunction of two absence grades is the absence grade of the
  union of their forbidden sets.
* `absence_correlation`: `μ(G₁ ∧ G₂) · ∏_{F₁ ∩ F₂} (1 - p) = μ(G₁) · μ(G₂)`, in every
  commutative ring.
* `harris_absence`, `harris_absence_eq_iff`: absence grades are positively correlated, with
  equality exactly when the overlap of the forbidden sets has probability zero or some forbidden
  fact is certain. `harris_absence_eq_iff_of_uncertain`: without certain facts, equality is
  disjointness on the facts of positive probability.
* `write_read`, `write_read_eq_iff`: presence of the facts one part writes and absence of the
  facts another part forbids are negatively correlated, and independent exactly when the two sets
  are disjoint (for probabilities strictly between `0` and `1`).
* `measure_count`: the chance of exactly `n` forbidden facts is the coefficient of `X ^ n` in
  `∏_{a ∈ F} (1 - p a + p a X)`.
* Controls: strict correlation, equality on an overlap of probability zero, the certain fact that
  forces equality (`a_certain_fact_forces_equality`), counting grades that are neither up- nor
  down-closed (`counting_is_not_monotone`) and negatively correlated
  (`counting_is_negatively_correlated`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight

open Finset

universe u v

variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ## Surroundings and their chance -/

section Ring

variable {R : Type v} [CommRing R]

/-- **The chance of a surrounding**: every fact is present independently, with probability `p a`. -/
def chance (p : α → R) (T : Finset α) : R := (∏ a ∈ T, p a) * ∏ a ∈ Tᶜ, (1 - p a)

open Classical in
/-- **The measure of a grade**: the total chance of the surroundings it accepts. -/
noncomputable def measure (p : α → R) (G : Finset α → Prop) : R :=
  ∑ T ∈ (univ : Finset (Finset α)).filter G, chance p T

/-- **The generating identity of independent surroundings.** -/
theorem sum_prod_compl (f g : α → R) :
    ∑ T : Finset α, (∏ a ∈ T, f a) * ∏ a ∈ Tᶜ, g a = ∏ a, (f a + g a) := by
  rw [prod_add, powerset_univ]
  refine sum_congr rfl fun T _ => ?_
  rw [compl_eq_univ_sdiff]

/-- Grades that accept the same surroundings have the same measure. -/
theorem measure_congr (p : α → R) {G H : Finset α → Prop} (same : ∀ T, G T ↔ H T) :
    measure p G = measure p H := by
  have equal : G = H := funext fun T => propext (same T)
  rw [equal]

/-- The total chance is one. -/
theorem measure_true (p : α → R) : measure p (fun _ => True) = 1 := by
  unfold measure
  rw [filter_true]
  unfold chance
  rw [sum_prod_compl]
  simp

/-- An impossible grade has measure zero. -/
theorem measure_false (p : α → R) : measure p (fun _ => False) = 0 := by
  unfold measure
  rw [filter_false, sum_empty]

/-- **Every fact of `S` present and no fact of `F`.** -/
theorem measure_cylinder (p : α → R) (S F : Finset α) :
    measure p (fun T => S ⊆ T ∧ Disjoint T F) =
      ∏ a, ((if a ∈ F then 0 else p a) + (if a ∈ S then 0 else 1 - p a)) := by
  rw [← sum_prod_compl]
  unfold measure
  rw [sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with accepted
  · obtain ⟨sub, apart⟩ := accepted
    unfold chance
    congr 1
    · exact prod_congr rfl fun a member => (if_neg (disjoint_left.mp apart member)).symm
    · exact prod_congr rfl fun a member =>
        (if_neg fun inS => (mem_compl.mp member) (sub inS)).symm
  · rcases not_and_or.mp accepted with notSub | notApart
    · obtain ⟨a, inS, notT⟩ := not_subset.mp notSub
      have zero : ∏ x ∈ Tᶜ, (if x ∈ S then (0 : R) else 1 - p x) = 0 :=
        prod_eq_zero (mem_compl.mpr notT) (if_pos inS)
      rw [zero, mul_zero]
    · obtain ⟨a, inT, inF⟩ := not_disjoint_iff.mp notApart
      have zero : ∏ x ∈ T, (if x ∈ F then (0 : R) else p x) = 0 :=
        prod_eq_zero inT (if_pos inF)
      rw [zero, zero_mul]

/-- **Survival of absence.** The chance that no fact of `F` is present is `∏_{a ∈ F} (1 - p a)`. -/
theorem measure_absence (p : α → R) (F : Finset α) :
    measure p (fun T => Disjoint T F) = ∏ a ∈ F, (1 - p a) := by
  rw [measure_congr p (G := fun T => Disjoint T F) (H := fun T => ∅ ⊆ T ∧ Disjoint T F)
    (fun T => ⟨fun apart => ⟨empty_subset T, apart⟩, And.right⟩), measure_cylinder]
  have rhs : ∏ a ∈ F, (1 - p a) = ∏ a, (if a ∈ F then 1 - p a else 1) := by
    rw [prod_ite_mem, univ_inter]
  rw [rhs]
  refine prod_congr rfl fun a _ => ?_
  by_cases inF : a ∈ F <;> simp [inF]

/-- **Presence.** The chance that every fact of `S` is present is `∏_{a ∈ S} p a`. -/
theorem measure_presence (p : α → R) (S : Finset α) :
    measure p (fun T => S ⊆ T) = ∏ a ∈ S, p a := by
  rw [measure_congr p (G := fun T => S ⊆ T) (H := fun T => S ⊆ T ∧ Disjoint T ∅)
    (fun T => ⟨fun sub => ⟨sub, disjoint_empty_right T⟩, And.left⟩), measure_cylinder]
  have rhs : ∏ a ∈ S, p a = ∏ a, (if a ∈ S then p a else 1) := by
    rw [prod_ite_mem, univ_inter]
  rw [rhs]
  refine prod_congr rfl fun a _ => ?_
  by_cases inS : a ∈ S <;> simp [inS]

/-- **Presence of `S` and absence of `F`**: zero when they meet, the product when they do not. -/
theorem measure_presence_absence (p : α → R) (S F : Finset α) :
    measure p (fun T => S ⊆ T ∧ Disjoint T F) =
      if Disjoint S F then (∏ a ∈ S, p a) * ∏ a ∈ F, (1 - p a) else 0 := by
  rw [measure_cylinder]
  split_ifs with apart
  · have left : ∏ a ∈ S, p a = ∏ a, (if a ∈ S then p a else 1) := by rw [prod_ite_mem, univ_inter]
    have right : ∏ a ∈ F, (1 - p a) = ∏ a, (if a ∈ F then 1 - p a else 1) := by
      rw [prod_ite_mem, univ_inter]
    rw [left, right, ← prod_mul_distrib]
    refine prod_congr rfl fun a _ => ?_
    by_cases inS : a ∈ S
    · have notF : a ∉ F := disjoint_left.mp apart inS
      simp [inS, notF]
    · by_cases inF : a ∈ F <;> simp [inS, inF]
  · obtain ⟨a, inS, inF⟩ := not_disjoint_iff.mp apart
    exact prod_eq_zero (mem_univ a) (by simp [inS, inF])

/-- **The forbidden set of a conjunction is the union.** -/
theorem absence_conjunction (p : α → R) (F₁ F₂ : Finset α) :
    measure p (fun T => Disjoint T F₁ ∧ Disjoint T F₂) = ∏ a ∈ F₁ ∪ F₂, (1 - p a) := by
  rw [measure_congr p (G := fun T => Disjoint T F₁ ∧ Disjoint T F₂)
    (H := fun T => Disjoint T (F₁ ∪ F₂)) (fun T => disjoint_union_right.symm), measure_absence]

/-- **The correlation identity of absence grades**, in every commutative ring. -/
theorem absence_correlation (p : α → R) (F₁ F₂ : Finset α) :
    measure p (fun T => Disjoint T F₁ ∧ Disjoint T F₂) * ∏ a ∈ F₁ ∩ F₂, (1 - p a) =
      measure p (fun T => Disjoint T F₁) * measure p (fun T => Disjoint T F₂) := by
  rw [absence_conjunction, measure_absence, measure_absence, prod_union_inter]

open Polynomial in
/-- The chance of exactly `n` forbidden facts, as a polynomial coefficient: one factor
`1 - p a + p a X` per fact of `F`. -/
theorem measure_count (p : α → R) (F : Finset α) (n : ℕ) :
    measure p (fun T => (T ∩ F).card = n) =
      (∏ a ∈ F, (C (1 - p a) + C (p a) * X)).coeff n := by
  have generating := sum_prod_compl (R := R[X]) (fun a => C (p a) * (if a ∈ F then X else 1))
    (fun a => C (1 - p a))
  have term : ∀ T : Finset α, (∏ a ∈ T, C (p a) * (if a ∈ F then X else 1)) *
      ∏ a ∈ Tᶜ, C (1 - p a) = C (chance p T) * X ^ (T ∩ F).card := by
    intro T
    rw [prod_mul_distrib, prod_ite_mem, prod_const, ← map_prod, ← map_prod, chance, map_mul]
    ring
  have factor : ∏ a, (C (p a) * (if a ∈ F then X else 1) + C (1 - p a)) =
      ∏ a ∈ F, (C (1 - p a) + C (p a) * X) := by
    have rhs : ∏ a ∈ F, (C (1 - p a) + C (p a) * X) =
        ∏ a, (if a ∈ F then C (1 - p a) + C (p a) * X else 1) := by
      rw [prod_ite_mem, univ_inter]
    rw [rhs]
    refine prod_congr rfl fun a _ => ?_
    split_ifs
    · ring
    · rw [mul_one, C_sub, C_1]
      ring
  have coefficients : measure p (fun T => (T ∩ F).card = n) =
      ∑ T : Finset α, (C (chance p T) * X ^ (T ∩ F).card).coeff n := by
    unfold measure
    rw [sum_filter]
    refine sum_congr rfl fun T _ => ?_
    rw [coeff_C_mul_X_pow]
    split_ifs <;> first | rfl | (exfalso; omega)
  have expanded : ∑ T : Finset α, C (chance p T) * X ^ (T ∩ F).card =
      ∏ a, (C (p a) * (if a ∈ F then X else 1) + C (1 - p a)) := by
    rw [← generating]
    exact sum_congr rfl fun T _ => (term T).symm
  rw [coefficients, ← finsetSum_coeff, expanded, factor]

end Ring

/-! ## Probabilities: correlation inequalities -/

section Real

omit [Fintype α] in
/-- Products of complements of probabilities are one exactly when every probability is zero. -/
theorem prod_one_sub_eq_one_iff (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (s : Finset α) : ∏ a ∈ s, (1 - p a) = 1 ↔ ∀ a ∈ s, p a = 0 := by
  constructor
  · intro one a member
    by_contra positive
    have lower : 0 < p a := lt_of_le_of_ne (probability a).1 (Ne.symm positive)
    have rest : ∏ x ∈ s.erase a, (1 - p x) ≤ 1 :=
      prod_le_one (fun x _ => sub_nonneg.mpr (probability x).2)
        (fun x _ => by linarith [(probability x).1])
    have split := mul_prod_erase s (fun x => 1 - p x) member
    have bound : ∏ x ∈ s, (1 - p x) ≤ 1 - p a := by
      rw [← split]
      exact mul_le_of_le_one_right (sub_nonneg.mpr (probability a).2) rest
    linarith
  · intro zero
    exact prod_eq_one fun a member => by rw [zero a member, sub_zero]

omit [Fintype α] [DecidableEq α] in
/-- Products of complements vanish exactly when some fact is certain. -/
theorem prod_one_sub_eq_zero_iff (p : α → ℝ) (s : Finset α) :
    ∏ a ∈ s, (1 - p a) = 0 ↔ ∃ a ∈ s, p a = 1 := by
  rw [prod_eq_zero_iff]
  constructor
  · rintro ⟨a, member, zero⟩
    exact ⟨a, member, by linarith⟩
  · rintro ⟨a, member, one⟩
    exact ⟨a, member, by linarith⟩

/-- **Absence grades are positively correlated** (Harris). -/
theorem harris_absence (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (F₁ F₂ : Finset α) :
    measure p (fun T => Disjoint T F₁) * measure p (fun T => Disjoint T F₂) ≤
      measure p (fun T => Disjoint T F₁ ∧ Disjoint T F₂) := by
  rw [← absence_correlation, absence_conjunction]
  have nonneg : 0 ≤ ∏ a ∈ F₁ ∪ F₂, (1 - p a) :=
    prod_nonneg fun a _ => sub_nonneg.mpr (probability a).2
  have atMostOne : ∏ a ∈ F₁ ∩ F₂, (1 - p a) ≤ 1 :=
    prod_le_one (fun a _ => sub_nonneg.mpr (probability a).2)
      (fun a _ => by linarith [(probability a).1])
  calc (∏ a ∈ F₁ ∪ F₂, (1 - p a)) * ∏ a ∈ F₁ ∩ F₂, (1 - p a)
      ≤ (∏ a ∈ F₁ ∪ F₂, (1 - p a)) * 1 := mul_le_mul_of_nonneg_left atMostOne nonneg
    _ = ∏ a ∈ F₁ ∪ F₂, (1 - p a) := mul_one _

/-- **Equality in the correlation of absence grades**: the overlap of the forbidden sets has
probability zero, or some forbidden fact is certain. -/
theorem harris_absence_eq_iff (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (F₁ F₂ : Finset α) :
    measure p (fun T => Disjoint T F₁) * measure p (fun T => Disjoint T F₂) =
        measure p (fun T => Disjoint T F₁ ∧ Disjoint T F₂) ↔
      (∀ a ∈ F₁ ∩ F₂, p a = 0) ∨ ∃ a ∈ F₁ ∪ F₂, p a = 1 := by
  rw [← absence_correlation, absence_conjunction, ← prod_one_sub_eq_one_iff p probability (F₁ ∩ F₂),
    ← prod_one_sub_eq_zero_iff p (F₁ ∪ F₂)]
  constructor
  · intro same
    by_cases zero : ∏ a ∈ F₁ ∪ F₂, (1 - p a) = 0
    · exact Or.inr zero
    · exact Or.inl (mul_left_cancel₀ zero (same.trans (mul_one _).symm))
  · rintro (one | zero)
    · rw [one, mul_one]
    · rw [zero, zero_mul]

/-- **Without certain facts, absence grades are independent exactly when their forbidden sets are
disjoint on the facts of positive probability.** -/
theorem harris_absence_eq_iff_of_uncertain (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (uncertain : ∀ a, p a < 1) (F₁ F₂ : Finset α) :
    measure p (fun T => Disjoint T F₁) * measure p (fun T => Disjoint T F₂) =
        measure p (fun T => Disjoint T F₁ ∧ Disjoint T F₂) ↔
      ∀ a ∈ F₁ ∩ F₂, p a = 0 := by
  rw [harris_absence_eq_iff p probability]
  constructor
  · rintro (none | ⟨a, _, certain⟩)
    · exact none
    · exact absurd certain (uncertain a).ne
  · exact Or.inl

/-- **What one part writes and what another forbids are negatively correlated.** -/
theorem write_read (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (S F : Finset α) :
    measure p (fun T => S ⊆ T ∧ Disjoint T F) ≤
      measure p (fun T => S ⊆ T) * measure p (fun T => Disjoint T F) := by
  rw [measure_presence_absence, measure_presence, measure_absence]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (prod_nonneg fun a _ => (probability a).1)
      (prod_nonneg fun a _ => sub_nonneg.mpr (probability a).2)

/-- **They are independent exactly when the written facts avoid the forbidden ones**, for
probabilities strictly between `0` and `1`. -/
theorem write_read_eq_iff (p : α → ℝ) (positive : ∀ a, 0 < p a) (uncertain : ∀ a, p a < 1)
    (S F : Finset α) :
    measure p (fun T => S ⊆ T ∧ Disjoint T F) =
        measure p (fun T => S ⊆ T) * measure p (fun T => Disjoint T F) ↔ Disjoint S F := by
  rw [measure_presence_absence, measure_presence, measure_absence]
  split_ifs with apart
  · exact ⟨fun _ => apart, fun _ => rfl⟩
  · refine ⟨fun zero => absurd zero.symm (mul_pos ?_ ?_).ne', fun disjoint => absurd disjoint apart⟩
    · exact prod_pos fun a _ => positive a
    · exact prod_pos fun a _ => sub_pos.mpr (uncertain a)

end Real

/-! ## Controls -/

namespace ChanceControls

/-- One fact of probability one half. -/
noncomputable def half : Bool → ℝ := fun _ => 1 / 2

theorem half_probability : ∀ a, 0 ≤ half a ∧ half a ≤ 1 := fun _ => by norm_num [half]

/-- **Strict positive correlation**: two grades forbidding the same fact of probability `1/2`. -/
theorem shared_fact_is_strictly_correlated :
    measure half (fun T => Disjoint T {true}) * measure half (fun T => Disjoint T {true}) <
      measure half (fun T => Disjoint T {true} ∧ Disjoint T {true}) := by
  rw [measure_absence, absence_conjunction, union_self, prod_singleton]
  norm_num [half]

/-- A fact of probability zero. -/
noncomputable def never : Bool → ℝ := fun b => if b then 0 else 1 / 2

theorem never_probability : ∀ a, 0 ≤ never a ∧ never a ≤ 1 := by
  intro a
  cases a <;> norm_num [never]

/-- **Equality on an overlap of probability zero.** -/
theorem overlap_of_probability_zero :
    measure never (fun T => Disjoint T {true}) * measure never (fun T => Disjoint T {true}) =
      measure never (fun T => Disjoint T {true} ∧ Disjoint T {true}) :=
  (harris_absence_eq_iff never never_probability {true} {true}).mpr
    (Or.inl fun a member => by
      rw [inter_self, mem_singleton] at member
      subst member
      simp [never])

/-- A certain fact `false` beside a fact `true` of probability one half. -/
noncomputable def certainBeside : Bool → ℝ := fun b => if b then 1 / 2 else 1

theorem certainBeside_probability : ∀ a, 0 ≤ certainBeside a ∧ certainBeside a ≤ 1 := by
  intro a
  cases a <;> norm_num [certainBeside]

/-- **A certain fact forces equality although the overlap has positive probability**: the
hypothesis of `harris_absence_eq_iff_of_uncertain` is needed. -/
theorem a_certain_fact_forces_equality :
    measure certainBeside (fun T => Disjoint T {false, true}) *
        measure certainBeside (fun T => Disjoint T {true}) =
      measure certainBeside (fun T => Disjoint T {false, true} ∧ Disjoint T {true}) ∧
    ¬ ∀ a ∈ ({false, true} : Finset Bool) ∩ {true}, certainBeside a = 0 := by
  refine ⟨(harris_absence_eq_iff certainBeside certainBeside_probability _ _).mpr
    (Or.inr ⟨false, by decide, by simp [certainBeside]⟩), fun none => ?_⟩
  have value := none true (by decide)
  norm_num [certainBeside] at value

/-- **Counting grades are neither down-closed nor up-closed.** -/
theorem counting_is_not_monotone :
    ¬ ((∅ : Finset Bool) ∩ {false, true}).card = 1 ∧ ({true} ∩ {false, true} : Finset Bool).card = 1 ∧
      ¬ (({false, true} : Finset Bool) ∩ {false, true}).card = 1 := by
  decide

/-- **Counting grades can be negatively correlated**: "exactly one" and "exactly none" of the
same fact. -/
theorem counting_is_negatively_correlated :
    measure half (fun T => (T ∩ {true}).card = 1 ∧ (T ∩ {true}).card = 0) <
      measure half (fun T => (T ∩ {true}).card = 1) * measure half (fun T => (T ∩ {true}).card = 0) := by
  have impossible :
      measure half (fun T => (T ∩ {true}).card = 1 ∧ (T ∩ {true}).card = 0) = 0 := by
    rw [measure_congr half (G := fun T => (T ∩ {true}).card = 1 ∧ (T ∩ {true}).card = 0)
      (H := fun _ => False)
      (fun T => ⟨fun both => by have first := both.1; have second := both.2; omega, False.elim⟩),
      measure_false]
  have one : measure half (fun T => (T ∩ {true}).card = 1) = 1 / 2 := by
    rw [measure_congr half (G := fun T => (T ∩ {true}).card = 1) (H := fun T => {true} ⊆ T)
      (fun T => ?_), measure_presence, prod_singleton]
    · rfl
    · rw [singleton_subset_iff]
      by_cases member : true ∈ T
      · simp [inter_singleton_of_mem member, member]
      · simp [inter_singleton_of_notMem member, member]
  have zero : measure half (fun T => (T ∩ {true}).card = 0) = 1 / 2 := by
    rw [measure_congr half (G := fun T => (T ∩ {true}).card = 0) (H := fun T => Disjoint T {true})
      (fun T => ?_), measure_absence, prod_singleton]
    · norm_num [half]
    · rw [card_eq_zero, ← disjoint_iff_inter_eq_empty]
  rw [impossible, one, zero]
  norm_num

end ChanceControls

end Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight
