import Mettapedia.Logic.LinearLogic.KnowledgeTensorWeightChance
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Harris's inequality for every grade that shrinks

`harris_absence` computes the correlation of absence grades exactly. Here the inequality is
proved for **every** pair of down-closed grades, by the Fortuin–Kasteleyn–Ginibre inequality
(`fkg`, from the four functions theorem) on the order dual of the lattice of surroundings.

* `chance_eq_prod`: the chance of a surrounding is a product over all facts.
* `chance_mul_chance`: the product measure is log-modular,
  `chance S · chance T = chance (S ∩ T) · chance (S ∪ T)`.
* `harris_down_closed`: two grades that survive the removal of facts are positively correlated
  in every independent random surrounding.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight

open Finset

universe u v

variable {α : Type u} [Fintype α] [DecidableEq α]

section Ring

variable {R : Type v} [CommRing R]

/-- The chance of a surrounding, fact by fact. -/
theorem chance_eq_prod (p : α → R) (T : Finset α) :
    chance p T = ∏ a, (if a ∈ T then p a else 1 - p a) := by
  have split : ∀ a, (if a ∈ T then p a else 1 - p a) =
      (if a ∈ T then p a else 1) * (if a ∈ Tᶜ then 1 - p a else 1) := by
    intro a
    by_cases member : a ∈ T <;> simp [member]
  rw [prod_congr rfl (fun a _ => split a), prod_mul_distrib, prod_ite_mem, prod_ite_mem,
    univ_inter, univ_inter]
  rfl

/-- **The product measure is log-modular.** -/
theorem chance_mul_chance (p : α → R) (S T : Finset α) :
    chance p S * chance p T = chance p (S ∩ T) * chance p (S ∪ T) := by
  rw [chance_eq_prod, chance_eq_prod, chance_eq_prod, chance_eq_prod, ← prod_mul_distrib,
    ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  by_cases inS : a ∈ S <;> by_cases inT : a ∈ T <;> simp [inS, inT, mul_comm]

/-- The total chance, as a plain sum. -/
theorem sum_chance (p : α → R) : ∑ T : Finset α, chance p T = 1 := by
  unfold chance
  rw [sum_prod_compl]
  simp

/-- A measure as a sum of chances against an indicator. -/
theorem measure_eq_sum_indicator (p : α → R) (G : Finset α → Prop) [DecidablePred G] :
    measure p G = ∑ T : Finset α, chance p T * (if G T then 1 else 0) := by
  unfold measure
  rw [sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

end Ring

/-- **Harris's inequality for grades that shrink.** Two grades that survive the removal of facts
are positively correlated in every independent random surrounding. -/
theorem harris_down_closed (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (G H : Finset α → Prop) (shrinksG : ∀ S T, S ⊆ T → G T → G S)
    (shrinksH : ∀ S T, S ⊆ T → H T → H S) :
    measure p G * measure p H ≤ measure p (fun T => G T ∧ H T) := by
  classical
  let μ : (Finset α)ᵒᵈ → ℝ := fun T => chance p (OrderDual.ofDual T)
  let f : (Finset α)ᵒᵈ → ℝ := fun T => if G (OrderDual.ofDual T) then 1 else 0
  let g : (Finset α)ᵒᵈ → ℝ := fun T => if H (OrderDual.ofDual T) then 1 else 0
  have nonneg : 0 ≤ μ := fun T =>
    mul_nonneg (prod_nonneg fun a _ => (probability a).1)
      (prod_nonneg fun a _ => sub_nonneg.mpr (probability a).2)
  have fNonneg : 0 ≤ f := fun T => by
    show (0 : ℝ) ≤ if G (OrderDual.ofDual T) then 1 else 0
    split_ifs <;> norm_num
  have gNonneg : 0 ≤ g := fun T => by
    show (0 : ℝ) ≤ if H (OrderDual.ofDual T) then 1 else 0
    split_ifs <;> norm_num
  have fMono : Monotone f := by
    intro a b le
    show (if G (OrderDual.ofDual a) then (1 : ℝ) else 0) ≤ if G (OrderDual.ofDual b) then 1 else 0
    split_ifs with ha hb
    · exact le_rfl
    · exact absurd (shrinksG _ _ (OrderDual.ofDual_le_ofDual.mpr le) ha) hb
    · norm_num
    · exact le_rfl
  have gMono : Monotone g := by
    intro a b le
    show (if H (OrderDual.ofDual a) then (1 : ℝ) else 0) ≤ if H (OrderDual.ofDual b) then 1 else 0
    split_ifs with ha hb
    · exact le_rfl
    · exact absurd (shrinksH _ _ (OrderDual.ofDual_le_ofDual.mpr le) ha) hb
    · norm_num
    · exact le_rfl
  have modular : ∀ a b : (Finset α)ᵒᵈ, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b) := by
    intro a b
    apply le_of_eq
    show chance p (OrderDual.ofDual a) * chance p (OrderDual.ofDual b) =
      chance p (OrderDual.ofDual (a ⊓ b)) * chance p (OrderDual.ofDual (a ⊔ b))
    rw [_root_.ofDual_inf, _root_.ofDual_sup, sup_eq_union, inf_eq_inter, chance_mul_chance,
      mul_comm]
  have key := fkg (f := f) (g := g) (μ := μ) nonneg fNonneg gNonneg fMono gMono modular
  have sumF : ∑ a, μ a * f a = measure p G := by
    rw [measure_eq_sum_indicator]
    exact Fintype.sum_equiv OrderDual.ofDual _ _ fun _ => rfl
  have sumG : ∑ a, μ a * g a = measure p H := by
    rw [measure_eq_sum_indicator]
    exact Fintype.sum_equiv OrderDual.ofDual _ _ fun _ => rfl
  have sumBoth : ∑ a, μ a * (f a * g a) = measure p (fun T => G T ∧ H T) := by
    rw [measure_eq_sum_indicator]
    refine Fintype.sum_equiv OrderDual.ofDual _ _ fun T => ?_
    show chance p (OrderDual.ofDual T) *
        ((if G (OrderDual.ofDual T) then (1 : ℝ) else 0) *
          (if H (OrderDual.ofDual T) then 1 else 0)) =
      chance p (OrderDual.ofDual T) *
        (if G (OrderDual.ofDual T) ∧ H (OrderDual.ofDual T) then 1 else 0)
    split_ifs <;> simp_all
  have total : ∑ a, μ a = 1 := by
    rw [← sum_chance p]
    exact Fintype.sum_equiv OrderDual.ofDual _ _ fun _ => rfl
  rw [sumF, sumG, sumBoth, total, one_mul] at key
  exact key

omit [Fintype α] [DecidableEq α] in
/-- Absence grades shrink, so `harris_down_closed` contains `harris_absence`. -/
theorem absence_shrinks (F : Finset α) : ∀ S T : Finset α, S ⊆ T → Disjoint T F → Disjoint S F :=
  fun _ _ smaller apart => disjoint_of_subset_left smaller apart

/-- **Control: a counting grade does not shrink.** -/
theorem counting_does_not_shrink :
    ¬ ∀ S T : Finset Bool, S ⊆ T → (T ∩ {true}).card = 1 → (S ∩ {true}).card = 1 := by
  intro shrinks
  exact absurd (shrinks ∅ {true} (empty_subset _) (by decide)) (by decide)

end Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight
