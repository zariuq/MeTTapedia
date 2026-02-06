import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

/-!
# Markov de Finetti (Hard Direction) — Basic product bounds

Elementary inequalities on products of numbers in `[0,1]`. These lemmas are used
to compare “sampling without replacement” vs. “with replacement” probabilities
by reducing a difference of products to a sum of pointwise differences.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped BigOperators

namespace MarkovDeFinettiHardBounds

/-! ## Products of bounded reals -/

lemma prod_nonneg_of_bounds :
    ∀ (l : List ℝ), (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.prod
  | [], _ => by simp
  | x :: xs, h => by
      have hx : 0 ≤ x := h x (by simp)
      have hxs : 0 ≤ xs.prod := prod_nonneg_of_bounds xs (by
        intro y hy
        exact h y (by simp [hy]))
      simp [List.prod_cons, mul_nonneg hx hxs]

lemma prod_le_one_of_bounds :
    ∀ (l : List ℝ), (∀ x ∈ l, 0 ≤ x ∧ x ≤ 1) → l.prod ≤ 1
  | [], _ => by simp
  | x :: xs, h => by
      have hx : 0 ≤ x ∧ x ≤ 1 := h x (by simp)
      have hxs : xs.prod ≤ 1 :=
        prod_le_one_of_bounds xs (by
          intro y hy
          exact h y (by simp [hy]))
      have hxs_nonneg : 0 ≤ xs.prod :=
        prod_nonneg_of_bounds xs (by
          intro y hy
          exact (h y (by simp [hy])).1)
      -- x * xs.prod ≤ 1 * xs.prod ≤ 1
      calc
        (x * xs.prod) ≤ (1 * xs.prod) := by
          exact mul_le_mul_of_nonneg_right hx.2 hxs_nonneg
        _ = xs.prod := by ring
        _ ≤ 1 := hxs

lemma abs_prod_le_one_of_bounds (l : List ℝ)
    (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ 1) : |l.prod| ≤ 1 := by
  have hnonneg : 0 ≤ l.prod :=
    prod_nonneg_of_bounds l (by
      intro y hy
      exact (h y hy).1)
  have hle : l.prod ≤ 1 := prod_le_one_of_bounds l h
  simpa [abs_of_nonneg hnonneg] using hle

/-! ## Product difference bound -/

lemma abs_prod_diff_le_sum_abs
    (l : List (ℝ × ℝ))
    (h :
      ∀ x ∈ l,
        0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1) :
    |(l.map Prod.fst).prod - (l.map Prod.snd).prod| ≤
      (l.map (fun x => |x.1 - x.2|)).sum := by
  classical
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      -- set up bounds for head and tail
      have hx : 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1 := h x (by simp)
      have hxs :
          ∀ y ∈ xs, 0 ≤ y.1 ∧ y.1 ≤ 1 ∧ 0 ≤ y.2 ∧ y.2 ≤ 1 := by
        intro y hy
        exact h y (by simp [hy])
      -- abbreviate products
      have hP : |(xs.map Prod.fst).prod| ≤ 1 :=
        abs_prod_le_one_of_bounds (xs.map Prod.fst) (by
          intro y hy
          -- unpack membership in map
          rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
          exact ⟨(hxs z hz).1, (hxs z hz).2.1⟩)
      have hQ : |(xs.map Prod.snd).prod| ≤ 1 :=
        abs_prod_le_one_of_bounds (xs.map Prod.snd) (by
          intro y hy
          rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
          exact ⟨(hxs z hz).2.2.1, (hxs z hz).2.2.2⟩)
      -- main inequality
      have hsplit :
          |(x.1 * (xs.map Prod.fst).prod) - (x.2 * (xs.map Prod.snd).prod)| ≤
            |x.1| * |(xs.map Prod.fst).prod - (xs.map Prod.snd).prod| +
              |x.1 - x.2| * |(xs.map Prod.snd).prod| := by
        -- use triangle inequality
        have :
            (x.1 * (xs.map Prod.fst).prod) - (x.2 * (xs.map Prod.snd).prod) =
              x.1 * ((xs.map Prod.fst).prod - (xs.map Prod.snd).prod) +
                (x.1 - x.2) * (xs.map Prod.snd).prod := by
          ring
        -- apply |a+b| ≤ |a|+|b|
        calc
          |(x.1 * (xs.map Prod.fst).prod) - (x.2 * (xs.map Prod.snd).prod)| =
              |x.1 * ((xs.map Prod.fst).prod - (xs.map Prod.snd).prod) +
                (x.1 - x.2) * (xs.map Prod.snd).prod| := by
                simp [this]
          _ ≤ |x.1 * ((xs.map Prod.fst).prod - (xs.map Prod.snd).prod)| +
                |(x.1 - x.2) * (xs.map Prod.snd).prod| := by
                exact abs_add_le _ _
          _ = |x.1| * |(xs.map Prod.fst).prod - (xs.map Prod.snd).prod| +
                |x.1 - x.2| * |(xs.map Prod.snd).prod| := by
                simp [abs_mul]
      have hx1 : |x.1| ≤ 1 := by
        have hx1' : 0 ≤ x.1 := hx.1
        have hx1'' : x.1 ≤ 1 := hx.2.1
        simpa [abs_of_nonneg hx1'] using hx1''
      have hdiff : |(xs.map Prod.fst).prod - (xs.map Prod.snd).prod| ≤
            (xs.map (fun x => |x.1 - x.2|)).sum := ih hxs
      calc
        |((x :: xs).map Prod.fst).prod - ((x :: xs).map Prod.snd).prod| =
            |(x.1 * (xs.map Prod.fst).prod) - (x.2 * (xs.map Prod.snd).prod)| := by
              simp
        _ ≤ |x.1| * |(xs.map Prod.fst).prod - (xs.map Prod.snd).prod| +
              |x.1 - x.2| * |(xs.map Prod.snd).prod| := hsplit
        _ ≤ 1 * |(xs.map Prod.fst).prod - (xs.map Prod.snd).prod| +
              |x.1 - x.2| * 1 := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_right hx1 (abs_nonneg _)
              · exact mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
        _ = |(xs.map Prod.fst).prod - (xs.map Prod.snd).prod| + |x.1 - x.2| := by
              ring
        _ ≤ (xs.map (fun x => |x.1 - x.2|)).sum + |x.1 - x.2| := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right hdiff |x.1 - x.2|)
        _ = |x.1 - x.2| + (List.map (fun x => |x.1 - x.2|) xs).sum := by
              ac_rfl
        _ = (List.map (fun y => |y.1 - y.2|) (x :: xs)).sum := by
              simp

end MarkovDeFinettiHardBounds

end Mettapedia.Logic
