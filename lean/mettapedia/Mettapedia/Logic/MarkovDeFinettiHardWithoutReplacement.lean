import Mettapedia.Logic.MarkovDeFinettiHardApproxBounds
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Markov de Finetti (Hard Direction) — Without‑replacement product bounds

This file provides generic bounds for comparing two product probabilities
`∏ p_i` vs `∏ q_i` over a finite list.  These bounds are used in the
excursion‑based approximation step, where `p_i` are without‑replacement
step probabilities and `q_i` are with‑replacement (i.i.d.) probabilities.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped BigOperators

namespace MarkovDeFinettiHardWithoutReplacement

open MarkovDeFinettiHardBounds

variable {α : Type*}

/-- Repackage the pair‑list product bound for lists mapped by two functions. -/
lemma abs_prod_diff_le_sum_abs_map
    (xs : List α) (p q : α → ℝ)
    (h : ∀ a ∈ xs, 0 ≤ p a ∧ p a ≤ 1 ∧ 0 ≤ q a ∧ q a ≤ 1) :
    |(xs.map p).prod - (xs.map q).prod| ≤
      (xs.map (fun a => |p a - q a|)).sum := by
  -- turn the list into a list of pairs and apply the pair lemma
  have h' :
      ∀ x ∈ xs.map (fun a => (p a, q a)),
        0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact h a ha
  -- apply the pair lemma
  simpa using
    (MarkovDeFinettiHardBounds.abs_prod_diff_le_sum_abs
      (l := xs.map (fun a => (p a, q a))) h')

/-- If each step differs by at most `ε`, then the product differs by at most
`len * ε`. -/
lemma abs_prod_diff_le_length_mul_eps
    (xs : List α) (p q : α → ℝ) (ε : ℝ)
    (hbound : ∀ a ∈ xs, |p a - q a| ≤ ε)
    (h : ∀ a ∈ xs, 0 ≤ p a ∧ p a ≤ 1 ∧ 0 ≤ q a ∧ q a ≤ 1) :
    |(xs.map p).prod - (xs.map q).prod| ≤ (xs.length : ℝ) * ε := by
  -- bound each term by ε and sum by induction on the list
  have hsum :
      (xs.map (fun a => |p a - q a|)).sum ≤ (xs.length : ℝ) * ε := by
    induction xs with
    | nil =>
        simp
    | cons a xs ih =>
        have hbound_a : |p a - q a| ≤ ε := hbound a (by simp)
        have hbound_xs : ∀ b ∈ xs, |p b - q b| ≤ ε := by
          intro b hb
          exact hbound b (by simp [hb])
        have h_xs : ∀ b ∈ xs, 0 ≤ p b ∧ p b ≤ 1 ∧ 0 ≤ q b ∧ q b ≤ 1 := by
          intro b hb
          exact h b (by simp [hb])
        have ih' : (xs.map (fun b => |p b - q b|)).sum ≤ (xs.length : ℝ) * ε :=
          ih hbound_xs h_xs
        calc
          (List.map (fun b => |p b - q b|) (a :: xs)).sum
              = |p a - q a| + (xs.map (fun b => |p b - q b|)).sum := by simp
          _ ≤ ε + (xs.length : ℝ) * ε := by
              exact add_le_add hbound_a ih'
          _ = ((xs.length : ℝ) + 1) * ε := by
              ring
          _ = ((xs.length + 1 : ℕ) : ℝ) * ε := by
              norm_cast
          _ = ((a :: xs).length : ℝ) * ε := by
              simp
  have hprod := abs_prod_diff_le_sum_abs_map (xs := xs) (p := p) (q := q) h
  exact hprod.trans hsum

end MarkovDeFinettiHardWithoutReplacement

end Mettapedia.Logic
