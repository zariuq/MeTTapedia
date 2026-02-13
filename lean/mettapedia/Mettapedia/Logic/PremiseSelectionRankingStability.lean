import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mettapedia.Logic.PremiseSelectionOptimality
import Mettapedia.Logic.PremiseSelectionPUCalibration

/-!
# Ranking Stability Under Bounded Perturbations

This module adds margin-style ranking robustness lemmas for premise-selection
surrogate scores.

The guiding pattern is:
- if perturbations are uniformly bounded by `ε`
- and base pairwise margins exceed `2ε`
then pairwise order is preserved.

We also provide a Bayes-ranking transfer theorem under tie-equivariant perturbations.
-/

namespace Mettapedia.Logic.PremiseSelectionOptimality

open Mettapedia.Logic.PremiseSelection

/-- Additive perturbation wrapper for scores. -/
def perturbedScore {X : Type*} (s δ : X → ℝ) : X → ℝ :=
  fun x => s x + δ x

@[simp] theorem perturbedScore_apply {X : Type*} (s δ : X → ℝ) (x : X) :
    perturbedScore s δ x = s x + δ x := rfl

/-- Pairwise strict order is stable under bounded perturbations if the base margin
is larger than `2ε`. -/
theorem pairwise_lt_stable_of_margin
    {X : Type*} (s δ : X → ℝ) (x y : X) (ε : ℝ)
    (hmargin : s y - s x > 2 * ε)
    (hδx : |δ x| ≤ ε)
    (hδy : |δ y| ≤ ε) :
    perturbedScore s δ x < perturbedScore s δ y := by
  have hx := abs_le.mp hδx
  have hy := abs_le.mp hδy
  have hdelta_lower : -(2 * ε) ≤ δ y - δ x := by
    linarith
  have hsum_pos : (s y - s x) + (δ y - δ x) > 0 := by
    linarith
  have hdiff :
      (perturbedScore s δ y) - (perturbedScore s δ x) =
        (s y - s x) + (δ y - δ x) := by
    simp [perturbedScore]
    ring
  have hgt : (perturbedScore s δ y) - (perturbedScore s δ x) > 0 := by
    linarith [hsum_pos, hdiff]
  linarith

/-- Full Bayes-ranking stability under bounded perturbations, strict pairwise margin,
and tie-equivariant perturbations. -/
theorem bayesRanking_stable_of_margin_and_tie_equivariant
    {X : Type*} (η s δ : X → ℝ) (ε : ℝ)
    (hopt : BayesOptimalRanking η s)
    (hbound : ∀ x, |δ x| ≤ ε)
    (hmargin : ∀ x y, η x < η y → s y - s x > 2 * ε)
    (htie : ∀ x y, η x = η y → δ x = δ y) :
    BayesOptimalRanking η (perturbedScore s δ) := by
  intro x y
  by_cases hxy : η x = η y
  · have hsxy_le : s x ≤ s y := (hopt x y).2 (by simp [hxy])
    have hsyx_le : s y ≤ s x := (hopt y x).2 (by simp [hxy])
    have hsxy : s x = s y := le_antisymm hsxy_le hsyx_le
    have hdxy : δ x = δ y := htie x y hxy
    have hpeq : perturbedScore s δ x = perturbedScore s δ y := by
      simp [perturbedScore, hsxy, hdxy]
    constructor <;> intro _
    · simp [hxy]
    · exact le_of_eq hpeq
  · have hne : η x ≠ η y := hxy
    cases lt_or_gt_of_ne hne with
    | inl hlt =>
      have hxy' : perturbedScore s δ x < perturbedScore s δ y :=
        pairwise_lt_stable_of_margin s δ x y ε
          (hmargin x y hlt) (hbound x) (hbound y)
      constructor
      · intro _
        exact le_of_lt hlt
      · intro _
        exact le_of_lt hxy'
    | inr hgt =>
      have hyx' : perturbedScore s δ y < perturbedScore s δ x :=
        pairwise_lt_stable_of_margin s δ y x ε
          (hmargin y x hgt) (hbound y) (hbound x)
      constructor
      · intro hle
        exfalso
        exact (not_le_of_gt hyx') hle
      · intro hη
        exfalso
        exact (not_le_of_gt hgt) hη

/-- Specialized stability theorem for weak-negative adjustment:
if weak-negative perturbations are unit-bounded and margins exceed `2w`,
Bayes ranking is preserved. -/
theorem bayesRanking_stable_of_weakNegative_margin
    {X : Type*} (η s z : X → ℝ) (w : ℝ)
    (hopt : BayesOptimalRanking η s)
    (hw : 0 ≤ w)
    (hz_unit : ∀ x, |z x| ≤ 1)
    (hmargin : ∀ x y, η x < η y → s y - s x > 2 * w)
    (htie : ∀ x y, η x = η y → z x = z y) :
    BayesOptimalRanking η (weakNegativeAdjusted s z w) := by
  let δ : X → ℝ := fun x => -w * z x
  have hbound : ∀ x, |δ x| ≤ w := by
    intro x
    simpa [δ] using weakNegativeDelta_abs_le_weight z w hw hz_unit x
  have htieδ : ∀ x y, η x = η y → δ x = δ y := by
    intro x y hxy
    have hzxy : z x = z y := htie x y hxy
    simp [δ, hzxy]
  have hstable :=
    bayesRanking_stable_of_margin_and_tie_equivariant
      (η := η) (s := s) (δ := δ) (ε := w)
      hopt hbound hmargin htieδ
  -- `weakNegativeAdjusted` is exactly this perturbation form.
  simpa [weakNegativeAdjusted, perturbedScore, δ, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, mul_comm] using hstable

/-- Support-bias perturbation theorem:
adding `λ * u(x)` with `u(x) ∈ [0,1]` preserves Bayes ranking under margin `> 2λ`
and tie-equivariant support scores. -/
theorem bayesRanking_stable_of_support_bias_margin
    {X : Type*} (η s u : X → ℝ) (lam : ℝ)
    (hopt : BayesOptimalRanking η s)
    (hlam : 0 ≤ lam)
    (hu : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hmargin : ∀ x y, η x < η y → s y - s x > 2 * lam)
    (htie : ∀ x y, η x = η y → u x = u y) :
    BayesOptimalRanking η (fun x => s x + lam * u x) := by
  let δ : X → ℝ := fun x => lam * u x
  have hbound : ∀ x, |δ x| ≤ lam := by
    intro x
    have hux_nonneg : 0 ≤ u x := (hu x).1
    have hux_le_one : u x ≤ 1 := (hu x).2
    have hδ_nonneg : 0 ≤ δ x := by
      exact mul_nonneg hlam hux_nonneg
    calc
      |δ x| = δ x := abs_of_nonneg hδ_nonneg
      _ = lam * u x := rfl
      _ ≤ lam * 1 := by exact mul_le_mul_of_nonneg_left hux_le_one hlam
      _ = lam := by ring
  have htieδ : ∀ x y, η x = η y → δ x = δ y := by
    intro x y hxy
    simp [δ, htie x y hxy]
  have hstable :=
    bayesRanking_stable_of_margin_and_tie_equivariant
      (η := η) (s := s) (δ := δ) (ε := lam)
      hopt hbound hmargin htieδ
  simpa [perturbedScore, δ, add_comm, add_left_comm, add_assoc] using hstable

end Mettapedia.Logic.PremiseSelectionOptimality
