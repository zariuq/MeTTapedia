import Mettapedia.MachineLearning.SearchGuidance.DistinctCoverage

/-!
# Sharpness, union, exclusivity, and portfolio allocation

This file supplies the sharpness and multi-arm parts of the budgeted-search
theory.  The sharpness fixture is a genuine inverse-temperature power family
over fixed scores.  The portfolio quantities are expectations expanded over
pairs of independently sampled finite words.
-/

noncomputable section

namespace Mettapedia.MachineLearning.SearchGuidance

open Finset BigOperators
open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

/-! ## T3: a fixed-ranking sharpness family with an interior optimum -/

/-- Fixed positive ranking scores.  Outcome `0` is the highest-ranked but
checker-rejected prefix; outcomes `1` and `2` are accepted, and outcome `3` is
the lowest-ranked rejected prefix. -/
def rankedBaseWeight (i : Fin 4) : ℝ :=
  if i.val = 0 then 4 else if i.val = 1 then 3 else if i.val = 2 then 3 else 1

theorem rankedBaseWeight_nonneg (i : Fin 4) : 0 ≤ rankedBaseWeight i := by
  fin_cases i <;> norm_num [rankedBaseWeight]

/-- Partition function for integer inverse temperature `β`. -/
def rankedPartition (β : ℕ) : ℝ :=
  ∑ i : Fin 4, rankedBaseWeight i ^ β

theorem rankedPartition_closedForm (β : ℕ) :
    rankedPartition β = 4 ^ β + 3 ^ β + 3 ^ β + 1 := by
  rw [rankedPartition, Fin.sum_univ_four]
  norm_num [rankedBaseWeight]

theorem rankedPartition_pos (β : ℕ) : 0 < rankedPartition β := by
  rw [rankedPartition_closedForm]
  positivity

/-- Power-softmax family `score^β / Zβ`; increasing `β` sharpens a fixed
ranking without changing its order. -/
def rankedPowerPrior (β : ℕ) : ProbSimplex 4 :=
  ⟨fun i => rankedBaseWeight i ^ β / rankedPartition β, by
    constructor
    · intro i
      exact div_nonneg (pow_nonneg (rankedBaseWeight_nonneg i) β)
        (rankedPartition_pos β).le
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt (rankedPartition_pos β))⟩

@[simp] theorem rankedPowerPrior_apply (β : ℕ) (i : Fin 4) :
    (rankedPowerPrior β : Fin 4 → ℝ) i =
      rankedBaseWeight i ^ β / rankedPartition β := rfl

def rankedAccepted : Finset (Fin 4) := {1, 2}

theorem sum_rankedAccepted (f : Fin 4 → ℝ) :
    ∑ i ∈ rankedAccepted, f i = f 1 + f 2 := by
  simp [rankedAccepted, show (1 : Fin 4) ≠ 2 by decide]

@[simp] theorem rankedPowerPrior_zero_one :
    (rankedPowerPrior 0 : Fin 4 → ℝ) 1 = 1 / 4 := by
  change rankedBaseWeight 1 ^ 0 / rankedPartition 0 = 1 / 4
  rw [rankedPartition_closedForm]
  norm_num [rankedBaseWeight]

@[simp] theorem rankedPowerPrior_zero_two :
    (rankedPowerPrior 0 : Fin 4 → ℝ) 2 = 1 / 4 := by
  change rankedBaseWeight 2 ^ 0 / rankedPartition 0 = 1 / 4
  rw [rankedPartition_closedForm]
  norm_num [rankedBaseWeight]

@[simp] theorem rankedPowerPrior_one_one :
    (rankedPowerPrior 1 : Fin 4 → ℝ) 1 = 3 / 11 := by
  change rankedBaseWeight 1 ^ 1 / rankedPartition 1 = 3 / 11
  rw [rankedPartition_closedForm]
  norm_num [rankedBaseWeight]

@[simp] theorem rankedPowerPrior_one_two :
    (rankedPowerPrior 1 : Fin 4 → ℝ) 2 = 3 / 11 := by
  change rankedBaseWeight 2 ^ 1 / rankedPartition 1 = 3 / 11
  rw [rankedPartition_closedForm]
  norm_num [rankedBaseWeight]

@[simp] theorem rankedPowerPrior_three_one :
    (rankedPowerPrior 3 : Fin 4 → ℝ) 1 = 27 / 119 := by
  change rankedBaseWeight 1 ^ 3 / rankedPartition 3 = 27 / 119
  rw [rankedPartition_closedForm]
  norm_num [rankedBaseWeight]

@[simp] theorem rankedPowerPrior_three_two :
    (rankedPowerPrior 3 : Fin 4 → ℝ) 2 = 27 / 119 := by
  change rankedBaseWeight 2 ^ 3 / rankedPartition 3 = 27 / 119
  rw [rankedPartition_closedForm]
  norm_num [rankedBaseWeight]

theorem rankedPowerPrior_hot_distinctCoverage :
    iidExpectedDistinctCoverage (rankedPowerPrior 0) 2 rankedAccepted = 7 / 8 := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow]
  rw [sum_rankedAccepted]
  norm_num [rankedPartition_closedForm, rankedBaseWeight]

theorem rankedPowerPrior_warm_distinctCoverage :
    iidExpectedDistinctCoverage (rankedPowerPrior 1) 2 rankedAccepted = 114 / 121 := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow]
  rw [sum_rankedAccepted]
  norm_num [rankedPartition_closedForm, rankedBaseWeight]

theorem rankedPowerPrior_cold_distinctCoverage :
    iidExpectedDistinctCoverage (rankedPowerPrior 3) 2 rankedAccepted =
      11394 / 14161 := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow]
  rw [sum_rankedAccepted]
  norm_num [rankedPartition_closedForm, rankedBaseWeight]

theorem rankedPowerPrior_warm_gt_hot :
    iidExpectedDistinctCoverage (rankedPowerPrior 0) 2 rankedAccepted <
      iidExpectedDistinctCoverage (rankedPowerPrior 1) 2 rankedAccepted := by
  rw [rankedPowerPrior_hot_distinctCoverage,
    rankedPowerPrior_warm_distinctCoverage]
  norm_num

theorem rankedPowerPrior_warm_gt_cold :
    iidExpectedDistinctCoverage (rankedPowerPrior 3) 2 rankedAccepted <
      iidExpectedDistinctCoverage (rankedPowerPrior 1) 2 rankedAccepted := by
  rw [rankedPowerPrior_cold_distinctCoverage,
    rankedPowerPrior_warm_distinctCoverage]
  norm_num

/-- T3 interior optimum fixture: sharpening from `β=0` to `β=1` helps by
removing mass from the lowest-ranked rejected prefix, while further sharpening
to `β=3` hurts because the highest-ranked rejected prefix dominates. -/
theorem sharpness_has_interior_optimum_fixture :
    iidExpectedDistinctCoverage (rankedPowerPrior 0) 2 rankedAccepted <
        iidExpectedDistinctCoverage (rankedPowerPrior 1) 2 rankedAccepted ∧
      iidExpectedDistinctCoverage (rankedPowerPrior 3) 2 rankedAccepted <
        iidExpectedDistinctCoverage (rankedPowerPrior 1) 2 rankedAccepted :=
  ⟨rankedPowerPrior_warm_gt_hot, rankedPowerPrior_warm_gt_cold⟩

theorem rankedPowerPrior_distinctCoverage_not_monotone :
    ¬ Monotone (fun β : ℕ =>
      iidExpectedDistinctCoverage (rankedPowerPrior β) 2 rankedAccepted) := by
  intro h
  have h13 := h (show 1 ≤ 3 by norm_num)
  exact (not_lt_of_ge h13) rankedPowerPrior_warm_gt_cold

theorem rankedPowerPrior_distinctCoverage_not_antitone :
    ¬ Antitone (fun β : ℕ =>
      iidExpectedDistinctCoverage (rankedPowerPrior β) 2 rankedAccepted) := by
  intro h
  have h01 := h (show 0 ≤ 1 by norm_num)
  exact (not_lt_of_ge h01) rankedPowerPrior_warm_gt_hot

/-- Shannon entropy of the finite action prior. -/
def categoricalEntropy {k : ℕ} (θ : ProbSimplex k) : ℝ :=
  -∑ i : Fin k,
    (θ : Fin k → ℝ) i * Real.log ((θ : Fin k → ℝ) i)

theorem low_high_prior_entropy_eq :
    categoricalEntropy lowTargetMassPrior =
      categoricalEntropy highTargetMassPrior := by
  unfold categoricalEntropy
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [lowTargetMassPrior, highTargetMassPrior,
    binaryPrior_otherMass, binaryPrior_targetMass]
  norm_num
  ring

/-- Equal action entropy does not determine gold mass or distinct verified
yield.  The strict order is inherited from the derived singleton coverage. -/
theorem equal_entropy_strictly_ordered_distinctYield
    (budget : ℕ) (hbudget : 0 < budget) :
    categoricalEntropy lowTargetMassPrior =
        categoricalEntropy highTargetMassPrior ∧
      iidExpectedDistinctCoverage lowTargetMassPrior budget {1} <
        iidExpectedDistinctCoverage highTargetMassPrior budget {1} := by
  constructor
  · exact low_high_prior_entropy_eq
  · rw [iidExpectedDistinctCoverage_singleton_eq,
      iidExpectedDistinctCoverage_singleton_eq]
    exact low_high_prior_atLeastOneSuccess_strict budget hbudget

/-! ## T4: two-arm union and exclusivity from the joint draw model -/

def twoArmUnionCoverage {k n₁ n₂ : ℕ}
    (xs : Fin n₁ → Fin k) (ys : Fin n₂ → Fin k)
    (accepted : Finset (Fin k)) : ℕ := by
  classical
  exact ∑ target ∈ accepted,
    if wordContains xs target ∨ wordContains ys target then 1 else 0

def twoArmSharedCoverage {k n₁ n₂ : ℕ}
    (xs : Fin n₁ → Fin k) (ys : Fin n₂ → Fin k)
    (accepted : Finset (Fin k)) : ℕ := by
  classical
  exact ∑ target ∈ accepted,
    if wordContains xs target ∧ wordContains ys target then 1 else 0

def twoArmExclusiveLeftCoverage {k n₁ n₂ : ℕ}
    (xs : Fin n₁ → Fin k) (ys : Fin n₂ → Fin k)
    (accepted : Finset (Fin k)) : ℕ := by
  classical
  exact ∑ target ∈ accepted,
    if wordContains xs target ∧ ¬ wordContains ys target then 1 else 0

def twoArmExclusiveRightCoverage {k n₁ n₂ : ℕ}
    (xs : Fin n₁ → Fin k) (ys : Fin n₂ → Fin k)
    (accepted : Finset (Fin k)) : ℕ := by
  classical
  exact ∑ target ∈ accepted,
    if ¬ wordContains xs target ∧ wordContains ys target then 1 else 0

theorem twoArmUnionCoverage_decomposition {k n₁ n₂ : ℕ}
    (xs : Fin n₁ → Fin k) (ys : Fin n₂ → Fin k)
    (accepted : Finset (Fin k)) :
    twoArmUnionCoverage xs ys accepted =
      twoArmSharedCoverage xs ys accepted +
        twoArmExclusiveLeftCoverage xs ys accepted +
          twoArmExclusiveRightCoverage xs ys accepted := by
  classical
  unfold twoArmUnionCoverage twoArmSharedCoverage
    twoArmExclusiveLeftCoverage twoArmExclusiveRightCoverage
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro target _htarget
  by_cases hx : wordContains xs target <;>
    by_cases hy : wordContains ys target <;> simp [hx, hy]

def twoArmExpectedUnionCoverage {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) : ℝ :=
  ∑ xs : Fin budget₁ → Fin k, ∑ ys : Fin budget₂ → Fin k,
    categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
      categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
        (twoArmUnionCoverage xs ys accepted : ℝ)

def twoArmExpectedSharedCoverage {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) : ℝ :=
  ∑ xs : Fin budget₁ → Fin k, ∑ ys : Fin budget₂ → Fin k,
    categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
      categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
        (twoArmSharedCoverage xs ys accepted : ℝ)

def twoArmExpectedExclusiveLeftCoverage {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) : ℝ :=
  ∑ xs : Fin budget₁ → Fin k, ∑ ys : Fin budget₂ → Fin k,
    categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
      categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
        (twoArmExclusiveLeftCoverage xs ys accepted : ℝ)

def twoArmExpectedExclusiveRightCoverage {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) : ℝ :=
  ∑ xs : Fin budget₁ → Fin k, ∑ ys : Fin budget₂ → Fin k,
    categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
      categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
        (twoArmExclusiveRightCoverage xs ys accepted : ℝ)

/-- Expected union is not a posited functional: it decomposes because every
sampled word pair decomposes pointwise into shared and exclusive coverage. -/
theorem twoArmExpectedUnionCoverage_decomposition {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) :
    twoArmExpectedUnionCoverage θ₁ budget₁ θ₂ budget₂ accepted =
      twoArmExpectedSharedCoverage θ₁ budget₁ θ₂ budget₂ accepted +
        twoArmExpectedExclusiveLeftCoverage θ₁ budget₁ θ₂ budget₂ accepted +
          twoArmExpectedExclusiveRightCoverage θ₁ budget₁ θ₂ budget₂ accepted := by
  classical
  unfold twoArmExpectedUnionCoverage twoArmExpectedSharedCoverage
    twoArmExpectedExclusiveLeftCoverage twoArmExpectedExclusiveRightCoverage
  calc
    (∑ xs, ∑ ys,
      categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
        categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
          (twoArmUnionCoverage xs ys accepted : ℝ)) =
      ∑ xs, ∑ ys,
        (categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (twoArmSharedCoverage xs ys accepted : ℝ) +
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (twoArmExclusiveLeftCoverage xs ys accepted : ℝ) +
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (twoArmExclusiveRightCoverage xs ys accepted : ℝ)) := by
        apply Finset.sum_congr rfl
        intro xs _hxs
        apply Finset.sum_congr rfl
        intro ys _hys
        rw [twoArmUnionCoverage_decomposition]
        push_cast
        ring
    _ = _ := by
      simp only [Finset.sum_add_distrib]

/-! ## Closed forms for shared and exclusive coverage -/

noncomputable def wordContainsIndicator {k n : ℕ}
    (xs : Fin n → Fin k) (target : Fin k) : ℝ := by
  classical
  exact if wordContains xs target then 1 else 0

noncomputable def wordAvoidsIndicator {k n : ℕ}
    (xs : Fin n → Fin k) (target : Fin k) : ℝ := by
  classical
  exact if ¬ wordContains xs target then 1 else 0

theorem expected_wordContains_indicator {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (target : Fin k) :
    (∑ xs : Fin budget → Fin k,
      categoricalProductPMF (θ : Fin k → ℝ) xs *
        wordContainsIndicator xs target) =
      iidAtLeastOneTargetSuccess θ budget {target} := by
  classical
  unfold iidAtLeastOneTargetSuccess wordContainsIndicator
  apply Finset.sum_congr rfl
  intro xs _hxs
  rw [wordContains_iff_hits_singleton]
  by_cases h : wordHitsTargetSet xs {target} <;> simp [h]

theorem expected_not_wordContains_indicator {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (target : Fin k) :
    (∑ xs : Fin budget → Fin k,
      categoricalProductPMF (θ : Fin k → ℝ) xs *
        wordAvoidsIndicator xs target) =
      iidNoTargetSuccess θ budget {target} := by
  classical
  unfold iidNoTargetSuccess wordAvoidsIndicator
  apply Finset.sum_congr rfl
  intro xs _hxs
  rw [wordContains_iff_hits_singleton]
  by_cases h : wordHitsTargetSet xs {target} <;> simp [h]

theorem twoArmExpectedSharedCoverage_eq_sum_products {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) :
    twoArmExpectedSharedCoverage θ₁ budget₁ θ₂ budget₂ accepted =
      ∑ target ∈ accepted,
        iidAtLeastOneTargetSuccess θ₁ budget₁ {target} *
          iidAtLeastOneTargetSuccess θ₂ budget₂ {target} := by
  classical
  unfold twoArmExpectedSharedCoverage twoArmSharedCoverage
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  calc
    (∑ xs, ∑ ys, ∑ target ∈ accepted,
      categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
        categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
          (if wordContains xs target ∧ wordContains ys target then 1 else 0)) =
        ∑ xs, ∑ target ∈ accepted, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if wordContains xs target ∧ wordContains ys target then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro xs _hxs
      rw [Finset.sum_comm]
    _ = ∑ target ∈ accepted, ∑ xs, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if wordContains xs target ∧ wordContains ys target then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ target ∈ accepted,
        iidAtLeastOneTargetSuccess θ₁ budget₁ {target} *
          iidAtLeastOneTargetSuccess θ₂ budget₂ {target} := by
      apply Finset.sum_congr rfl
      intro target _htarget
      calc
        (∑ xs, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if wordContains xs target ∧ wordContains ys target then 1 else 0)) =
          (∑ xs, categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
              wordContainsIndicator xs target) *
            (∑ ys, categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              wordContainsIndicator ys target) := by
                rw [Finset.sum_mul_sum]
                apply Finset.sum_congr rfl
                intro xs _hxs
                apply Finset.sum_congr rfl
                intro ys _hys
                unfold wordContainsIndicator
                by_cases hx : wordContains xs target <;>
                  by_cases hy : wordContains ys target <;> simp [hx, hy]
        _ = _ := by
          rw [expected_wordContains_indicator, expected_wordContains_indicator]

theorem twoArmExpectedExclusiveLeftCoverage_eq_sum_products {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) :
    twoArmExpectedExclusiveLeftCoverage θ₁ budget₁ θ₂ budget₂ accepted =
      ∑ target ∈ accepted,
        iidAtLeastOneTargetSuccess θ₁ budget₁ {target} *
          iidNoTargetSuccess θ₂ budget₂ {target} := by
  classical
  unfold twoArmExpectedExclusiveLeftCoverage twoArmExclusiveLeftCoverage
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  calc
    (∑ xs, ∑ ys, ∑ target ∈ accepted,
      categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
        categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
          (if wordContains xs target ∧ ¬ wordContains ys target then 1 else 0)) =
        ∑ xs, ∑ target ∈ accepted, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if wordContains xs target ∧ ¬ wordContains ys target then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro xs _hxs
      rw [Finset.sum_comm]
    _ = ∑ target ∈ accepted, ∑ xs, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if wordContains xs target ∧ ¬ wordContains ys target then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ target ∈ accepted,
        iidAtLeastOneTargetSuccess θ₁ budget₁ {target} *
          iidNoTargetSuccess θ₂ budget₂ {target} := by
      apply Finset.sum_congr rfl
      intro target _htarget
      calc
        (∑ xs, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if wordContains xs target ∧ ¬ wordContains ys target then 1 else 0)) =
          (∑ xs, categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
              wordContainsIndicator xs target) *
            (∑ ys, categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              wordAvoidsIndicator ys target) := by
                rw [Finset.sum_mul_sum]
                apply Finset.sum_congr rfl
                intro xs _hxs
                apply Finset.sum_congr rfl
                intro ys _hys
                unfold wordContainsIndicator wordAvoidsIndicator
                by_cases hx : wordContains xs target <;>
                  by_cases hy : wordContains ys target <;> simp [hx, hy]
        _ = _ := by
          rw [expected_wordContains_indicator, expected_not_wordContains_indicator]

theorem twoArmExpectedExclusiveRightCoverage_eq_sum_products {k : ℕ}
    (θ₁ : ProbSimplex k) (budget₁ : ℕ)
    (θ₂ : ProbSimplex k) (budget₂ : ℕ)
    (accepted : Finset (Fin k)) :
    twoArmExpectedExclusiveRightCoverage θ₁ budget₁ θ₂ budget₂ accepted =
      ∑ target ∈ accepted,
        iidNoTargetSuccess θ₁ budget₁ {target} *
          iidAtLeastOneTargetSuccess θ₂ budget₂ {target} := by
  classical
  unfold twoArmExpectedExclusiveRightCoverage twoArmExclusiveRightCoverage
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  calc
    (∑ xs, ∑ ys, ∑ target ∈ accepted,
      categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
        categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
          (if ¬ wordContains xs target ∧ wordContains ys target then 1 else 0)) =
        ∑ xs, ∑ target ∈ accepted, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if ¬ wordContains xs target ∧ wordContains ys target then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro xs _hxs
      rw [Finset.sum_comm]
    _ = ∑ target ∈ accepted, ∑ xs, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if ¬ wordContains xs target ∧ wordContains ys target then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ target ∈ accepted,
        iidNoTargetSuccess θ₁ budget₁ {target} *
          iidAtLeastOneTargetSuccess θ₂ budget₂ {target} := by
      apply Finset.sum_congr rfl
      intro target _htarget
      calc
        (∑ xs, ∑ ys,
          categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
            categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              (if ¬ wordContains xs target ∧ wordContains ys target then 1 else 0)) =
          (∑ xs, categoricalProductPMF (θ₁ : Fin k → ℝ) xs *
              wordAvoidsIndicator xs target) *
            (∑ ys, categoricalProductPMF (θ₂ : Fin k → ℝ) ys *
              wordContainsIndicator ys target) := by
                rw [Finset.sum_mul_sum]
                apply Finset.sum_congr rfl
                intro xs _hxs
                apply Finset.sum_congr rfl
                intro ys _hys
                unfold wordContainsIndicator wordAvoidsIndicator
                by_cases hx : wordContains xs target <;>
                  by_cases hy : wordContains ys target <;> simp [hx, hy]
        _ = _ := by
          rw [expected_not_wordContains_indicator, expected_wordContains_indicator]

/-- One-draw overlap of accepted priors; this is expected shared coverage at
budgets one and one. -/
def acceptedPriorOverlap {k : ℕ}
    (θ₁ θ₂ : ProbSimplex k) (accepted : Finset (Fin k)) : ℝ :=
  ∑ target ∈ accepted,
    (θ₁ : Fin k → ℝ) target * (θ₂ : Fin k → ℝ) target

theorem targetSetMass_eq_sum_accepted {k : ℕ}
    (θ : ProbSimplex k) (accepted : Finset (Fin k)) :
    targetSetMass θ accepted =
      ∑ target ∈ accepted, (θ : Fin k → ℝ) target := by
  classical
  simp [targetSetMass]

theorem twoArmExpectedSharedCoverage_one_one {k : ℕ}
    (θ₁ θ₂ : ProbSimplex k) (accepted : Finset (Fin k)) :
    twoArmExpectedSharedCoverage θ₁ 1 θ₂ 1 accepted =
      acceptedPriorOverlap θ₁ θ₂ accepted := by
  rw [twoArmExpectedSharedCoverage_eq_sum_products]
  unfold acceptedPriorOverlap
  apply Finset.sum_congr rfl
  intro target _htarget
  simp [iidAtLeastOne_singleton_eq]

/-- Sum of both arms' exclusive coverage at one draw each. -/
def totalOneDrawExclusivity {k : ℕ}
    (θ₁ θ₂ : ProbSimplex k) (accepted : Finset (Fin k)) : ℝ :=
  targetSetMass θ₁ accepted + targetSetMass θ₂ accepted -
    2 * acceptedPriorOverlap θ₁ θ₂ accepted

/-- The exclusivity functional is the sum of the two actual word-level
exclusive-coverage expectations, not a separately posited surrogate. -/
theorem twoArmExpectedTotalExclusive_one_one {k : ℕ}
    (θ₁ θ₂ : ProbSimplex k) (accepted : Finset (Fin k)) :
    twoArmExpectedExclusiveLeftCoverage θ₁ 1 θ₂ 1 accepted +
        twoArmExpectedExclusiveRightCoverage θ₁ 1 θ₂ 1 accepted =
      totalOneDrawExclusivity θ₁ θ₂ accepted := by
  rw [twoArmExpectedExclusiveLeftCoverage_eq_sum_products,
    twoArmExpectedExclusiveRightCoverage_eq_sum_products]
  simp_rw [iidAtLeastOne_singleton_eq,
    iidNoTargetSuccess_eq_pow, targetSetMass_singleton, pow_one]
  simp only [sub_sub_cancel]
  unfold totalOneDrawExclusivity acceptedPriorOverlap
  rw [targetSetMass_eq_sum_accepted, targetSetMass_eq_sum_accepted]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x ∈ accepted,
        ((θ₁ : Fin k → ℝ) x * (1 - (θ₂ : Fin k → ℝ) x) +
          (1 - (θ₁ : Fin k → ℝ) x) * (θ₂ : Fin k → ℝ) x)) =
        ∑ x ∈ accepted,
          ((θ₁ : Fin k → ℝ) x + (θ₂ : Fin k → ℝ) x -
            2 * ((θ₁ : Fin k → ℝ) x * (θ₂ : Fin k → ℝ) x)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- At fixed accepted mass, decorrelation (smaller overlap) strictly increases
the exact one-draw exclusivity functional. -/
theorem totalOneDrawExclusivity_strict_of_overlap_lt {k : ℕ}
    (θ₁ θ₂ φ₁ φ₂ : ProbSimplex k) (accepted : Finset (Fin k))
    (hmass₁ : targetSetMass θ₁ accepted = targetSetMass φ₁ accepted)
    (hmass₂ : targetSetMass θ₂ accepted = targetSetMass φ₂ accepted)
    (hoverlap : acceptedPriorOverlap φ₁ φ₂ accepted <
      acceptedPriorOverlap θ₁ θ₂ accepted) :
    totalOneDrawExclusivity θ₁ θ₂ accepted <
      totalOneDrawExclusivity φ₁ φ₂ accepted := by
  unfold totalOneDrawExclusivity
  rw [← hmass₁, ← hmass₂]
  linarith

/-- At fixed accepted mass, smaller overlap strictly increases the sum of the
two actual exclusive-coverage expectations. -/
theorem twoArmExpectedTotalExclusive_strict_of_overlap_lt {k : ℕ}
    (θ₁ θ₂ φ₁ φ₂ : ProbSimplex k) (accepted : Finset (Fin k))
    (hmass₁ : targetSetMass θ₁ accepted = targetSetMass φ₁ accepted)
    (hmass₂ : targetSetMass θ₂ accepted = targetSetMass φ₂ accepted)
    (hoverlap : acceptedPriorOverlap φ₁ φ₂ accepted <
      acceptedPriorOverlap θ₁ θ₂ accepted) :
    twoArmExpectedExclusiveLeftCoverage θ₁ 1 θ₂ 1 accepted +
        twoArmExpectedExclusiveRightCoverage θ₁ 1 θ₂ 1 accepted <
      twoArmExpectedExclusiveLeftCoverage φ₁ 1 φ₂ 1 accepted +
        twoArmExpectedExclusiveRightCoverage φ₁ 1 φ₂ 1 accepted := by
  rw [twoArmExpectedTotalExclusive_one_one,
    twoArmExpectedTotalExclusive_one_one]
  exact totalOneDrawExclusivity_strict_of_overlap_lt
    θ₁ θ₂ φ₁ φ₂ accepted hmass₁ hmass₂ hoverlap

/-! ## Fixed-split loss and computable allocation -/

def bestPortfolioPrior : ProbSimplex 3 :=
  ⟨fun i => if i.val = 0 then 1 / 2 else if i.val = 1 then 1 / 2 else 0, by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      norm_num⟩

def unproductivePortfolioPrior : ProbSimplex 3 :=
  ⟨fun i => if i.val = 2 then 1 else 0, by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      norm_num⟩

@[simp] theorem bestPortfolioPrior_zero :
    (bestPortfolioPrior : Fin 3 → ℝ) 0 = 1 / 2 := rfl

@[simp] theorem bestPortfolioPrior_one :
    (bestPortfolioPrior : Fin 3 → ℝ) 1 = 1 / 2 := rfl

@[simp] theorem unproductivePortfolioPrior_zero :
    (unproductivePortfolioPrior : Fin 3 → ℝ) 0 = 0 := rfl

@[simp] theorem unproductivePortfolioPrior_one :
    (unproductivePortfolioPrior : Fin 3 → ℝ) 1 = 0 := rfl

def portfolioAccepted : Finset (Fin 3) := {0, 1}

theorem sum_portfolioAccepted (f : Fin 3 → ℝ) :
    ∑ i ∈ portfolioAccepted, f i = f 0 + f 1 := by
  simp [portfolioAccepted, show (0 : Fin 3) ≠ 1 by decide]

theorem bestPortfolio_fullBudget_yield :
    iidExpectedDistinctCoverage bestPortfolioPrior 2 portfolioAccepted = 3 / 2 := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow]
  rw [sum_portfolioAccepted]
  norm_num

theorem fixedSplitPortfolio_yield :
    twoArmExpectedUnionCoverage bestPortfolioPrior 1
      unproductivePortfolioPrior 1 portfolioAccepted = 1 := by
  rw [twoArmExpectedUnionCoverage_decomposition,
    twoArmExpectedSharedCoverage_eq_sum_products,
    twoArmExpectedExclusiveLeftCoverage_eq_sum_products,
    twoArmExpectedExclusiveRightCoverage_eq_sum_products]
  norm_num [portfolioAccepted,
    iidAtLeastOne_singleton_eq, iidNoTargetSuccess_eq_pow,
    targetSetMass_singleton]

/-- Campaign-paradox fixture: an equal fixed split is strictly worse than
putting the entire fixed budget on the best arm. -/
theorem fixedSplit_strictly_loses_to_bestSingle :
    twoArmExpectedUnionCoverage bestPortfolioPrior 1
        unproductivePortfolioPrior 1 portfolioAccepted <
      iidExpectedDistinctCoverage bestPortfolioPrior 2 portfolioAccepted := by
  rw [fixedSplitPortfolio_yield, bestPortfolio_fullBudget_yield]
  norm_num

/-- The concrete computable allocation `(2,0)` evaluated in the same joint
word sampler has the best arm's full-budget yield. -/
theorem fullBestAllocation_yield :
    twoArmExpectedUnionCoverage bestPortfolioPrior 2
      unproductivePortfolioPrior 0 portfolioAccepted = 3 / 2 := by
  rw [twoArmExpectedUnionCoverage_decomposition,
    twoArmExpectedSharedCoverage_eq_sum_products,
    twoArmExpectedExclusiveLeftCoverage_eq_sum_products,
    twoArmExpectedExclusiveRightCoverage_eq_sum_products]
  norm_num [portfolioAccepted,
    iidAtLeastOne_singleton_eq, iidNoTargetSuccess_eq_pow,
    targetSetMass_singleton]

/-- The computable allocation `(2,0)` dominates both the losing split and the
best-single baseline (strictly for the split, by equality for the baseline). -/
theorem computableAllocation_dominates_split_and_single :
    twoArmExpectedUnionCoverage bestPortfolioPrior 1
        unproductivePortfolioPrior 1 portfolioAccepted <
        twoArmExpectedUnionCoverage bestPortfolioPrior 2
          unproductivePortfolioPrior 0 portfolioAccepted ∧
      iidExpectedDistinctCoverage bestPortfolioPrior 2 portfolioAccepted =
        twoArmExpectedUnionCoverage bestPortfolioPrior 2
          unproductivePortfolioPrior 0 portfolioAccepted := by
  rw [fixedSplitPortfolio_yield, bestPortfolio_fullBudget_yield,
    fullBestAllocation_yield]
  norm_num

#print axioms sharpness_has_interior_optimum_fixture
#print axioms equal_entropy_strictly_ordered_distinctYield
#print axioms twoArmExpectedUnionCoverage_decomposition
#print axioms twoArmExpectedTotalExclusive_strict_of_overlap_lt
#print axioms fixedSplit_strictly_loses_to_bestSingle
#print axioms computableAllocation_dominates_split_and_single

end Mettapedia.MachineLearning.SearchGuidance
