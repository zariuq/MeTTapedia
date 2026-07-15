import Mettapedia.ProbabilityTheory.Exchangeability.CategoricalMixture

/-!
# Decisiveness and finite-search yield

This file analyzes budgeted independent categorical sampling on a finite
sample space.  The product weights are proved to form a probability mass
function, and expected target hits are computed from the full finite weighted
sum rather than introduced by a closed-form definition.

The binary fixture then separates two objectives: priors symmetric around a
half-half soft target have equal cross-entropy, while the prior assigning more
mass to the actual target has strictly larger expected search yield.
-/

noncomputable section

namespace Mettapedia.MachineLearning.SearchGuidance

open Finset BigOperators
open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

/-! ## Finite i.i.d. categorical sampling -/

/-- Number of occurrences of one target in a finite categorical word. -/
def targetHitCount {k n : ℕ} (xs : Fin n → Fin k) (target : Fin k) : ℕ :=
  ∑ i, if xs i = target then 1 else 0

theorem targetHitCount_cons {k n : ℕ}
    (head : Fin k) (tail : Fin n → Fin k) (target : Fin k) :
    targetHitCount (Fin.cons head tail) target =
      (if head = target then 1 else 0) + targetHitCount tail target := by
  unfold targetHitCount
  rw [Fin.sum_univ_succ]
  rfl

theorem categoricalProductPMF_cons {k n : ℕ}
    (θ : Fin k → ℝ) (head : Fin k) (tail : Fin n → Fin k) :
    categoricalProductPMF θ (Fin.cons head tail) =
      θ head * categoricalProductPMF θ tail := by
  unfold categoricalProductPMF
  rw [Fin.prod_univ_succ]
  rfl

/-- Product masses of all categorical words of a fixed length sum to one. -/
theorem sum_categoricalProductPMF_eq_one {k : ℕ} (θ : ProbSimplex k) :
    ∀ n : ℕ,
      ∑ xs : Fin n → Fin k, categoricalProductPMF (θ : Fin k → ℝ) xs = 1 := by
  intro n
  induction n with
  | zero =>
      simp [categoricalProductPMF]
  | succ n ih =>
      have hdecomp :
          (∑ xs : Fin (n + 1) → Fin k,
              categoricalProductPMF (θ : Fin k → ℝ) xs) =
            ∑ p : Fin k × (Fin n → Fin k),
              categoricalProductPMF (θ : Fin k → ℝ) (Fin.cons p.1 p.2) := by
        simpa using
          (Fintype.sum_equiv
            (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Fin k))
            (fun p => categoricalProductPMF (θ : Fin k → ℝ) (Fin.cons p.1 p.2))
            (fun xs => categoricalProductPMF (θ : Fin k → ℝ) xs)
            (fun _p => rfl)).symm
      rw [hdecomp, Fintype.sum_prod_type]
      simp_rw [categoricalProductPMF_cons, ← Finset.mul_sum]
      rw [ih]
      simp [probSimplex_sum_one θ]

/-- The real product weights are a finite probability mass function. -/
theorem categoricalProductPMF_isProbabilityMass {k n : ℕ}
    (θ : ProbSimplex k) :
    (∀ xs : Fin n → Fin k,
      0 ≤ categoricalProductPMF (θ : Fin k → ℝ) xs) ∧
      ∑ xs : Fin n → Fin k,
        categoricalProductPMF (θ : Fin k → ℝ) xs = 1 := by
  exact ⟨categoricalProductPMF_nonneg θ, sum_categoricalProductPMF_eq_one θ n⟩

/-- Expected target-hit count, expanded as a finite expectation over every
categorical word in the sampling budget. -/
def iidExpectedTargetHits {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (target : Fin k) : ℝ :=
  ∑ xs : Fin budget → Fin k,
    categoricalProductPMF (θ : Fin k → ℝ) xs * (targetHitCount xs target : ℝ)

/-- The finite i.i.d. expectation is the budget times
the prior mass assigned to the target. -/
theorem iidExpectedTargetHits_eq_budget_mul_targetMass {k : ℕ}
    (θ : ProbSimplex k) (target : Fin k) :
    ∀ budget : ℕ,
      iidExpectedTargetHits θ budget target =
        (budget : ℝ) * (θ : Fin k → ℝ) target := by
  intro budget
  induction budget with
  | zero =>
      simp [iidExpectedTargetHits, categoricalProductPMF, targetHitCount]
  | succ n ih =>
      unfold iidExpectedTargetHits
      have hdecomp :
          (∑ xs : Fin (n + 1) → Fin k,
              categoricalProductPMF (θ : Fin k → ℝ) xs *
                (targetHitCount xs target : ℝ)) =
            ∑ p : Fin k × (Fin n → Fin k),
              categoricalProductPMF (θ : Fin k → ℝ) (Fin.cons p.1 p.2) *
                (targetHitCount (Fin.cons p.1 p.2) target : ℝ) := by
        simpa using
          (Fintype.sum_equiv
            (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Fin k))
            (fun p =>
              categoricalProductPMF (θ : Fin k → ℝ) (Fin.cons p.1 p.2) *
                (targetHitCount (Fin.cons p.1 p.2) target : ℝ))
            (fun xs =>
              categoricalProductPMF (θ : Fin k → ℝ) xs *
                (targetHitCount xs target : ℝ))
            (fun _p => rfl)).symm
      rw [hdecomp, Fintype.sum_prod_type]
      simp_rw [categoricalProductPMF_cons, targetHitCount_cons, Nat.cast_add,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      have hmass := sum_categoricalProductPMF_eq_one θ n
      have hbranch (a : Fin k) :
          (∑ xs : Fin n → Fin k,
              ((θ : Fin k → ℝ) a *
                categoricalProductPMF (θ : Fin k → ℝ) xs) *
                ((if a = target then (1 : ℝ) else 0) +
                  (targetHitCount xs target : ℝ))) =
            (θ : Fin k → ℝ) a * (if a = target then (1 : ℝ) else 0) +
              (θ : Fin k → ℝ) a *
                ((n : ℝ) * (θ : Fin k → ℝ) target) := by
        calc
          _ = ∑ xs : Fin n → Fin k,
                (((θ : Fin k → ℝ) a *
                  (if a = target then (1 : ℝ) else 0)) *
                    categoricalProductPMF (θ : Fin k → ℝ) xs +
                (θ : Fin k → ℝ) a *
                  (categoricalProductPMF (θ : Fin k → ℝ) xs *
                    (targetHitCount xs target : ℝ))) := by
              apply Finset.sum_congr rfl
              intro xs _hxs
              ring
          _ = ((θ : Fin k → ℝ) a *
                (if a = target then (1 : ℝ) else 0)) *
                  (∑ xs : Fin n → Fin k,
                    categoricalProductPMF (θ : Fin k → ℝ) xs) +
                (θ : Fin k → ℝ) a *
                  (∑ xs : Fin n → Fin k,
                    categoricalProductPMF (θ : Fin k → ℝ) xs *
                      (targetHitCount xs target : ℝ)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = _ := by
              rw [hmass]
              change _ + _ * iidExpectedTargetHits θ n target = _
              rw [ih]
              ring
      simp_rw [hbranch]
      rw [Finset.sum_add_distrib]
      have hindicator :
          (∑ a : Fin k,
              (θ : Fin k → ℝ) a * (if a = target then (1 : ℝ) else 0)) =
            (θ : Fin k → ℝ) target := by
        simp
      rw [hindicator, ← Finset.sum_mul, probSimplex_sum_one θ]
      ring

/-- Expected yield is monotone in the categorical prior mass on the target. -/
theorem iidExpectedTargetHits_mono_targetMass {k : ℕ}
    (θ₁ θ₂ : ProbSimplex k) (budget : ℕ) (target : Fin k)
    (hmass : (θ₁ : Fin k → ℝ) target ≤ (θ₂ : Fin k → ℝ) target) :
    iidExpectedTargetHits θ₁ budget target ≤
      iidExpectedTargetHits θ₂ budget target := by
  rw [iidExpectedTargetHits_eq_budget_mul_targetMass,
    iidExpectedTargetHits_eq_budget_mul_targetMass]
  exact mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg budget)

/-- A positive sampling budget turns a strict target-mass improvement into a
strict expected-yield improvement. -/
theorem iidExpectedTargetHits_strictMono_targetMass {k : ℕ}
    (θ₁ θ₂ : ProbSimplex k) (budget : ℕ) (target : Fin k)
    (hbudget : 0 < budget)
    (hmass : (θ₁ : Fin k → ℝ) target < (θ₂ : Fin k → ℝ) target) :
    iidExpectedTargetHits θ₁ budget target <
      iidExpectedTargetHits θ₂ budget target := by
  rw [iidExpectedTargetHits_eq_budget_mul_targetMass,
    iidExpectedTargetHits_eq_budget_mul_targetMass]
  exact mul_lt_mul_of_pos_left hmass (by exact_mod_cast hbudget)

/-! ## Equal soft-target cross-entropy, unequal search yield -/

/-- Binary categorical prior with target symbol `1` assigned mass `p`. -/
def binaryPrior (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ProbSimplex 2 :=
  ⟨fun i => if i = 0 then 1 - p else p, by
    constructor
    · intro i
      fin_cases i <;> simp <;> linarith
    · norm_num⟩

@[simp] theorem binaryPrior_targetMass
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryPrior p hp0 hp1 : Fin 2 → ℝ) 1 = p := by
  change (if (1 : Fin 2) = 0 then 1 - p else p) = p
  norm_num

@[simp] theorem binaryPrior_otherMass
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryPrior p hp0 hp1 : Fin 2 → ℝ) 0 = 1 - p := by
  change (if (0 : Fin 2) = 0 then 1 - p else p) = 1 - p
  norm_num

/-- Cross-entropy against the soft binary target `(1/2, 1/2)`. -/
noncomputable def softHalfTargetCrossEntropy (θ : ProbSimplex 2) : ℝ :=
  -(1 / 2) * Real.log ((θ : Fin 2 → ℝ) 0) -
    (1 / 2) * Real.log ((θ : Fin 2 → ℝ) 1)

noncomputable def lowTargetMassPrior : ProbSimplex 2 :=
  binaryPrior (1 / 4) (by norm_num) (by norm_num)

noncomputable def highTargetMassPrior : ProbSimplex 2 :=
  binaryPrior (3 / 4) (by norm_num) (by norm_num)

theorem low_high_prior_crossEntropy_eq :
    softHalfTargetCrossEntropy lowTargetMassPrior =
      softHalfTargetCrossEntropy highTargetMassPrior := by
  change -(1 / 2) * Real.log (1 - 1 / 4) -
      (1 / 2) * Real.log (1 / 4) =
    -(1 / 2) * Real.log (1 - 3 / 4) -
      (1 / 2) * Real.log (3 / 4)
  have hlow : (1 - 1 / 4 : ℝ) = 3 / 4 := by norm_num
  have hhigh : (1 - 3 / 4 : ℝ) = 1 / 4 := by norm_num
  rw [hlow, hhigh]
  ring

theorem low_high_prior_expectedYield_strict
    (budget : ℕ) (hbudget : 0 < budget) :
    iidExpectedTargetHits lowTargetMassPrior budget 1 <
      iidExpectedTargetHits highTargetMassPrior budget 1 := by
  apply iidExpectedTargetHits_strictMono_targetMass
  · exact hbudget
  · change (1 / 4 : ℝ) < 3 / 4
    norm_num

/-- Equal cross-entropy against a soft target does not
determine finite search yield. -/
theorem equal_crossEntropy_strictly_ordered_expectedYield :
    softHalfTargetCrossEntropy lowTargetMassPrior =
        softHalfTargetCrossEntropy highTargetMassPrior ∧
      ∀ budget : ℕ, 0 < budget →
        iidExpectedTargetHits lowTargetMassPrior budget 1 <
          iidExpectedTargetHits highTargetMassPrior budget 1 := by
  exact ⟨low_high_prior_crossEntropy_eq, low_high_prior_expectedYield_strict⟩

/-! ## Positive and negative fixtures -/

theorem fourSample_expectedYield_positive_example :
    iidExpectedTargetHits highTargetMassPrior 4 1 = 3 := by
  rw [iidExpectedTargetHits_eq_budget_mul_targetMass]
  change (4 : ℝ) * (3 / 4) = 3
  norm_num

/-- Equal soft-target cross-entropy cannot be used as a substitute for equal
target yield, even for a four-sample budget. -/
theorem equal_crossEntropy_does_not_force_equalYield_negative_example :
    softHalfTargetCrossEntropy lowTargetMassPrior =
        softHalfTargetCrossEntropy highTargetMassPrior ∧
      iidExpectedTargetHits lowTargetMassPrior 4 1 ≠
        iidExpectedTargetHits highTargetMassPrior 4 1 := by
  constructor
  · exact low_high_prior_crossEntropy_eq
  · rw [iidExpectedTargetHits_eq_budget_mul_targetMass,
      iidExpectedTargetHits_eq_budget_mul_targetMass]
    change (4 : ℝ) * (1 / 4) ≠ 4 * (3 / 4)
    norm_num

end Mettapedia.MachineLearning.SearchGuidance
