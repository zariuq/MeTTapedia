import Mettapedia.MachineLearning.SearchGuidance.DecisivenessYield

/-!
# Distinct verified coverage under a finite sampling budget

This file extends multiplicity-counting search yield to the quantity used by a
checker-backed search campaign: the number of distinct accepted outcomes seen
at least once.  Every expectation is expanded over finite i.i.d. words before
being reduced to a closed form.

The scope is fixed-prior i.i.d. categorical sampling with a deterministic
acceptance set.  Duplicate rejection, without-replacement enumeration, and
adaptive allocation are identified explicitly when they depart from that
scope.
-/

noncomputable section

namespace Mettapedia.MachineLearning.SearchGuidance

open Finset BigOperators
open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

/-! ## T1: distinct coverage derived from finite words -/

/-- A word contains a particular categorical outcome. -/
def wordContains {k n : ℕ} (xs : Fin n → Fin k) (target : Fin k) : Prop :=
  ∃ i, xs i = target

theorem wordContains_iff_hits_singleton {k n : ℕ}
    (xs : Fin n → Fin k) (target : Fin k) :
    wordContains xs target ↔ wordHitsTargetSet xs {target} := by
  simp only [wordContains, wordHitsTargetSet, Finset.mem_singleton]

/-- Each accepted outcome contributes one exactly when it occurs at least
once.  Repeated occurrences therefore never increase this count. -/
noncomputable def distinctVerifiedCoverage {k n : ℕ}
    (xs : Fin n → Fin k) (accepted : Finset (Fin k)) : ℕ := by
  classical
  exact ∑ target ∈ accepted, if wordContains xs target then 1 else 0

/-- Accepted hits counted with multiplicity.  This is the existing target-hit
quantity summed over the deterministic checker's accepted outcomes. -/
def verifiedHitCount {k n : ℕ}
    (xs : Fin n → Fin k) (accepted : Finset (Fin k)) : ℕ :=
  ∑ target ∈ accepted, targetHitCount xs target

/-- Word-level duplicate burden.  It is stated over the two genuine counts;
the later expectation theorem shows that it is their exact complement. -/
def verifiedDuplicateBurden {k n : ℕ}
    (xs : Fin n → Fin k) (accepted : Finset (Fin k)) : ℝ :=
  (verifiedHitCount xs accepted : ℝ) -
    (distinctVerifiedCoverage xs accepted : ℝ)

/-- Finite expectation of distinct verified coverage over all categorical
words in the budget. -/
def iidExpectedDistinctCoverage {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (accepted : Finset (Fin k)) : ℝ :=
  ∑ xs : Fin budget → Fin k,
    categoricalProductPMF (θ : Fin k → ℝ) xs *
      (distinctVerifiedCoverage xs accepted : ℝ)

/-- Finite expectation of accepted hits with multiplicity. -/
def iidExpectedVerifiedHits {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (accepted : Finset (Fin k)) : ℝ :=
  ∑ xs : Fin budget → Fin k,
    categoricalProductPMF (θ : Fin k → ℝ) xs *
      (verifiedHitCount xs accepted : ℝ)

/-- Finite expectation of the word-level duplicate burden. -/
def iidExpectedDuplicateBurden {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (accepted : Finset (Fin k)) : ℝ :=
  ∑ xs : Fin budget → Fin k,
    categoricalProductPMF (θ : Fin k → ℝ) xs *
      verifiedDuplicateBurden xs accepted

theorem iidExpectedDistinctCoverage_eq_sum_success {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (accepted : Finset (Fin k)) :
    iidExpectedDistinctCoverage θ budget accepted =
      ∑ target ∈ accepted,
        iidAtLeastOneTargetSuccess θ budget {target} := by
  classical
  unfold iidExpectedDistinctCoverage distinctVerifiedCoverage
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target htarget
  unfold iidAtLeastOneTargetSuccess
  apply Finset.sum_congr rfl
  intro xs _hxs
  rw [wordContains_iff_hits_singleton]
  by_cases h : wordHitsTargetSet xs {target} <;> simp [h]

/-- T1 exact expectation: each accepted target contributes the probability of
being observed at least once. -/
theorem iidExpectedDistinctCoverage_eq_sum_one_sub_pow {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (accepted : Finset (Fin k)) :
    iidExpectedDistinctCoverage θ budget accepted =
      ∑ target ∈ accepted,
        (1 - (1 - (θ : Fin k → ℝ) target) ^ budget) := by
  rw [iidExpectedDistinctCoverage_eq_sum_success]
  apply Finset.sum_congr rfl
  intro target _htarget
  rw [iidAtLeastOne_singleton_eq]

theorem iidExpectedVerifiedHits_eq_budget_mul_mass {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (accepted : Finset (Fin k)) :
    iidExpectedVerifiedHits θ budget accepted =
      (budget : ℝ) * targetSetMass θ accepted := by
  classical
  calc
    iidExpectedVerifiedHits θ budget accepted =
        ∑ target ∈ accepted, iidExpectedTargetHits θ budget target := by
      unfold iidExpectedVerifiedHits verifiedHitCount iidExpectedTargetHits
      simp_rw [Nat.cast_sum, mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ target ∈ accepted,
        (budget : ℝ) * (θ : Fin k → ℝ) target := by
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [iidExpectedTargetHits_eq_budget_mul_targetMass]
    _ = (budget : ℝ) * targetSetMass θ accepted := by
      rw [← Finset.mul_sum]
      unfold targetSetMass
      simp

/-- The old expected-hit quantity is recovered exactly by a singleton
acceptance set; the multiplicity-counting development is not orphaned. -/
theorem iidExpectedVerifiedHits_singleton_eq {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (target : Fin k) :
    iidExpectedVerifiedHits θ budget {target} =
      iidExpectedTargetHits θ budget target := by
  classical
  unfold iidExpectedVerifiedHits verifiedHitCount
  change (∑ xs : Fin budget → Fin k,
      categoricalProductPMF (θ : Fin k → ℝ) xs *
        (targetHitCount xs target : ℝ)) = _
  rfl

theorem iidExpectedDistinctCoverage_singleton_eq {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (target : Fin k) :
    iidExpectedDistinctCoverage θ budget {target} =
      iidAtLeastOneTargetSuccess θ budget {target} := by
  rw [iidExpectedDistinctCoverage_eq_sum_success]
  simp

/-- Expected duplicate burden is exactly multiplicity yield minus distinct
yield, because the word-level definition is that genuine count difference. -/
theorem iidExpectedDuplicateBurden_eq_hits_sub_distinct {k : ℕ}
    (θ : ProbSimplex k) (budget : ℕ) (accepted : Finset (Fin k)) :
    iidExpectedDuplicateBurden θ budget accepted =
      iidExpectedVerifiedHits θ budget accepted -
        iidExpectedDistinctCoverage θ budget accepted := by
  classical
  unfold iidExpectedDuplicateBurden verifiedDuplicateBurden
  calc
    (∑ xs : Fin budget → Fin k,
        categoricalProductPMF (θ : Fin k → ℝ) xs *
          ((verifiedHitCount xs accepted : ℝ) -
            (distinctVerifiedCoverage xs accepted : ℝ))) =
        ∑ xs : Fin budget → Fin k,
          (categoricalProductPMF (θ : Fin k → ℝ) xs *
              (verifiedHitCount xs accepted : ℝ) -
            categoricalProductPMF (θ : Fin k → ℝ) xs *
              (distinctVerifiedCoverage xs accepted : ℝ)) := by
          apply Finset.sum_congr rfl
          intro xs _hxs
          ring
    _ = iidExpectedVerifiedHits θ budget accepted -
        iidExpectedDistinctCoverage θ budget accepted := by
          rw [Finset.sum_sub_distrib]
          rfl

/-! ## T2: collision mass, effective support, and the canonicalization boundary -/

/-- Rényi-2 collision mass of a finite categorical prior. -/
def collisionMass {k : ℕ} (θ : ProbSimplex k) : ℝ :=
  ∑ target : Fin k, (θ : Fin k → ℝ) target ^ 2

/-- Reciprocal collision mass, the usual Rényi-2 effective support. -/
def effectiveSupport {k : ℕ} (θ : ProbSimplex k) : ℝ :=
  (collisionMass θ)⁻¹

/-- The probability that two independent draws coincide, derived from the
two-word product mass, is exactly collision mass. -/
theorem twoDrawCollisionProbability_eq_collisionMass {k : ℕ}
    (θ : ProbSimplex k) :
    (∑ xs : Fin 2 → Fin k,
      if xs 0 = xs 1 then categoricalProductPMF (θ : Fin k → ℝ) xs else 0) =
      collisionMass θ := by
  classical
  have hdecomp :
      (∑ xs : Fin 2 → Fin k,
        if xs 0 = xs 1 then categoricalProductPMF (θ : Fin k → ℝ) xs else 0) =
        ∑ p : Fin k × Fin k,
          if p.1 = p.2 then
            (θ : Fin k → ℝ) p.1 * (θ : Fin k → ℝ) p.2 else 0 := by
    simpa [categoricalProductPMF, Fin.prod_univ_succ] using
      (Fintype.sum_equiv
        (finTwoArrowEquiv (Fin k))
        (fun xs =>
          if xs 0 = xs 1 then categoricalProductPMF (θ : Fin k → ℝ) xs else 0)
        (fun p =>
          if p.1 = p.2 then
            (θ : Fin k → ℝ) p.1 * (θ : Fin k → ℝ) p.2 else 0)
        (fun xs => by
          by_cases h : xs 0 = xs 1 <;> simp [h, categoricalProductPMF,
            Fin.prod_univ_succ]))
  rw [hdecomp, Fintype.sum_prod_type]
  simp [collisionMass, pow_two]

/-- With every outcome accepted, two-draw distinct coverage is two minus the
pair-collision probability. -/
theorem twoDraw_expectedDistinct_eq_two_sub_collision {k : ℕ}
    (θ : ProbSimplex k) :
    iidExpectedDistinctCoverage θ 2 Finset.univ = 2 - collisionMass θ := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow]
  unfold collisionMass
  calc
    (∑ x : Fin k, (1 - (1 - (θ : Fin k → ℝ) x) ^ 2)) =
        ∑ x : Fin k, (2 * (θ : Fin k → ℝ) x -
          (θ : Fin k → ℝ) x ^ 2) := by
            apply Finset.sum_congr rfl
            intro x _hx
            ring
    _ = 2 - ∑ x : Fin k, (θ : Fin k → ℝ) x ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        probSimplex_sum_one]
      ring

/-- Uniform prior on a nonempty finite support. -/
def uniformPrior (k : ℕ) (hk : 0 < k) : ProbSimplex k :=
  ⟨fun _ => (k : ℝ)⁻¹, by
    constructor
    · intro _i
      positivity
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      simp [hkR]⟩

@[simp] theorem uniformPrior_apply (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (uniformPrior k hk : Fin k → ℝ) i = (k : ℝ)⁻¹ := rfl

theorem uniformPrior_collisionMass (k : ℕ) (hk : 0 < k) :
    collisionMass (uniformPrior k hk) = (k : ℝ)⁻¹ := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold collisionMass
  simp [uniformPrior_apply, pow_two, hkR]

theorem uniformPrior_effectiveSupport (k : ℕ) (hk : 0 < k) :
    effectiveSupport (uniformPrior k hk) = k := by
  rw [effectiveSupport, uniformPrior_collisionMass]
  simp

/-- Exact budget/effective-support relation in the uniform-support model.  No
claim that collision mass alone determines nonuniform all-budget yield is made. -/
theorem uniformPrior_expectedDistinct_fixedPoint
    (k : ℕ) (hk : 0 < k) (budget : ℕ) :
    iidExpectedDistinctCoverage (uniformPrior k hk) budget Finset.univ =
      (k : ℝ) * (1 - (1 - (k : ℝ)⁻¹) ^ budget) := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow]
  simp [uniformPrior_apply]
  ring

/-! A duplicate-free canonical enumerator is a different sampling rule, not
post-processing of the same i.i.d. draws.  For two draws its exact gain over
i.i.d. sampling is collision mass. -/

def firstTwoDistinctWord {k : ℕ} (hk : 2 ≤ k) : Fin 2 → Fin k
  | 0 => ⟨0, lt_of_lt_of_le (by norm_num) hk⟩
  | 1 => ⟨1, hk⟩

theorem firstTwoDistinctWord_coverage {k : ℕ} (hk : 2 ≤ k) :
    distinctVerifiedCoverage (firstTwoDistinctWord hk) Finset.univ = 2 := by
  classical
  have hne : (firstTwoDistinctWord hk 0) ≠ firstTwoDistinctWord hk 1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [firstTwoDistinctWord] at this
  unfold distinctVerifiedCoverage
  rw [show (∑ target ∈ (Finset.univ : Finset (Fin k)),
      if wordContains (firstTwoDistinctWord hk) target then 1 else 0) =
      ((Finset.univ.filter
        (fun target => wordContains (firstTwoDistinctWord hk) target)).card) by
        simp]
  have hfilter :
      Finset.univ.filter (fun target => wordContains (firstTwoDistinctWord hk) target) =
        {firstTwoDistinctWord hk 0, firstTwoDistinctWord hk 1} := by
    ext target
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro h
      rcases h with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  rw [hfilter]
  simp [hne]

theorem twoDraw_duplicateFree_gain_eq_collisionMass {k : ℕ}
    (θ : ProbSimplex k) (hk : 2 ≤ k) :
    (distinctVerifiedCoverage (firstTwoDistinctWord hk) Finset.univ : ℝ) -
        iidExpectedDistinctCoverage θ 2 Finset.univ = collisionMass θ := by
  rw [firstTwoDistinctWord_coverage, twoDraw_expectedDistinct_eq_two_sub_collision]
  ring

/-! ## Positive and negative duplicate fixtures -/

theorem repeated_word_counts_once_negative_example :
    distinctVerifiedCoverage (fun _ : Fin 4 => (1 : Fin 2)) {1} = 1 ∧
      verifiedHitCount (fun _ : Fin 4 => (1 : Fin 2)) {1} = 4 := by
  constructor
  · norm_num [distinctVerifiedCoverage, wordContains]
  · norm_num [verifiedHitCount, targetHitCount, Fin.sum_univ_succ]

theorem uniformTwo_twoDraw_duplicate_gain_positive_example :
    (distinctVerifiedCoverage (firstTwoDistinctWord (k := 2) (by norm_num))
        Finset.univ : ℝ) -
      iidExpectedDistinctCoverage (uniformPrior 2 (by norm_num)) 2 Finset.univ =
        1 / 2 := by
  rw [twoDraw_duplicateFree_gain_eq_collisionMass,
    uniformPrior_collisionMass]
  norm_num

/-! ## Collision mass does not determine arbitrary nonuniform all-budget yield -/

def halfHalfZeroPrior : ProbSimplex 3 :=
  ⟨fun i => if i.val = 0 then 1 / 2 else if i.val = 1 then 1 / 2 else 0, by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      norm_num⟩

def twoThirdsSixthsPrior : ProbSimplex 3 :=
  ⟨fun i => if i.val = 0 then 2 / 3 else 1 / 6, by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      norm_num⟩

@[simp] theorem halfHalfZeroPrior_zero :
    (halfHalfZeroPrior : Fin 3 → ℝ) 0 = 1 / 2 := rfl

@[simp] theorem halfHalfZeroPrior_one :
    (halfHalfZeroPrior : Fin 3 → ℝ) 1 = 1 / 2 := rfl

@[simp] theorem halfHalfZeroPrior_two :
    (halfHalfZeroPrior : Fin 3 → ℝ) 2 = 0 := rfl

@[simp] theorem twoThirdsSixthsPrior_zero :
    (twoThirdsSixthsPrior : Fin 3 → ℝ) 0 = 2 / 3 := rfl

@[simp] theorem twoThirdsSixthsPrior_one :
    (twoThirdsSixthsPrior : Fin 3 → ℝ) 1 = 1 / 6 := rfl

@[simp] theorem twoThirdsSixthsPrior_two :
    (twoThirdsSixthsPrior : Fin 3 → ℝ) 2 = 1 / 6 := rfl

theorem halfHalf_twoThirds_collisionMass_eq :
    collisionMass halfHalfZeroPrior = collisionMass twoThirdsSixthsPrior := by
  unfold collisionMass
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  norm_num

theorem halfHalf_threeDraw_distinctCoverage :
    iidExpectedDistinctCoverage halfHalfZeroPrior 3 Finset.univ = 7 / 4 := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow, Fin.sum_univ_three]
  norm_num

theorem twoThirds_threeDraw_distinctCoverage :
    iidExpectedDistinctCoverage twoThirdsSixthsPrior 3 Finset.univ = 65 / 36 := by
  rw [iidExpectedDistinctCoverage_eq_sum_one_sub_pow, Fin.sum_univ_three]
  norm_num

/-- Negative boundary for the effective-support heuristic: equal collision
mass (and hence equal Rényi-2 effective support) does not determine distinct
coverage once a nonuniform budget reaches three draws. -/
theorem equal_collisionMass_different_threeDrawCoverage :
    collisionMass halfHalfZeroPrior = collisionMass twoThirdsSixthsPrior ∧
      iidExpectedDistinctCoverage halfHalfZeroPrior 3 Finset.univ ≠
        iidExpectedDistinctCoverage twoThirdsSixthsPrior 3 Finset.univ := by
  constructor
  · exact halfHalf_twoThirds_collisionMass_eq
  · rw [halfHalf_threeDraw_distinctCoverage,
      twoThirds_threeDraw_distinctCoverage]
    norm_num

/-! ## A nontrivial canonical-form boundary fixture -/

/-- Two syntactic outcomes (`0`,`1`) denote semantic outcome `0`; syntax `2`
denotes semantic outcome `1`. -/
def duplicateSyntaxCanonicalForm (i : Fin 3) : Fin 2 :=
  if i.val = 2 then 1 else 0

def duplicateSyntaxPrior : ProbSimplex 3 :=
  ⟨fun i => if i.val = 0 then 1 / 4 else if i.val = 1 then 1 / 4 else 1 / 2, by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      norm_num⟩

/-- Actual raw-word expectation after semantic canonicalization. -/
def iidExpectedPostCanonicalCoverage (budget : ℕ) : ℝ :=
  ∑ xs : Fin budget → Fin 3,
    categoricalProductPMF (duplicateSyntaxPrior : Fin 3 → ℝ) xs *
      (distinctVerifiedCoverage
        (fun i => duplicateSyntaxCanonicalForm (xs i)) Finset.univ : ℝ)

theorem duplicateSyntaxCanonicalForm_zero :
    duplicateSyntaxCanonicalForm 0 = 0 := rfl

theorem duplicateSyntaxCanonicalForm_one :
    duplicateSyntaxCanonicalForm 1 = 0 := rfl

theorem duplicateSyntaxCanonicalForm_two :
    duplicateSyntaxCanonicalForm 2 = 1 := rfl

theorem duplicateSyntaxPrior_zero :
    (duplicateSyntaxPrior : Fin 3 → ℝ) 0 = 1 / 4 := rfl

theorem duplicateSyntaxPrior_one :
    (duplicateSyntaxPrior : Fin 3 → ℝ) 1 = 1 / 4 := rfl

theorem duplicateSyntaxPrior_two :
    (duplicateSyntaxPrior : Fin 3 → ℝ) 2 = 1 / 2 := rfl

theorem postCanonical_twoDraw_coverage :
    iidExpectedPostCanonicalCoverage 2 = 3 / 2 := by
  classical
  unfold iidExpectedPostCanonicalCoverage
  have hdecomp :
      (∑ xs : Fin 2 → Fin 3,
        categoricalProductPMF (duplicateSyntaxPrior : Fin 3 → ℝ) xs *
          (distinctVerifiedCoverage
            (fun i => duplicateSyntaxCanonicalForm (xs i)) Finset.univ : ℝ)) =
        ∑ p : Fin 3 × Fin 3,
          (duplicateSyntaxPrior : Fin 3 → ℝ) p.1 *
            (duplicateSyntaxPrior : Fin 3 → ℝ) p.2 *
              (distinctVerifiedCoverage
                ![duplicateSyntaxCanonicalForm p.1,
                  duplicateSyntaxCanonicalForm p.2] Finset.univ : ℝ) := by
    simpa [categoricalProductPMF, Fin.prod_univ_two] using
      Fintype.sum_equiv
        (finTwoArrowEquiv (Fin 3))
        (fun xs =>
          categoricalProductPMF (duplicateSyntaxPrior : Fin 3 → ℝ) xs *
            (distinctVerifiedCoverage
              (fun i => duplicateSyntaxCanonicalForm (xs i)) Finset.univ : ℝ))
        (fun p =>
          (duplicateSyntaxPrior : Fin 3 → ℝ) p.1 *
            (duplicateSyntaxPrior : Fin 3 → ℝ) p.2 *
              (distinctVerifiedCoverage
                ![duplicateSyntaxCanonicalForm p.1,
                  duplicateSyntaxCanonicalForm p.2] Finset.univ : ℝ))
        (fun xs => by
          have hword :
              (fun i => duplicateSyntaxCanonicalForm (xs i)) =
                ![duplicateSyntaxCanonicalForm (xs 0),
                  duplicateSyntaxCanonicalForm (xs 1)] := by
            funext i
            fin_cases i <;> rfl
          rw [hword]
          simp [categoricalProductPMF, Fin.prod_univ_succ])
  have h00 : distinctVerifiedCoverage
      (![(0 : Fin 2), (0 : Fin 2)] : Fin 2 → Fin 2) Finset.univ = 1 := by
    norm_num [distinctVerifiedCoverage, wordContains, Fin.sum_univ_two]
  have h_all_01 :
      Finset.univ.filter (fun x : Fin 2 => (0 : Fin 2) = x ∨ (1 : Fin 2) = x) =
        Finset.univ := by
    ext x
    fin_cases x <;> simp
  have h_all_10 :
      Finset.univ.filter (fun x : Fin 2 => (1 : Fin 2) = x ∨ (0 : Fin 2) = x) =
        Finset.univ := by
    ext x
    fin_cases x <;> simp
  have h01 : distinctVerifiedCoverage
      (![(0 : Fin 2), (1 : Fin 2)] : Fin 2 → Fin 2) Finset.univ = 2 := by
    norm_num [distinctVerifiedCoverage, wordContains, Fin.sum_univ_two, h_all_01]
  have h10 : distinctVerifiedCoverage
      (![(1 : Fin 2), (0 : Fin 2)] : Fin 2 → Fin 2) Finset.univ = 2 := by
    norm_num [distinctVerifiedCoverage, wordContains, Fin.sum_univ_two, h_all_10]
  have h11 : distinctVerifiedCoverage
      (![(1 : Fin 2), (1 : Fin 2)] : Fin 2 → Fin 2) Finset.univ = 1 := by
    norm_num [distinctVerifiedCoverage, wordContains, Fin.sum_univ_two]
  rw [hdecomp, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three, Fin.sum_univ_three]
  norm_num [duplicateSyntaxPrior_zero, duplicateSyntaxPrior_one,
    duplicateSyntaxPrior_two, duplicateSyntaxCanonicalForm_zero,
    duplicateSyntaxCanonicalForm_one, duplicateSyntaxCanonicalForm_two,
    h00, h01, h10, h11]

/-- Mere semantics-preserving postprocessing gives exactly the pushforward
uniform semantic prior's coverage; it is not the strict-improvement lever. -/
theorem canonical_postprocessing_no_strict_gain_fixture :
    iidExpectedPostCanonicalCoverage 2 =
      iidExpectedDistinctCoverage (uniformPrior 2 (by norm_num)) 2 Finset.univ := by
  rw [postCanonical_twoDraw_coverage,
    uniformPrior_expectedDistinct_fixedPoint]
  norm_num

#print axioms iidExpectedDistinctCoverage_eq_sum_one_sub_pow
#print axioms iidExpectedVerifiedHits_eq_budget_mul_mass
#print axioms twoDrawCollisionProbability_eq_collisionMass
#print axioms uniformPrior_expectedDistinct_fixedPoint
#print axioms twoDraw_duplicateFree_gain_eq_collisionMass
#print axioms equal_collisionMass_different_threeDrawCoverage
#print axioms canonical_postprocessing_no_strict_gain_fixture

end Mettapedia.MachineLearning.SearchGuidance
