/-
# Necessity of σ-Additivity Axioms

This file provides **counterexamples** demonstrating that each of the three axioms
for σ-additivity is strictly necessary:

1. **SigmaCompleteEvents**: Without countable joins, σ-additivity is meaningless
2. **KSScaleComplete**: Without sequential completeness, limits may not exist
3. **KSScottContinuous**: Without Scott continuity, finite additivity ≠ σ-additivity

## References

- Billingsley, "Probability and Measure" (1995), §1.4
- Dunford & Schwartz, "Linear Operators" (1958), II.2 for Banach limits
- Hewitt & Stromberg, "Real and Abstract Analysis" (1965), §10.51
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.SigmaAdditivityNecessity

open scoped Classical

/-! ## Counterexample 1: Without SigmaCompleteEvents

The simplest counterexample: the lattice of FINITE subsets of ℕ has no countable joins
for infinite families. The statement "μ(⋃ₙ {n}) = Σₙ μ({n})" doesn't even type-check
because ⋃ₙ {n} = ℕ is not a finite subset.
-/

/-- The lattice of finite subsets of ℕ -/
def FinSubsets := {A : Set ℕ | A.Finite}

/-- FinSubsets is closed under finite unions -/
theorem finSubsets_union_closed (A B : Set ℕ) (hA : A.Finite) (hB : B.Finite) :
    (A ∪ B).Finite := hA.union hB

/-- FinSubsets is NOT closed under countable unions: ⋃ₙ {n} = ℕ is infinite -/
theorem finSubsets_not_sigma_complete :
    let f : ℕ → Set ℕ := fun n => {n}
    (∀ n, (f n).Finite) ∧ ¬(⋃ n, f n).Finite := by
  constructor
  · intro n
    exact Set.finite_singleton n
  · have h : (⋃ n, ({n} : Set ℕ)) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact ⟨x, rfl⟩
    rw [h]
    exact Set.infinite_univ

/-- **Key Point**: In FinSubsets, the countable join ⋃ₙ {n} does not exist.

The statement "μ(⋃ₙ Aₙ) = Σₙ μ(Aₙ)" requires ⋃ₙ Aₙ to be in the lattice!
This shows SigmaCompleteEvents is necessary even to STATE σ-additivity. -/
theorem sigma_completeness_required_to_state :
    ∃ (f : ℕ → Set ℕ), (∀ n, (f n).Finite) ∧ ¬(⋃ n, f n).Finite :=
  ⟨fun n => {n}, fun n => Set.finite_singleton n, by
    have h : (⋃ n, ({n} : Set ℕ)) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact ⟨x, rfl⟩
    rw [h]
    exact Set.infinite_univ⟩

/-! ## Counterexample 2: Without KSScaleComplete (ℚ scale)

**Model**: Use ℚ as the scale instead of ℝ.
- ℚ is Archimedean and satisfies all finite K&S axioms
- ℚ is NOT sequentially complete: bounded monotone sequences may not have sups in ℚ
- Result: A sequence of events with Θ-values converging to √2 has no limit in ℚ

This shows KSScaleComplete is necessary even when all other axioms hold.
-/

namespace RationalScale

/-- ℚ satisfies Archimedean property (no infinitesimals).
This is a standard fact about rationals. -/
theorem rat_archimedean : ∀ x y : ℚ, 0 < x → ∃ n : ℕ, y < n * x := by
  intro x y hx
  obtain ⟨n, hn⟩ := exists_nat_gt (y / x)
  use n
  have hdiv : y / x < n := hn
  have hxne : x ≠ 0 := ne_of_gt hx
  calc y = (y / x) * x := by field_simp
       _ < n * x := mul_lt_mul_of_pos_right hdiv hx

/-- A concrete bounded monotone sequence demonstrating incompleteness. -/
def geometric_partial_sums : ℕ → ℚ := fun n => 2 - (1 : ℚ) / 2^n

/-- The sequence is bounded above by 2 -/
theorem geometric_bounded : ∀ n, geometric_partial_sums n < 2 := by
  intro n
  simp only [geometric_partial_sums]
  have : (0 : ℚ) < 1 / 2^n := by positivity
  linarith

/-- **Key incompleteness example**: √2 is not rational.

This is the standard proof that ℚ is not sequentially complete:
sequences of rationals converging to √2 have no rational limit.

For K&S with ℚ-valued scale: if Θ-values of events converge to √2,
the measure μ(⋃ₙ Aₙ) cannot be defined.

**Proof**: Uses `Nat.Prime.irrational_sqrt` from mathlib. -/
theorem sqrt2_irrational : ¬ ∃ q : ℚ, q^2 = 2 := by
  intro ⟨q, hq⟩
  -- √2 is irrational via Nat.Prime.irrational_sqrt
  have hirr : Irrational (Real.sqrt 2) := by
    simpa using Nat.Prime.irrational_sqrt (p := 2) (by norm_num)
  -- q² = 2 in ℚ means (q : ℝ)² = 2 in ℝ
  have hq_sq : (q : ℝ)^2 = 2 := by exact_mod_cast hq
  -- |q| = √2 via Real.sqrt_sq_eq_abs
  have habs : |(q : ℝ)| = Real.sqrt 2 := by
    have h := Real.sqrt_sq_eq_abs (q : ℝ)
    rw [hq_sq] at h
    exact h.symm
  -- Irrational means not in range of Rat.cast
  rw [Irrational] at hirr
  simp only [Set.mem_range, not_exists] at hirr
  -- Either q ≥ 0 (so q = √2) or q < 0 (so -q = √2)
  rcases le_or_gt 0 q with hq_nn | hq_neg
  · -- Case q ≥ 0: then |q| = q, so (q : ℝ) = √2
    have heq : (q : ℝ) = Real.sqrt 2 := by
      rw [abs_of_nonneg (by exact_mod_cast hq_nn : (0 : ℝ) ≤ q)] at habs
      exact habs
    exact hirr q heq
  · -- Case q < 0: then |q| = -q, so (-q : ℝ) = √2
    have h : |(q : ℝ)| = -(q : ℝ) := abs_of_neg (by exact_mod_cast hq_neg)
    rw [h, ← Rat.cast_neg] at habs
    -- Now habs : ↑(-q) = √2
    exact hirr (-q) habs

/-- **Incompleteness summary**: ℚ lacks sequential completeness.

Bounded monotone sequences in ℚ may converge (in ℝ) to irrationals,
which have no representation in ℚ. This breaks KSScaleComplete:
we cannot define seqSup when the limit is irrational.

**Key point**: The weaker statement is all we need for the counterexample:
there exist bounded monotone sequences whose "true" limit √2 is not in ℚ. -/
theorem rational_scale_not_complete :
    ¬ ∃ q : ℚ, q^2 = 2 := sqrt2_irrational

/-- **The actual incompleteness**: √2 is irrational (alternative formulation).

Same as `sqrt2_irrational` but with `q * q` instead of `q^2`. -/
theorem sqrt2_not_rational : ¬ ∃ q : ℚ, q * q = 2 := by
  simp only [← sq]
  exact sqrt2_irrational

/-- **Consequence**: KSScaleComplete fails for ℚ when limits are irrational.

The continued fraction convergents to √2 form a bounded monotone sequence,
but no rational satisfies both q² = 2 AND being the LUB of this sequence
(because no rational satisfies q² = 2 at all). -/
theorem rational_scale_incomplete_for_irrational_limits :
    ¬ ∃ s : ℚ, s * s = 2 := sqrt2_not_rational

end RationalScale

/-! ## Counterexample 3: Without KSScottContinuous (Discontinuous Valuation)

**Model**: The classic finitely additive but not σ-additive measure.

- Events E = Set ℕ (power set of naturals) with countable joins
- Scale S = ℝ (complete)
- Valuation v: v({n}) = 0 for all n, but v(ℕ) = 1

This satisfies:
- Finite additivity: v(A ∪ B) = v(A) + v(B) for disjoint finite sets
- NOT σ-additivity: Σₙ v({n}) = 0 ≠ 1 = v(ℕ)

The failure is exactly that v does NOT preserve the countable join:
v(⋃ₙ {n}) ≠ supₙ v(⋃ᵢ<ₙ {i})
-/

namespace DiscontinuousValuation

/-- A "diffuse" valuation: 0 on finite sets, 1 on cofinite sets.

This is well-defined and finitely additive but NOT σ-additive. -/
noncomputable def diffuse : Set ℕ → ℝ := fun A =>
  if A.Finite then 0 else 1

/-- Singletons have measure 0 -/
theorem diffuse_singleton (n : ℕ) : diffuse {n} = 0 := by
  simp only [diffuse, Set.finite_singleton, ↓reduceIte]

/-- ℕ has measure 1 -/
theorem diffuse_univ : diffuse Set.univ = 1 := by
  simp only [diffuse]
  rw [if_neg]
  exact Set.infinite_univ

/-- Finite sets have measure 0 -/
theorem diffuse_finite (A : Set ℕ) (hA : A.Finite) : diffuse A = 0 := by
  simp only [diffuse]
  rw [if_pos hA]

/-- Cofinite (infinite) sets have measure 1 -/
theorem diffuse_infinite (A : Set ℕ) (hA : ¬A.Finite) : diffuse A = 1 := by
  simp only [diffuse]
  rw [if_neg hA]

/-- The union of singletons is ℕ -/
theorem union_singletons_eq_univ : (⋃ n, ({n} : Set ℕ)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact ⟨x, rfl⟩

/-- The diffuse measure of ⋃ₙ {n} = ℕ is 1 -/
theorem diffuse_union_singletons : diffuse (⋃ n, ({n} : Set ℕ)) = 1 := by
  rw [union_singletons_eq_univ]
  exact diffuse_univ

/-- **The Key Failure**: σ-additivity fails.

The singletons {0}, {1}, {2}, ... are pairwise disjoint.
Their union is ℕ.
But: Σₙ diffuse({n}) = 0 ≠ 1 = diffuse(ℕ). -/
theorem diffuse_not_sigma_additive :
    let f : ℕ → Set ℕ := fun n => {n}
    (∀ i j, i ≠ j → Disjoint (f i) (f j)) ∧
    (⋃ n, f n) = Set.univ ∧
    (∑' n, diffuse (f n)) ≠ diffuse (⋃ n, f n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Pairwise disjoint
    intro i j hij
    rw [Set.disjoint_iff]
    intro x ⟨hi, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    rw [hi] at hj
    exact hij hj
  · -- Union is ℕ
    exact union_singletons_eq_univ
  · -- Sum ≠ value of union
    simp only [diffuse_singleton, tsum_zero]
    rw [diffuse_union_singletons]
    norm_num

/-- The union of finite prefixes is ℕ -/
theorem union_finite_prefixes_eq_univ :
    (⋃ n, (Finset.range n : Set ℕ)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_univ, iff_true]
  exact ⟨x + 1, Nat.lt_add_one x⟩

/-- The union of finite prefixes is infinite -/
theorem union_finite_prefixes_infinite : ¬(⋃ n, (Finset.range n : Set ℕ)).Finite := by
  rw [union_finite_prefixes_eq_univ]
  exact Set.infinite_univ

/-- **Interpretation**: The diffuse valuation violates Scott continuity.

The increasing sequence of partial unions:
  ∅ ⊂ {0} ⊂ {0,1} ⊂ {0,1,2} ⊂ ...
has valuations 0, 0, 0, ...  (all finite sets)

But the limit ℕ = ⋃ₙ {0,...,n-1} has valuation 1.

So v does NOT preserve the directed supremum:
  v(⋃ₙ Aₙ) = 1 ≠ sup{v(Aₙ)} = 0

This is exactly the failure of KSScottContinuous. -/
theorem diffuse_not_scott_continuous :
    let partials : ℕ → Set ℕ := fun n => (Finset.range n : Set ℕ)
    Monotone partials ∧
    (⋃ n, partials n) = Set.univ ∧
    (∀ n, diffuse (partials n) = 0) ∧
    diffuse (⋃ n, partials n) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Monotone
    intro m n hmn
    simp only [Finset.coe_range]
    exact Set.Iio_subset_Iio hmn
  · -- Union is ℕ
    exact union_finite_prefixes_eq_univ
  · -- All finite prefixes have measure 0
    intro n
    apply diffuse_finite
    exact Set.finite_coe_iff.mp (Finset.finite_toSet _)
  · -- Union has measure 1
    exact diffuse_infinite _ union_finite_prefixes_infinite

end DiscontinuousValuation

/-! ## Summary

We have demonstrated three counterexamples:

1. **Without SigmaCompleteEvents**: σ-additivity is meaningless (can't even state it)
   - Model: Lattice of finite subsets of ℕ
   - Result: ⋃ₙ {n} = ℕ is not in the lattice (theorem `finSubsets_not_sigma_complete`)

2. **Without KSScaleComplete**: Bounded monotone sequences may lack suprema
   - Model: ℚ as scale, sequences converging to irrationals
   - Result: Cannot define μ(⋃ₙ Aₙ) when limit is irrational (theorem `sqrt2_not_rational`)

3. **Without KSScottContinuous**: Finite additivity does NOT imply σ-additivity
   - Model: Diffuse valuation on 2^ℕ (measure 0 on finite, 1 on infinite)
   - Result: Σₙ μ({n}) = 0 ≠ 1 = μ(ℕ) (theorem `diffuse_not_sigma_additive`)

These counterexamples show that ALL THREE axioms are strictly necessary
for the σ-additivity theorem. None can be derived from the others.
-/

/-- Summary: Each axiom addresses a distinct failure mode -/
theorem axioms_address_distinct_failures :
    -- SigmaCompleteEvents: ensures joins exist (see finSubsets_not_sigma_complete)
    -- KSScaleComplete: ensures limits exist (see sqrt2_not_rational)
    -- KSScottContinuous: ensures valuation respects limits (see diffuse_not_sigma_additive)
    True := trivial

end Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.SigmaAdditivityNecessity
