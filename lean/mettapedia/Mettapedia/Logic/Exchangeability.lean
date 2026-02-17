import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Choose.Basic
import Mettapedia.Logic.EvidenceCounts

/-!
# Exchangeability for Binary Sequences

This file defines exchangeability for sequences of binary random variables, a key concept
for connecting PLN Evidence to de Finetti's representation theorem.

## The Core Insight (from νPLN via de Finetti)

An infinite sequence of binary random variables is **exchangeable** if and only if it can be
represented as a mixture of i.i.d. Bernoulli sequences (de Finetti's theorem).

This means for exchangeable binary data:
- **Counts (n⁺, n⁻) are sufficient statistics** - order doesn't matter!
- PLN Evidence = (n⁺, n⁻) is exactly what captures all relevant information
- PLN strength n⁺/(n⁺+n⁻) = Beta posterior mean (with uniform prior)

## Main Definitions

* `FiniteExchangeable` : Finite sequence where any permutation has same probability
* `InfiniteExchangeable` : Infinite sequence where all finite prefixes are exchangeable
* `countTrue` : Count of true values in a sequence
* `countFalse` : Count of false values in a sequence

## Main Theorems

* `finiteExchangeable_perm_invariant` : Explicit permutation invariance
* `exchangeable_depends_on_counts` : Probability depends only on (n⁺, n⁻)
* `exchangeable_same_counts_same_prob` : Sequences with same counts have same probability

## References

- de Finetti, B. (1931). "Funzione caratteristica di un fenomeno aleatorio"
- Hewitt & Savage (1955). "Symmetric measures on Cartesian products"
- Aldous, D. (1985). "Exchangeability and related topics"
- Goertzel et al., PLN and νPLN documents

-/

namespace Mettapedia.Logic.Exchangeability

open MeasureTheory Finset BigOperators

/-! ## Counting Functions for Binary Sequences -/

section Counting

variable {n : ℕ}

/-- Count of true values in a finite binary sequence -/
def countTrue (X : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => X i = true)).card

/-- Count of false values in a finite binary sequence -/
def countFalse (X : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => X i = false)).card

/-- The counts partition n -/
theorem count_partition (X : Fin n → Bool) : countTrue X + countFalse X = n := by
  unfold countTrue countFalse
  have h1 : (univ.filter (fun i => X i = true)) ∪ (univ.filter (fun i => X i = false)) = univ := by
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and]
    cases X i <;> simp
  have h2 : (univ.filter (fun i => X i = true)) ∩ (univ.filter (fun i => X i = false)) = ∅ := by
    ext i
    simp only [mem_inter, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro htrue hfalse
    rw [htrue] at hfalse
    exact Bool.false_ne_true hfalse.symm
  rw [← card_union_of_disjoint (disjoint_iff_inter_eq_empty.mpr h2)]
  rw [h1]
  exact Fintype.card_fin n

/-- Applying a permutation preserves the count of true values -/
theorem countTrue_perm (X : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    countTrue (X ∘ σ) = countTrue X := by
  unfold countTrue
  -- The filter {i | X(σ i) = true} has same cardinality as {i | X i = true}
  -- because σ is a bijection
  have h : (univ.filter (fun i => (X ∘ σ) i = true)).card =
           (univ.filter (fun i => X i = true)).card := by
    apply Finset.card_bij (fun i _ => σ i)
    · intro i hi
      simp only [Function.comp_apply, mem_filter, mem_univ, true_and] at hi ⊢
      exact hi
    · intro i₁ _ i₂ _ heq
      exact σ.injective heq
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      refine ⟨σ.symm j, ?_, ?_⟩
      · simp only [Function.comp_apply, mem_filter, mem_univ, true_and, Equiv.apply_symm_apply]
        exact hj
      · exact Equiv.apply_symm_apply σ j
  exact h

/-- Applying a permutation preserves the count of false values -/
theorem countFalse_perm (X : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    countFalse (X ∘ σ) = countFalse X := by
  -- Both sides count n - countTrue
  have h1 := count_partition X
  have h2 := count_partition (X ∘ σ)
  rw [countTrue_perm X σ] at h2
  omega

end Counting

/-! ## Finite Exchangeability -/

section FiniteExchangeable

/-- A probability distribution P on finite binary sequences satisfies finite exchangeability
    if for all permutations σ, the probability of any sequence equals the probability of
    its permuted version.

    Formally: P({ω | X(ω) = vals}) = P({ω | X∘σ(ω) = vals}) for all σ, vals
-/
structure FiniteExchangeable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (X : Fin n → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop where
  /-- The distribution is invariant under permutations -/
  perm_invariant : ∀ (σ : Equiv.Perm (Fin n)) (vals : Fin n → Bool),
    μ {ω | ∀ i, X i ω = vals i} = μ {ω | ∀ i, X (σ i) ω = vals i}

/-- Alternative characterization: permuting the values gives same probability.

    For an exchangeable sequence, P(X = vals) = P(X = vals ∘ σ.symm) for any permutation σ.
    This is because exchangeability says the joint distribution is permutation-invariant.
-/
theorem finiteExchangeable_perm_values {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin n → Ω → Bool} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : FiniteExchangeable n X μ) (σ : Equiv.Perm (Fin n)) (vals : Fin n → Bool) :
    μ {ω | ∀ i, X i ω = vals i} = μ {ω | ∀ i, X i ω = vals (σ.symm i)} := by
  -- perm_invariant gives: μ {ω | ∀ i, X i ω = vals' i} = μ {ω | ∀ i, X (σ i) ω = vals' i}
  -- We use vals' = vals and reindex the RHS
  have key := h.perm_invariant σ vals
  -- key : μ {ω | ∀ i, X i ω = vals i} = μ {ω | ∀ i, X (σ i) ω = vals i}
  rw [key]
  -- Now show: μ {ω | ∀ i, X (σ i) ω = vals i} = μ {ω | ∀ i, X i ω = vals (σ.symm i)}
  -- These are the same set: substitute j = σ i, so i = σ.symm j
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h' i
  · -- h' : ∀ i, X (σ i) ω = vals i, need X i ω = vals (σ.symm i)
    have := h' (σ.symm i)
    simp only [Equiv.apply_symm_apply] at this
    exact this
  · -- h' : ∀ i, X i ω = vals (σ.symm i), need X (σ i) ω = vals i
    have := h' (σ i)
    simp only [Equiv.symm_apply_apply] at this
    exact this

end FiniteExchangeable

/-! ## Probability Depends Only on Counts -/

section DependsOnCounts

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ} (X : Fin n → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Key observation: two sequences with the same counts can be related by a permutation.

    This is a standard combinatorial fact: if two 0-1 vectors have the same number of 1s,
    there exists a permutation mapping one to the other.
-/
theorem same_counts_exists_perm (vals₁ vals₂ : Fin n → Bool)
    (h : countTrue vals₁ = countTrue vals₂) :
    ∃ σ : Equiv.Perm (Fin n), vals₂ = vals₁ ∘ σ := by
  classical
  -- Rephrase "same number of `true`s" as "same cardinality of the subtype `{i // vals i = true}`",
  -- then build a permutation by transporting along the canonical `sumCompl` decomposition.
  let p₁ : Fin n → Prop := fun i => vals₁ i = true
  let p₂ : Fin n → Prop := fun i => vals₂ i = true

  have card_true :
      Fintype.card { i : Fin n // p₂ i } = Fintype.card { i : Fin n // p₁ i } := by
    -- `countTrue` is exactly the cardinality of the `true`-positions.
    have h₁ :
        Fintype.card { i : Fin n // p₁ i } = countTrue vals₁ := by
      simpa [p₁, countTrue] using (Fintype.card_subtype (α := Fin n) (p := p₁))
    have h₂ :
        Fintype.card { i : Fin n // p₂ i } = countTrue vals₂ := by
      simpa [p₂, countTrue] using (Fintype.card_subtype (α := Fin n) (p := p₂))
    -- Flip `h` as needed to align sides.
    calc
      Fintype.card { i : Fin n // p₂ i }
          = countTrue vals₂ := by simp [h₂]
      _   = countTrue vals₁ := by simpa using h.symm
      _   = Fintype.card { i : Fin n // p₁ i } := by simp [h₁]

  have card_false :
      Fintype.card { i : Fin n // ¬ p₂ i } = Fintype.card { i : Fin n // ¬ p₁ i } := by
    -- Complements have the remaining cardinality.
    have h₁ :
        Fintype.card { i : Fin n // ¬ p₁ i } =
          Fintype.card (Fin n) - Fintype.card { i : Fin n // p₁ i } := by
      simpa [p₁] using (Fintype.card_subtype_compl (α := Fin n) (p := p₁))
    have h₂ :
        Fintype.card { i : Fin n // ¬ p₂ i } =
          Fintype.card (Fin n) - Fintype.card { i : Fin n // p₂ i } := by
      simpa [p₂] using (Fintype.card_subtype_compl (α := Fin n) (p := p₂))
    -- Rewrite both sides via `h₁`/`h₂` and use `card_true`.
    calc
      Fintype.card { i : Fin n // ¬ p₂ i }
          = Fintype.card (Fin n) - Fintype.card { i : Fin n // p₂ i } := by
              simp [h₂]
      _   = Fintype.card (Fin n) - Fintype.card { i : Fin n // p₁ i } := by
              simp [card_true]
      _   = Fintype.card { i : Fin n // ¬ p₁ i } := by
              simp [h₁]

  let eT : { i : Fin n // p₂ i } ≃ { i : Fin n // p₁ i } :=
    Fintype.equivOfCardEq card_true
  let eF : { i : Fin n // ¬ p₂ i } ≃ { i : Fin n // ¬ p₁ i } :=
    Fintype.equivOfCardEq card_false

  -- Combine the equivalences on the `true` and `false` indices into a permutation of `Fin n`.
  let σ : Equiv.Perm (Fin n) :=
    (Equiv.sumCompl p₂).symm.trans ((Equiv.sumCongr eT eF).trans (Equiv.sumCompl p₁))

  refine ⟨σ, ?_⟩
  ext i
  by_cases hi : p₂ i
  · -- `i` is a `true` position in `vals₂`; `σ i` lands in a `true` position of `vals₁`.
    have : p₁ (σ i) := by
      -- `eT` lands in the `p₁` subtype, so its `.2` field is exactly the desired fact.
      simpa [σ, hi, p₁, p₂] using (eT ⟨i, hi⟩).2
    -- Turn the Prop fact `p₁ (σ i)` into a Bool equality.
    simpa [p₂, hi] using this.symm
  · -- `i` is a `false` position in `vals₂`; `σ i` lands in a `false` position of `vals₁`.
    have hσ : ¬ p₁ (σ i) := by
      simpa [σ, hi, p₁, p₂] using (eF ⟨i, hi⟩).2
    have hvals₁ : vals₁ (σ i) = false := Bool.eq_false_iff.mpr hσ
    have hvals₂ : vals₂ i = false := Bool.eq_false_iff.mpr hi
    simp [hvals₂, hvals₁]

/-- Main theorem: For exchangeable sequences, probability depends only on counts.

    If X is exchangeable and we know the count of true values (k), then there exists
    a function f such that P(countTrue X = k) = f(k).

    More precisely: any two sequences with the same counts have the same probability.
-/
theorem exchangeable_same_counts_same_prob
    (hexch : FiniteExchangeable n X μ)
    (vals₁ vals₂ : Fin n → Bool)
    (hcount : countTrue vals₁ = countTrue vals₂) :
    μ {ω | ∀ i, X i ω = vals₁ i} = μ {ω | ∀ i, X i ω = vals₂ i} := by
  -- Since countTrue vals₁ = countTrue vals₂, there exists σ with vals₂ = vals₁ ∘ σ
  obtain ⟨σ, hσ⟩ := same_counts_exists_perm vals₁ vals₂ hcount
  rw [hσ]
  -- Now use exchangeability
  exact finiteExchangeable_perm_values hexch σ.symm vals₁

/-- Corollary: The probability of k successes in n trials only depends on k.

    This justifies why PLN Evidence (n⁺, n⁻) = (k, n-k) captures all relevant information
    about exchangeable binary observations.
-/
theorem exchangeable_prob_only_depends_on_k
    (hexch : FiniteExchangeable n X μ)
    (k : ℕ) (_hk : k ≤ n)
    (vals₁ vals₂ : Fin n → Bool)
    (h₁ : countTrue vals₁ = k)
    (h₂ : countTrue vals₂ = k) :
    μ {ω | ∀ i, X i ω = vals₁ i} = μ {ω | ∀ i, X i ω = vals₂ i} := by
  exact exchangeable_same_counts_same_prob X μ hexch vals₁ vals₂ (h₁.trans h₂.symm)

end DependsOnCounts

/-! ## Sufficient Statistics -/

section SufficientStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ} (X : Fin n → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The count statistic for a binary sequence -/
def countStatistic (X : Fin n → Ω → Bool) : Ω → ℕ × ℕ :=
  fun ω => (countTrue (fun i => X i ω), countFalse (fun i => X i ω))

/-- Informal statement: (countTrue, countFalse) is a sufficient statistic for exchangeable binary.

    This means: given the counts, the conditional distribution is uniform over all
    sequences with those counts. This is the precise sense in which PLN Evidence
    (n⁺, n⁻) captures "all the information" for exchangeable observations.
-/
theorem counts_sufficient_informal
    (hexch : FiniteExchangeable n X μ)
    (vals : Fin n → Bool)
    (k : ℕ) (hk : countTrue vals = k) :
    -- All sequences with k successes have the same probability
    ∀ vals' : Fin n → Bool, countTrue vals' = k →
      μ {ω | ∀ i, X i ω = vals i} = μ {ω | ∀ i, X i ω = vals' i} := by
  intro vals' hk'
  exact exchangeable_same_counts_same_prob X μ hexch vals vals' (hk.trans hk'.symm)

/-- The number of sequences with exactly k true values -/
def numSequencesWithKTrue (n k : ℕ) : ℕ := n.choose k

/- For exchangeable binary, each specific sequence with k successes has probability
   P(k successes) / (n choose k).

   TODO: prove this by:
   1) using `exchangeable_same_counts_same_prob` to show all sequences with `k` trues have
      the same probability, and
   2) partitioning the event `{ω | countTrue (fun i => X i ω) = k}` into the disjoint union
      over these sequences, so the measure is `(n.choose k) * p`.
-/

end SufficientStatistics

/-! ## Infinite Exchangeability -/

section InfiniteExchangeable

/-- An infinite sequence of binary random variables is exchangeable if all finite
    initial segments are finitely exchangeable.

    By de Finetti's theorem, this is equivalent to being a mixture of i.i.d. Bernoulli.
-/
structure InfiniteExchangeable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop where
  /-- Every finite initial segment is exchangeable -/
  finite_segments : ∀ n : ℕ,
    FiniteExchangeable n (fun i : Fin n => X i.val) μ

/-- Extendability: infinite exchangeability implies each finite prefix is exchangeable -/
theorem infinite_exchangeable_finite_prefix {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Bool} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : InfiniteExchangeable X μ) (n : ℕ) :
    FiniteExchangeable n (fun i : Fin n => X i.val) μ :=
  h.finite_segments n

end InfiniteExchangeable

/-! ## Connection to PLN Evidence -/

section PLNConnection

/-- Given n observations with k positive and (n-k) negative, the PLN Evidence is (k, n-k).

    This is exactly the sufficient statistic for exchangeable binary observations.
-/
def evidenceFromCounts (n_pos n_neg : ℕ) : ℕ × ℕ := (n_pos, n_neg)

/-- The PLN strength is k/(k + (n-k)) = k/n.

    For exchangeable binary data with Beta(1,1) prior (uniform), this is exactly
    the posterior mean.
-/
noncomputable abbrev strengthFromCounts (n_pos n_neg : ℕ) : ℝ :=
  Mettapedia.Logic.EvidenceCounts.plnStrength n_pos n_neg

/-- With Jeffreys prior Beta(1/2, 1/2), the posterior mean is (k + 1/2)/(n + 1) -/
noncomputable abbrev jeffreysPosteriorMean (n_pos n_neg : ℕ) : ℝ :=
  Mettapedia.Logic.EvidenceCounts.jeffreysPosteriorMean n_pos n_neg

/- TODO: PLN strength vs Beta posterior mean.

   This is proved (with explicit bounds) in `Mettapedia.Logic.EvidenceBeta` for the uniform prior.
-/

/- TODO: main νPLN connection theorem.

   This is currently developed in `Mettapedia.Logic.DeFinetti` and `Mettapedia.Logic.EvidenceBeta`.
-/

end PLNConnection

end Mettapedia.Logic.Exchangeability
