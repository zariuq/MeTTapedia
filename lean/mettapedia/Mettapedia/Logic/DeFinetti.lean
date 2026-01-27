import Mettapedia.Logic.Exchangeability
import Mettapedia.Logic.EvidenceBeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# De Finetti's Representation Theorem

This file formalizes de Finetti's theorem: an infinite exchangeable binary sequence
can be represented as a mixture of i.i.d. Bernoulli sequences.

## The Core Theorem

**De Finetti's Theorem** (1931): If (X₁, X₂, X₃, ...) is an infinite exchangeable
sequence of binary random variables, then there exists a probability measure μ on [0,1]
such that:

  P(X₁ = x₁, ..., Xₙ = xₙ) = ∫₀¹ θ^k (1-θ)^(n-k) dμ(θ)

where k = #{i : xᵢ = 1}.

## Implications for PLN

1. **Sufficient Statistics**: The counts (k, n-k) capture all information
2. **Beta-Bernoulli**: With Beta prior on θ, posterior is Beta(α+k, β+n-k)
3. **PLN Evidence**: (n⁺, n⁻) = (k, n-k) is exactly the sufficient statistic

## Main Definitions

* `BernoulliMixture` : A mixture of Bernoulli distributions
* `deFinettiRepresentation` : The mixing measure μ for an exchangeable sequence

## Main Theorems

* `deFinetti_finite` : Finite version (approximate representation)
* `deFinetti_infinite` : Full infinite version
* `exchangeable_iff_bernoulli_mixture` : Characterization theorem

## References

- de Finetti, B. (1931). "Funzione caratteristica di un fenomeno aleatorio"
- Hewitt & Savage (1955). "Symmetric measures on Cartesian products"
- Diaconis & Freedman (1980). "Finite Exchangeable Sequences"
- [McCall 2004](https://onlinelibrary.wiley.com/doi/abs/10.1111/j.0026-1386.2004.00190.x)

-/

namespace Mettapedia.Logic.DeFinetti

open MeasureTheory Finset BigOperators ENNReal
open scoped BigOperators
open Mettapedia.Logic.Exchangeability
open Mettapedia.Logic.EvidenceBeta

/-! ## Bernoulli Distribution -/

section Bernoulli

/-- Bernoulli probability mass function: P(X = true) = θ, P(X = false) = 1 - θ -/
noncomputable def bernoulliPMF (θ : ℝ) (x : Bool) : ℝ :=
  if x then θ else 1 - θ

/-- Product of Bernoulli PMFs for a sequence -/
noncomputable def bernoulliProductPMF {n : ℕ} (θ : ℝ) (xs : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, bernoulliPMF θ (xs i)

/-- The product simplifies to θ^k (1-θ)^(n-k) where k = count of true values -/
theorem bernoulliProductPMF_eq_power {n : ℕ} (θ : ℝ) (xs : Fin n → Bool) :
    bernoulliProductPMF θ xs = θ ^ (countTrue xs) * (1 - θ) ^ (countFalse xs) := by
  classical
  unfold bernoulliProductPMF bernoulliPMF countTrue countFalse
  -- Split the product over indices where `xs i = true` and where `xs i = false`.
  set sTrue : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => xs i = true)
  set sFalse : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => xs i = false)
  have hsFalse :
      (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => ¬ (xs i = true)) = sFalse := by
    ext i
    cases xs i <;> simp [sFalse]
  have hsplit :
      (∏ i : Fin n, (if xs i then θ else 1 - θ)) =
        (∏ i ∈ sTrue, (if xs i then θ else 1 - θ)) * ∏ i ∈ sFalse, (if xs i then θ else 1 - θ) := by
    have h :=
      (Finset.prod_filter_mul_prod_filter_not
          (s := (Finset.univ : Finset (Fin n)))
          (p := fun i : Fin n => xs i = true)
          (f := fun i : Fin n => if xs i then θ else 1 - θ)).symm
    simpa [sTrue, sFalse, hsFalse] using h
  have hTrue :
      (∏ i ∈ sTrue, (if xs i then θ else 1 - θ)) = θ ^ sTrue.card := by
    refine Finset.prod_eq_pow_card (s := sTrue) (f := fun i : Fin n => if xs i then θ else 1 - θ)
      (b := θ) ?_
    intro i hi
    have hxi : xs i = true := by
      simpa [sTrue] using hi
    simp [hxi]
  have hFalse :
      (∏ i ∈ sFalse, (if xs i then θ else 1 - θ)) = (1 - θ) ^ sFalse.card := by
    refine Finset.prod_eq_pow_card (s := sFalse) (f := fun i : Fin n => if xs i then θ else 1 - θ)
      (b := 1 - θ) ?_
    intro i hi
    have hxi : xs i = false := by
      simpa [sFalse] using hi
    simp [hxi]
  calc
    (∏ i : Fin n, (if xs i then θ else 1 - θ))
        = (∏ i ∈ sTrue, (if xs i then θ else 1 - θ)) * ∏ i ∈ sFalse, (if xs i then θ else 1 - θ) := by
          simpa using hsplit
    _ = θ ^ sTrue.card * (1 - θ) ^ sFalse.card := by
          simp [hTrue, hFalse]

end Bernoulli

/-! ## Mixture Distributions -/

section Mixture

/-- A Bernoulli mixture is a probability distribution on binary sequences
    defined by integrating Bernoulli products against a mixing measure μ on [0,1]. -/
structure BernoulliMixture where
  /-- The mixing measure on [0,1] -/
  mixingMeasure : Measure ℝ
  /-- The mixing measure is a probability measure -/
  isProbability : IsProbabilityMeasure mixingMeasure
  /-- The mixing measure is supported on [0,1] -/
  support_unit : mixingMeasure (Set.Icc 0 1)ᶜ = 0

namespace BernoulliMixture

/-- The probability of a specific binary sequence under a Bernoulli mixture -/
noncomputable def prob {n : ℕ} (M : BernoulliMixture) (xs : Fin n → Bool) : ℝ :=
  ∫ θ in Set.Icc 0 1, bernoulliProductPMF θ xs ∂M.mixingMeasure

/-- The probability of k successes in n trials under a Bernoulli mixture -/
noncomputable def probKSuccesses (M : BernoulliMixture) (n k : ℕ) : ℝ :=
  ∫ θ in Set.Icc 0 1, (n.choose k : ℝ) * θ ^ k * (1 - θ) ^ (n - k) ∂M.mixingMeasure

/-- Key property: probability depends only on counts, not order -/
theorem prob_depends_only_on_counts {n : ℕ} (M : BernoulliMixture)
    (xs₁ xs₂ : Fin n → Bool) (h : countTrue xs₁ = countTrue xs₂) :
    M.prob xs₁ = M.prob xs₂ := by
  unfold prob
  -- Both integrands are equal by `bernoulliProductPMF_eq_power` and count equality.
  have hfalse : countFalse xs₁ = countFalse xs₂ := by
    have h₁ := (count_partition (n := n) xs₁)
    have h₂ := (count_partition (n := n) xs₂)
    have h₁' : countTrue xs₂ + countFalse xs₁ = n := by
      simpa [h] using h₁
    have : countTrue xs₂ + countFalse xs₁ = countTrue xs₂ + countFalse xs₂ := by
      exact h₁'.trans h₂.symm
    exact Nat.add_left_cancel this
  have hintegrand :
      (fun θ : ℝ => bernoulliProductPMF θ xs₁) =
        fun θ : ℝ => bernoulliProductPMF θ xs₂ := by
    funext θ
    simp [bernoulliProductPMF_eq_power, h, hfalse]
  simp [hintegrand]

end BernoulliMixture

end Mixture

/-! ## De Finetti's Theorem -/

section DeFinetti

variable {Ω : Type*} [MeasurableSpace Ω]

/-- De Finetti's theorem (finite version):

    For a finitely exchangeable binary sequence of length n, the joint distribution
    is approximately a Bernoulli mixture, with error O(k/n) where k is fixed.

    Reference: Diaconis & Freedman (1980)
-/
theorem deFinetti_finite {n : ℕ} (X : Fin n → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hexch : FiniteExchangeable n X μ) :
    -- Finite de Finetti (exact, count-based form): exchangeability implies the
    -- probability of a sequence depends only on its number of `true`s.
    ∀ (xs₁ xs₂ : Fin n → Bool), countTrue xs₁ = countTrue xs₂ →
      μ {ω | ∀ i, X i ω = xs₁ i} = μ {ω | ∀ i, X i ω = xs₂ i} := by
  intro xs₁ xs₂ hcount
  exact exchangeable_same_counts_same_prob X μ hexch xs₁ xs₂ hcount

/-! ### A Derived Consequence: Infinite Exchangeability ⇒ Count Invariance

For our νPLN development, the key usable consequence of exchangeability is that finite-prefix
probabilities depend only on the number of `true` values, i.e. on the sufficient statistics
`(n⁺, n⁻)`.

This lemma is a direct corollary of `InfiniteExchangeable.finite_segments` plus the finite result.
-/
theorem infiniteExchangeable_same_counts_same_prob (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hexch : InfiniteExchangeable X μ) {n : ℕ}
    (xs₁ xs₂ : Fin n → Bool) (hcount : countTrue xs₁ = countTrue xs₂) :
    μ {ω | ∀ i : Fin n, X i.val ω = xs₁ i} = μ {ω | ∀ i : Fin n, X i.val ω = xs₂ i} := by
  have hexch' : FiniteExchangeable n (fun i : Fin n => X i.val) μ :=
    hexch.finite_segments n
  exact exchangeable_same_counts_same_prob (fun i : Fin n => X i.val) μ hexch' xs₁ xs₂ hcount

/-! ### Kirsch's Elementary Proof Components

We follow the elementary proof of de Finetti's theorem from Kirsch (2018), arXiv:1809.00882.
The proof uses the method of moments rather than martingale convergence.

**Key Ideas:**
1. For measures on [0,1], moments determine the measure (Hausdorff moment problem)
2. The k-th moment of the de Finetti measure equals E[X₁ · X₂ · ... · Xₖ]
3. Exchangeability + idempotence (X² = X for {0,1}-valued) simplifies counting
4. "Collision" terms where ρ(i₁,...,iₖ) < k vanish as N → ∞

Reference: W. Kirsch, "An elementary proof of de Finetti's Theorem", arXiv:1809.00882 (2018)
-/

/-- The number of distinct elements in a k-tuple of indices (Kirsch's ρ function) -/
def numDistinct {k : ℕ} (indices : Fin k → ℕ) : ℕ :=
  (Finset.univ.image indices).card

/- Kirsch's Corollary 7: For `{0,1}`-valued exchangeable sequences,
   `E[X_{i₁} · ... · X_{iₖ}] = E[X₁ · ... · Xᵣ]` where `r` is the number of
   distinct indices.

   This uses:
   - `X² = X` for `{0,1}`-valued random variables
   - Exchangeability to reindex to the first `r` indices
-/
/- NOTE: Kirsch's Corollary 7 is the statement that for exchangeable `{0,1}`-valued sequences,
`P(∀ j ∈ S, X_j = 1)` depends only on `|S|`.  We do **not** use it directly in this file yet;
instead, we will prove the specific finite-difference identities we need for Hausdorff/de Finetti
in the sections below. -/

/-- Kirsch's Lemma 8: For exchangeable {0,1}-valued sequences, the probability of a specific
    pattern with m ones in k positions equals (1/C(k,m)) × P(sum of first k = m).

    This is a direct consequence of exchangeability: all patterns with the same number
    of ones have equal probability, and there are C(k,m) such patterns.
-/
theorem lemma8_uniform_given_count {k : ℕ} (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hexch : InfiniteExchangeable X μ)
    (xs₁ xs₂ : Fin k → Bool) (hcount : countTrue xs₁ = countTrue xs₂) :
    μ {ω | ∀ i : Fin k, X i.val ω = xs₁ i} = μ {ω | ∀ i : Fin k, X i.val ω = xs₂ i} := by
  exact infiniteExchangeable_same_counts_same_prob X μ hexch xs₁ xs₂ hcount

/-! ### Cylinder Patterns -/

/-- The cylinder event associated to a finite Boolean pattern `xs` (viewed as the first `n` bits). -/
def cyl {n : ℕ} (X : ℕ → Ω → Bool) (xs : Fin n → Bool) : Set Ω :=
  {ω | ∀ i : Fin n, X i.val ω = xs i}

/-- The canonical pattern consisting of `k` `true`s followed by `n` `false`s. -/
def onesThenZeros (k n : ℕ) : Fin (k + n) → Bool :=
  Fin.append (fun _ : Fin k => true) (fun _ : Fin n => false)

/-- The canonical pattern consisting of `n` `false`s followed by `k` `true`s. -/
def zerosThenOnes (n k : ℕ) : Fin (n + k) → Bool :=
  Fin.append (fun _ : Fin n => false) (fun _ : Fin k => true)

/-- The canonical pattern consisting of `n` `false`s, then `k` `true`s, then a final `false`. -/
def zerosThenOnesThenZero (n k : ℕ) : Fin (n + k + 1) → Bool :=
  Fin.append (zerosThenOnes n k) (fun _ : Fin 1 => false)

/-- Cylinder events are measurable when all coordinates `X i` are measurable. -/
theorem measurableSet_cyl {n : ℕ} (X : ℕ → Ω → Bool)
    (hX : ∀ i : ℕ, Measurable (X i)) (xs : Fin n → Bool) :
    MeasurableSet (cyl X xs) := by
  classical
  -- Rewrite the `∀ i` constraint as an intersection of measurable preimages.
  have hrepr :
      cyl X xs = ⋂ i : Fin n, X i.val ⁻¹' ({xs i} : Set Bool) := by
    ext ω
    simp [cyl]
  -- Each individual constraint is measurable since `Bool` is discrete/measurable.
  have hmeas : ∀ i : Fin n, MeasurableSet (X i.val ⁻¹' ({xs i} : Set Bool)) := by
    intro i
    exact measurableSet_preimage (hX i.val) (measurableSet_singleton (xs i))
  simpa [hrepr] using MeasurableSet.iInter hmeas

/-! ### Counting Lemmas for Canonical Patterns -/

@[simp]
lemma countTrue_const_true (n : ℕ) : countTrue (fun _ : Fin n => true) = n := by
  simp [countTrue]

@[simp]
lemma countTrue_const_false (n : ℕ) : countTrue (fun _ : Fin n => false) = 0 := by
  simp [countTrue]

/-- `countTrue` respects `Fin.append`. -/
theorem countTrue_append_fin {m n : ℕ} (a : Fin m → Bool) (b : Fin n → Bool) :
    countTrue (Fin.append a b) = countTrue a + countTrue b := by
  classical
  -- Convert `countTrue` to subtype cardinals, split using `finSumFinEquiv`,
  -- and convert back.
  have hAppend :
      Fintype.card { i : Fin (m + n) // Fin.append a b i = true } = countTrue (Fin.append a b) := by
    simpa [countTrue] using
      (Fintype.card_subtype (α := Fin (m + n)) (p := fun i => Fin.append a b i = true))
  have hA : Fintype.card { i : Fin m // a i = true } = countTrue a := by
    simpa [countTrue] using (Fintype.card_subtype (α := Fin m) (p := fun i => a i = true))
  have hB : Fintype.card { i : Fin n // b i = true } = countTrue b := by
    simpa [countTrue] using (Fintype.card_subtype (α := Fin n) (p := fun i => b i = true))

  let pSum : Fin m ⊕ Fin n → Prop :=
    Sum.elim (fun i : Fin m => a i = true) (fun j : Fin n => b j = true)

  have eSum :
      { x : Fin m ⊕ Fin n // pSum x } ≃ ({i : Fin m // a i = true} ⊕ {j : Fin n // b j = true}) := by
    refine
      { toFun := fun x => ?_,
        invFun := fun y => ?_,
        left_inv := ?_,
        right_inv := ?_ }
    · rcases x with ⟨x, hx⟩
      cases x with
      | inl i => exact Sum.inl ⟨i, hx⟩
      | inr j => exact Sum.inr ⟨j, hx⟩
    · cases y with
      | inl i => exact ⟨Sum.inl i.1, i.2⟩
      | inr j => exact ⟨Sum.inr j.1, j.2⟩
    · rintro ⟨x, hx⟩
      cases x <;> rfl
    · intro y
      cases y <;> rfl

  have cardSumSubtype :
      Fintype.card { x : Fin m ⊕ Fin n // pSum x }
        = Fintype.card { i : Fin m // a i = true } + Fintype.card { j : Fin n // b j = true } := by
    calc
      Fintype.card { x : Fin m ⊕ Fin n // pSum x }
          = Fintype.card ({i : Fin m // a i = true} ⊕ {j : Fin n // b j = true}) := by
              simpa using (Fintype.card_congr eSum)
      _ = Fintype.card { i : Fin m // a i = true } + Fintype.card { j : Fin n // b j = true } := by
            simpa using (Fintype.card_sum ({i : Fin m // a i = true}) ({j : Fin n // b j = true}))

  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv

  have hPred : ∀ x : Fin m ⊕ Fin n, pSum x ↔ (Fin.append a b (e x) = true) := by
    intro x
    cases x with
    | inl i =>
        simp [pSum, e, finSumFinEquiv, Fin.append]
    | inr j =>
        simp [pSum, e, finSumFinEquiv, Fin.append]

  let eSub :
      { x : Fin m ⊕ Fin n // pSum x } ≃ { i : Fin (m + n) // Fin.append a b i = true } :=
    e.subtypeEquiv (fun x => hPred x)

  have cardAppendSubtype :
      Fintype.card { i : Fin (m + n) // Fin.append a b i = true }
        = Fintype.card { x : Fin m ⊕ Fin n // pSum x } := by
    simpa using (Fintype.card_congr eSub.symm)

  have hCountTrue :
      countTrue (Fin.append a b) = Fintype.card { i : Fin (m + n) // Fin.append a b i = true } :=
    hAppend.symm

  calc
    countTrue (Fin.append a b)
        = Fintype.card { i : Fin (m + n) // Fin.append a b i = true } := hCountTrue
    _ = Fintype.card { x : Fin m ⊕ Fin n // pSum x } := by
          simpa [cardAppendSubtype]
    _ = Fintype.card { i : Fin m // a i = true } + Fintype.card { j : Fin n // b j = true } :=
          cardSumSubtype
    _ = countTrue a + countTrue b := by
          simpa [hA, hB]

@[simp]
lemma countTrue_zerosThenOnes (n k : ℕ) : countTrue (zerosThenOnes n k) = k := by
  simp [zerosThenOnes, countTrue_append_fin]

@[simp]
lemma countTrue_zerosThenOnesThenZero (n k : ℕ) :
    countTrue (zerosThenOnesThenZero n k) = k := by
  simp [zerosThenOnesThenZero, countTrue_append_fin]

/-! ### De Finetti Moment Sequence
 
For {0,1}-valued exchangeable X, define the moment sequence:
  mₖ = E[X₁ · X₂ · ... · Xₖ] = P(X₁ = 1, ..., Xₖ = 1)

This sequence satisfies:
- m₀ = 1 (probability measure)
- 0 ≤ mₖ ≤ 1 (it's a probability)
- mₖ₊₁ ≤ mₖ (more constraints can only reduce probability)

These are the moments of the de Finetti mixing measure.
-/

/-- The k-th de Finetti moment for an exchangeable binary sequence.
    This is E[X₁ · X₂ · ... · Xₖ] = P(X₁ = 1, ..., Xₖ = 1). -/
noncomputable def deFinettiMoment (X : ℕ → Ω → Bool) (μ : Measure Ω) (k : ℕ) : ℝ :=
  (μ {ω | ∀ i : Fin k, X i.val ω = true}).toReal

/-- The moment sequence is bounded in [0,1] -/
theorem deFinettiMoment_mem_unit_interval (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (k : ℕ) :
    deFinettiMoment X μ k ∈ Set.Icc 0 1 := by
  simp only [Set.mem_Icc, deFinettiMoment]
  constructor
  · exact ENNReal.toReal_nonneg
  · calc (μ {ω | ∀ i : Fin k, X i.val ω = true}).toReal
        ≤ (μ Set.univ).toReal := by
            apply ENNReal.toReal_mono (measure_ne_top _ _)
            exact measure_mono (Set.subset_univ _)
      _ = 1 := by simp [measure_univ]

/-- The moment sequence is decreasing -/
theorem deFinettiMoment_antitone (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    Antitone (deFinettiMoment X μ) := by
  intro m n hmn
  simp only [deFinettiMoment]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro i
  exact hω ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩

/-- The 0-th moment is 1 (for probability measures) -/
theorem deFinettiMoment_zero (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    deFinettiMoment X μ 0 = 1 := by
  simp only [deFinettiMoment]
  have h : {ω : Ω | ∀ i : Fin 0, X i.val ω = true} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro i
    exact Fin.elim0 i
  rw [h]
  simp [measure_univ]

/-! ### Complete Monotonicity

The de Finetti moments form a **completely monotone** sequence:
all finite differences are non-negative. This is the key property
that characterizes moment sequences of measures on [0,1] (Hausdorff).

For {0,1}-valued exchangeable X:
  Δⁿmₖ = E[(1-X₁)·...·(1-Xₙ)·Xₙ₊₁·...·Xₙ₊ₖ] ≥ 0

This is non-negative because it's an expectation of a product of
non-negative {0,1}-valued random variables.
-/

/-- Forward difference operator (in the Hausdorff convention): `Δ m k = m k - m (k+1)`. -/
def fwdDiff (m : ℕ → ℝ) : ℕ → ℝ :=
  fun k => m k - m (k + 1)

/-- Iterated forward differences `Δⁿ m` in the Hausdorff convention.

We define this via Mathlib's forward difference operator:
`_root_.fwdDiff (h := 1) m k = m (k+1) - m k`.
Our convention is the alternating-sign variant `m k - m (k+1)`, so we multiply by `(-1)^n`.
-/
def fwdDiffIter (n : ℕ) (m : ℕ → ℝ) : ℕ → ℝ :=
  fun k => ((-1 : ℝ) ^ n) * ((_root_.fwdDiff (h := (1 : ℕ)))^[n] m k)

/-- A sequence is *completely monotone* if all iterated forward differences are nonnegative. -/
def CompletelyMonotone (m : ℕ → ℝ) : Prop :=
  ∀ n k, 0 ≤ fwdDiffIter n m k

/-- Recurrence for Hausdorff forward differences:
`Δ^{n+1} m k = Δ^n m k - Δ^n m (k+1)`. -/
lemma fwdDiffIter_succ (m : ℕ → ℝ) (n k : ℕ) :
    fwdDiffIter (n + 1) m k = fwdDiffIter n m k - fwdDiffIter n m (k + 1) := by
  -- Unfold into Mathlib forward differences (`f (k+1) - f k`) and simplify signs.
  unfold fwdDiffIter
  -- Write `Δ := _root_.fwdDiff (h := 1)` and use the iterate-succ rule.
  simp [Function.iterate_succ_apply', _root_.fwdDiff, pow_succ, mul_assoc, mul_left_comm, mul_comm,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul]

/-- Simplify the alternating signs coming from the translation between conventions:
for `j ≤ n`, we have `(-1)^n * (-1)^(n-j) = (-1)^j`. -/
lemma neg_one_pow_mul_neg_one_pow_sub (n j : ℕ) (hj : j ≤ n) :
    ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ (n - j)) = (-1 : ℝ) ^ j := by
  -- Rewrite `n` as `j + (n-j)`, then cancel the duplicated factor using `(-1)^2 = 1`.
  have hn : n = j + (n - j) := (Nat.add_sub_of_le hj).symm
  calc
    ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ (n - j))
        = ((-1 : ℝ) ^ (j + (n - j))) * ((-1 : ℝ) ^ (n - j)) := by
            -- Avoid `simp` here (it can loop trying to simplify nested `Nat.sub`).
            have hpow : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (j + (n - j)) :=
              congrArg (fun t : ℕ => (-1 : ℝ) ^ t) hn
            rw [hpow]
    _ = (((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ (n - j))) * ((-1 : ℝ) ^ (n - j)) := by
          simp [pow_add, mul_assoc]
    _ = ((-1 : ℝ) ^ j) * (((-1 : ℝ) ^ (n - j)) * ((-1 : ℝ) ^ (n - j))) := by
          simp [mul_assoc]
    _ = ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ ((n - j) + (n - j))) := by
          simpa [pow_add, mul_assoc] using (pow_add (-1 : ℝ) (n - j) (n - j)).symm
    _ = ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ (2 * (n - j))) := by
          -- `a + a = 2*a`
          simpa [two_mul] using rfl
    _ = ((-1 : ℝ) ^ j) * ((((-1 : ℝ) ^ 2) ^ (n - j))) := by
          -- `(-1)^(2*(n-j)) = ((-1)^2)^(n-j)`
          simpa [pow_mul, mul_assoc]
    _ = (-1 : ℝ) ^ j := by
          simp [neg_one_sq]

/-- Closed form for iterated forward differences (binomial alternating sum). -/
theorem fwdDiffIter_eq_sum_choose (m : ℕ → ℝ) :
    ∀ n k, fwdDiffIter n m k =
      ∑ j ∈ Finset.range (n + 1), ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) * m (k + j) := by
  classical
  intro n k
  have h :=
    _root_.fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) (f := m) (n := n) (y := k)
  -- Push the outer `(-1)^n` inside the sum and simplify casts; the remaining work is the
  -- sign identity `(-1)^n * (-1)^(n-j) = (-1)^j`.
  simp [fwdDiffIter, h, Finset.mul_sum, nsmul_one, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, mul_assoc, mul_left_comm, mul_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp [neg_one_pow_mul_neg_one_pow_sub n j hjle, mul_assoc, mul_left_comm, mul_comm]

/-- The first finite difference of the de Finetti moments is non-negative:
    Δ¹mₖ = mₖ - mₖ₊₁ ≥ 0 -/
theorem deFinettiMoment_diff_nonneg (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (_hexch : InfiniteExchangeable X μ) (k : ℕ) :
    deFinettiMoment X μ (k + 1) ≤ deFinettiMoment X μ k :=
  deFinettiMoment_antitone X μ (Nat.le_succ k)

/-! ### Hausdorff Moment Theorem (Statement)

The following is the **Hausdorff moment theorem** restricted to our use case:
given a sequence (mₖ) that satisfies the properties of de Finetti moments
(bounded in [0,1], decreasing, m₀ = 1), there exists a probability measure
on [0,1] whose k-th moment is mₖ.

**Mathematical Background (Hausdorff 1921)**:
A sequence (aₖ)_{k≥0} is the moment sequence of a probability measure on [0,1]
if and only if it is "completely monotone", meaning:
  Δⁿaₖ := ∑_{j=0}^n (-1)^j C(n,j) a_{k+j} ≥ 0 for all n, k ≥ 0

For our de Finetti moments mₖ = E[X₁·...·Xₖ] from exchangeable binary X:
  Δⁿmₖ = E[(1-X₁)·...·(1-Xₙ)·X_{n+1}·...·X_{n+k}] ≥ 0
because it's an expectation of a product of non-negative random variables.

**Proof Approach** (not yet formalized):
1. Show (mₖ) is completely monotone using exchangeability
2. Define a linear functional Λ on polynomials: Λ(x^k) = mₖ
3. Show Λ is positive on positive polynomials (uses Bernstein representation)
4. Extend Λ to C[0,1] by density (Stone-Weierstrass)
5. Apply Riesz-Markov-Kakutani to get the measure

**Reference**: Kirsch (2018) arXiv:1809.00882, Proposition 2.1
-/

/-- **Hausdorff Moment Theorem (specialized)**:
    A sequence that is bounded in `[0,1]`, is completely monotone, and starts at `1`
    is the moment sequence of some probability measure on `[0,1]`.

    This is the key result needed for de Finetti's theorem.
    The full Hausdorff theorem characterizes such sequences as "completely monotone".

    **Current status**: Not formalized in Mathlib. This is the gap in `deFinetti_infinite`. -/
theorem hausdorff_moment_exists (m : ℕ → ℝ)
    (hbnd : ∀ k, m k ∈ Set.Icc 0 1)
    (hcm : CompletelyMonotone m)
    (hzero : m 0 = 1) :
    ∃ (μ : Measure ℝ), IsProbabilityMeasure μ ∧ μ (Set.Icc 0 1)ᶜ = 0 ∧
      ∀ k, ∫ θ in Set.Icc 0 1, θ ^ k ∂μ = m k := by
  -- The proof requires showing that (mₖ) being bounded, decreasing, and starting at 1
  -- implies it's completely monotone, which is equivalent to being moments of a measure.
  -- This involves:
  -- 1. Using complete monotonicity (`hcm`) to build a positive linear functional on polynomials
  -- 2. Constructing a positive functional on C[0,1] from the moments
  -- 3. Applying Riesz representation
  --
  -- These steps require substantial analysis not yet in Mathlib.
  sorry

/-- De Finetti's theorem (infinite version):
    An infinite exchangeable binary sequence can be represented as a Bernoulli mixture.

    **Proof**: Uses `hausdorff_moment_exists` to construct the mixing measure from
    the de Finetti moment sequence. -/
theorem deFinetti_infinite (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hexch : InfiniteExchangeable X μ) :
    ∃ (M : BernoulliMixture), ∀ (n : ℕ) (xs : Fin n → Bool),
      μ {ω | ∀ i : Fin n, X i.val ω = xs i} = ENNReal.ofReal (M.prob xs) := by
  -- Step 1: Get the mixing measure from Hausdorff
  have hbnd := fun k => deFinettiMoment_mem_unit_interval X μ k
  have hzero := deFinettiMoment_zero X μ
  have hcm : CompletelyMonotone (deFinettiMoment X μ) := by
    -- TODO: prove using exchangeability (finite-difference = canonical pattern probability).
    -- This should not require Hausdorff; it is a purely probabilistic/combinatorial lemma.
    sorry
  obtain ⟨ν, hprob, hsupp, hmoments⟩ := hausdorff_moment_exists (deFinettiMoment X μ) hbnd hcm hzero
  -- Step 2: Construct the BernoulliMixture
  refine ⟨⟨ν, hprob, ?_⟩, ?_⟩
  · -- Show support is in [0,1]
    exact hsupp
  · -- Step 3: Show the representation holds
    intro n xs
    -- Need to show: μ {ω | ∀ i, X i ω = xs i} = ∫ θ, ∏ᵢ Bernoulli(θ)(xs i) dν(θ)
    -- This follows from:
    -- 1. By exchangeability, the probability depends only on countTrue xs
    -- 2. The moment hmoments k gives us ∫ θ^k dν = E[X₁·...·Xₖ]
    -- 3. These combine to give the Bernoulli mixture formula
    --
    -- Technical gap: proving the integral representation matches
    sorry

/-- **Practical νPLN Theorem (Direct)**: Exchangeability implies counts are sufficient.

    This is the key result we actually need for PLN, independent of constructing
    the de Finetti mixing measure. It's a direct corollary of exchangeability.

    **For νPLN**: This justifies that PLN Evidence = (n⁺, n⁻) captures all relevant
    information when observations are exchangeable binary.
-/
theorem exchangeable_counts_sufficient_practical (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hexch : InfiniteExchangeable X μ) :
    ∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ →
      μ {ω | ∀ i : Fin n, X i.val ω = xs₁ i} = μ {ω | ∀ i : Fin n, X i.val ω = xs₂ i} :=
  fun _n xs₁ xs₂ h => infiniteExchangeable_same_counts_same_prob X μ hexch xs₁ xs₂ h

/-- The converse: a Bernoulli mixture is exchangeable -/
theorem bernoulliMixture_is_exchangeable (M : BernoulliMixture) :
    -- Any Bernoulli mixture defines an exchangeable distribution
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
      M.prob xs = M.prob (xs ∘ σ.symm) := by
  intro n σ xs
  -- Permuting doesn't change counts, so doesn't change Bernoulli product
  apply BernoulliMixture.prob_depends_only_on_counts
  -- countTrue (xs ∘ σ.symm) = countTrue xs
  exact (countTrue_perm xs σ.symm).symm

/-- Characterization: Exchangeable ↔ Bernoulli Mixture -/
def Represents {Ω : Type*} [MeasurableSpace Ω] (M : BernoulliMixture) (X : ℕ → Ω → Bool)
    (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ) (xs : Fin n → Bool),
    μ {ω | ∀ i : Fin n, X i.val ω = xs i} = ENNReal.ofReal (M.prob xs)

/-- Characterization (stubbed via `deFinetti_infinite`): infinite exchangeability
    iff there exists a Bernoulli-mixture representation of all finite prefixes. -/
theorem exchangeable_iff_bernoulliMixture (X : ℕ → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    InfiniteExchangeable X μ ↔ ∃ (M : BernoulliMixture), Represents M X μ := by
  constructor
  · intro hexch
    rcases deFinetti_infinite X μ hexch with ⟨M, hM⟩
    exact ⟨M, hM⟩
  · rintro ⟨M, hrep⟩
    refine ⟨?_⟩
    intro n
    refine ⟨?_⟩
    intro σ vals
    -- Rewrite both sides using the representation and the fact that `M.prob` is permutation-invariant.
    have hL : μ {ω | ∀ i : Fin n, X i.val ω = vals i} = ENNReal.ofReal (M.prob vals) := hrep n vals
    have hR' :
        μ {ω | ∀ i : Fin n, X (σ i).val ω = vals i} =
          μ {ω | ∀ i : Fin n, X i.val ω = vals (σ.symm i)} := by
      -- These are the same set by reindexing.
      congr 1
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h i
      · have := h (σ.symm i)
        simpa using this
      · have := h (σ i)
        simpa using this
    have hR : μ {ω | ∀ i : Fin n, X (σ i).val ω = vals i} =
        ENNReal.ofReal (M.prob (vals ∘ σ.symm)) := by
      -- Use representation on the reindexed values.
      simpa [hR'] using (hrep n (vals ∘ σ.symm))
    -- Now use `bernoulliMixture_is_exchangeable` to show `M.prob vals = M.prob (vals ∘ σ.symm)`.
    have hprob : M.prob vals = M.prob (vals ∘ σ.symm) := bernoulliMixture_is_exchangeable M n σ vals
    -- Combine.
    simp [hL, hR, hprob]

end DeFinetti

/-! ## Connection to Sufficient Statistics -/

section SufficientStatistics

/-- For a Bernoulli mixture, (k, n-k) is a sufficient statistic.

    This is the formal justification for PLN Evidence:
    - Observe n binary outcomes with k positives
    - Evidence = (k, n-k)
    - This captures ALL information about θ (the mixing parameter)
-/
theorem counts_sufficient_for_mixture (M : BernoulliMixture) (_n : ℕ) :
    -- For any two sequences with the same counts, the likelihood is the same
    ∀ (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ →
      M.prob xs₁ = M.prob xs₂ :=
  fun xs₁ xs₂ h => M.prob_depends_only_on_counts xs₁ xs₂ h

/- The posterior distribution of θ given k successes in n trials.

    With prior μ (the mixing measure), the posterior is:
    dμ_posterior(θ) ∝ θ^k (1-θ)^(n-k) dμ(θ)

    For Beta(α,β) prior, this gives Beta(α+k, β+n-k) posterior.
-/
-- TODO: formalize the posterior mixing measure as a conditional probability measure
-- obtained by weighting `mixingMeasure` with the likelihood `θ^k (1-θ)^(n-k)` and
-- normalizing. This needs conditional-measure infrastructure.

end SufficientStatistics

/-! ## The νPLN Connection -/

section NuPLN

/-- The main theorem connecting de Finetti to PLN:

    For exchangeable binary observations:
    1. De Finetti: sequence is a Bernoulli mixture
    2. Counts (k, n-k) are sufficient statistics
    3. With Beta prior, posterior is Beta(α+k, β+n-k)
    4. PLN Evidence = (k, n-k)
    5. PLN Strength k/(k+n-k) → posterior mean as n → ∞

    Therefore: **PLN is exact Bayesian inference for exchangeable binary domains**
-/
theorem pln_is_exact_for_exchangeable :
    -- Under exchangeability assumption:
    -- - PLN Evidence captures sufficient statistics (by de Finetti)
    -- - PLN inference matches Bayesian inference (by conjugacy)
    -- - PLN strength equals optimal point estimate (by posterior mean)
    (∀ n_pos n_neg : ℕ, evidenceFromCounts n_pos n_neg = (n_pos, n_neg)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n_pos n_neg : ℕ, n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
        |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg| < ε) := by
  simpa using Mettapedia.Logic.EvidenceBeta.pln_is_bayes_optimal_for_exchangeable

/- Domain characterization for νPLN:

    PLN is the exact optimal inference method when:
    1. Observations are binary (success/failure)
    2. Observations are exchangeable (order doesn't matter)
    3. Prior is Beta (or approaches improper uniform)

    Outside this domain, PLN may be an approximation.
-/
-- TODO: make the "domain characterization" precise as a predicate on observation
-- processes and priors, and connect it to the `Exchangeability`/`EvidenceBeta` lemmas.

end NuPLN

end Mettapedia.Logic.DeFinetti
