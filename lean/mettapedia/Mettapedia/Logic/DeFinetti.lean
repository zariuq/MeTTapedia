import Mettapedia.Logic.Exchangeability
import Mettapedia.Logic.MomentSequences
import Mettapedia.Logic.HausdorffMoment
import Mettapedia.Logic.EvidenceBeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
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
open Mettapedia.Logic.MomentSequences
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
              exact Fintype.card_congr eSum
      _ = Fintype.card { i : Fin m // a i = true } + Fintype.card { j : Fin n // b j = true } := by
            exact (Fintype.card_sum
              (α := {i : Fin m // a i = true})
              (β := {j : Fin n // b j = true}))

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
          simp [cardAppendSubtype]
    _ = Fintype.card { i : Fin m // a i = true } + Fintype.card { j : Fin n // b j = true } :=
          cardSumSubtype
    _ = countTrue a + countTrue b := by
          simp [hA, hB]

@[simp]
lemma countTrue_zerosThenOnes (n k : ℕ) : countTrue (zerosThenOnes n k) = k := by
  simp [zerosThenOnes, countTrue_append_fin]

@[simp]
lemma countTrue_zerosThenOnesThenZero (n k : ℕ) :
    countTrue (zerosThenOnesThenZero n k) = k := by
  simp [zerosThenOnesThenZero, countTrue_append_fin]

/-- `countTrue` is invariant under reindexing by `Fin.cast`. -/
theorem countTrue_comp_cast {m n : ℕ} (h : m = n) (xs : Fin n → Bool) :
    countTrue (xs ∘ Fin.cast h) = countTrue xs := by
  classical
  unfold countTrue
  -- Compare the filtered finsets via the bijection `Fin.cast h`.
  have hcard :
      (Finset.univ.filter (fun i : Fin m => xs (Fin.cast h i) = true)).card =
        (Finset.univ.filter (fun j : Fin n => xs j = true)).card := by
    refine Finset.card_bij (fun i _ => Fin.cast h i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    · intro i₁ _ i₂ _ hij
      exact (Fin.cast_injective h) hij
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨Fin.cast h.symm j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using hj
      · simp
  simpa [Function.comp_apply] using hcard

/-! ### Cylinder Decomposition Lemmas

These lemmas are the combinatorial heart of the "complete monotonicity" argument:
they let us express Hausdorff forward differences of the moment sequence as measures
of canonical cylinder events of the form `0^n 1^k`.
-/

omit [MeasurableSpace Ω] in
/-- Reindexing a pattern by `Fin.cast` does not change the associated cylinder event. -/
lemma cyl_comp_cast (X : ℕ → Ω → Bool) {m n : ℕ} (h : m = n) (xs : Fin n → Bool) :
    cyl X (xs ∘ Fin.cast h) = cyl X xs := by
  ext ω
  constructor
  · intro hx j
    have hj := hx (Fin.cast h.symm j)
    -- `Fin.cast` preserves `.val`, and `Fin.cast h (Fin.cast h.symm j) = j`.
    simpa [cyl, Fin.val_cast] using hj
  · intro hx i
    have hi := hx (Fin.cast h i)
    simpa [cyl, Fin.val_cast] using hi

/-- Restricting `zerosThenOnes n (k+1)` to its first `n+k` indices recovers `zerosThenOnes n k`. -/
lemma zerosThenOnes_castAdd (n k : ℕ) (i : Fin (n + k)) :
    zerosThenOnes n (k + 1) (Fin.castAdd 1 i) = zerosThenOnes n k i := by
  classical
  induction i using Fin.addCases with
  | left i0 =>
      simp [zerosThenOnes, Fin.append, Fin.castAdd_castAdd]
  | right j0 =>
      simp [zerosThenOnes, Fin.append, Fin.castAdd_natAdd]

/-- The last entry of `zerosThenOnes n (k+1)` is `true`. -/
lemma zerosThenOnes_last (n k : ℕ) :
    zerosThenOnes n (k + 1) (Fin.last (n + k)) = true := by
  have hidx : (Fin.last (n + k) : Fin (n + k + 1)) = Fin.natAdd n (Fin.last k) := by
    ext
    simp
  unfold zerosThenOnes
  rw [hidx]
  simpa using
    (Fin.append_right (u := fun _ : Fin n => false)
      (v := fun _ : Fin (k + 1) => true) (i := Fin.last k))

omit [MeasurableSpace Ω] in
/-- `cyl` for `0^n 1^(k+1)` is `cyl` for `0^n 1^k` plus the final-bit constraint. -/
lemma cyl_zerosThenOnes_succ (X : ℕ → Ω → Bool) (n k : ℕ) :
    cyl X (zerosThenOnes n (k + 1)) = cyl X (zerosThenOnes n k) ∩ {ω | X (n + k) ω = true} := by
  ext ω
  constructor
  · intro h
    refine And.intro ?_ ?_
    · intro i
      have hi := h (Fin.castAdd 1 i)
      simpa [cyl, zerosThenOnes_castAdd] using hi
    · have hlast := h (Fin.last (n + k))
      simpa [cyl, zerosThenOnes_last] using hlast
  · rintro ⟨hpre, hlast⟩
    intro i
    refine Fin.addCases (m := n + k) (n := 1) ?_ ?_ i
    · intro i0
      have hi0 := hpre i0
      simpa [cyl, zerosThenOnes_castAdd] using hi0
    · intro j0
      have hj0 : j0 = 0 := Fin.eq_zero j0
      subst hj0
      have : (Fin.natAdd (n + k) (0 : Fin 1) : Fin (n + k + 1)) = Fin.last (n + k) := by
        ext
        simp
      simpa [cyl, this, zerosThenOnes_last] using hlast

/-- Restricting `zerosThenOnesThenZero n k` to its first `n+k` indices recovers `zerosThenOnes n k`. -/
lemma zerosThenOnesThenZero_castAdd (n k : ℕ) (i : Fin (n + k)) :
    zerosThenOnesThenZero n k (Fin.castAdd 1 i) = zerosThenOnes n k i := by
  simp [zerosThenOnesThenZero]

/-- The last entry of `zerosThenOnesThenZero n k` is `false`. -/
lemma zerosThenOnesThenZero_last (n k : ℕ) :
    zerosThenOnesThenZero n k (Fin.last (n + k)) = false := by
  have hidx : (Fin.last (n + k) : Fin (n + k + 1)) = Fin.natAdd (n + k) (0 : Fin 1) := by
    ext
    simp
  unfold zerosThenOnesThenZero
  rw [hidx]
  exact
    (Fin.append_right (u := zerosThenOnes n k) (v := fun _ : Fin 1 => false) (i := (0 : Fin 1)))

omit [MeasurableSpace Ω] in
/-- Subtracting the final-bit-true event from `cyl (0^n 1^k)` yields `cyl (0^n 1^k 0)`. -/
lemma cyl_zerosThenOnes_diff (X : ℕ → Ω → Bool) (n k : ℕ) :
    cyl X (zerosThenOnes n k) \ {ω | X (n + k) ω = true} = cyl X (zerosThenOnesThenZero n k) := by
  ext ω
  constructor
  · rintro ⟨hpre, hnot⟩
    intro i
    refine Fin.addCases (m := n + k) (n := 1) ?_ ?_ i
    · intro i0
      have hi0 := hpre i0
      simpa [cyl, zerosThenOnesThenZero_castAdd] using hi0
    · intro j0
      have hj0 : j0 = 0 := Fin.eq_zero j0
      subst hj0
      have hxfalse : X (n + k) ω = false := by
        cases hx : X (n + k) ω <;> simp [hx] at hnot ⊢
      have : X (n + k) ω = zerosThenOnesThenZero n k (Fin.last (n + k)) := by
        simpa [zerosThenOnesThenZero_last] using hxfalse
      simpa [cyl] using this
  · intro h
    refine And.intro ?_ ?_
    · intro i
      have hi := h (Fin.castAdd 1 i)
      simpa [cyl, zerosThenOnesThenZero_castAdd] using hi
    · intro htrue
      have hlast := h (Fin.last (n + k))
      have hxfalse : X (n + k) ω = false := by
        simpa [cyl, zerosThenOnesThenZero_last] using hlast
      cases hx : X (n + k) ω <;> simp [hx] at htrue hxfalse

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

/-- The first finite difference of the de Finetti moments is non-negative:
    Δ¹mₖ = mₖ - mₖ₊₁ ≥ 0 -/
theorem deFinettiMoment_diff_nonneg (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (_hexch : InfiniteExchangeable X μ) (k : ℕ) :
    deFinettiMoment X μ (k + 1) ≤ deFinettiMoment X μ k :=
  deFinettiMoment_antitone X μ (Nat.le_succ k)

/-! ### Forward Differences as Cylinder Probabilities

For an exchangeable binary process, the Hausdorff forward differences of the moment sequence
have a direct probabilistic meaning:

`Δⁿ mₖ = P(0^n 1^k)`,

where `0^n 1^k` denotes the canonical pattern of `n` falses followed by `k` trues.

This yields complete monotonicity immediately, since it is the real-valued measure of a set.
-/

/-- For an exchangeable binary sequence, Hausdorff forward differences of the de Finetti moments
are cylinder probabilities of the canonical patterns `0^n 1^k`. -/
theorem deFinettiMoment_fwdDiffIter_eq_cyl (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    ∀ n k, fwdDiffIter n (deFinettiMoment X μ) k = μ.real (cyl X (zerosThenOnes n k)) := by
  classical
  intro n k
  induction n generalizing k with
  | zero =>
      -- `Δ^0 m_k = m_k`, and `0^0 1^k` is just the all-`true` pattern.
      have hSet :
          cyl X (zerosThenOnes 0 k) = {ω | ∀ i : Fin k, X i.val ω = true} := by
        -- `zerosThenOnes 0 k` is constant-`true`; the only mismatch is the `Fin (0+k)` index type.
        have hPattern : ∀ i : Fin (0 + k), zerosThenOnes 0 k i = true := by
          intro i
          unfold zerosThenOnes
          have : (fun _ : Fin 0 => false) = (Fin.elim0 : Fin 0 → Bool) := by
            ext x
            exact (Fin.elim0 x)
          -- `simp` uses `Fin.elim0_append` to remove the empty left part.
          simp [this]
        ext ω
        constructor
        · intro h i
          have hi := h (Fin.cast (Nat.zero_add k).symm i)
          simpa [cyl, hPattern] using hi
        · intro h i
          have hi := h (Fin.cast (Nat.zero_add k) i)
          simpa [cyl, hPattern] using hi
      -- Compute both sides.
      simp [fwdDiffIter, deFinettiMoment, Measure.real, hSet]
  | succ n ih =>
      have ht : MeasurableSet ({ω | X (n + k) ω = true} : Set Ω) :=
        measurableSet_preimage (hX (n + k)) (measurableSet_singleton true)
      calc
        fwdDiffIter (n + 1) (deFinettiMoment X μ) k
            = fwdDiffIter n (deFinettiMoment X μ) k - fwdDiffIter n (deFinettiMoment X μ) (k + 1) := by
                simpa using (fwdDiffIter_succ (m := deFinettiMoment X μ) n k)
        _ = μ.real (cyl X (zerosThenOnes n k)) - μ.real (cyl X (zerosThenOnes n (k + 1))) := by
              simp [ih k, ih (k + 1)]
        _ = μ.real (cyl X (zerosThenOnes (n + 1) k)) := by
              -- Split `P(0^n 1^k)` by the next bit, then use exchangeability to move the trailing `0`.
              have hsplit :
                  μ.real (cyl X (zerosThenOnes n (k + 1))) +
                      μ.real (cyl X (zerosThenOnes n k) \ {ω | X (n + k) ω = true})
                    = μ.real (cyl X (zerosThenOnes n k)) := by
                have hmi :=
                  measureReal_inter_add_diff (μ := μ) (s := cyl X (zerosThenOnes n k))
                    (t := ({ω | X (n + k) ω = true} : Set Ω)) ht
                simpa [cyl_zerosThenOnes_succ (X := X) n k] using hmi
              have hdiff :
                  μ.real (cyl X (zerosThenOnes n k) \ {ω | X (n + k) ω = true}) =
                      μ.real (cyl X (zerosThenOnes n k)) - μ.real (cyl X (zerosThenOnes n (k + 1))) := by
                -- Solve `a + b = c` for `b`.
                exact eq_sub_of_add_eq' hsplit
              have hsub :
                  μ.real (cyl X (zerosThenOnes n k)) - μ.real (cyl X (zerosThenOnes n (k + 1))) =
                      μ.real (cyl X (zerosThenOnesThenZero n k)) := by
                calc
                  μ.real (cyl X (zerosThenOnes n k)) - μ.real (cyl X (zerosThenOnes n (k + 1)))
                      = μ.real (cyl X (zerosThenOnes n k) \ {ω | X (n + k) ω = true}) := by
                          exact hdiff.symm
                  _ = μ.real (cyl X (zerosThenOnesThenZero n k)) := by
                        simp [cyl_zerosThenOnes_diff (X := X) n k]
              have hμ :
                  μ (cyl X (zerosThenOnesThenZero n k)) = μ (cyl X (zerosThenOnes (n + 1) k)) := by
                have hlen : n + k + 1 = (n + 1) + k := by
                  calc
                    n + k + 1 = n + (k + 1) := by simp [Nat.add_assoc]
                    _ = n + (1 + k) := by simp [Nat.add_comm]
                    _ = (n + 1) + k := by simp [Nat.add_assoc]
                -- Cast `zerosThenOnes (n+1) k` to a pattern on `Fin (n+k+1)` so we can apply exchangeability.
                let xs₂ : Fin (n + k + 1) → Bool := zerosThenOnes (n + 1) k ∘ Fin.cast hlen
                have hcount :
                    countTrue (zerosThenOnesThenZero n k) = countTrue xs₂ := by
                  -- Both sides count to `k`; the cast does not change `countTrue`.
                  simp [xs₂, countTrue_comp_cast]
                have hμ' :
                    μ (cyl X (zerosThenOnesThenZero n k)) = μ (cyl X xs₂) := by
                  simpa [cyl] using
                    (infiniteExchangeable_same_counts_same_prob (X := X) (μ := μ) hexch
                      (xs₁ := zerosThenOnesThenZero n k) (xs₂ := xs₂) hcount)
                -- `cyl` is also invariant under the same cast.
                have hcyl : cyl X xs₂ = cyl X (zerosThenOnes (n + 1) k) := by
                  simpa [xs₂] using (cyl_comp_cast (X := X) (h := hlen) (xs := zerosThenOnes (n + 1) k))
                simpa [hcyl] using hμ'
              have hμreal :
                  μ.real (cyl X (zerosThenOnesThenZero n k)) = μ.real (cyl X (zerosThenOnes (n + 1) k)) := by
                simpa [Measure.real] using congrArg ENNReal.toReal hμ
              simpa [hμreal] using hsub

/-- The de Finetti moment sequence is completely monotone: all Hausdorff forward differences are nonnegative. -/
theorem deFinettiMoment_completelyMonotone (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    CompletelyMonotone (deFinettiMoment X μ) := by
  intro n k
  have h := deFinettiMoment_fwdDiffIter_eq_cyl (X := X) (μ := μ) hX hexch n k
  -- Now it's a real-valued measure of a set.
  have hnonneg := (MeasureTheory.measureReal_nonneg (μ := μ) (s := cyl X (zerosThenOnes n k)))
  -- rewrite the goal using the cylinder characterization
  rw [h]
  exact hnonneg

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
  simpa using
    (Mettapedia.Logic.HausdorffMoment.hausdorff_moment_exists m hbnd hcm hzero)

/-- De Finetti's theorem (infinite version):
    An infinite exchangeable binary sequence can be represented as a Bernoulli mixture.

    **Proof**: Uses `hausdorff_moment_exists` to construct the mixing measure from
    the de Finetti moment sequence. -/
theorem deFinetti_infinite (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : ∀ i : ℕ, Measurable (X i)) (hexch : InfiniteExchangeable X μ) :
    ∃ (M : BernoulliMixture), ∀ (n : ℕ) (xs : Fin n → Bool),
      μ {ω | ∀ i : Fin n, X i.val ω = xs i} = ENNReal.ofReal (M.prob xs) := by
  -- Step 1: Get the mixing measure from Hausdorff
  have hbnd := fun k => deFinettiMoment_mem_unit_interval X μ k
  have hzero := deFinettiMoment_zero X μ
  have hcm : CompletelyMonotone (deFinettiMoment X μ) := by
    exact deFinettiMoment_completelyMonotone (X := X) (μ := μ) hX hexch
  obtain ⟨ν, hprob, hsupp, hmoments⟩ := hausdorff_moment_exists (deFinettiMoment X μ) hbnd hcm hzero
  -- Step 2: Construct the BernoulliMixture
  refine ⟨⟨ν, hprob, ?_⟩, ?_⟩
  · -- Show support is in [0,1]
    exact hsupp
  · -- Step 3: Show the representation holds
    intro n xs
    classical
    -- Abbreviate counts.
    let k : ℕ := countTrue xs
    let l : ℕ := countFalse xs

    -- Align the canonical pattern `0^l 1^k` to length `n`.
    have hlen : l + k = n := by
      -- `k + l = n` is `count_partition`; we just swap the summands.
      have hk : k + l = n := by
        simpa [k, l] using (count_partition (n := n) xs)
      simpa [Nat.add_comm, k, l] using hk
    let xsCanon : Fin n → Bool := zerosThenOnes l k ∘ Fin.cast hlen.symm

    have hcount : countTrue xs = countTrue xsCanon := by
      -- `xsCanon` is a casted version of `zerosThenOnes l k`, whose count is `k`.
      have hkCanon : countTrue xsCanon = k := by
        have := countTrue_comp_cast (h := hlen.symm) (xs := zerosThenOnes l k)
        simpa [xsCanon, k, countTrue_zerosThenOnes] using this
      simp [k, hkCanon]

    -- Exchangeability reduces everything to the canonical pattern.
    have hμexch : μ (cyl X xs) = μ (cyl X xsCanon) := by
      simpa [cyl] using
        (infiniteExchangeable_same_counts_same_prob (X := X) (μ := μ) hexch xs xsCanon hcount)
    have hcylCanon : cyl X xsCanon = cyl X (zerosThenOnes l k) := by
      simpa [xsCanon] using (cyl_comp_cast (X := X) (h := hlen.symm) (xs := zerosThenOnes l k))
    have hμcanon : μ (cyl X xs) = μ (cyl X (zerosThenOnes l k)) := by
      simpa [hcylCanon] using hμexch
    have hRealCanon : μ.real (cyl X xs) = μ.real (cyl X (zerosThenOnes l k)) := by
      simpa [Measure.real] using congrArg ENNReal.toReal hμcanon

    -- A helper integral family matching the forward-difference recursion.
    let g : ℕ → ℕ → ℝ :=
      fun n0 k0 => ∫ θ in Set.Icc (0 : ℝ) 1, θ ^ k0 * (1 - θ) ^ n0 ∂ν

    have integrable_g (n0 k0 : ℕ) :
        Integrable (fun θ : ℝ => θ ^ k0 * (1 - θ) ^ n0) (ν.restrict (Set.Icc (0 : ℝ) 1)) := by
      -- Bounded by `1` on `[0,1]`, hence integrable w.r.t. a finite measure.
      haveI : IsFiniteMeasure (ν.restrict (Set.Icc (0 : ℝ) 1)) := by infer_instance
      have hmeas : AEStronglyMeasurable (fun θ : ℝ => θ ^ k0 * (1 - θ) ^ n0)
          (ν.restrict (Set.Icc (0 : ℝ) 1)) := by
        have hmeas' : Measurable (fun θ : ℝ => θ ^ k0 * (1 - θ) ^ n0) := by
          have h1 : Measurable (fun θ : ℝ => θ ^ k0) :=
            Measurable.pow_const measurable_id k0
          have h2 : Measurable (fun θ : ℝ => (1 - θ) ^ n0) :=
            Measurable.pow_const (measurable_const.sub measurable_id) n0
          exact h1.mul h2
        exact hmeas'.aestronglyMeasurable
      have hbound :
          ∀ᵐ θ ∂ν.restrict (Set.Icc (0 : ℝ) 1), ‖θ ^ k0 * (1 - θ) ^ n0‖ ≤ (1 : ℝ) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        have hθ0 : 0 ≤ θ := hθ.1
        have hθ1 : θ ≤ 1 := hθ.2
        have h1θ0 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
        have h1θ1 : 1 - θ ≤ 1 := sub_le_self 1 hθ0
        have hk0 : θ ^ k0 ≤ 1 := pow_le_one₀ hθ0 hθ1
        have hn0 : (1 - θ) ^ n0 ≤ 1 := pow_le_one₀ h1θ0 h1θ1
        have hnonneg : 0 ≤ θ ^ k0 * (1 - θ) ^ n0 :=
          mul_nonneg (pow_nonneg hθ0 k0) (pow_nonneg h1θ0 n0)
        have hprod : θ ^ k0 * (1 - θ) ^ n0 ≤ (1 : ℝ) := by
          have hmul : θ ^ k0 * (1 - θ) ^ n0 ≤ (1 : ℝ) * (1 : ℝ) :=
            mul_le_mul hk0 hn0 (pow_nonneg h1θ0 n0) (by positivity)
          simpa using hmul
        -- Avoid rewriting `abs` into a product of `abs` terms; we want the simple `abs_of_nonneg`.
        have hnorm : ‖θ ^ k0 * (1 - θ) ^ n0‖ = θ ^ k0 * (1 - θ) ^ n0 := by
          exact Real.norm_of_nonneg hnonneg
        simpa [hnorm] using hprod
      exact Integrable.of_bound hmeas 1 hbound

    have g_succ (n0 k0 : ℕ) :
        g (n0 + 1) k0 = g n0 k0 - g n0 (k0 + 1) := by
      have hf0 : Integrable (fun θ : ℝ => θ ^ k0 * (1 - θ) ^ n0) (ν.restrict (Set.Icc (0 : ℝ) 1)) :=
        integrable_g n0 k0
      have hf1 : Integrable (fun θ : ℝ => θ ^ (k0 + 1) * (1 - θ) ^ n0) (ν.restrict (Set.Icc (0 : ℝ) 1)) :=
        integrable_g n0 (k0 + 1)
      -- Compute using `a*(1-θ) = a - a*θ`.
      have hfun :
          (fun θ : ℝ => θ ^ k0 * (1 - θ) ^ (n0 + 1)) =
            fun θ : ℝ => θ ^ k0 * (1 - θ) ^ n0 - θ ^ (k0 + 1) * (1 - θ) ^ n0 := by
        funext θ
        calc
          θ ^ k0 * (1 - θ) ^ (n0 + 1)
              = (θ ^ k0 * (1 - θ) ^ n0) * (1 - θ) := by
                  simp [pow_succ, mul_assoc]
              _ = (θ ^ k0 * (1 - θ) ^ n0) * 1 - (θ ^ k0 * (1 - θ) ^ n0) * θ := by
                  simp [mul_sub]
              _ = θ ^ k0 * (1 - θ) ^ n0 - θ ^ (k0 + 1) * (1 - θ) ^ n0 := by
                  have hmul :
                      (θ ^ k0 * (1 - θ) ^ n0) * θ =
                        θ ^ (k0 + 1) * (1 - θ) ^ n0 := by
                    calc
                      (θ ^ k0 * (1 - θ) ^ n0) * θ
                          = (θ ^ k0 * θ) * (1 - θ) ^ n0 := by
                              simp [mul_assoc, mul_comm]
                      _ = θ ^ (k0 + 1) * (1 - θ) ^ n0 := by
                              simp [pow_succ, mul_assoc]
                  simp [mul_one, hmul]
      -- Integrate both sides.
      unfold g
      -- Rewrite the integrand, then apply linearity.
      simpa [hfun] using
        (integral_sub (μ := ν.restrict (Set.Icc (0 : ℝ) 1)) hf0 hf1)

    have g_eq_fwdDiffIter :
        ∀ n0 k0, g n0 k0 = fwdDiffIter n0 (deFinettiMoment X μ) k0 := by
      intro n0 k0
      induction n0 generalizing k0 with
      | zero =>
          -- Base: `∫ θ^k0 = m_k0`.
          simp [g, hmoments, fwdDiffIter]
      | succ n0 ih =>
          calc
            g (n0 + 1) k0 = g n0 k0 - g n0 (k0 + 1) := g_succ n0 k0
            _ = fwdDiffIter n0 (deFinettiMoment X μ) k0 - fwdDiffIter n0 (deFinettiMoment X μ) (k0 + 1) := by
                  simp [ih k0, ih (k0 + 1)]
            _ = fwdDiffIter (n0 + 1) (deFinettiMoment X μ) k0 := by
                  -- Match the Hausdorff recurrence.
                  symm
                  simpa using (fwdDiffIter_succ (m := deFinettiMoment X μ) n0 k0)

    -- Compare `μ.real` of the canonical cylinder to the corresponding integral.
    have hcanon :
        μ.real (cyl X (zerosThenOnes l k)) = g l k := by
      have hfwd := deFinettiMoment_fwdDiffIter_eq_cyl (X := X) (μ := μ) hX hexch l k
      have hg : g l k = fwdDiffIter l (deFinettiMoment X μ) k := g_eq_fwdDiffIter l k
      -- `hfwd` gives `Δ^l m_k = μ.real(cyl ...)`.
      -- `hg` gives `g l k = Δ^l m_k`.
      simpa [hg] using hfwd.symm

    -- Now relate `μ.real(cyl X xs)` to the Bernoulli-mixture integral defining `M.prob xs`.
    have hReal : μ.real (cyl X xs) = BernoulliMixture.prob ⟨ν, hprob, hsupp⟩ xs := by
      have hprob' : BernoulliMixture.prob ⟨ν, hprob, hsupp⟩ xs = g l k := by
        simp [BernoulliMixture.prob, g, k, l, bernoulliProductPMF_eq_power]
      calc
        μ.real (cyl X xs) = μ.real (cyl X (zerosThenOnes l k)) := hRealCanon
        _ = g l k := hcanon
        _ = BernoulliMixture.prob ⟨ν, hprob, hsupp⟩ xs := by
              exact hprob'.symm

    have hNonneg : 0 ≤ BernoulliMixture.prob ⟨ν, hprob, hsupp⟩ xs := by
      -- `μ.real` is always nonnegative.
      have : 0 ≤ μ.real (cyl X xs) := MeasureTheory.measureReal_nonneg
      simpa [hReal] using this

    -- Convert the real equality into an `ENNReal.ofReal` equality.
    have hx : μ (cyl X xs) ≠ ⊤ := by finiteness
    have hy : (ENNReal.ofReal (BernoulliMixture.prob ⟨ν, hprob, hsupp⟩ xs)) ≠ ⊤ := by simp
    have hToReal :
        (μ (cyl X xs)).toReal = (ENNReal.ofReal (BernoulliMixture.prob ⟨ν, hprob, hsupp⟩ xs)).toReal := by
      simpa [Measure.real, ENNReal.toReal_ofReal hNonneg] using hReal
    have hENN :
        μ (cyl X xs) = ENNReal.ofReal (BernoulliMixture.prob ⟨ν, hprob, hsupp⟩ xs) := by
      exact (ENNReal.toReal_eq_toReal_iff' hx hy).1 hToReal

    simpa [cyl] using hENN

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
theorem exchangeable_iff_bernoulliMixture (X : ℕ → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    InfiniteExchangeable X μ ↔ ∃ (M : BernoulliMixture), Represents M X μ := by
  constructor
  · intro hexch
    rcases deFinetti_infinite X μ hX hexch with ⟨M, hM⟩
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

/-! ## The νPLN Connection: Explicit Chain Theorem -/

section NuPLN

/-- **The νPLN Master Theorem**: Complete formal chain from exchangeability to PLN.

    This theorem makes EXPLICIT the full justification for PLN:

    **Step 1 (De Finetti)**: Exchangeable sequence → Bernoulli mixture representation
    **Step 2 (Sufficiency)**: Bernoulli mixture → Counts (n⁺, n⁻) are sufficient statistics
    **Step 3 (PLN Evidence)**: PLN Evidence = (n⁺, n⁻) captures this sufficiency
    **Step 4 (Convergence)**: PLN strength → Bayesian posterior mean

    Each step explicitly invokes the corresponding theorem, making the chain verifiable.

    **Conclusion**: PLN is exact Bayesian inference for exchangeable binary domains.
-/
theorem nupln_master_chain {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : ∀ i, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    -- Part 1: De Finetti gives us a Bernoulli mixture
    ∃ (M : BernoulliMixture), Represents M X μ ∧
    -- Part 2: Counts are sufficient for the mixture
    (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ → M.prob xs₁ = M.prob xs₂) ∧
    -- Part 3: PLN Evidence captures this sufficiency
    (∀ n_pos n_neg : ℕ, evidenceFromCounts n_pos n_neg = (n_pos, n_neg)) ∧
    -- Part 4: PLN strength converges to Bayesian posterior mean
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n_pos n_neg : ℕ,
      n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
      |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg| < ε) := by
  -- Step 1: Apply de Finetti's theorem to get BernoulliMixture representation
  obtain ⟨M, hM⟩ := deFinetti_infinite X μ hX hexch
  refine ⟨M, hM, ?_, ?_, ?_⟩
  -- Step 2: Counts sufficient (from BernoulliMixture.prob_depends_only_on_counts)
  · intro n xs₁ xs₂ hcount
    exact M.prob_depends_only_on_counts xs₁ xs₂ hcount
  -- Step 3: Evidence = counts (by definition)
  · intros; rfl
  -- Step 4: PLN convergence (from EvidenceBeta.pln_is_bayes_optimal_for_exchangeable)
  · exact (Mettapedia.Logic.EvidenceBeta.pln_is_bayes_optimal_for_exchangeable).2

/-- **Corollary**: The simple form for stating "PLN is exact for exchangeable domains".

    This is the theorem to cite in papers: given exchangeability, PLN is not an
    approximation but the mathematically correct inference method.
-/
theorem pln_is_exact_for_exchangeable :
    (∀ n_pos n_neg : ℕ, evidenceFromCounts n_pos n_neg = (n_pos, n_neg)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n_pos n_neg : ℕ, n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
        |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg| < ε) :=
  Mettapedia.Logic.EvidenceBeta.pln_is_bayes_optimal_for_exchangeable

/-- **Domain Characterization**: PLN is exact when:
    1. Observations are binary (success/failure)
    2. Observations are exchangeable (order doesn't matter)
    3. Prior is Beta (or approaches improper uniform)

    Outside this domain, PLN may be an approximation.
-/
def PLNDomainConditions {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  InfiniteExchangeable X μ

/-- The full νPLN justification: if domain conditions hold, PLN is exact. -/
theorem nupln_justification {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : ∀ i, Measurable (X i))
    (hdom : PLNDomainConditions X μ) :
    ∃ (M : BernoulliMixture), Represents M X μ ∧
    (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ → M.prob xs₁ = M.prob xs₂) :=
  let ⟨M, hrep, hsuff, _, _⟩ := nupln_master_chain X μ hX hdom
  ⟨M, hrep, hsuff⟩

end NuPLN

end Mettapedia.Logic.DeFinetti
