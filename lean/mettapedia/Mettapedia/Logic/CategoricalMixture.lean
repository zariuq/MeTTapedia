/-
LLM primer:
- `stdSimplex ℝ (Fin k) = {f : Fin k → ℝ | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}`
- Access simplex coordinates: `(θ : ProbSimplex k)` → `(θ : Fin k → ℝ) a` for component `a`
- `countVector xs a` generalizes `countTrue`/`countFalse` from Bool to Fin k
- `categoricalProductPMF_eq_power` is the key: ∏ᵢ θ(xsᵢ) = ∏ₐ θ(a)^countVector(a)
- Permutation invariance of countVector gives exchangeability for free
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Fintype.BigOperators

/-!
# Categorical Mixture Distributions (Generalized de Finetti)

This file generalizes `Mettapedia.Logic.DeFinetti` from binary (`Bool`) observations to
k-ary categorical (`Fin k`) observations.

## The Generalization

| Binary (DeFinetti.lean) | Categorical (this file) |
|------------------------|------------------------|
| `bernoulliPMF θ b` | `θ a` (direct lookup) |
| `bernoulliProductPMF θ xs` | `categoricalProductPMF θ xs` |
| `countTrue`/`countFalse` | `countVector xs a` |
| `θ^k (1-θ)^(n-k)` | `∏ₐ θ(a)^(countVector xs a)` |
| `BernoulliMixture` (mixing on [0,1]) | `CategoricalMixture k` (mixing on Δ_{k-1}) |
| `Icc 0 1` parameter space | `stdSimplex ℝ (Fin k)` |

## Main Definitions

* `ProbSimplex k` : The probability simplex `Δ_{k-1}` as a subtype of `Fin k → ℝ`
* `categoricalProductPMF` : Product of categorical probabilities for a word
* `countVector` : Count of each symbol in a word (generalizes countTrue/countFalse)
* `CategoricalMixture k` : Mixture of categorical distributions (k-ary de Finetti model)

## Main Theorems

* `categoricalProductPMF_eq_power` : Product factors as `∏ₐ θ(a)^(count a)`
* `countVector_sum` : Count vector sums to word length
* `countVector_perm` : Count vector is permutation-invariant
* `CategoricalMixture.prob_depends_only_on_counts` : Probability depends only on count vector
* `CategoricalMixture.prob_perm_invariant` : Mixture probability is exchangeable

## References

* de Finetti, B. (1931). "Funzione caratteristica di un fenomeno aleatorio"
* Diaconis & Freedman (1980). "Finite Exchangeable Sequences"
* EvidenceDirichlet.lean (the k-ary Bayesian update side)
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.CategoricalDeFinetti

open MeasureTheory Finset BigOperators

/-! ## Parameter Space: The Probability Simplex -/

/-- The probability simplex for k outcomes, as a subtype of `Fin k → ℝ`.
    This is `Δ_{k-1} = {θ : ℝ^k | ∀ i, θ(i) ≥ 0, ∑ θ(i) = 1}`. -/
abbrev ProbSimplex (k : ℕ) : Type := ↥(stdSimplex ℝ (Fin k))

lemma probSimplex_nonneg {k : ℕ} (θ : ProbSimplex k) (a : Fin k) :
    0 ≤ (θ : Fin k → ℝ) a := θ.2.1 a

lemma probSimplex_sum_one {k : ℕ} (θ : ProbSimplex k) :
    ∑ a, (θ : Fin k → ℝ) a = 1 := θ.2.2

lemma measurableSet_stdSimplex (k : ℕ) : MeasurableSet (stdSimplex ℝ (Fin k)) :=
  (isClosed_stdSimplex (Fin k)).measurableSet

/-! ## Categorical PMF -/

/-- Product of categorical step probabilities for a word of length n.

    `categoricalProductPMF θ xs = ∏ᵢ θ(xsᵢ)` is the likelihood of observing
    word `xs` under the categorical distribution with parameter `θ`. -/
def categoricalProductPMF {k n : ℕ} (θ : Fin k → ℝ) (xs : Fin n → Fin k) : ℝ :=
  ∏ i : Fin n, θ (xs i)

/-! ## Count Vector -/

/-- Count vector: for each symbol `a : Fin k`, how many times it appears in `xs`.

    This generalizes `countTrue` (Bool case: k=2, counting symbol `1`)
    and `countFalse` (counting symbol `0`). -/
def countVector {k n : ℕ} (xs : Fin n → Fin k) (a : Fin k) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => xs i = a)).card

/-- The count vector sums to the word length n. -/
theorem countVector_sum {k n : ℕ} (xs : Fin n → Fin k) :
    ∑ a : Fin k, countVector xs a = n := by
  classical
  unfold countVector
  have h : (∑ a : Fin k, (Finset.univ.filter (fun i : Fin n => xs i = a)).card) =
      (Finset.univ : Finset (Fin n)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext i
      simp [Finset.mem_biUnion, Finset.mem_filter]
    · intro a _ b _ hab
      exact Finset.disjoint_filter.mpr (fun i _ hai hbi => hab (hai ▸ hbi))
  simp [h]

/-- The count vector is permutation-invariant: reordering the word doesn't change counts. -/
theorem countVector_perm {k n : ℕ} (xs : Fin n → Fin k) (σ : Equiv.Perm (Fin n)) (a : Fin k) :
    countVector (xs ∘ σ) a = countVector xs a := by
  classical
  unfold countVector
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi ⊢
    exact hi
  · intro i₁ _ i₂ _ h
    exact σ.injective h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨σ.symm j, by simp [Function.comp_apply, hj], by simp⟩

/-! ## Product PMF Structure -/

/-- **Key factorization**: The product PMF factors as `∏ₐ θ(a)^(countVector xs a)`.

    This is the categorical generalization of `bernoulliProductPMF_eq_power`:
    instead of `θ^k (1-θ)^(n-k)`, we get `∏ₐ θ(a)^(nₐ)` where `nₐ` is the
    count of symbol `a` in the word. -/
theorem categoricalProductPMF_eq_power {k n : ℕ} (θ : Fin k → ℝ) (xs : Fin n → Fin k) :
    categoricalProductPMF θ xs = ∏ a : Fin k, θ a ^ countVector xs a := by
  classical
  unfold categoricalProductPMF countVector
  rw [← Finset.prod_fiberwise_of_maps_to (g := xs) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  congr 1
  ext a
  have : ∀ i ∈ Finset.univ.filter (fun x => xs x = a), θ (xs i) = θ a := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; rw [hi]
  rw [Finset.prod_eq_pow_card this]

/-- The product PMF depends only on the count vector, not the specific word. -/
theorem categoricalProductPMF_depends_on_counts {k n : ℕ}
    (θ : Fin k → ℝ) (xs₁ xs₂ : Fin n → Fin k)
    (h : ∀ a : Fin k, countVector xs₁ a = countVector xs₂ a) :
    categoricalProductPMF θ xs₁ = categoricalProductPMF θ xs₂ := by
  simp [categoricalProductPMF_eq_power, h]

/-- The product PMF is nonneg on the simplex. -/
theorem categoricalProductPMF_nonneg {k n : ℕ} (θ : ProbSimplex k) (xs : Fin n → Fin k) :
    0 ≤ categoricalProductPMF (θ : Fin k → ℝ) xs := by
  unfold categoricalProductPMF
  exact Finset.prod_nonneg (fun i _ => probSimplex_nonneg θ (xs i))

/-- The product PMF is at most 1 on the simplex. -/
theorem categoricalProductPMF_le_one {k n : ℕ} (θ : ProbSimplex k) (xs : Fin n → Fin k) :
    categoricalProductPMF (θ : Fin k → ℝ) xs ≤ 1 := by
  rw [categoricalProductPMF_eq_power]
  refine Finset.prod_le_one (fun a _ => ?_) (fun a _ => ?_)
  · exact pow_nonneg (probSimplex_nonneg θ a) _
  · exact pow_le_one₀ (probSimplex_nonneg θ a) (by
      have hsum := probSimplex_sum_one θ
      have := Finset.single_le_sum (fun j _ => probSimplex_nonneg θ j) (Finset.mem_univ a)
      linarith)

/-! ## Categorical Mixture -/

/-- A categorical mixture is a probability distribution on categorical sequences
    defined by integrating categorical product PMFs against a mixing measure
    on the probability simplex `Δ_{k-1}`.

    This generalizes `BernoulliMixture` (which mixes over `[0,1]`). -/
structure CategoricalMixture (k : ℕ) where
  /-- The mixing measure on `ℝ^k` (supported on the simplex). -/
  mixingMeasure : Measure (Fin k → ℝ)
  /-- The mixing measure is a probability measure. -/
  isProbability : IsProbabilityMeasure mixingMeasure
  /-- The mixing measure is supported on the probability simplex. -/
  support_simplex : mixingMeasure (stdSimplex ℝ (Fin k))ᶜ = 0

namespace CategoricalMixture

variable {k : ℕ}

/-- The probability of a specific categorical sequence under a mixture. -/
def prob {n : ℕ} (M : CategoricalMixture k) (xs : Fin n → Fin k) : ℝ :=
  ∫ θ in stdSimplex ℝ (Fin k), categoricalProductPMF θ xs ∂M.mixingMeasure

/-- The probability depends only on the count vector, not the specific word.

    This is the fundamental sufficiency result: for a categorical mixture,
    the count vector `(n₁, ..., nₖ)` captures all information about the word. -/
theorem prob_depends_only_on_counts {n : ℕ} (M : CategoricalMixture k)
    (xs₁ xs₂ : Fin n → Fin k) (h : ∀ a : Fin k, countVector xs₁ a = countVector xs₂ a) :
    M.prob xs₁ = M.prob xs₂ := by
  unfold prob
  congr 1
  funext θ
  exact categoricalProductPMF_depends_on_counts θ xs₁ xs₂ h

/-- The probability is permutation-invariant (exchangeable).

    This is the "easy direction" of categorical de Finetti: any mixture of
    i.i.d. categorical distributions is exchangeable. -/
theorem prob_perm_invariant {n : ℕ} (M : CategoricalMixture k)
    (xs : Fin n → Fin k) (σ : Equiv.Perm (Fin n)) :
    M.prob (xs ∘ σ) = M.prob xs :=
  M.prob_depends_only_on_counts (xs ∘ σ) xs (countVector_perm xs σ)

end CategoricalMixture

/-! ## Connection to Binary Case

For `k = 2`, we recover the Bernoulli case:
- `ProbSimplex 2 ≅ [0,1]` via `θ ↦ θ(1)` (the "success probability")
- `categoricalProductPMF θ xs = θ(0)^n₀ · θ(1)^n₁ = (1-p)^n₀ · p^n₁`
  where `p = θ(1)` and `n₀ + n₁ = n`
- `countVector xs 0 = countFalse xs`, `countVector xs 1 = countTrue xs`

The categorical mixture `CategoricalMixture 2` is isomorphic to `BernoulliMixture`
via the identification `θ(1) ↔ p ∈ [0,1]`.

See `Mettapedia.Logic.DeFinetti` for the binary-specific formalization
and `Mettapedia.Logic.EvidenceDirichlet` for the corresponding k-ary Bayesian update.
-/

end Mettapedia.Logic.CategoricalDeFinetti
