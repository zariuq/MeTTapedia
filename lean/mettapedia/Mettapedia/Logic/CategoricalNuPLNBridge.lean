/-
LLM primer:
- `boolToFin2 xs i` = if xs i then 1 else 0 (Bool → Fin 2 encoding)
- `countVector_fin2_eq_countTrue` : key bijection for k=2 compatibility
- `categorical_pln_sufficiency` : the theorem to cite for categorical PLN
- `Fin.prod_univ_two` expands ∏ over Fin 2 into f 0 * f 1
-/
import Mettapedia.Logic.CategoricalMixture
import Mettapedia.Logic.DeFinetti
import Mettapedia.Logic.EvidenceDirichlet

/-!
# Categorical ↔ νPLN Bridge

This file connects the categorical (Fin k) infrastructure from `CategoricalMixture.lean`
to the binary PLN evidence chain from `DeFinetti.lean` and `EvidenceDirichlet.lean`.

## Main Results

* `countVector_fin2_eq_countTrue` : For k=2, countVector(1) = countTrue
* `countVector_fin2_eq_countFalse` : For k=2, countVector(0) = countFalse
* `categoricalProductPMF_fin2_eq_bernoulliProductPMF` : Categorical PMF at k=2 = Bernoulli PMF
* `countVector_to_multiEvidence` : Convert count vector to MultiEvidence
* `categorical_pln_sufficiency` : Categorical mixture prob depends only on MultiEvidence

## Integration

This file establishes that `CategoricalMixture 2 ≅ BernoulliMixture` (shape-level),
connecting the categorical generalization back to the binary PLN master chain
(`nupln_master_chain` in DeFinetti.lean) and the k-ary evidence aggregation
(`EvidenceDirichlet.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.CategoricalNuPLNBridge

open Mettapedia.Logic.CategoricalDeFinetti
open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.Exchangeability
open Mettapedia.Logic.EvidenceDirichlet
open Finset BigOperators

/-! ## Bool ↔ Fin 2 Encoding -/

/-- Encode a Bool word as a Fin 2 word: true ↦ 1, false ↦ 0. -/
def boolToFin2 {n : ℕ} (xs : Fin n → Bool) : Fin n → Fin 2 :=
  fun i => if xs i then 1 else 0

/-! ## countVector ↔ countTrue/countFalse (k=2) -/

/-- For k=2, countVector at index 1 equals countTrue (via Bool ↔ Fin 2). -/
theorem countVector_fin2_eq_countTrue {n : ℕ} (xs : Fin n → Bool) :
    countVector (boolToFin2 xs) 1 = countTrue xs := by
  classical
  unfold countVector boolToFin2 countTrue
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_cases hx : xs i = true
    · exact hx
    · simp [hx] at h
  · intro h
    simp [h]

/-- For k=2, countVector at index 0 equals countFalse. -/
theorem countVector_fin2_eq_countFalse {n : ℕ} (xs : Fin n → Bool) :
    countVector (boolToFin2 xs) 0 = countFalse xs := by
  classical
  unfold countVector boolToFin2 countFalse
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_cases hx : xs i = true
    · simp [hx] at h
    · exact Bool.eq_false_iff.mpr hx
  · intro h
    simp [h]

/-! ## CategoricalProductPMF = BernoulliProductPMF at k=2 -/

/-- For k=2, categorical product PMF equals Bernoulli product PMF
    under the identification `θ = ![1 - p, p]`, i.e. `θ(0) = 1-p, θ(1) = p`.

    This is the core compatibility theorem: the categorical generalization
    truly subsumes the binary theory. -/
theorem categoricalProductPMF_fin2_eq_bernoulliProductPMF {n : ℕ}
    (p : ℝ) (xs : Fin n → Bool) :
    categoricalProductPMF (![1 - p, p]) (boolToFin2 xs)
    = bernoulliProductPMF p xs := by
  rw [categoricalProductPMF_eq_power, bernoulliProductPMF_eq_power]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [countVector_fin2_eq_countTrue, countVector_fin2_eq_countFalse]
  ring

/-! ## countVector → MultiEvidence Bridge -/

/-- Convert a categorical count vector to MultiEvidence.
    This packages the categorical sufficient statistic as PLN evidence. -/
def countVector_to_multiEvidence {k n : ℕ} (xs : Fin n → Fin k) : MultiEvidence k :=
  ⟨fun a => countVector xs a⟩

/-- The total of converted evidence equals word length. -/
theorem countVector_to_multiEvidence_total {k n : ℕ} (xs : Fin n → Fin k) :
    (countVector_to_multiEvidence xs).total = n := by
  unfold countVector_to_multiEvidence MultiEvidence.total
  exact countVector_sum xs

/-- Permutation invariance: evidence from a permuted word equals evidence from the original. -/
theorem countVector_to_multiEvidence_perm {k n : ℕ}
    (xs : Fin n → Fin k) (σ : Equiv.Perm (Fin n)) :
    countVector_to_multiEvidence (xs ∘ σ) = countVector_to_multiEvidence xs := by
  ext a
  simp [countVector_to_multiEvidence, countVector_perm]

/-! ## Categorical PLN Sufficiency -/

/-- **Categorical PLN sufficiency**: Mixture probability depends only on MultiEvidence.

    This is the k-ary generalization of the binary sufficiency in `nupln_master_chain`:
    for any categorical mixture, two words with the same count vector (= same MultiEvidence)
    have the same probability. Combined with `EvidenceDirichlet`, this shows that
    PLN evidence aggregation is exact Bayesian inference for exchangeable categorical domains. -/
theorem categorical_pln_sufficiency {k : ℕ} (M : CategoricalMixture k)
    {n : ℕ} (xs₁ xs₂ : Fin n → Fin k)
    (h : countVector_to_multiEvidence xs₁ = countVector_to_multiEvidence xs₂) :
    M.prob xs₁ = M.prob xs₂ := by
  apply M.prob_depends_only_on_counts
  intro a
  have := congr_arg (fun e => e.counts a) h
  simpa [countVector_to_multiEvidence] using this

/-! ## Binary Compatibility: countVector_to_multiEvidence matches binaryEvidence_to_multi -/

/-- For k=2, the categorical evidence bridge agrees with the binary evidence bridge.

    Note: `binaryEvidence_to_multi n_pos n_neg = ⟨![n_pos, n_neg]⟩` stores
    index 0 = first arg, index 1 = second arg.  Since `boolToFin2` maps
    false ↦ 0 and true ↦ 1, the natural correspondence is
    `countVector 0 = countFalse` and `countVector 1 = countTrue`. -/
theorem countVector_to_multiEvidence_fin2_eq {n : ℕ} (xs : Fin n → Bool) :
    countVector_to_multiEvidence (boolToFin2 xs) =
    binaryEvidence_to_multi (countFalse xs) (countTrue xs) := by
  ext a
  simp only [countVector_to_multiEvidence, binaryEvidence_to_multi]
  fin_cases a <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
    countVector_fin2_eq_countFalse, countVector_fin2_eq_countTrue]

end Mettapedia.Logic.CategoricalNuPLNBridge
