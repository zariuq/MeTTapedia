import Mettapedia.InformationTheory.Basic
import Mettapedia.InformationTheory.ShannonEntropy.Properties
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Shannon-Khinchin Axiomatic Characterization of Shannon Entropy

This file formalizes the Shannon-Khinchin axioms (1957) for entropy.

## Shannon-Khinchin Axioms (5 + relabeling invariance)

0. **Symmetry / Relabeling invariance**: H is invariant under permutations of outcomes.
   (Often treated as “built in” when entropy is viewed as a function of an *unordered* distribution.
   Since `ProbVec n` is represented as an ordered function `Fin n → ℝ`, we include this explicitly.)
1. **Continuity (SK1)**: H is continuous (full continuity on all ProbVec n)
2. **Maximality (SK2)**: For fixed n, H is maximized at the uniform distribution
3. **Expansibility (SK3)**: H(p₁,...,pₙ,0) = H(p₁,...,pₙ)
4. **Strong Additivity (SK4)**: Grouping/Chain rule for partitions
5. **Normalization (SK5)**: H(1/2, 1/2) = 1

## Comparison to Faddeev (1956)

Shannon-Khinchin explicitly ASSUMES what Faddeev DERIVES:

| Property | Shannon-Khinchin | Faddeev |
|----------|------------------|---------|
| Full continuity | **ASSUMES** | DERIVES (from F=log₂) |
| Maximality | **ASSUMES** | DERIVES (from F=log₂) |
| Expansibility | **ASSUMES** | DERIVES (from recursivity) |
| Binary continuity | - | ASSUMES |
| Symmetry (relabeling invariance) | **ASSUMES** | ASSUMES |
| Strong additivity | ASSUMES | ASSUMES (=recursivity) |
| Normalization | ASSUMES | ASSUMES |
| **Total axioms (in this encoding)** | **5 + relabeling** | **4** |

Faddeev's 1956 system is strictly more minimal. See `Interface.lean` for details.

## Main Results

* `ShannonKhinchinEntropy` - Structure encoding Shannon-Khinchin axioms
* `shannonShannonKhinchin` - Shannon entropy satisfies the axioms
* `shannonKhinchin_continuous_binary` - Full continuity implies binary continuity
* `shannonKhinchin_symmetry` - Permutation invariance lemma (projection of the axiom)

## References

* Khinchin, A.I. "Mathematical Foundations of Information Theory" (1957)
* Shannon, C.E. "A Mathematical Theory of Communication" (1948)
* Faddeev, D.K. "On the concept of entropy" (1956) - The minimal axiomatization
-/

namespace Mettapedia.InformationTheory

open Finset Real

/-! ## Shannon-Khinchin Axioms -/

/-- **Shannon-Khinchin entropy**: A family of functions H : ProbVec n → ℝ
    satisfying the Shannon-Khinchin axioms. -/
structure ShannonKhinchinEntropy where
  /-- The entropy function for each arity n ≥ 1 -/
  H : ∀ {n : ℕ}, ProbVec n → ℝ
  /-- SK1: Continuity (full continuity, not just binary) -/
  continuity : ∀ {n : ℕ}, Continuous (H (n := n))
  /-- Symmetry under permutations (relabeling invariance).

  In many textbook statements this is treated as "built in" (entropy depends only on the multiset
  of probabilities, not their ordering). Since `ProbVec n` is represented as an *ordered* function
  `Fin n → ℝ`, we include permutation invariance explicitly. -/
  symmetry : ∀ {n : ℕ} (p : ProbVec n) (σ : Equiv.Perm (Fin n)), H (permute σ p) = H p
  /-- SK2: Maximality - uniform distribution maximizes entropy -/
  maximality : ∀ {n : ℕ} (hn : 0 < n) (p : ProbVec n), H p ≤ H (uniformDist n hn)
  /-- SK3: Expansibility - adding a zero probability doesn't change entropy -/
  expansibility : ∀ {n : ℕ} (p : ProbVec n), H (expandZero p) = H p
  /-- SK4: Strong Additivity / Grouping axiom
      This is equivalent to Faddeev's recursivity but stated differently. -/
  strong_additivity : ∀ {n : ℕ} (p : ProbVec (n + 2)) (h : 0 < p.1 0 + p.1 1),
    H p = H (groupFirstTwo p h) + (p.1 0 + p.1 1) * H (normalizeBinary (p.1 0) (p.1 1)
      (p.nonneg 0) (p.nonneg 1) h)
  /-- Normalization: H(1/2, 1/2) = 1 -/
  normalization : H binaryUniform = 1

/-! ## Shannon Entropy Satisfies Shannon-Khinchin Axioms -/

/-- Shannon entropy (normalized) satisfies all of Shannon-Khinchin's axioms. -/
noncomputable def shannonShannonKhinchin : ShannonKhinchinEntropy where
  H := @shannonEntropyNormalized
  continuity := by
    intro n
    unfold shannonEntropyNormalized
    exact continuous_shannonEntropy.div_const _
  symmetry := fun p σ => by
    unfold shannonEntropyNormalized
    rw [shannonEntropy_permute]
  maximality := fun {n} hn p => by
    unfold shannonEntropyNormalized
    apply div_le_div_of_nonneg_right
    · rw [shannonEntropy_uniform n hn]
      exact shannonEntropy_le_log_card hn p
    · exact le_of_lt (log_pos one_lt_two)
  expansibility := fun p => by
    unfold shannonEntropyNormalized
    rw [shannonEntropy_expandZero]
  strong_additivity := fun p h => by
    unfold shannonEntropyNormalized
    rw [shannonEntropy_recursivity p h]
    ring
  normalization := shannonEntropyNormalized_binaryUniform

/-! ## Shannon-Khinchin Uniqueness Theorem -/

/-! ### Helper Lemmas for Uniqueness -/

/-- F(2) = 1 follows from normalization since uniform_2 = binaryUniform. -/
theorem sk_F2_eq_one (E : ShannonKhinchinEntropy) :
    E.H (uniformDist 2 (by norm_num : 0 < 2)) = 1 := by
  have h : uniformDist 2 (by norm_num : 0 < 2) = binaryUniform := by
    apply Subtype.ext
    funext i
    fin_cases i
    · show (1 : ℝ) / 2 = (![1/2, 1 - 1/2] : Fin 2 → ℝ) 0
      simp only [Matrix.cons_val_zero]
    · show (1 : ℝ) / 2 = (![1/2, 1 - 1/2] : Fin 2 → ℝ) 1
      simp only [Matrix.cons_val_one]
      norm_num
  rw [h]
  exact E.normalization

/-- F(1) = 0 for any S-K entropy. The uniform distribution on 1 outcome is a point mass.

    Proof: Use maximality. For n = 1, any distribution p must satisfy p 0 = 1 (point mass).
    By maximality, H(p) ≤ H(uniform_1) = H(p), so H(uniform_1) = H(point mass).
    But we can also show H(point mass) = 0 using expansibility and strong additivity. -/
theorem sk_F1_eq_zero (E : ShannonKhinchinEntropy) :
    E.H (uniformDist 1 (by norm_num : 0 < 1)) = 0 := by
  -- For n = 1, uniform_1 is the unique point mass on Fin 1
  -- We prove F(1) = 0 by showing H(1, 0) = H(uniform_1) and then using
  -- the strong additivity structure.
  -- Key insight: expandZero (uniform_1) = (1, 0), and by expansibility
  -- H(1, 0) = H(uniform_1). Also, strong_additivity on (1, 0) gives:
  -- H(1, 0) = H(groupFirstTwo (1,0)) + 1 * H(normalizeBinary 1 0)
  -- groupFirstTwo (1, 0) = uniform_1, normalizeBinary 1 0 = (1, 0)
  -- So H(1, 0) = H(uniform_1) + H(1, 0), which implies H(uniform_1) = 0
  set u1 := uniformDist 1 (by norm_num : 0 < 1) with hu1
  have h_expand : expandZero u1 = binaryDist 1 (by norm_num) (by norm_num) := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [expandZero, hu1, uniformDist, binaryDist]
    · simp [expandZero, hu1, uniformDist, binaryDist, Fin.snoc]
  have h_exp : E.H (binaryDist 1 (by norm_num) (by norm_num)) = E.H u1 := by
    simpa [h_expand] using E.expansibility u1
  -- Apply strong_additivity to p = (1, 0)
  set p := binaryDist 1 (by norm_num) (by norm_num) with hp
  have h_sum : 0 < p.1 0 + p.1 1 := by
    simp [hp, binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h_rec := E.strong_additivity p h_sum
  have h_sum_val : p.1 0 + p.1 1 = 1 := by
    simp [hp, binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h_sum_val] at h_rec
  have h_norm : normalizeBinary (p.1 0) (p.1 1) (p.nonneg 0) (p.nonneg 1) h_sum = p := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [hp, normalizeBinary, binaryDist, Matrix.cons_val_zero]
    · simp [hp, normalizeBinary, binaryDist, Matrix.cons_val_one]
  have h_group : groupFirstTwo p h_sum = u1 := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [groupFirstTwo, hu1, hp, binaryDist, uniformDist]
  rw [h_norm, h_group] at h_rec
  -- h_rec: E.H p = E.H u1 + E.H p
  have : E.H u1 = 0 := by linarith
  simpa [h_exp] using this

/-!
The Shannon–Khinchin uniqueness theorem is intentionally postponed in this file.

We currently use the `Shannon1948.lean` development as the primary “historical”
uniqueness path, and keep this file focused on the axiom interface plus
verification that `shannonEntropyNormalized` satisfies it.
-/
/-- Shannon-Khinchin entropy restricted to binary distributions is continuous.
    This follows from the full continuity axiom SK1. -/
theorem shannonKhinchin_continuous_binary (E : ShannonKhinchinEntropy) :
    Continuous (fun p : Set.Icc (0 : ℝ) 1 => E.H (binaryDist p.1 p.2.1 p.2.2)) := by
  -- binaryDist is continuous in p, and E.H is continuous on ProbVec 2
  have h1 : Continuous (fun p : Set.Icc (0 : ℝ) 1 => binaryDist p.1 p.2.1 p.2.2) := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · -- i = 0: need continuity of (fun p => ![p.1, 1-p.1] 0) = (fun p => p.1)
      exact continuous_subtype_val
    · -- i = 1: need continuity of (fun p => ![p.1, 1-p.1] 1) = (fun p => 1-p.1)
      exact continuous_const.sub continuous_subtype_val
  exact E.continuity.comp h1

/-- Shannon-Khinchin entropy is symmetric (invariant under permutation).

This follows from the S-K axioms via the uniqueness theorem:
After uniqueness, E.H = shannonEntropyNormalized which is symmetric.

Alternatively, it can be derived directly from the axioms using:
1. Maximality: uniform distribution maximizes
2. Expansibility + Strong Additivity: entropy depends only on multiset of probabilities
-/
theorem shannonKhinchin_symmetry (E : ShannonKhinchinEntropy) (p : ProbVec n) (σ : Equiv.Perm (Fin n)) :
    E.H (permute σ p) = E.H p := by
  simpa using E.symmetry p σ

end Mettapedia.InformationTheory
