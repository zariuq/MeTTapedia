import Mettapedia.InformationTheory.ShannonEntropy.Faddeev
import Mettapedia.InformationTheory.ShannonEntropy.Shannon1948
import Mettapedia.InformationTheory.ShannonEntropy.ShannonKhinchin
import KnuthSkilling.Information.InformationEntropy

/-!
# Unified Entropy Axiom Interface

This file compares finite Shannon-entropy axiom systems and transfers their
derived properties. Faddeev's binary-continuity formulation derives full
continuity, maximality and expansibility instead of assuming them.

## Unified Interface

This file also bridges different probability distribution representations:
- **ProbVec n** = `↥(stdSimplex ℝ (Fin n))` - mathlib-grounded
- **ProbDist n** = `{p : Fin n → ℝ, nonneg, sum_one}` - K&S standalone

The bridge (`probVecEquivProbDist`) shows they are equivalent, allowing unified
definitions of entropy and KL divergence across all formalization approaches:
1. **Mathlib** - `stdSimplex`, `negMulLog`, `klFun`
2. **Axiomatics** - Faddeev (4 clauses), Shannon-Khinchin (5 clauses plus relabeling)
3. **K&S Derivation** - Shannon entropy derived from variational framework

## Axiom Presentations

### Faddeev (1956) - 4 Clauses
- **F1**: Binary continuity ONLY (H(p, 1-p) is continuous)
- **F2**: Symmetry (permutation invariance)
- **F3**: Recursivity (chain rule / grouping property)
- **F4**: Normalization H(1/2, 1/2) = 1

### Shannon-Khinchin (1957) - 5 Named Clauses, Plus Relabeling
- **Relabeling**: Symmetry is an explicit field for ordered probability vectors
- **SK1**: FULL continuity (on ALL distributions)
- **SK2**: Maximality (uniform distribution maximizes entropy)
- **SK3**: Expansibility (adding zero probability doesn't change entropy)
- **SK4**: Strong additivity (= recursivity)
- **SK5**: Normalization

### Shannon (1948) - 4 Clauses, with Normalization Separate
- Relabeling invariance
- FULL continuity
- Monotonicity on uniform distributions
- Grouping (= recursivity)
- Optional fair-coin normalization (not a field of `Shannon1948Entropy`)

## Key Insight: Faddeev DERIVES What Others ASSUME

| Property | Faddeev | Shannon | Shannon-Khinchin |
|----------|---------|---------|------------------|
| Binary continuity | **ASSUMES** | - | - |
| Full continuity | **DERIVES** | ASSUMES | ASSUMES |
| Symmetry | ASSUMES | ASSUMES | ASSUMES (relabeling) |
| Recursivity | ASSUMES | ASSUMES | ASSUMES |
| Monotonicity | **DERIVES** | ASSUMES | - |
| Maximality | **DERIVES** | - | ASSUMES |
| Expansibility | **DERIVES** | - | ASSUMES |
| Named clauses | 4 | 4, plus optional normalization | 5, plus relabeling |

These counts describe the presentations used here, not independence of their
assumptions or an absolute minimum number of axioms.

## Main Results

* `faddeev_F_eq_log2` - F(n) = log₂(n), downstream of Faddeev Lemma 9
* `faddeev_F_monotone` - Monotonicity derived from F = log₂
* `faddeev_implies_shannon_monotonicity` - Faddeev implies Shannon's monotonicity axiom
* `faddeev_implies_sk_maximality` - Faddeev implies S-K's maximality axiom

## References

* Faddeev, D.K. "On the concept of entropy" (1956) - Binary-continuity characterization
* Shannon, C.E. "A Mathematical Theory of Communication" (1948) - Original axioms
* Khinchin, A.I. "Mathematical Foundations of Information Theory" (1957) - Reformulation
-/

namespace Mettapedia.InformationTheory

open Finset Real

/-! ## Derived Axioms

These theorems demonstrate that Faddeev's axioms derive properties that Shannon and
Shannon-Khinchin explicitly assume. They are consequences of the normalized
entropy uniqueness theorem, not merely comparisons of presentation sizes.
-/

/-- **KEY THEOREM**: Faddeev axioms imply Shannon's monotonicity axiom.

Monotonicity follows from the uniform-entropy formula and is not assumed. -/
theorem faddeev_implies_shannon_monotonicity (E : FaddeevEntropy) :
    ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n), m ≤ n →
    E.H (uniformDist m hm) ≤ E.H (uniformDist n hn) :=
  fun m n hm hn hmn => faddeev_F_monotone (m := m) (n := n) E hm hn hmn

/-- **KEY THEOREM**: Faddeev axioms imply Shannon-Khinchin's maximality axiom.

Full entropy uniqueness transfers Shannon entropy's uniform upper bound.
The statement is weak maximality; it does not assert a strict inequality. -/
theorem faddeev_implies_sk_maximality (E : FaddeevEntropy) :
    ∀ (n : ℕ) (hn : 0 < n) (p : ProbVec n),
    E.H p ≤ E.H (uniformDist n hn) := by
  intro n hn p
  simpa using faddeev_maximality (n := n) E hn p

/-- **KEY THEOREM**: Faddeev axioms imply Shannon-Khinchin's expansibility axiom.

Adding a zero probability outcome doesn't change entropy. -/
theorem faddeev_implies_sk_expansibility (E : FaddeevEntropy) :
    ∀ (n : ℕ) (p : ProbVec n),
    E.H (expandZero p) = E.H p := by
  intro n p
  simpa using faddeev_expansibility (n := n) E p

/-! ## Presentation Count Comparison

The historical names below are retained. The theorems compare the named-clause
counts only; they are not proofs of axiom independence or absolute minimality.
-/

/-- Number of the four Faddeev clauses in this presentation. -/
def faddeev_axiom_count : ℕ := 4

/-- Number of clauses in the normalized Shannon presentation: four structural
    clauses plus optional normalization, which is not a `Shannon1948Entropy` field. -/
def shannon1948_axiom_count : ℕ := 5

/-- Number of clauses labeled SK1-SK5; the explicit relabeling field is separate. -/
def shannonKhinchin_axiom_count : ℕ := 5

/-- Four Faddeev clauses are fewer than the five clauses in the normalized
    Shannon presentation counted here. -/
theorem faddeev_more_minimal_than_shannon :
    faddeev_axiom_count < shannon1948_axiom_count := by
  simp only [faddeev_axiom_count, shannon1948_axiom_count]
  norm_num

/-- Four Faddeev clauses are fewer than the five clauses labeled SK1-SK5. -/
theorem faddeev_more_minimal_than_shannonKhinchin :
    faddeev_axiom_count < shannonKhinchin_axiom_count := by
  simp only [faddeev_axiom_count, shannonKhinchin_axiom_count]
  norm_num

/-! ## Hierarchy Coercions

Every Faddeev entropy gives rise to a Shannon-Khinchin entropy
(and vice versa, showing they characterize the same function).
-/

/-- Coercion: Any Faddeev entropy induces a Shannon-Khinchin entropy.

This shows Faddeev's axioms are **sufficient** for Shannon-Khinchin's. -/
noncomputable def FaddeevEntropy.toShannonKhinchin (E : FaddeevEntropy) :
    ShannonKhinchinEntropy where
  H := E.H
  -- SK1: Full continuity - DERIVED from Faddeev via uniqueness
  continuity := fun {n} => by
    simpa using faddeev_full_continuity (n := n) E
  symmetry := fun p σ => E.symmetry p σ
  -- SK2: Maximality - DERIVED from Faddeev
  maximality := fun hn p => faddeev_implies_sk_maximality E _ hn p
  -- SK3: Expansibility - DERIVED from Faddeev
  expansibility := fun p => faddeev_implies_sk_expansibility E _ p
  -- SK4: Strong additivity = Faddeev's recursivity (identical)
  strong_additivity := E.recursivity
  -- SK5: Normalization (identical)
  normalization := E.normalization

/-! ## Summary: From Binary Continuity to Full Uniqueness

Faddeev's 1956 result is remarkable: with just 4 axioms (and notably, only
**binary** continuity instead of full continuity), he uniquely characterized
Shannon entropy.

The proof strategy (formalized in Faddeev.lean):
1. From recursivity: F(mn) = F(m) + F(n) (multiplicativity)
2. From normalization: F(2) = 1, hence F(2^k) = k
3. From binary continuity: The "entropy increment" λₙ = F(n) - F(n-1) → 0
4. Via prime power analysis (Lemma 8-9): All c_p = F(p)/log(p) are equal
5. Conclusion: F(n) = log₂(n) for all n ≥ 1
6. Grouping determines rational binary entropy; continuity and density give all
   binary distributions, and recursivity extends uniqueness to every arity
7. Uniform monotonicity, full continuity, maximality and expansibility follow

Together with symmetry and normalization, binary continuity and recursivity
force the normalized Shannon formula on every finite probability vector.
-/

/-! ## Bridge: ProbVec ↔ ProbDist

The two probability distribution types in this codebase are mathematically equivalent.
This section provides bidirectional conversions and proves key properties transfer.
-/

/-- Alias for the K&S ProbDist type. -/
abbrev KSProbDist (n : ℕ) :=
  KnuthSkilling.Information.InformationEntropy.ProbDist n

namespace ProbVec

/-- Convert ProbVec (mathlib-grounded) to ProbDist (K&S). -/
def toProbDist {n : ℕ} (p : ProbVec n) : KSProbDist n where
  p := p.1
  nonneg := p.nonneg
  sum_one := p.sum_eq_one

end ProbVec

namespace KSProbDist

/-- Convert ProbDist (K&S) to ProbVec (mathlib-grounded). -/
def toProbVec {n : ℕ} (p : KSProbDist n) : ProbVec n :=
  ⟨p.p, p.nonneg, p.sum_one⟩

end KSProbDist

/-- The conversions are inverses (ProbVec → ProbDist → ProbVec). -/
@[simp]
theorem ProbVec.toProbDist_toProbVec {n : ℕ} (p : ProbVec n) :
    (p.toProbDist).toProbVec = p := rfl

/-- The conversions are inverses (ProbDist → ProbVec → ProbDist). -/
@[simp]
theorem KSProbDist.toProbVec_toProbDist {n : ℕ} (p : KSProbDist n) :
    (p.toProbVec).toProbDist = p := by
  ext i
  simp only [KSProbDist.toProbVec, ProbVec.toProbDist]

/-- **Equivalence**: ProbVec n ≃ ProbDist n. -/
def probVecEquivProbDist (n : ℕ) : ProbVec n ≃ KSProbDist n where
  toFun := ProbVec.toProbDist
  invFun := KSProbDist.toProbVec
  left_inv := fun _ => rfl
  right_inv := fun p => by simp

/-! ## Shannon Entropy Equivalence

The three entropy definitions in this codebase agree (up to normalization). -/

open KnuthSkilling.Information.InformationEntropy in
/-- **Shannon entropy equivalence**: InformationTheory.shannonEntropy = K&S.shannonEntropy
    via the bridge.

Both use the formula -Σ pᵢ log pᵢ with the 0·log(0) = 0 convention. -/
theorem shannonEntropy_eq_ks_shannonEntropy {n : ℕ} (p : ProbVec n) :
    shannonEntropy p =
      KnuthSkilling.Information.InformationEntropy.shannonEntropy
        p.toProbDist := by
  unfold shannonEntropy
  rw [KnuthSkilling.Information.InformationEntropy.shannonEntropy_eq'
    p.toProbDist]
  simp only [negMulLog, ProbVec.toProbDist]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext i
  ring

/-! ## Uniform Distribution Bridge -/

open KnuthSkilling.Information.InformationEntropy in
/-- The InformationTheory uniform distribution matches K&S uniform distribution. -/
theorem uniformDist_eq_ks_uniformDist (n : ℕ) (hn : 0 < n) :
    (uniformDist n hn).toProbDist =
      KnuthSkilling.Information.InformationEntropy.uniformDist n hn :=
    by
  apply KnuthSkilling.Information.InformationEntropy.ProbDist.ext
  intro i
  simp [ProbVec.toProbDist, uniformDist,
        KnuthSkilling.Information.InformationEntropy.uniformDist]

/-! ## KL Divergence Interface

Unified KL divergence across ProbVec and ProbDist. -/

open KnuthSkilling.Information.InformationEntropy in
/-- **Unified KL divergence** on ProbVec via the bridge. -/
noncomputable def klDivergenceVec {n : ℕ} (P Q : ProbVec n)
    (hQ_pos : ∀ i, P.1 i ≠ 0 → 0 < Q.1 i) : ℝ :=
  klDivergence P.toProbDist Q.toProbDist (by intro i hi; exact hQ_pos i hi)

open KnuthSkilling.Information.InformationEntropy in
open scoped ENNReal in
/-- **Extended KL divergence** (ℝ≥0∞-valued) on ProbVec. -/
noncomputable def klDivergenceVecTop {n : ℕ} (P Q : ProbVec n) : ENNReal :=
  klDivergenceTop P.toProbDist Q.toProbDist

open KnuthSkilling.Information.InformationEntropy in
/-- **Gibbs' inequality**: KL divergence is non-negative. -/
theorem klDivergenceVec_nonneg {n : ℕ} (P Q : ProbVec n)
    (hQ_pos : ∀ i, P.1 i ≠ 0 → 0 < Q.1 i) :
    0 ≤ klDivergenceVec P Q hQ_pos :=
  klDivergence_nonneg' P.toProbDist Q.toProbDist (by intro i hi; exact hQ_pos i hi)

open KnuthSkilling.Information.InformationEntropy in
/-- **Shannon entropy via KL**: S(P) = log(n) - D(P ‖ Uniform_n). -/
theorem shannonEntropy_via_klDivergence {n : ℕ} (P : ProbVec n) (hn : 0 < n) :
    shannonEntropy P = log n - klDivergenceVec P (uniformDist n hn) (by
      intro i _; unfold uniformDist; simp; positivity) := by
  rw [shannonEntropy_eq_ks_shannonEntropy]
  -- Use the K&S theorem connecting entropy and KL divergence
  have hU_pos : ∀ i, P.toProbDist.p i ≠ 0 →
      0 <
          (KnuthSkilling.Information.InformationEntropy.uniformDist n
                hn).p
            i := by
    intro i _
    simp [KnuthSkilling.Information.InformationEntropy.uniformDist]
    positivity
  have h := klDivergence_uniform_eq_log_sub_shannonEntropy P.toProbDist hn
  -- The goal: KS.shannonEntropy P.toProbDist = log n - klDivergenceVec ...
  -- h says: KS.klDivergence P.toProbDist (KS.uniformDist n hn) ... = log n - KS.shannonEntropy P.toProbDist
  -- So KS.shannonEntropy = log n - KS.klDivergence
  -- And klDivergenceVec unfolds to KS.klDivergence P.toProbDist (uniformDist n hn).toProbDist
  -- which equals KS.klDivergence P.toProbDist (KS.uniformDist n hn) by uniformDist_eq_ks_uniformDist
  have heq : (uniformDist n hn).toProbDist =
      KnuthSkilling.Information.InformationEntropy.uniformDist n hn :=
    uniformDist_eq_ks_uniformDist n hn
  simp only [klDivergenceVec, heq]
  linarith

end Mettapedia.InformationTheory
