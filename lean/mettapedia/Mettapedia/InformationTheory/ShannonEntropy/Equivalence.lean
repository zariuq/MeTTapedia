import Mettapedia.InformationTheory.ShannonEntropy.Faddeev
import Mettapedia.InformationTheory.ShannonEntropy.ShannonKhinchin

/-!
# Equivalence of Faddeev and Shannon–Khinchin Axioms

This file contains "glue" theorems relating the two axiom systems.
It is intentionally kept separate so that `ShannonKhinchin.lean` does not
depend on `Faddeev.lean`.

## Key Result: Logical Equivalence

Faddeev ↔ Shannon-Khinchin (same function characterized)

## Assumptions and Derived Properties

Both systems characterize the same entropy function, but:
- **Faddeev**: 4 axioms (binary continuity, symmetry, recursivity, normalization)
- **Shannon-Khinchin**: 5 named clauses (full continuity, maximality, expansibility,
  strong additivity, normalization), plus explicit relabeling invariance

Faddeev's 4 axioms **derive** what Shannon-Khinchin's 5 axioms **assume**:
- Full continuity, maximality and expansibility follow from full entropy uniqueness

See `Interface.lean` for the derived properties and presentation-count comparisons.
Those counts do not establish independence or absolute minimality.

## Main Theorems

* `faddeev_implies_shannonKhinchin` - Faddeev axioms imply S-K axioms
* `shannonKhinchin_implies_faddeev` - S-K axioms imply Faddeev axioms
* `faddeev_iff_shannonKhinchin` - Logical equivalence of the systems
-/

namespace Mettapedia.InformationTheory

open Finset Real

/-! ## Axiom-System Bridges -/

/-- Faddeev axioms imply Shannon-Khinchin axioms.

This direction uses Faddeev-side corollaries (`faddeev_full_continuity`,
`faddeev_maximality`, `faddeev_expansibility`) proved via full entropy uniqueness. -/
theorem faddeev_implies_shannonKhinchin (E : FaddeevEntropy) :
    ∃ (E' : ShannonKhinchinEntropy), ∀ (n : ℕ) (p : ProbVec n), E'.H p = E.H p := by
  use
    { H := @E.H
      continuity := fun {n} => faddeev_full_continuity E
      symmetry := fun p σ => E.symmetry p σ
      maximality := fun {n} hn p => faddeev_maximality E hn p
      expansibility := fun {n} p => faddeev_expansibility E p
      strong_additivity := fun p h => E.recursivity p h
      normalization := E.normalization }
  intro n p
  rfl

/-- Shannon-Khinchin axioms imply Faddeev axioms.

Strong additivity is exactly the “group first two outcomes” form of Faddeev’s
recursivity axiom, and full continuity implies binary continuity. -/
theorem shannonKhinchin_implies_faddeev (E : ShannonKhinchinEntropy) :
    ∃ (E' : FaddeevEntropy), ∀ (n : ℕ) (p : ProbVec n), E'.H p = E.H p := by
  use
    { H := @E.H
      continuous_binary := shannonKhinchin_continuous_binary E
      symmetry := fun p σ => E.symmetry p σ
      recursivity := fun p h => E.strong_additivity p h
      normalization := E.normalization }
  intro n p
  rfl

/-- Existence of a Faddeev entropy iff existence of a Shannon–Khinchin entropy.

This is a minimal “inhabitedness” bridge, useful for keeping later files honest
about which axiom system they assume. -/
theorem faddeev_iff_shannonKhinchin :
    (∃ (_E : FaddeevEntropy), True) ↔ (∃ (_E : ShannonKhinchinEntropy), True) := by
  constructor
  · intro ⟨E, _⟩
    obtain ⟨E', _⟩ := faddeev_implies_shannonKhinchin E
    exact ⟨E', trivial⟩
  · intro ⟨E, _⟩
    obtain ⟨E', _⟩ := shannonKhinchin_implies_faddeev E
    exact ⟨E', trivial⟩

/-! ## Summary: Why Faddeev Matters

The two axiom-system bridges preserve the entropy function. The separate
`faddeev_iff_shannonKhinchin` theorem records only equivalence of inhabitedness.

| System | Axiom Count | Key Assumptions |
|--------|-------------|-----------------|
| **Faddeev** | 4 | Binary continuity only |
| Shannon-Khinchin | 5, plus relabeling | Full continuity, maximality, expansibility |

The power of Faddeev's approach lies in the **Lemma 9 proof** (in `Faddeev.lean`):
1. From recursivity: `F(mn) = F(m) + F(n)` (multiplicativity)
2. From normalization: `F(2) = 1`, hence `F(2^k) = k`
3. Via prime power analysis: All `c_p = F(p)/log(p)` are equal
4. Conclusion: `F(n) = log₂(n)` for all `n ≥ 1`
5. Grouping, binary continuity and induction extend uniqueness to every arity
6. Full continuity, monotonicity, maximality and expansibility follow

This is formalized in `faddeev_F_eq_log2` and `faddeev_F_monotone`.
-/

end Mettapedia.InformationTheory
