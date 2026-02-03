import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropyMathlib
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.ScaleCompleteness
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.OpIsAddition

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# K&S → Mathlib Probability Bridge

This file provides the **grounded** bridge from Knuth-Skilling axioms to mathlib's
probability theory, maintaining the theoretical justification at every step.

## Key Design Principle

Everything is **derived from K&S axioms** where possible:
- `op → +` is DERIVED via the representation theorem (see `Additive/Axioms/OpIsAddition.lean`)
- Finite probability distributions emerge from finite atomic K&S algebras
- σ-additivity (for countable case) requires the **natural extension** of
  `SigmaCompleteEvents` + `KSScaleComplete` + `KSScottContinuous`

## The Grounded Path

```
K&S Axioms + KSSeparation
        │
        │  DERIVED: Θ(op x y) = Θ x + Θ y  (representation theorem)
        ↓
RepresentationResult S  (Additive/Representation.lean)
        │
        ├─── Finite case ───────────────────────────────────
        │    ProbDist n  (InformationEntropy.lean)
        │         │
        │         │  toMeasureTop (InformationEntropyMathlib.lean)
        │         ↓
        │    Measure (Fin n) [IsProbabilityMeasure]
        │         │
        │         │  toProbabilityMeasure (this file)
        │         ↓
        │    ProbabilityMeasure (Fin n)
        │
        └── See InformationEntropyMathlib.lean for the implementation
```

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
- `Additive/Axioms/OpIsAddition.lean` - Documents that op ≅ + is DERIVED
- `InformationEntropyMathlib.lean` - Existing finite bridge
- `ScaleCompleteness.lean` - σ-additivity theorem
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.MathlibProbability

open MeasureTheory Classical
open Mettapedia.ProbabilityTheory.KnuthSkilling.Information
open scoped BigOperators ENNReal

/-! ## Section 1: Finite Case - ProbDist → ProbabilityMeasure

The finite case is already handled in `InformationEntropyMathlib.lean`:
- `ProbDist.toMeasureTop` converts to `Measure (Fin n)`
- `instIsProbabilityMeasure_toMeasureTop` proves it's a probability measure

We add the wrapper to create `ProbabilityMeasure (Fin n)` (the subtype).
-/

namespace FiniteProbDist

variable {n : ℕ}

/-- Convert a K&S-grounded finite probability distribution to mathlib's `ProbabilityMeasure`.

This completes the path:
  K&S → Θ representation → ProbDist n → Measure (Fin n) → ProbabilityMeasure (Fin n)

The measure construction is in `InformationEntropyMathlib.lean`; this just wraps it. -/
noncomputable def toProbabilityMeasure (P : InformationEntropy.ProbDist n) :
    @ProbabilityMeasure (Fin n) ⊤ :=
  ⟨P.toMeasureTop, InformationEntropy.ProbDist.instIsProbabilityMeasure_toMeasureTop P⟩

/-- The underlying measure of the probability measure is the same as `toMeasureTop`. -/
@[simp]
theorem toProbabilityMeasure_toMeasure (P : InformationEntropy.ProbDist n) :
    (toProbabilityMeasure P : Measure (Fin n)) = P.toMeasureTop := rfl

/-- Coercion to measure preserves singleton values. -/
theorem toProbabilityMeasure_singleton (P : InformationEntropy.ProbDist n) (i : Fin n) :
    (toProbabilityMeasure P : Measure (Fin n)) {i} = ENNReal.ofReal (P.p i) := by
  simp [toProbabilityMeasure, InformationEntropy.ProbDist.toMeasureTop_apply_singleton]

/-- The probability measure has total mass 1. -/
theorem toProbabilityMeasure_univ (P : InformationEntropy.ProbDist n) :
    (toProbabilityMeasure P : Measure (Fin n)) Set.univ = 1 := by
  simp only [toProbabilityMeasure_toMeasure, InformationEntropy.ProbDist.toMeasureTop_univ]

end FiniteProbDist

/-! ## Section 2: Countable Case - KSMeasure Construction

For countable spaces, we use the σ-additivity theorem from `ScaleCompleteness.lean`.
This requires the natural extension axioms:
- `SigmaCompleteEvents E`: countable joins exist in the event algebra
- `KSScaleComplete S R`: the scale is sequentially complete
- `KSScottContinuous E S R`: the valuation is Scott continuous

These are **necessary** additional axioms (cannot be derived from basic K&S),
but they are mathematically natural extensions of the finite theory.

The main theorem `ks_sigma_additive` in ScaleCompleteness.lean shows that under these
axioms, the composition μ = Θ ∘ v is σ-additive for pairwise disjoint sequences.
-/

/-- Package for building a measure from general σ-additive data.

This structure collects all the data needed to construct a `Measure` from
a σ-additive function on a measurable space. -/
structure SigmaAdditiveMeasureData (E : Type*) [MeasurableSpace E] where
  /-- The valuation function assigning real values to measurable sets -/
  μ : Set E → ℝ
  /-- Non-negativity -/
  μ_nonneg : ∀ s : Set E, MeasurableSet s → 0 ≤ μ s
  /-- Empty set has measure 0 -/
  μ_empty : μ ∅ = 0
  /-- σ-additivity for disjoint countable unions -/
  μ_sigma_additive : ∀ ⦃f : ℕ → Set E⦄,
    (∀ n, MeasurableSet (f n)) →
    Pairwise (Function.onFun Disjoint f) →
    (Summable (μ ∘ f)) ∧ μ (⋃ n, f n) = ∑' n, μ (f n)

namespace SigmaAdditiveMeasureData

variable {E : Type*} [MeasurableSpace E]

/-- Convert SigmaAdditiveMeasureData to a mathlib Measure. -/
noncomputable def toMeasure (m : SigmaAdditiveMeasureData E) : Measure E :=
  Measure.ofMeasurable
    (fun s _ => ENNReal.ofReal (m.μ s))
    (by simp [m.μ_empty])
    (by
      intro f hf hd
      have h_nonneg : ∀ n, 0 ≤ m.μ (f n) := fun n => m.μ_nonneg (f n) (hf n)
      obtain ⟨h_sum, h_eq⟩ := m.μ_sigma_additive hf hd
      simp only
      rw [h_eq, ENNReal.ofReal_tsum_of_nonneg h_nonneg h_sum])

/-- The measure assigns the expected value to measurable sets. -/
theorem toMeasure_apply (m : SigmaAdditiveMeasureData E) (s : Set E) (hs : MeasurableSet s) :
    m.toMeasure s = ENNReal.ofReal (m.μ s) :=
  Measure.ofMeasurable_apply s hs

end SigmaAdditiveMeasureData

/-! ## Section 3: Summary

### What This File Provides

1. **Finite case** (`FiniteProbDist.toProbabilityMeasure`):
   - Bridge from `ProbDist n` to `ProbabilityMeasure (Fin n)`
   - Uses existing construction in `InformationEntropyMathlib.lean`

2. **Countable case** (`SigmaAdditiveMeasureData`):
   - Generic structure for packaging σ-additive functions as measures
   - The K&S-specific construction using `ks_sigma_additive` can be built on top

### Theoretical Foundation

The key insight is that **nothing is assumed that could have been derived**:
- `op → +` is DERIVED via representation theorem (see `Additive/Axioms/OpIsAddition.lean`)
- Finite additivity is DERIVED from K&S axioms
- σ-additivity requires NECESSARY additional axioms, treated as natural extensions

### Validation: Connection to Information Theory

The bridges in `InformationEntropyMathlib.lean` and `DivergenceMathlib.lean` show that
K&S-derived quantities match mathlib's definitions:

**KL Divergence** (`InformationEntropyMathlib.lean`):
  - `klDiv_toMeasureTop_eq_klDivergenceTop`: K&S `klDivergenceTop P Q` = mathlib `klDiv P.toMeasureTop Q.toMeasureTop`

**Countable Divergence** (`DivergenceMathlib.lean`):
  - `Countable.klDiv_toMeasure_eq_divergenceInfTop`: K&S countable divergence = mathlib klDiv

These validation theorems confirm that the K&S → mathlib bridge preserves the
mathematical content of the K&S axioms.

This completes the theoretical grounding of K&S probability theory in mathlib.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.MathlibProbability
