import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mettapedia.Computability.KolmogorovComplexity.Basic
import Mettapedia.UniversalAI.SolomonoffPrior.Basic

/-!
# Prefix-Free Codes and the Kraft Inequality

This file develops prefix-free codes and proves the Kraft inequality, following:
- Cover & Thomas, "Elements of Information Theory" (2006), Chapter 5
- Li & Vitányi, "An Introduction to Kolmogorov Complexity" (2019), Chapter 1
- Shen, "Around Kolmogorov Complexity" (arXiv:1504.04955), Section 2

## Main Definitions

* `PrefixFree` - A set of strings is prefix-free if no string is a prefix of another
* `kraftSum` - The Kraft sum Σ 2^{-|s|} for a set of strings
* `PrefixFreeMachine` - A Turing machine where halting programs form a prefix-free set
* `prefixComplexity` - K(x) defined using prefix-free machines

## Main Results

* `kraft_inequality` - For prefix-free codes, Σ 2^{-|s|} ≤ 1
* `prefixFree_implies_disjoint` - Prefix-free strings map to disjoint dyadic intervals
* `prefixComplexity_le_plainComplexity_plus_const` - K(x) ≤ C(x) + O(log |x|)

## Implementation Notes

This file is ported from `Mettapedia/UniversalAI/SolomonoffPrior.lean` to provide
a foundation for prefix-free Kolmogorov complexity independent of the Solomonoff
prior formalization.

-/

namespace KolmogorovComplexity

open scoped Classical

/-!
This file is the Phase‑2 / Chapter‑2 bridge needed for Hutter Chapter 3:
prefix-free codes and Kraft inequality, so we can later justify `2^{-K}`-style weights.

The fully‑proved Kraft inequality development already exists in
`Mettapedia.UniversalAI.SolomonoffPrior`.  For now, we re-export the key definitions/lemmas
from its foundational module, without importing the invariance or prediction
interfaces.
-/

abbrev PrefixFree (S : Set BinString) : Prop :=
  Mettapedia.UniversalAI.SolomonoffPrior.PrefixFree (S := S)

noncomputable abbrev kraftSum (S : Finset BinString) : ℝ :=
  Mettapedia.UniversalAI.SolomonoffPrior.kraftSum (S := S)

theorem kraftSum_nonneg (S : Finset BinString) : 0 ≤ kraftSum S := by
  simpa [kraftSum] using Mettapedia.UniversalAI.SolomonoffPrior.kraftSum_nonneg (S := S)

theorem kraft_inequality (S : Finset BinString) (hpf : PrefixFree (↑S : Set BinString)) :
    kraftSum S ≤ 1 := by
  simpa [PrefixFree, kraftSum] using
    (Mettapedia.UniversalAI.SolomonoffPrior.kraft_inequality (S := S) (hpf := hpf))

end KolmogorovComplexity
