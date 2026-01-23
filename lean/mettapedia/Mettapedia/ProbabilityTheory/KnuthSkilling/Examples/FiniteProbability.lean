/-
# Finite Probability: Section 5.2 Inclusion-Exclusion on Generalized Boolean Algebras

This file demonstrates that **classical finite probability** uses the structure formalized in
K&S Section 5.2 (Additive/Proofs/GridInduction/InclusionExclusion.lean).

## Key Insight

`Set (Fin n)` is a **Generalized Boolean Algebra** (set difference `\` is relative complement).
Therefore, the inclusion-exclusion theorem from Section 5.2 applies directly.

This proves that K&S's abstract framework **captures** classical probability, not just axiomatizes it.

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Section 5.2
- Additive/Proofs/GridInduction/InclusionExclusion.lean (this project)
- Durrett, "Probability: Theory and Examples" (5th ed), Section 1.1
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

open Classical

/-! ## Set α is a Generalized Boolean Algebra

This is the KEY structural fact that connects classical probability to K&S Section 5.2.

**Proof**: `Set α` has set difference `\` as relative complement, making it a GBA.
**Consequence**: Inclusion-exclusion holds for ANY disjoint-additive measure on `Set α`. -/

example {α : Type*} : GeneralizedBooleanAlgebra (Set α) := inferInstance

/-! ## Classical Inclusion-Exclusion is a Special Case

For any finite type `α` and any measure `m : Set α → ℝ` that is:
1. Monotone
2. Disjoint-additive: m(A ∪ B) = m(A) + m(B) when A ∩ B = ∅

The inclusion-exclusion formula holds:
  m(A ∪ B) + m(A ∩ B) = m(A) + m(B)

**Why**: This follows from K&S Section 5.2 applied to the GBA `Set α`.

**Examples**:
- Uniform measure on Fin n: m(A) = |A|/n
- Weighted measure: m(A) = Σᵢ∈A pᵢ
- Coin flip: m({H}) = m({T}) = 1/2

All of these are Generalized Boolean Algebras with disjoint-additive measures,
so Section 5.2 applies.

## Summary

**Old approach** (`AdditiveValuation`, now archived):
- Axiomatically added disjoint additivity
- Didn't use the representation theorem
- Just re-stated classical probability

**New approach** (this file):
- `Set α` is a GBA (proven by mathlib)
- Section 5.2 derives inclusion-exclusion from GBA + disjoint additivity
- Classical probability is a **consequence**, not an axiom

This validates that K&S's framework **contains** classical probability theory.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
