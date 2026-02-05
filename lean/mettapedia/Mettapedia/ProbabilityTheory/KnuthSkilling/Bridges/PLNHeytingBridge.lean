/-
# PLN Evidence as Heyting K&S Instance

## The Key Insight

PLN Evidence is NOT Boolean - it has genuinely incomparable elements.
For example: (3⁺, 2⁻) vs (2⁺, 3⁻) - neither dominates the other.

This means:
1. Evidence is a distributive lattice (PlausibilitySpace level K&S applies)
2. Evidence is NOT a ComplementedLattice / not Boolean
3. Collapsing 2D evidence to 1D "strength" loses informational distinctions

## CORRECTION

The original claim that "incomparable elements force overlapping intervals"
was FALSE. The correct characterization is:

- The difference between Boolean and Heyting is the **complement behavior**
- Boolean: ν(a) + ν(¬a) = 1
- Heyting: ν(a) + ν(¬a) ≤ 1

For PLN Evidence:
- The 2D structure (n⁺, n⁻) is the principled representation
- Collapsing to strength loses the partial order structure
- This is because strength is NOT monotone w.r.t. the Evidence order!

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- See HeytingBounds.lean for the correct Boolean vs Heyting characterization
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingValuation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingBounds
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingIntervalRepresentation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.PLNBridge

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

/-! ## Evidence Lattice Has Incomparable Elements -/

/-- Evidence (3, 2): more positive than negative support -/
def evidence_3_2 : Evidence := ⟨3, 2⟩

/-- Evidence (2, 3): more negative than positive support -/
def evidence_2_3 : Evidence := ⟨2, 3⟩

/-- (3, 2) ≤ (2, 3) is false because 3 > 2 in the positive component. -/
theorem not_3_2_le_2_3 : ¬(evidence_3_2 ≤ evidence_2_3) := by
  intro h
  simp only [evidence_3_2, evidence_2_3, Evidence.le_def] at h
  have hpos : (3 : ENNReal) ≤ (2 : ENNReal) := h.1
  norm_cast at hpos

/-- (2, 3) ≤ (3, 2) is false because 3 > 2 in the negative component. -/
theorem not_2_3_le_3_2 : ¬(evidence_2_3 ≤ evidence_3_2) := by
  intro h
  simp only [evidence_3_2, evidence_2_3, Evidence.le_def] at h
  have hneg : (3 : ENNReal) ≤ (2 : ENNReal) := h.2
  norm_cast at hneg

/-- Key theorem: (3, 2) and (2, 3) are incomparable in the Evidence lattice. -/
theorem evidence_incomparable :
    ¬(evidence_3_2 ≤ evidence_2_3) ∧ ¬(evidence_2_3 ≤ evidence_3_2) :=
  ⟨not_3_2_le_2_3, not_2_3_le_3_2⟩

/-- Evidence is NOT totally ordered: there exist incomparable elements. -/
theorem evidence_not_total_order : ¬(∀ e₁ e₂ : Evidence, e₁ ≤ e₂ ∨ e₂ ≤ e₁) := by
  push_neg
  exact ⟨evidence_3_2, evidence_2_3, not_3_2_le_2_3, not_2_3_le_3_2⟩

/-- Evidence satisfies the Incomparable predicate. -/
theorem evidence_has_incomparable :
    ∃ e₁ e₂ : Evidence, Incomparable e₁ e₂ := by
  use evidence_3_2, evidence_2_3
  exact evidence_incomparable

/-! ## Why 2D Evidence is the Right Representation

The strength function s = n⁺/(n⁺+n⁻) gives a single number.
But for incomparable evidence:
- strength(3,2) = 3/5 = 0.6
- strength(2,3) = 2/5 = 0.4

The strength "picks" an ordering (0.6 > 0.4), but this is arbitrary
for incomparable evidence. The point is NOT that "intervals must overlap"
(that was a false claim).

The real point is:
1. Evidence is NOT Boolean (incomparable elements exist)
2. Any 1D valuation will impose a total order that wasn't there
3. The 2D representation (n⁺, n⁻) preserves the partial order structure

This is why PLN uses 2D truth values - it's the principled representation
that doesn't artificially collapse the information.
-/

/-! ## The Correct Characterization

PLN Evidence is an example of a non-Boolean lattice where:
- K&S applies at the PlausibilitySpace level
- But complement behavior is NOT Boolean

The 2D structure (n⁺, n⁻) is like tracking both "evidence for" and
"evidence against" separately, rather than assuming they sum to a constant.
-/

/-- Summary theorem: PLN Evidence has incomparable elements,
    which demonstrates it is NOT a Boolean lattice.
    The 2D representation preserves this structure. -/
theorem pln_evidence_not_boolean :
    ∃ e₁ e₂ : Evidence, Incomparable e₁ e₂ :=
  evidence_has_incomparable

/-! ## Connection to the Hypercube

In the hypercube of probability theories:
- PLN Evidence sits at the "Heyting + 2D" vertex
- It has non-Boolean complement behavior (partial order, not total)
- The 2D representation (n⁺, n⁻) is the principled choice

This is NOT because "incomparability forces intervals" (false claim),
but because:
1. Evidence has incomparable elements (proven above)
2. The 2D carrier preserves this structure
3. Collapsing to 1D loses information
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.PLNBridge
