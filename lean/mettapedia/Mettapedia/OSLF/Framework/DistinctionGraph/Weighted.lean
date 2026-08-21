import Mettapedia.OSLF.Framework.DistinctionGraph
import Mettapedia.OSLF.Framework.EvidenceSemantics
import Mettapedia.PLN.Evidence.EvidenceKSBridge
import Mettapedia.PLN.Evidence.HeytingValuationOnEvidence

/-!
# Weighted Distinction Graph + Projection Separation

Extends the distinction graph with two edge-weight types:

1. **BinaryEvidence-lattice weight** (`indistWeightE`): Heyting implication over all formulas.
   Lives in `BinaryEvidence` (complete Heyting algebra / Frame). Order-theoretic, preserves
   the full imprecision structure.

2. **Strength-scalar weight** (`indistWeightS`): Projects to `ℝ≥0∞` via `toStrength`.
   Lossy — loses the neg/pos decomposition.

The projection-separation theorem establishes two different facts:
- total evidence `pos + neg` is monotone in the coordinatewise order;
- the strength ratio `pos / (pos + neg)` is not monotone in that order.

This is a property of the chosen evidence readouts, not a restriction on K&S
one-way scalar fidelity.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Goertzel, "Graphtropy" (2026)
- Goertzel, "Graph Probability" (2026)
-/

namespace Mettapedia.OSLF.Framework.DistinctionGraph.Weighted

open Mettapedia.OSLF.Framework.DistinctionGraph
open Mettapedia.OSLF.Framework.EvidenceSemantics
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidenceKSBridge
open Mettapedia.PLN.Evidence.HeytingValuationOnEvidence
open Mettapedia.OSLF.Formula

open scoped ENNReal

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-! ## Weighted Edge Definitions -/

/-- BinaryEvidence-lattice edge weight: measures how well φ-truth at p implies φ-truth at q,
across all formulas φ. Uses the Heyting implication `⇨` in BinaryEvidence's Frame.

High weight (close to ⊤) = very indistinguishable.
Low weight (close to ⊥) = easily distinguished.

This is the "imprecise" (2D) view that preserves full BinaryEvidence structure. -/
noncomputable def indistWeightE (R : Pat → Pat → Prop) (I : EvidenceAtomSem)
    (p q : Pat) : BinaryEvidence :=
  ⨅ φ : OSLFFormula, semE R I φ p ⇨ semE R I φ q

/-- Strength-scalar edge weight: projects the BinaryEvidence-lattice weight to [0,∞] via
`toStrength`. This is the "scalar" (1D) view that loses the pos/neg decomposition. -/
noncomputable def indistWeightS (R : Pat → Pat → Prop) (I : EvidenceAtomSem)
    (p q : Pat) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (indistWeightE R I p q)

/-! ## Basic Properties -/

/-- Self-weight is ⊤: every pattern is maximally indistinguishable from itself.
Uses `himp_self : a ⇨ a = ⊤`. -/
theorem indistWeightE_self_top (R : Pat → Pat → Prop) (I : EvidenceAtomSem)
    (p : Pat) : indistWeightE R I p p = ⊤ := by
  simp only [indistWeightE, himp_self]
  exact @iInf_const _ _ _ ⊤ ⟨.top⟩

/-- Edge weight is bounded above by ⊤. -/
theorem indistWeightE_le_top (R : Pat → Pat → Prop) (I : EvidenceAtomSem)
    (p q : Pat) : indistWeightE R I p q ≤ ⊤ :=
  le_top

/-! ## Projection Separation -/

/-- Total evidence is monotone in the coordinatewise evidence order. -/
theorem totalEvidence_monotone :
    ∀ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ → e₁.total ≤ e₂.total :=
  total_monotone

/-- The strength projection is not monotone in the coordinatewise evidence order.
Adding negative evidence increases in the lattice order but decreases strength.
 -/
theorem strengthProjection_not_monotone :
    ∃ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ ∧ e₂.toStrength < e₁.toStrength :=
  strength_not_monotone

/-- Total evidence and strength are distinct scalar readouts: the former is
monotone, while the latter is not.

Specifically:
- `total` preserves evidence ordering
- `toStrength` does NOT preserve the lattice order on BinaryEvidence

Thus coordinatewise-ordered evidence values need not remain ordered after the
strength projection. -/
theorem projection_separation :
    -- Positive: total is monotone
    (∀ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ → e₁.total ≤ e₂.total) ∧
    -- Negative: strength is not monotone
    (∃ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ ∧ e₂.toStrength < e₁.toStrength) :=
  ⟨total_monotone, strength_not_monotone⟩

/-- BinaryEvidence has no Boolean complement: there exists an evidence value with no
complement. -/
theorem no_boolean_complement_witness :
    ∃ e : BinaryEvidence, ∀ c : BinaryEvidence, ¬(e ⊔ c = ⊤ ∧ e ⊓ c = ⊥) :=
  evidence_not_boolean

/-! ## Structural Properties -/

/-- The bidirectional BinaryEvidence weight: min of both implication directions.
This gives a symmetric measure of "mutual indistinguishability". -/
noncomputable def indistWeightE_sym (R : Pat → Pat → Prop) (I : EvidenceAtomSem)
    (p q : Pat) : BinaryEvidence :=
  indistWeightE R I p q ⊓ indistWeightE R I q p

/-- The symmetric weight is truly symmetric. -/
theorem indistWeightE_sym_comm (R : Pat → Pat → Prop) (I : EvidenceAtomSem)
    (p q : Pat) : indistWeightE_sym R I p q = indistWeightE_sym R I q p := by
  simp only [indistWeightE_sym, inf_comm]

/-- Self-symmetric-weight is ⊤. -/
theorem indistWeightE_sym_self_top (R : Pat → Pat → Prop) (I : EvidenceAtomSem)
    (p : Pat) : indistWeightE_sym R I p p = ⊤ := by
  simp [indistWeightE_sym, indistWeightE_self_top]

/-- BinaryEvidence-richer-than-strength: same strength can correspond to
different lattice weights with different confidence. The scalar view is lossy. -/
theorem scalar_view_lossy :
    ∃ e₁ e₂ : BinaryEvidence,
      _root_.Mettapedia.PLN.Evidence.EvidenceIntervalBounds.strength e₁ =
        _root_.Mettapedia.PLN.Evidence.EvidenceIntervalBounds.strength e₂ ∧
      e₁ ≠ e₂ ∧ totalEvidence e₁ ≠ totalEvidence e₂ :=
  evidence_richer_than_strength

end Mettapedia.OSLF.Framework.DistinctionGraph.Weighted
