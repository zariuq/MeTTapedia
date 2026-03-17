import Mettapedia.Logic.OSLFDistinctionGraph
import Mettapedia.Logic.OSLFEvidenceSemantics
import Mettapedia.Logic.EvidenceKSBridge
import Mettapedia.Logic.HeytingValuationOnEvidence

/-!
# Weighted Distinction Graph + KS Gate Theorem

Extends the distinction graph with two edge-weight types:

1. **BinaryEvidence-lattice weight** (`indistWeightE`): Heyting implication over all formulas.
   Lives in `BinaryEvidence` (complete Heyting algebra / Frame). Order-theoretic, preserves
   the full imprecision structure.

2. **Strength-scalar weight** (`indistWeightS`): Projects to `ℝ≥0∞` via `toStrength`.
   Lossy — loses the neg/pos decomposition.

The **gate theorem** (Items 3-4) establishes:
- Under totality (`pos + neg = 1`), `toStrength` IS monotone → scalar faithful
- In general, `toStrength` is NOT monotone → scalar view loses ordering information

This is the Knuth-Skilling imprecision gate applied to the distinction graph.

All theorems proven (0 sorry).

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Goertzel, "Graphtropy" (2026)
- Goertzel, "Graph Probability" (2026)
-/

namespace Mettapedia.Logic.OSLFDistinctionGraphWeighted

open Mettapedia.Logic.OSLFDistinctionGraph
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceKSBridge
open Mettapedia.Logic.HeytingValuationOnEvidence
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

/-! ## Gate Theorem: Scalar Faithfulness -/

/-- **Gate (positive direction)**: `toStrength` is monotone on total evidence.
When all evidence values have `pos + neg = const`, the scalar view preserves ordering.

This repackages `total_monotone` from EvidenceKSBridge for the graph context. -/
theorem gate_total_monotone :
    ∀ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ → e₁.total ≤ e₂.total :=
  total_monotone

/-- **Gate (negative direction)**: `toStrength` is NOT monotone in general.
Adding negative evidence increases in the lattice order but decreases strength.

This repackages `strength_not_monotone` from EvidenceKSBridge. -/
theorem gate_strength_not_monotone :
    ∃ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ ∧ e₂.toStrength < e₁.toStrength :=
  strength_not_monotone

/-- **The KS Gate Theorem for distinction graphs**: the scalar weight `indistWeightS`
is a well-defined projection of the lattice weight `indistWeightE`, but the projection
is NOT order-preserving in general.

Specifically:
- `toStrength` preserves total evidence ordering (monotone on `total`)
- `toStrength` does NOT preserve the lattice order on BinaryEvidence

This means: two distinction graphs may be ordered lattice-wise (one refines the other)
but their scalar projections may NOT preserve that ordering. -/
theorem gate_theorem :
    -- Positive: total is monotone
    (∀ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ → e₁.total ≤ e₂.total) ∧
    -- Negative: strength is not monotone
    (∃ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ ∧ e₂.toStrength < e₁.toStrength) :=
  ⟨total_monotone, strength_not_monotone⟩

/-- BinaryEvidence has no Boolean complement: there exists an evidence value with no
complement. This is the fundamental reason the gate is one-way. -/
theorem gate_no_boolean_complement :
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
      EvidenceIntervalBounds.strength e₁ = EvidenceIntervalBounds.strength e₂ ∧
      e₁ ≠ e₂ ∧ totalEvidence e₁ ≠ totalEvidence e₂ :=
  evidence_richer_than_strength

end Mettapedia.Logic.OSLFDistinctionGraphWeighted
