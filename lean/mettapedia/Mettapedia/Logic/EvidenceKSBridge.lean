import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic

/-!
# BinaryEvidence ↔ Knuth-Skilling Bridge: Intuitionistic Probability Theory

This file establishes the connection between PLN BinaryEvidence and Knuth-Skilling theory
at the **distributive lattice level** (PlausibilitySpace).

## Key Insight

K&S theory has multiple levels:
1. **PlausibilitySpace** (DistribLattice + BoundedOrder) - Valuations, conditional probability
2. **ComplementedLattice** (adds complements) - Product rule derivations
3. **BooleanAlgebra** (full LEM) - Sum rule, P(¬A) = 1 - P(A)

BinaryEvidence is a **Frame** (complete Heyting algebra), which gives:
- ✅ PlausibilitySpace (distributive lattice with ⊤, ⊥)
- ✅ Heyting implication (intuitionistic →)
- ❌ NOT ComplementedLattice (Heyting negation ≠ Boolean complement)
- ❌ NOT BooleanAlgebra (LEM fails)

Therefore, K&S theory at the PlausibilitySpace level applies to BinaryEvidence,
giving us **intuitionistic probability theory** where:
- Valuations are well-defined
- Conditional probability works
- But P(¬A) ≠ 1 - P(A) in general

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- PLN_KS_Bridge.lean (proves BinaryEvidence is NOT Boolean)
-/

namespace Mettapedia.Logic.EvidenceKSBridge

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## BinaryEvidence IS a PlausibilitySpace

These `#check` statements verify the instances exist:
-/

-- BinaryEvidence is a PlausibilitySpace (distributive lattice with ⊤, ⊥).
-- This follows automatically from BinaryEvidence being a Frame.
#check (inferInstance : PlausibilitySpace BinaryEvidence)

-- BinaryEvidence is a distributive lattice (inherited from Frame).
#check (inferInstance : DistribLattice BinaryEvidence)

-- BinaryEvidence has bounded order (⊤ and ⊥).
#check (inferInstance : BoundedOrder BinaryEvidence)

/-! ## Valuations on BinaryEvidence

A K&S valuation maps events to [0,1] with:
- Monotonicity: a ≤ b → val(a) ≤ val(b)
- Boundaries: val(⊥) = 0, val(⊤) = 1

BinaryEvidence's `toStrength` and `toConfidence` are NOT valuations in this sense
because they project the 2D BinaryEvidence structure to 1D. Instead, they lose information.

However, we CAN define valuations on BinaryEvidence that respect the partial order.
-/

/-- The "strength projection" is NOT a K&S Valuation because it doesn't respect
    the partial order: e₁ ≤ e₂ does NOT imply toStrength(e₁) ≤ toStrength(e₂).

    Counterexample: ⟨1, 0⟩ ≤ ⟨1, 1⟩ (coordinatewise)
    but toStrength(⟨1, 0⟩) = 1 > 0.5 = toStrength(⟨1, 1⟩)

    Adding negative evidence DECREASES strength while INCREASING in the order!
-/
theorem strength_not_monotone :
    ∃ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ ∧ e₂.toStrength < e₁.toStrength := by
  -- ⟨1, 0⟩ ≤ ⟨1, 1⟩ but toStrength(⟨1, 0⟩) = 1 > 0.5 = toStrength(⟨1, 1⟩)
  refine ⟨⟨1, 0⟩, ⟨1, 1⟩, ?_, ?_⟩
  · -- ⟨1, 0⟩ ≤ ⟨1, 1⟩
    simp [BinaryEvidence.le_def]
  · -- toStrength(⟨1, 1⟩) < toStrength(⟨1, 0⟩)
    simp only [BinaryEvidence.toStrength, BinaryEvidence.total]
    -- Need: (1 / (1 + 1)) < (1 / (1 + 0))
    -- i.e., 0.5 < 1
    norm_num

/-- The "total evidence" (pos + neg) IS monotone and could form a valuation
    (after normalization). -/
theorem total_monotone :
    ∀ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ → e₁.total ≤ e₂.total := by
  intro e₁ e₂ h
  simp only [BinaryEvidence.le_def, BinaryEvidence.total] at h ⊢
  exact add_le_add h.1 h.2

/-! ## Conditional Probability on BinaryEvidence

Even without Boolean structure, we can define conditional "plausibility":
  plaus(a | b) = plaus(a ⊓ b) / plaus(b)

For BinaryEvidence, the meet is coordinatewise min:
  e₁ ⊓ e₂ = ⟨min e₁.pos e₂.pos, min e₁.neg e₂.neg⟩
-/

/-- BinaryEvidence meet is coordinatewise minimum. -/
theorem evidence_inf_def (e₁ e₂ : BinaryEvidence) :
    e₁ ⊓ e₂ = ⟨min e₁.pos e₂.pos, min e₁.neg e₂.neg⟩ := rfl

/-- BinaryEvidence join is coordinatewise maximum. -/
theorem evidence_sup_def (e₁ e₂ : BinaryEvidence) :
    e₁ ⊔ e₂ = ⟨max e₁.pos e₂.pos, max e₁.neg e₂.neg⟩ := rfl

/-! ## Heyting Implication on BinaryEvidence

BinaryEvidence has Heyting implication (→) which satisfies:
  a ⊓ b ≤ c ↔ a ≤ (b → c)

This is the "intuitionistic" implication, NOT classical.
The Heyting negation ¬a := (a → ⊥) does NOT satisfy a ⊔ ¬a = ⊤.
-/

/-- BinaryEvidence has Heyting implication from Frame structure. -/
theorem evidence_has_himp : ∀ e₁ e₂ : BinaryEvidence, ∃ h : BinaryEvidence, h = e₁ ⇨ e₂ :=
  fun e₁ e₂ => ⟨e₁ ⇨ e₂, rfl⟩

/-- BinaryEvidence Heyting negation (complement). -/
theorem evidence_compl_def (e : BinaryEvidence) :
    eᶜ = e ⇨ ⊥ := rfl

/-! ## What K&S Theory Applies

At the PlausibilitySpace level, we have:
1. Monotone valuations val : BinaryEvidence → [0,1]
2. Conditional valuations val(a | b) = val(a ⊓ b) / val(b)
3. Some independence structure

What we DON'T have without Boolean:
1. P(¬A) = 1 - P(A) -- Heyting negation is weaker
2. Full sum rule P(A ∨ B) = P(A) + P(B) - P(A ∧ B) -- requires complements
-/

/-- Summary: BinaryEvidence satisfies K&S axioms at the PlausibilitySpace level,
    giving intuitionistic probability theory.

    This is witnessed by the PlausibilitySpace instance being inferrable. -/
theorem evidence_satisfies_ks_plausibility_axioms :
    Nonempty (PlausibilitySpace BinaryEvidence) :=
  ⟨inferInstance⟩

/-! ## Connection to PLN Operations

The PLN operations (hplus, tensor) on BinaryEvidence are ADDITIONAL structure
beyond what K&S PlausibilitySpace provides:

- `hplus` (⊕): BinaryEvidence aggregation / revision
- `tensor` (⊗): Sequential composition

These correspond to:
- hplus: "more observations" → combine evidence counts
- tensor: "independent conjunction" → multiply (scale by confidence)

The K&S framework at PlausibilitySpace level doesn't prescribe these operations;
they come from PLN's specific interpretation of BinaryEvidence as (n⁺, n⁻) counts.
-/

/-- BinaryEvidence hplus is additive in counts. -/
theorem evidence_hplus_additive (e₁ e₂ : BinaryEvidence) :
    (e₁ + e₂).pos = e₁.pos + e₂.pos ∧
    (e₁ + e₂).neg = e₁.neg + e₂.neg := by
  constructor <;> rfl

/-- BinaryEvidence tensor scales counts. -/
theorem evidence_tensor_multiplicative (e₁ e₂ : BinaryEvidence) :
    (e₁ * e₂).pos = e₁.pos * e₂.pos ∧
    (e₁ * e₂).neg = e₁.neg * e₂.neg := by
  constructor <;> rfl

end Mettapedia.Logic.EvidenceKSBridge
