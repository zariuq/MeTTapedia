import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic

/-!
# Evidence ↔ Knuth-Skilling Bridge: Intuitionistic Probability Theory

This file establishes the connection between PLN Evidence and Knuth-Skilling theory
at the **distributive lattice level** (PlausibilitySpace).

## Key Insight

K&S theory has multiple levels:
1. **PlausibilitySpace** (DistribLattice + BoundedOrder) - Valuations, conditional probability
2. **ComplementedLattice** (adds complements) - Product rule derivations
3. **BooleanAlgebra** (full LEM) - Sum rule, P(¬A) = 1 - P(A)

Evidence is a **Frame** (complete Heyting algebra), which gives:
- ✅ PlausibilitySpace (distributive lattice with ⊤, ⊥)
- ✅ Heyting implication (intuitionistic →)
- ❌ NOT ComplementedLattice (Heyting negation ≠ Boolean complement)
- ❌ NOT BooleanAlgebra (LEM fails)

Therefore, K&S theory at the PlausibilitySpace level applies to Evidence,
giving us **intuitionistic probability theory** where:
- Valuations are well-defined
- Conditional probability works
- But P(¬A) ≠ 1 - P(A) in general

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- PLN_KS_Bridge.lean (proves Evidence is NOT Boolean)
-/

namespace Mettapedia.Logic.EvidenceKSBridge

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## Evidence IS a PlausibilitySpace

These `#check` statements verify the instances exist:
-/

-- Evidence is a PlausibilitySpace (distributive lattice with ⊤, ⊥).
-- This follows automatically from Evidence being a Frame.
#check (inferInstance : PlausibilitySpace Evidence)

-- Evidence is a distributive lattice (inherited from Frame).
#check (inferInstance : DistribLattice Evidence)

-- Evidence has bounded order (⊤ and ⊥).
#check (inferInstance : BoundedOrder Evidence)

/-! ## Valuations on Evidence

A K&S valuation maps events to [0,1] with:
- Monotonicity: a ≤ b → val(a) ≤ val(b)
- Boundaries: val(⊥) = 0, val(⊤) = 1

Evidence's `toStrength` and `toConfidence` are NOT valuations in this sense
because they project the 2D Evidence structure to 1D. Instead, they lose information.

However, we CAN define valuations on Evidence that respect the partial order.
-/

/-- The "strength projection" is NOT a K&S Valuation because it doesn't respect
    the partial order: e₁ ≤ e₂ does NOT imply toStrength(e₁) ≤ toStrength(e₂).

    Counterexample: ⟨1, 0⟩ ≤ ⟨1, 1⟩ (coordinatewise)
    but toStrength(⟨1, 0⟩) = 1 > 0.5 = toStrength(⟨1, 1⟩)

    Adding negative evidence DECREASES strength while INCREASING in the order!
-/
theorem strength_not_monotone :
    ∃ e₁ e₂ : Evidence, e₁ ≤ e₂ ∧ e₂.toStrength < e₁.toStrength := by
  -- ⟨1, 0⟩ ≤ ⟨1, 1⟩ but toStrength(⟨1, 0⟩) = 1 > 0.5 = toStrength(⟨1, 1⟩)
  refine ⟨⟨1, 0⟩, ⟨1, 1⟩, ?_, ?_⟩
  · -- ⟨1, 0⟩ ≤ ⟨1, 1⟩
    simp [Evidence.le_def]
  · -- toStrength(⟨1, 1⟩) < toStrength(⟨1, 0⟩)
    simp only [Evidence.toStrength, Evidence.total]
    -- Need: (1 / (1 + 1)) < (1 / (1 + 0))
    -- i.e., 0.5 < 1
    norm_num

/-- The "total evidence" (pos + neg) IS monotone and could form a valuation
    (after normalization). -/
theorem total_monotone :
    ∀ e₁ e₂ : Evidence, e₁ ≤ e₂ → e₁.total ≤ e₂.total := by
  intro e₁ e₂ h
  simp only [Evidence.le_def, Evidence.total] at h ⊢
  exact add_le_add h.1 h.2

/-! ## Conditional Probability on Evidence

Even without Boolean structure, we can define conditional "plausibility":
  plaus(a | b) = plaus(a ⊓ b) / plaus(b)

For Evidence, the meet is coordinatewise min:
  e₁ ⊓ e₂ = ⟨min e₁.pos e₂.pos, min e₁.neg e₂.neg⟩
-/

/-- Evidence meet is coordinatewise minimum. -/
theorem evidence_inf_def (e₁ e₂ : Evidence) :
    e₁ ⊓ e₂ = ⟨min e₁.pos e₂.pos, min e₁.neg e₂.neg⟩ := rfl

/-- Evidence join is coordinatewise maximum. -/
theorem evidence_sup_def (e₁ e₂ : Evidence) :
    e₁ ⊔ e₂ = ⟨max e₁.pos e₂.pos, max e₁.neg e₂.neg⟩ := rfl

/-! ## Heyting Implication on Evidence

Evidence has Heyting implication (→) which satisfies:
  a ⊓ b ≤ c ↔ a ≤ (b → c)

This is the "intuitionistic" implication, NOT classical.
The Heyting negation ¬a := (a → ⊥) does NOT satisfy a ⊔ ¬a = ⊤.
-/

/-- Evidence has Heyting implication from Frame structure. -/
theorem evidence_has_himp : ∀ e₁ e₂ : Evidence, ∃ h : Evidence, h = e₁ ⇨ e₂ :=
  fun e₁ e₂ => ⟨e₁ ⇨ e₂, rfl⟩

/-- Evidence Heyting negation (complement). -/
theorem evidence_compl_def (e : Evidence) :
    eᶜ = e ⇨ ⊥ := rfl

/-! ## What K&S Theory Applies

At the PlausibilitySpace level, we have:
1. Monotone valuations val : Evidence → [0,1]
2. Conditional valuations val(a | b) = val(a ⊓ b) / val(b)
3. Some independence structure

What we DON'T have without Boolean:
1. P(¬A) = 1 - P(A) -- Heyting negation is weaker
2. Full sum rule P(A ∨ B) = P(A) + P(B) - P(A ∧ B) -- requires complements
-/

/-- Summary: Evidence satisfies K&S axioms at the PlausibilitySpace level,
    giving intuitionistic probability theory.

    This is witnessed by the PlausibilitySpace instance being inferrable. -/
theorem evidence_satisfies_ks_plausibility_axioms :
    Nonempty (PlausibilitySpace Evidence) :=
  ⟨inferInstance⟩

/-! ## Connection to PLN Operations

The PLN operations (hplus, tensor) on Evidence are ADDITIONAL structure
beyond what K&S PlausibilitySpace provides:

- `hplus` (⊕): Evidence aggregation / revision
- `tensor` (⊗): Sequential composition

These correspond to:
- hplus: "more observations" → combine evidence counts
- tensor: "independent conjunction" → multiply (scale by confidence)

The K&S framework at PlausibilitySpace level doesn't prescribe these operations;
they come from PLN's specific interpretation of Evidence as (n⁺, n⁻) counts.
-/

/-- Evidence hplus is additive in counts. -/
theorem evidence_hplus_additive (e₁ e₂ : Evidence) :
    (e₁ + e₂).pos = e₁.pos + e₂.pos ∧
    (e₁ + e₂).neg = e₁.neg + e₂.neg := by
  constructor <;> rfl

/-- Evidence tensor scales counts. -/
theorem evidence_tensor_multiplicative (e₁ e₂ : Evidence) :
    (e₁ * e₂).pos = e₁.pos * e₂.pos ∧
    (e₁ * e₂).neg = e₁.neg * e₂.neg := by
  constructor <;> rfl

end Mettapedia.Logic.EvidenceKSBridge
