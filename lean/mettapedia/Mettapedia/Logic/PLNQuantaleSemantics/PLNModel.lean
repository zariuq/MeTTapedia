import Mettapedia.Logic.PLNQuantaleSemantics.CDLogic

/-!
# PLN Formal Model Theory

This file defines what a "PLN model" is formally: a compositional assignment
of Evidence values to propositions that respects logical structure.

## Key Definitions

1. **Model**: Assigns Evidence to propositions compositionally
2. **Monotonicity**: Logical entailment implies evidence ordering
3. **Compositional laws**: Meet/join preserved by evidence assignment

## Design Principle

We define models abstractly over any proposition type α. The key insight is that
PLN models are Evidence-enriched: instead of Boolean truth values, propositions
have Evidence values that track both positive and negative support.

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- Lawvere, "Metric spaces, generalized logic, and closed categories" (1973)
-/

namespace Mettapedia.Logic.PLNQuantaleSemantics.Model

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open Mettapedia.Logic.PLNQuantaleSemantics.CDLogic
open scoped ENNReal

/-! ## Basic Model Definition -/

/-- A PLN model assigns Evidence to propositions of type α.

    The key property is that evidence assignment respects the lattice structure:
    if we know A entails B (in the model), then evidence for A should imply
    evidence for B in the information ordering.
-/
structure PLNModel (α : Type*) where
  /-- Evidence assignment: each proposition gets an Evidence value -/
  evidence : α → Evidence

variable {α : Type*}

/-! ## Evidence-Based Validity -/

/-- A proposition is "valid" in a model if it has positive evidence and no negative evidence.
    This corresponds to the pTrue corner of the p-bit square. -/
def isValid (M : PLNModel α) (p : α) : Prop :=
  PBit.isTrue (M.evidence p)

/-- A proposition is "invalid" in a model if it has negative evidence and no positive evidence.
    This corresponds to the pFalse corner. -/
def isInvalid (M : PLNModel α) (p : α) : Prop :=
  PBit.isFalse (M.evidence p)

/-- A proposition is "unknown" in a model if it has no evidence either way.
    This corresponds to the pNeither corner. -/
def isUnknown (M : PLNModel α) (p : α) : Prop :=
  PBit.isNeither (M.evidence p)

/-- A proposition is "contradictory" in a model if it has both positive and negative evidence.
    This corresponds to the pBoth corner. -/
def isContradictory (M : PLNModel α) (p : α) : Prop :=
  PBit.isBoth (M.evidence p)

/-! ## Mutual Exclusivity of Validity States -/

theorem valid_not_invalid (M : PLNModel α) (p : α) (h : isValid M p) : ¬isInvalid M p :=
  isTrue_not_isFalse (M.evidence p) h

theorem valid_not_unknown (M : PLNModel α) (p : α) (h : isValid M p) : ¬isUnknown M p :=
  isTrue_not_isNeither (M.evidence p) h

theorem valid_not_contradictory (M : PLNModel α) (p : α) (h : isValid M p) : ¬isContradictory M p :=
  isTrue_not_isBoth (M.evidence p) h

/-! ## Quantitative Measures -/

/-- The strength of a proposition in a model: ratio of positive to total evidence -/
noncomputable def strength (M : PLNModel α) (p : α) : ℝ≥0∞ :=
  Evidence.toStrength (M.evidence p)

/-- The total evidence for a proposition -/
noncomputable def totalEvidence (M : PLNModel α) (p : α) : ℝ≥0∞ :=
  (M.evidence p).total

/-- Strength is 1 for valid propositions with finite positive evidence -/
theorem strength_of_valid (M : PLNModel α) (p : α) (h : isValid M p)
    (hfin : (M.evidence p).pos ≠ ⊤) :
    strength M p = 1 := by
  unfold strength Evidence.toStrength Evidence.total isValid PBit.isTrue at *
  obtain ⟨hpos, hneg⟩ := h
  simp only [hneg, add_zero]
  have hne : (M.evidence p).pos ≠ 0 := ne_of_gt hpos
  simp only [hne, ↓reduceIte]
  exact ENNReal.div_self hne hfin

/-- Strength is 0 for invalid propositions (pure negative evidence) -/
theorem strength_of_invalid (M : PLNModel α) (p : α) (h : isInvalid M p) :
    strength M p = 0 := by
  unfold strength Evidence.toStrength Evidence.total isInvalid PBit.isFalse at *
  obtain ⟨hpos, _⟩ := h
  simp only [hpos, zero_add]
  -- Need to check if total = 0
  by_cases hneg : (M.evidence p).neg = 0
  · simp only [hneg, ↓reduceIte]
  · simp only [hneg, ↓reduceIte, ENNReal.zero_div]

/-! ## Combining Models -/

/-- Join of two models: take maximum evidence from each -/
noncomputable def join (M₁ M₂ : PLNModel α) : PLNModel α where
  evidence p := M₁.evidence p ⊔ M₂.evidence p

/-- Meet of two models: take minimum evidence from each -/
noncomputable def meet (M₁ M₂ : PLNModel α) : PLNModel α where
  evidence p := M₁.evidence p ⊓ M₂.evidence p

/-- Join gives at least as much evidence as each component model -/
theorem le_join_left (M₁ M₂ : PLNModel α) (p : α) :
    M₁.evidence p ≤ (join M₁ M₂).evidence p :=
  le_sup_left

theorem le_join_right (M₁ M₂ : PLNModel α) (p : α) :
    M₂.evidence p ≤ (join M₁ M₂).evidence p :=
  le_sup_right

/-- Meet gives at most as much evidence as each component model -/
theorem meet_le_left (M₁ M₂ : PLNModel α) (p : α) :
    (meet M₁ M₂).evidence p ≤ M₁.evidence p :=
  inf_le_left

theorem meet_le_right (M₁ M₂ : PLNModel α) (p : α) :
    (meet M₁ M₂).evidence p ≤ M₂.evidence p :=
  inf_le_right

/-! ## Tensor Composition of Models

When we have evidence for A→B and B→C, we can compose to get evidence for A→C.
This is the semantic foundation for PLN's deduction rule.
-/

/-- Compose evidence via tensor product.
    Given models M_AB (evidence for A→B) and M_BC (evidence for B→C),
    produce a model for A→C where evidence compounds multiplicatively.
-/
noncomputable def tensorCompose (M_AB M_BC : PLNModel α) : PLNModel α where
  evidence p := M_AB.evidence p ⊙ M_BC.evidence p

/-- Tensor composition is commutative -/
theorem tensorCompose_comm (M₁ M₂ : PLNModel α) (p : α) :
    (tensorCompose M₁ M₂).evidence p = (tensorCompose M₂ M₁).evidence p :=
  cdTensor_comm _ _

/-- Tensor composition is associative -/
theorem tensorCompose_assoc (M₁ M₂ M₃ : PLNModel α) (p : α) :
    (tensorCompose (tensorCompose M₁ M₂) M₃).evidence p =
    (tensorCompose M₁ (tensorCompose M₂ M₃)).evidence p :=
  cdTensor_assoc _ _ _

/-! ## Par Composition (Independent Evidence)

When we have independent evidence sources, they combine via par (⅋).
This corresponds to evidence aggregation from independent observations.
-/

/-- Combine independent evidence via par.
    Given models M₁ and M₂ with independent evidence, combine additively.
-/
noncomputable def parCompose (M₁ M₂ : PLNModel α) : PLNModel α where
  evidence p := M₁.evidence p ⅋ M₂.evidence p

/-- Par composition is commutative -/
theorem parCompose_comm (M₁ M₂ : PLNModel α) (p : α) :
    (parCompose M₁ M₂).evidence p = (parCompose M₂ M₁).evidence p :=
  cdPar_comm _ _

/-- Par composition is associative -/
theorem parCompose_assoc (M₁ M₂ M₃ : PLNModel α) (p : α) :
    (parCompose (parCompose M₁ M₂) M₃).evidence p =
    (parCompose M₁ (parCompose M₂ M₃)).evidence p :=
  cdPar_assoc _ _ _

/-! ## Tensor Distributes over Join (Quantale Law)

This is the key property that makes Evidence a quantale: tensor distributes over join.
In model terms: composing with the join of two models equals the join of compositions.
-/

/-- Tensor distributes over join on the left -/
theorem tensorCompose_join_left (M M₁ M₂ : PLNModel α) (p : α) :
    (tensorCompose M (join M₁ M₂)).evidence p =
    (join (tensorCompose M M₁) (tensorCompose M M₂)).evidence p :=
  cdTensor_sup_left _ _ _

/-- Tensor distributes over join on the right -/
theorem tensorCompose_join_right (M₁ M₂ M : PLNModel α) (p : α) :
    (tensorCompose (join M₁ M₂) M).evidence p =
    (join (tensorCompose M₁ M) (tensorCompose M₂ M)).evidence p :=
  cdTensor_sup_right _ _ _

/-! ## CD Negation for Models

The CD negation operation swaps positive and negative evidence.
This allows reasoning about "not p" in the paraconsistent sense.
-/

/-- Negate a model: swap positive and negative evidence for all propositions -/
def cdNegate (M : PLNModel α) : PLNModel α where
  evidence p := ∼(M.evidence p)

/-- CD negation is an involution on models -/
theorem cdNegate_involution (M : PLNModel α) (p : α) :
    (cdNegate (cdNegate M)).evidence p = M.evidence p :=
  cdNeg_involution _

/-- CD negation swaps validity states -/
theorem cdNegate_valid_iff_invalid (M : PLNModel α) (p : α) :
    isValid (cdNegate M) p ↔ isInvalid M p :=
  cdNeg_isTrue_iff_isFalse _

theorem cdNegate_invalid_iff_valid (M : PLNModel α) (p : α) :
    isInvalid (cdNegate M) p ↔ isValid M p :=
  cdNeg_isFalse_iff_isTrue _

/-- CD negation preserves unknown status -/
theorem cdNegate_unknown_iff (M : PLNModel α) (p : α) :
    isUnknown (cdNegate M) p ↔ isUnknown M p :=
  cdNeg_isNeither_iff _

/-- CD negation preserves contradictory status -/
theorem cdNegate_contradictory_iff (M : PLNModel α) (p : α) :
    isContradictory (cdNegate M) p ↔ isContradictory M p :=
  cdNeg_isBoth_iff _

/-! ## Summary

This file establishes:

1. **PLNModel**: A structure assigning Evidence to propositions

2. **Validity States**: Four mutually exclusive states based on p-bit quadrants
   - Valid: positive evidence only
   - Invalid: negative evidence only
   - Unknown: no evidence
   - Contradictory: evidence both ways

3. **Model Operations**:
   - `join`: Take maximum evidence (epistemic disjunction)
   - `meet`: Take minimum evidence (epistemic conjunction)
   - `tensorCompose`: Sequential evidence composition (for deduction)
   - `parCompose`: Independent evidence aggregation (for revision)
   - `cdNegate`: Swap positive/negative evidence

4. **Quantale Law**: Tensor distributes over join, giving models
   the structure of a quantale-enriched category.

5. **CD Negation**: Involutive negation that swaps validity states
   while preserving unknown/contradictory status.
-/

end Mettapedia.Logic.PLNQuantaleSemantics.Model
