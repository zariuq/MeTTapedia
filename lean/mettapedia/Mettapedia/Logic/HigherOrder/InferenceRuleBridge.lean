import Mettapedia.Logic.HigherOrder.HigherOrderReduction
import Mettapedia.Logic.PLNInferenceRules

/-!
# Bridge to Existing PLN Inference Rules

This file connects the new SatisfyingSet-based HOI→FOI reduction to the existing
PLN inference rules in `PLNInferenceRules.lean`.

## Goal

Show that our Inheritance definition is compatible with the existing
`memberToInheritance` conversion (lines 369-401 of PLNInferenceRules.lean).

## Status (Week 1-2)

**What we CAN prove now**:
- Structural compatibility: Our Inheritance definition uses Evidence division
- Member predicate matches: `Member X S = S.pred X` (definitional)

**What we CANNOT prove yet** (blockers documented):
- Exact formula match requires interpreting SimpleTruthValue ↔ Evidence conversion
- Need to formalize how `(s, c)` pairs map to `Evidence (pos, neg)`

This file provides the structural connection, leaving exact formula proofs for
when the Evidence/STV bridge is formalized.

## References

- PLNInferenceRules.lean lines 369-401: memberToInheritance formula
- HigherOrderReduction.lean: Our Inheritance definition
-/

namespace Mettapedia.Logic.HigherOrder

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNFirstOrder
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Logic.PLNInferenceRules
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open scoped ENNReal
open Classical

variable {U : Type*} [Fintype U]

/-! ## Structural Compatibility Theorems -/

/-- **Compatibility Theorem 1**: Member is definitional

Our Member predicate matches the SatisfyingSet semantics exactly.
This is the foundation for the memberToInheritance bridge.
-/
theorem member_is_pred (X : U) (S : SatisfyingSet U) :
    Member X S = S.pred X := rfl

/-- **Compatibility Theorem 2**: Inheritance uses division

Our Inheritance definition structurally matches the conditional probability
interpretation: P(B|A) = P(A∩B) / P(A).

This confirms we're using the right mathematical structure, even though
the exact formula match requires Evidence/STV conversion.
-/
theorem inheritance_uses_conditional_prob_structure
    (A B : SatisfyingSet U) (μ : WeightFunction U Evidence) :
    ∃ (numerator denominator : Evidence),
      Inheritance A B μ = numerator / denominator := by
  unfold Inheritance
  use weakness μ (Finset.univ.filter (fun (u, v) =>
        isTrue (A.pred u) ∧ isTrue (A.pred v) ∧
        isTrue (B.pred u) ∧ isTrue (B.pred v)))
  use weakness μ A.diagonal

/-! ## Future Work: Exact Formula Match

To prove that our Inheritance exactly matches `memberToInheritance`, we need:

1. **Evidence ↔ SimpleTruthValue conversion**:
   - Define `toSTV : Evidence → (ℝ × ℝ)` (strength, confidence)
   - Define `ofSTV : (ℝ × ℝ) → Evidence` (pos, neg counts)
   - Prove roundtrip properties

2. **Singleton SatisfyingSet interpretation**:
   - Show `Member x ⟨singleton⟩` corresponds to single-element evidence
   - Connect to existing `memberToInheritance s c k = (s, c*k)`

3. **Weakness as probability measure**:
   - Formalize `weakness μ H` as probability mass
   - Show division gives conditional probabilities

**Expected theorem (once infrastructure ready)**:
```lean
theorem inheritance_matches_member_conversion
    (S : SatisfyingSet U) (x : U) (μ : WeightFunction U Evidence) (k : ℝ) :
    let member_ev := Member x S
    let inh_ev := Inheritance ⟨fun _ => S.pred x⟩ S μ
    toSTV inh_ev = memberToInheritance (toSTV member_ev).1 (toSTV member_ev).2 k
```

This will require ~50-100 lines of proof once the Evidence/STV bridge is built.

## Blockers

Cannot complete proofs without:
- [ ] Evidence.toSTV and Evidence.ofSTV functions
- [ ] Formalization of PLN strength/confidence semantics in Evidence
- [ ] Connection between weakness and probability measures
- [ ] Interpretation of weight functions as probability distributions

These are substantial infrastructure gaps, not just "hard proofs". The theoretical
foundations need to be established first.
-/

end Mettapedia.Logic.HigherOrder
