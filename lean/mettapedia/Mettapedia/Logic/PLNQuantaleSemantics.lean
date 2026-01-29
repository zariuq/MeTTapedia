import Mettapedia.Logic.PLNQuantaleSemantics.PBit
import Mettapedia.Logic.PLNQuantaleSemantics.CDLogic
import Mettapedia.Logic.PLNQuantaleSemantics.PLNModel
import Mettapedia.Logic.PLNQuantaleSemantics.Soundness

/-!
# PLN Quantale Semantics

Formal semantics for Probabilistic Logic Networks grounded in:
1. **Goertzel's p-bits** - 4-valued paraconsistent truth values
2. **Quantale algebra** - Evidence as commutative quantale
3. **K&S representation** - Embedding into ℝ via Hölder theorem

## Architecture

```
Evidence (pos, neg : ℝ≥0∞) = Goertzel's p-bits
  ↓ (averaging over situations)
PLN Truth Values (strength, confidence)
  ↓ (quantale operations)
Sound inference rules with provable bounds
```

## What This Module Provides

### PBit.lean - P-Bit Foundation
- `pTrue`, `pFalse`, `pNeither`, `pBoth`: The four corners of the p-bit square
- `isTrue`, `isFalse`, `isNeither`, `isBoth`: Classification predicates
- `quadrant`: Classify evidence into its quadrant
- `evidence_not_boolean`: Proof that Evidence is Heyting but not Boolean

### CDLogic.lean - Constructible Duality Operations
- `cdNeg` (∼): Involutive negation (swap pos/neg)
- `cdTensor` (⊙): Multiplicative conjunction (coordinatewise ×)
- `cdPar` (⅋): Additive disjunction (coordinatewise +)
- `cdTensor_sup_left/right`: Quantale distributivity

### PLNModel.lean - Formal Model Theory
- `PLNModel`: Evidence assignment to propositions
- `isValid`, `isInvalid`, `isUnknown`, `isContradictory`: Validity states
- `tensorCompose`, `parCompose`: Model composition operations
- `cdNegate`: Model-level CD negation
- Quantale distributivity at the model level

### Soundness.lean - Inference Rule Soundness
- `tensor_monotone`: Tensor preserves evidence ordering
- `par_monotone`: Par preserves evidence ordering
- `tensor_strength_ge`: Strength lower bound (foundation of deduction)
- Corner preservation theorems
- Model-level monotonicity

## Key Results

1. **Evidence = P-bits**: The existing `Evidence` type from `PLNEvidence.lean`
   is exactly Goertzel's p-bit structure from arXiv:2012.14474.

2. **CD Logic is algebraic**: All CD logic operations are proven to satisfy
   their algebraic laws (involution, commutativity, associativity, distributivity).

3. **Evidence is a Frame**: Evidence has complete Heyting algebra structure
   (proven in `PLNEvidence.lean` via `Order.Frame Evidence`).

4. **Quantale law**: Tensor distributes over join (cdTensor_sup_left/right).

5. **Soundness**: PLN inference operations preserve evidence ordering.

6. **Strength bounds**: Tensor product strength ≥ product of individual strengths.

## Connection to Goertzel's Research

| Goertzel Concept | Our Formalization |
|------------------|-------------------|
| P-bits (H × H^op) | `Evidence` with pos/neg |
| CD Negation | `cdNeg` = swap components |
| CD Tensor | `cdTensor` = coordinatewise × |
| CD Par | `cdPar` = coordinatewise + |
| Averaging over situations | `strength`, `confidence` views |
| Second-order probability | Evidence counts + κ prior |
| Paraconsistent "both" | `pBoth` corner with pos > 0 ∧ neg > 0 |
| Epistemic "neither" | `pNeither` corner with pos = 0 ∧ neg = 0 |

## Building on Existing Infrastructure

This module builds on:
- `PLNEvidence.lean`: Evidence structure, quantale instance, Frame instance
- `PLNDeduction.lean`: Deduction formula, consistency bounds
- `EvidenceBeta.lean`: Beta-Evidence connection, conjugate prior

## References

- Goertzel et al., "Paraconsistent Foundations for Probabilistic Reasoning,
  Programming and Concept Learning" (arXiv:2012.14474)
- Girard, "Linear Logic" (1987)
- Knuth & Skilling, "Foundations of Inference" (2012)
- Lawvere, "Metric spaces, generalized logic, and closed categories" (1973)
-/
