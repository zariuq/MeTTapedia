import Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.Basic
import Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.HigherOrderReduction
import Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction.PredCode.Basic

/-!
# Higher-Order Probabilistic Logic Networks (HOI-PLN)

This module implements the HOI→FOI reduction from the PLN Book (Goertzel et al., 2009).

## Core Insight

**SatisfyingSets map Evaluation to Member**, enabling reduction of all higher-order
relations to first-order relations between sets.

## Main Components

- `PLN.RuleFamilies.HigherOrder.Reduction.Basic`: Foundation and imports
- `PLN.RuleFamilies.HigherOrder.Reduction.HigherOrderReduction`: Core HOI→FOI reduction theorems
- `PLN.RuleFamilies.HigherOrder.Reduction.PredCode.Basic`: Predicate code definitions

Bridges from this reduction surface to other PLN/HOL APIs live under
`Mettapedia.PLN.Bridges.Logic`.

## Status (Weeks 1-3 Complete, Week 4 Blocked)

✅ Week 1-2: All core definitions and reduction theorems (0 sorries, 0 axioms)
✅ Week 3: Strengthened structural properties (perfect implication/subset reflection)
❌ Week 4: PredCode BLOCKED - cannot prove Encodable for mutually recursive type
❌ Week 5: Solomonoff integration NOT STARTED - depends on Week 4

## Blockers

**Week 4 Blocker**: PredCode Encodable instance
- Mutually recursive inductive type creates circularity in instance resolution
- Requires custom derivation with well-founded recursion
- OR requires flattening to non-recursive representation
- This is NOT routine machinery - it requires substantial proof engineering

**Impact**: Without Encodable, cannot enumerate predicates for Solomonoff prior.
The evalPred function and basic properties are sound, but enumeration is blocked.

## Next Steps

- Resolve PredCode Encodable blocker (requires proof engineering expertise)
- OR explore alternative formalization that avoids mutual recursion
- Week 5 depends on Week 4 completion

## References

- PLN Book, Chapter 10, lines 1565-1612
- `PLNFirstOrder/` directory: 707 lines, 0 sorries
- `QuantaleWeakness.lean`: 820+ lines, complete weakness theory
-/
