import Mettapedia.Logic.PLNFirstOrder.SatisfyingSet
import Mettapedia.Logic.PLNFirstOrder.QuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.WeaknessConnection
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Algebra.QuantaleWeakness

/-!
# Higher-Order PLN: Core Definitions

This file provides the foundation for Higher-Order Probabilistic Logic Networks (HOI-PLN).

## Architecture

**Two Complementary Paths**:

```
                    Evidence (n⁺, n⁻) Foundation
                            |
                 +----------+----------+
                 |                     |
         Path 1: Classical         Path 2: HoTT
         HOI→FOI Reduction         Enrichment
                 |                     |
         "How many satisfy?"    "By what method?"
         (Computational)        (Proof-relevant)
```

## Path 1: HOI→FOI Reduction (This Module)

From PLN Book (Goertzel et al., 2009), Chapter 10, lines 1565-1612:

> "The main point of SatisfyingSets is that we can use them to map from higher-order
> into first-order. A SatisfyingSet maps Evaluation relationships into Member
> relationships, and hence has the side effect of mapping higher-order relations into
> ordinary first-order relations between sets."

**Key Reduction Equations**:
- `Member(X, S) = Evaluation(P, X)` where `S = SatisfyingSet(P)`
- `Implication(R1 A X, R2 B X) = Inheritance(SatisfyingSet(R1 A), SatisfyingSet(R2 B))`
- `Equivalence(R1 A X, R2 B X) = Similarity(SatisfyingSet(R1 A), SatisfyingSet(R2 B))`

This module implements these equations, making higher-order inference computable
via first-order quantale weakness operations.

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter 10
- `PLNFirstOrder/` directory: Complete first-order quantifier formalization (707 lines, 0 sorries)
- `QuantaleWeakness.lean`: Core weakness theory (820+ lines, proven)
- `EvidenceQuantale.lean`: Evidence quantale with Frame structure

-/

namespace Mettapedia.Logic.HigherOrder

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNFirstOrder
open Mettapedia.Algebra.QuantaleWeakness
open scoped ENNReal

end Mettapedia.Logic.HigherOrder
