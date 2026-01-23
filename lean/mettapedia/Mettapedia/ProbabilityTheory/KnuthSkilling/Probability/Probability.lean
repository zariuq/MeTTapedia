/-
# KnuthSkilling Probability - Interpretation Layer

This module provides the **probability interpretation** of the abstract
algebraic structures. It connects the Core representation theorems to
the familiar probability calculus and information measures.

## What's Exported

### Probability Calculus
- **ProbabilityDerivation**: Full derivation from Appendix A+B
- **ProbabilityCalculus**: Canonical interface (sum rule, product rule, Bayes)
- **ConditionalProbability**: K&S Section 7 (chaining axiom)
- **Independence**: Independence axioms and consequences

### Information Theory
- **Divergence**: K&S Section 6 (KL divergence foundations)
- **InformationEntropy**: K&S Section 8 (Shannon entropy)
- **DivergenceMathlib**: Bridge to `Mathlib.InformationTheory.klDiv`
- **InformationEntropyMathlib**: Bridge to mathlib entropy

## Layer Structure

```
Core (abstract algebra)
    ↓
Probability (interpretation)
    ↓
Applications (specific uses)
```

This module depends on Core but is NOT imported by Core,
ensuring clean layering.

## Usage

```lean
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.Probability

-- Access probability calculus
#check ProbabilityCalculus.sumRule
#check ProbabilityCalculus.bayesTheorem
```
-/

-- Probability calculus
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityCalculus
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ConditionalProbability
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.Independence

-- Information theory
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.DivergenceMathlib
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropyMathlib
