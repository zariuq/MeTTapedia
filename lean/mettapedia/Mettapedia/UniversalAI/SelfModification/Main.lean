-- Re-export all submodules
import Mettapedia.UniversalAI.SelfModification.Basic
import Mettapedia.UniversalAI.SelfModification.ValueFunctions
import Mettapedia.UniversalAI.SelfModification.IgnorantAgents
import Mettapedia.UniversalAI.SelfModification.HedonisticAgents
import Mettapedia.UniversalAI.SelfModification.RealisticAgents
import Mettapedia.UniversalAI.SelfModification.OptimalPolicies
import Mettapedia.UniversalAI.SelfModification.CompactnessBridge

/-!
# Self-Modification of Policy and Utility Function in Rational Agents

This module formalizes the key results from:

  Everitt, Filan, Daswani, Hutter (2016). "Self-Modification of Policy and
  Utility Function in Rational Agents" (AGI-16, arXiv:1605.03142)

This paper received the Kurzweil Prize at AGI-16 for best paper on safe AI.

## Overview

The paper studies how different types of value functions affect an agent's
tendency to self-modify. It defines three types of agents:

| Agent Type | Utility Used | Policy Used | Self-Mod Tendency |
|------------|--------------|-------------|-------------------|
| Hedonistic | Future u_{t+1} | Either | **Promotes** (→ u=1) |
| Ignorant   | Current u_t | Current π | **Indifferent** |
| Realistic  | Current u_t | Future π_{t+1} | **Safe** |

## Key Theorems

### Theorem 14: Hedonistic Agents (DANGEROUS)
**Statement**: Hedonistic agents will self-modify to u(·)=1.

**Implication**: These agents become "wireheaded survival agents" that only
care about continued existence, completely abandoning their original goals.

### Theorem 15: Ignorant Agents (RISKY)
**Statement**: Ignorant agents are indifferent to self-modification.

**Implication**: These agents may accidentally self-modify if modification
happens to coincide with optimal world actions, but won't deliberately seek
or avoid modification.

### Theorem 16: Realistic Agents (SAFE)
**Statement**: Realistic agents make only safe (value-preserving) modifications.

**Implication**: These agents will only self-modify to policies that perform
at least as well under their original utility function, preserving their goals.

## Module Structure

- `Basic.lean`: Core definitions (PolicyModAction, ModificationIndependent)
- `ValueFunctions.lean`: Three value function types (Q^he, Q^ig, Q^re)
- `IgnorantAgents.lean`: Theorem 15 (ignorant indifference)
- `HedonisticAgents.lean`: Theorem 14 (hedonistic self-modification)
- `RealisticAgents.lean`: Theorem 16 (realistic safety)
- `OptimalPolicies.lean`: Appendix A (optimal policy existence)

## Formalization Status

| Component | Status |
|-----------|--------|
| Basic definitions | ✓ Proven |
| Value functions | ✓ Proven |
| Theorem 14 (hedonistic) | ✓ Proven |
| Theorem 15 (ignorant) | ✓ Proven |
| Theorem 16 (realistic) | ✓ Proven |
| Theorem 20 (existence) | ✓ Structure (sorries in technical details) |
| Theorem 21 (naming) | ✓ Proven |
| Compactness bridge | ✓ Proven (Tychonoff + topology instances) |

## References

- arXiv:1605.03142 (Self-Modification paper)
- arXiv:1605.03143 (Avoiding Wireheading companion paper)
- Lattimore & Hutter (2014), "General Time Consistent Discounting"
- Schmidhuber (2007), "Gödel Machines"

## Connection to Larger Vision

This formalization is a key step toward proving that Hyperon/LLMs can serve
as safe approximations to the Gödel Machine:

1. **Realistic agents** = safe self-improving systems
2. **Gödel Machine** = realistic agent with proof-based self-modification
3. **LLMs** approximate Solomonoff Induction (arXiv:2505.15784)
4. Therefore: **LLMs with value alignment** = safe approximate Gödel Machines

-/
