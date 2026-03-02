# Governance Reasoning

Lean 4 formalization of deontic governance reasoning, from classical deontic
logic through eventuality reification to evidence-graded treaty compliance.

Based on the [governance-reasoning-engine](https://github.com/AugmentedDesignLab/governance-reasoning-engine)
(Formal-Methods-Group) and the PLN evidence algebra.

## Quick orientation

The formalization has three layers:

1. **Deontic logic** — the Deontic Traditional Scheme (DTS) with obligation
   as sole primitive; permission, optionality, and prohibition are derived.
   All 12 classical interdefinability axioms are *theorems*, not axioms.

2. **Eventuality reification** — Hobbs-style eventualities with ISO 24617-4
   thematic roles, connected to PLN world-model evidence via a query encoder.
   Three-level judgment architecture (eventuality → statement → governance).

3. **Treaty compliance** — proof-carrying treaty kernel with obligation
   fulfillment, prohibition violation, and deadline semantics.  An evidence-
   graded actuality layer gates acceptance on attestor provenance and evidence
   quality.

## File map

### Foundation
| File | What it does |
|------|-------------|
| `Core.lean` | DTS algebra, eventualities, thematic roles, modal μ-calculus embedding |
| `Bridge.lean` | Links governance types to PLN world-model evidence |
| `Judgments.lean` | 3-level judgment system (eventuality / statement / governance) |
| `Subsumption.lean` | Event subsumption (`is_complied_with_by`), role containment |

### Treaty kernel
| File | What it does |
|------|-------------|
| `TreatyKernel.lean` | Treaty clauses, traces, obligation/prohibition predicates; concrete AI subcall example |
| `TreatyKernelAcceptance.lean` | Provenance-first accepted-trace demo with 4 assessed events |
| `ActualityPolicy.lean` | Evidence-graded actuality, `AcceptancePolicy`, `AcceptanceBridge` theorem |
| `OccurrenceMVP.lean` | `admittedTrace`, `occursAt`, obligation/prohibition on admitted events |
| `AcceptancePreorder.lean` | Quality preorder on evidence (pos up, neg down), monotone policies |

### MeTTa refinement
| File | What it does |
|------|-------------|
| `PeTTaRefinement.lean` | DTS rules as PeTTa rewrite rules, evaluation bridge |
| `HERefinement.lean` | Same DTS rules via HE `MeTTaEval` inductive relation |
| `LetStarInterface.lean` | Shared `MeTTaLike` typeclass, let* unfolding theorems |
| `HECanonicalConformance.lean` | Closes the chain: canonical HE interpreter ↔ inductive relation |

## Key design choices

- **OB is the sole primitive.** PE(p) = ¬OB(¬p), OP(p) = ¬OB(p) ∧ ¬OB(¬p).
  The 12 DTS interdefinability laws are all proven, not postulated.

- **Evidence, not truth.** `rexist` is read as an evidence-graded occurrence
  channel, not binary "really exists."  Categorical acceptance is a downstream
  policy decision, parameterized by `AcceptancePolicy`.

- **Provenance-first acceptance.** The treaty acceptance demo checks attestor
  trust *and* evidence quality (pos ≥ 3, neg ≤ 1).  Both gates must pass.

- **Zero sorries, zero axioms** (beyond Lean's `propext`, `Quot.sound`,
  `Classical.choice`).

## References

- von Wright (1951), "Deontic Logic"
- Hobbs (1985), "Ontological Promiscuity"
- ISO 24617-4:2014, Semantic roles
- Carmo & Jones (2002), "Deontic Logic and Contrary-to-Duties"
- Goertzel et al. (2008), *Probabilistic Logic Networks*

## Paper

`papers/governance-deontic-logic.tex` — "Verified Dyadic Deontic Logic and
Governance Reasoning in Lean 4"
