# Governance Reasoning

How do you check, *formally*, whether someone kept a promise — or broke a rule?
Ordinary logic talks about what *is* true; **deontic logic** is the logic of what
*ought* to be: obligation, permission, and prohibition. This directory builds that
machinery in Lean 4 and uses it to decide, from logged events, whether the clauses
of a treaty (or an AI's operating contract) were complied with — and to do so under
*uncertainty*, where evidence about what actually happened is graded rather than
binary yes/no.

The pipeline runs from classical deontic logic, through Hobbs-style "eventuality"
reification (turning verbs-and-roles like *who did what to whom* into objects you
can reason about), to evidence-graded treaty compliance built on the PLN evidence
algebra.

Based on the [governance-reasoning-engine](https://github.com/AugmentedDesignLab/governance-reasoning-engine)
(Formal-Methods-Group) and the PLN evidence algebra.

## Quick orientation

The formalization has three layers:

1. **Deontic logic** — the Deontic Traditional Scheme (DTS) with obligation
   as sole primitive; permission, optionality, and prohibition are derived.
   The 12 classical interdefinability laws (the relations between obligation,
   permission, and prohibition) are *proven as theorems* here, not assumed as
   axioms.

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
  trust *and* evidence quality (pos ≥ 3, neg ≤ 1).  Both gates must pass
  (`TreatyKernelAcceptance.lean`, the `if (3 : ℝ≥0∞) ≤ ev.pos ∧ ev.neg ≤ 1` gate).

## Formalization status

All 13 `.lean` files in this directory are `sorry`-free.

**Trusted base.** There are no source-level `axiom` declarations here (a source
grep, *not* a per-theorem `#print axioms` audit — proofs built on Mathlib may
inherit standard Mathlib axioms such as `propext`, `Quot.sound`, and
`Classical.choice` transitively). Nothing in this directory uses `native_decide`,
so no `.lean` file here enlarges the trusted base via compile-time evaluation.

A note on the phrase "12 interdefinability laws are *theorems*": that is a claim
about deontic logic, not about the trusted base. With obligation `ob` as the only
primitive (`pe p := ¬ ob (neg p)`, `op p := ¬ ob p ∧ ¬ ob (neg p)` in `Core.lean`),
the 12 classical DTS interdefinabilities — including the trichotomy `dts_trichotomy`
and exclusivity `dts_exclusive` — are *derived and proven* in Lean, rather than
*postulated* as Lean `axiom`s. There are no `axiom` declarations behind them.

## References

- G. H. von Wright, "Deontic Logic," [*Mind* 60(237), 1951, pp. 1-15](https://academic.oup.com/mind/article-abstract/LX/237/1/941536) — the founding paper of deontic logic.
- Jerry R. Hobbs, "Ontological Promiscuity," in *Proceedings of the 23rd Annual Meeting of the ACL*, 1985 — Hobbs-style eventuality reification.
- ISO 24617-4:2014, [Language resource management — Semantic annotation framework (SemAF) — Part 4: Semantic roles (SemAF-SR)](https://www.iso.org/standard/56866.html) — the thematic-role inventory used in `Core.lean`.
- José Carmo & Andrew J. I. Jones, "Deontic Logic and Contrary-to-Duties," in *Handbook of Philosophical Logic*, vol. 8, Kluwer, 2002, pp. 265-343, [DOI 10.1007/978-94-010-0387-2_4](https://link.springer.com/chapter/10.1007/978-94-010-0387-2_4).
- Ben Goertzel, Matthew Iklé, Izabela Freire Goertzel & Ari Heljakka, [*Probabilistic Logic Networks: A Comprehensive Framework for Uncertain Inference*](https://link.springer.com/book/10.1007/978-0-387-76872-4) (Springer, 2008) — the PLN evidence algebra.

## Paper

`../../../../../papers/governance-deontic-logic.tex` — "Verified Dyadic Deontic Logic and
Governance Reasoning in Lean 4"

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 13 .lean files, 0 with sorries.*
