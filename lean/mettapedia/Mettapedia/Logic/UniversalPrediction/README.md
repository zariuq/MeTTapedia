# Universal Prediction

Suppose you see a binary string one bit at a time and must keep betting on the next
bit. Is there a *single, universal* predictor that does essentially as well as the
*best* computable predictor for whatever sequence nature happens to produce? The
remarkable answer — Solomonoff's — is yes: mix together *all* computable hypotheses,
weighting each by its description length, and the resulting predictor's error is
bounded by the (fixed) complexity of the true source. This directory formalizes that
theory in Lean 4, following Hutter's *Universal Artificial Intelligence: Sequential
Decisions Based on Algorithmic Probability* (Springer, 2005).

The technical engine is **dominance**: the universal mixture ξ dominates every
computable measure μ up to a constant (the weight μ carries in the mixture), and
*all* the prediction guarantees — convergence ξ → μ, error bounds, loss bounds,
Pareto optimality — follow from that one inequality.

**40 files (28 top-level + 12 `FiniteAlphabet/`). ~13,700 lines. Zero `sorry`.**

## Source

This directory covers Chapters 2–3 (universal sequence prediction).
Chapters 4–7 (agents, AIXI, problem classes, time-bounded AIXI) are
formalized in the sibling `Mettapedia/UniversalAI/` directory (~27,000
lines, 71 files).

### This directory (Chapters 2–3)

| Chapter | Topic | Coverage | Notes |
|---------|-------|----------|-------|
| Ch 2 — Algorithmic complexity | Prefix measures, LSC enumeration, machine models | ~95% | Levin/Hutter enumeration via `Nat.Partrec.Code`; Kraft inequality proven (not axiom); `BetaCode` + Markov extension. Missing: some specific Def 2.x items not yet formalized individually. |
| Ch 3 — Universal prediction | Dominance, convergence, loss/error bounds, optimality | ~90% | Theorems 3.11s, 3.19, 3.36, 3.48, 3.59, 3.60, 3.63–3.70 all kernel-checked. One non-blocking TODO in `Optimality.lean` (cylinder partition boilerplate). Missing: a few intermediate lemmas stated but not individually named. |
| Ch 2→3 bridge | Enumeration → mixture → dominance → regret | 100% | `EnumerationBridge.lean` (abstract) + `SolomonoffBridge.lean` (concrete M₁, M₂ mixtures with explicit code weights) |
| Ch 3 extensions | Tractable conjugate predictors (Hook B pattern) | 100% | Beta (Laplace/Jeffreys/Haldane), Markov(1) Beta, Markov(1) Dirichlet, hyperprior mixtures — all with regret bounds |
| Finite alphabet | Generic `[Fintype α]` parallel stack | 100% | 9 files: prefix measures through optimality for arbitrary finite alphabets; includes `StepModel` template for new predictor families |

### `Mettapedia/UniversalAI/` (Chapters 4–7)

| Chapter | Topic | Coverage | Notes |
|---------|-------|----------|-------|
| Ch 4 — Agents & environments | Action/observation/reward, value functions, AIXI agent | ~95% | `BayesianAgents.lean` + 5 supporting files (~5,800 lines, 0 sorries). History probability, posterior sampling, infinite-history compatibility. |
| Ch 5 — Optimality of AIXI | Intelligence measure, grain-of-truth, asymptotic optimality | ~85% | `Intelligence/Basic.lean` (Legg-Hutter Υ measure, 365 lines). `GrainOfTruth/` (18 files, ~11,900 lines): Thompson sampling convergence, posterior concentration, Nash equilibrium. 11 sorries in `ROADMAP.lean` marking planned extensions. |
| Ch 6 — Problem classes | SP, SG, FM, EX reductions to AIXI | ~95% | `ProblemClasses.lean` (2,045 lines, 0 sorries): sequence prediction, strategic games, function minimization, supervised learning — each reduced to AIXI with optimality theorems. |
| Ch 7 — Computation & AIXItl | Levin search, time-bounded AIXI, ε-optimality | ~90% | `TimeBoundedAIXI.lean` + 8 subdirs (~11,900 lines, 0 sorries): Levin search complexity, ξ^tl bounded prior, `aixitl_cycle_eps_optimal`, step-counting semantics. `UniversalAIBridge.lean` instantiates to Ch 6 embeddings. |
| Extensions | Multi-agent, self-modification, Gödel machines | WIP | `MultiAgent/` (2,560 lines, 0 sorries), `SelfModification/` (1,643 lines, 0 sorries), `GodelMachine/` (~1,500 lines, 10 sorries). |

## Architecture

Two main proof routes compose the theory:

**Route 1 — Mixture route (Ch 2 → Ch 3):**
Enumeration theorem → universal mixture ξ → dominance → regret bounds.
Keeps the heavy machine-model work localized in `HutterEnumeration*.lean`;
all Chapter 3 bounds apply once dominance is shown.

**Route 2 — Hook B (tractable competitors):**
Conjugate family → LSC proof → Hook B composition → automatic dominance.
New predictor families (Beta, Markov-Dirichlet, hyperprior mixtures) plug
in without duplicating the core theory.

## Foundation (Ch 3 core)

| File | Lines | Contents |
|------|-------|----------|
| `PrefixMeasure.lean` | 202 | `PrefixMeasure` — cylinder partitions on `BinString → ENNReal`; coercion to `Semimeasure` |
| `Entropy.lean` | 302 | Shannon entropy, KL divergence, Lemma 3.11s (`klBinary ≥ sqDistBinary`) |
| `Distances.lean` | 84 | Conditional probability from prefix measures; `pTrue` next-bit probability |
| `FiniteHorizon.lean` | 311 | Finite-horizon expectations and relative entropy sums |
| `ChainRule.lean` | 398 | Chain rule: `D_{n+1}` as `D_n` + expected one-step relative entropy |

## Convergence and Bounds (Ch 3 main results)

| File | Lines | Contents |
|------|-------|----------|
| `Convergence.lean` | 384 | **Theorem 3.19**: under dominance, ξ(·\|x₁:ₖ) → μ(·\|x₁:ₖ); `Sn_le_Dn`, `Dn_le_log_inv_c` |
| `ConvergenceCriteria.lean` | 297 | **Def 3.8 / Lemma 3.9**: a.s., in-mean, in-mean-square convergence modes and their relations |
| `ErrorBounds.lean` | 901 | **Theorem 3.36**: error probability bounds for universal prediction |
| `LossBounds.lean` | 1,107 | **Theorems 3.48, 3.59, 3.60**: unit loss, instantaneous loss, general loss bounds |
| `Optimality.lean` | 1,657 | **Theorems 3.63–3.70**: Pareto optimality, balanced Pareto, optimal weight theorems |
| `OptimalWeights.lean` | 1,162 | Theorem 3.70 utilities: dyadic encoding, `natToBinLen` |

## Enumeration (Ch 2)

| File | Lines | Contents |
|------|-------|----------|
| `HutterEnumeration.lean` | 151 | `LowerSemicomputableSemimeasure`, `LowerSemicomputablePrefixMeasure` — abstract interface |
| `HutterEnumerationTheorem.lean` | 235 | Levin/Hutter enumeration for prefix measures via `Nat.Partrec.Code` |
| `HutterEnumerationTheoremSemimeasure.lean` | 130 | Enumeration for semimeasures (Ch 2 canonical computability class) |
| `HutterV3Kpf.lean` | 409 | V3 universal mixture with prefix-free Kolmogorov weights; `Dₙ(μ‖M) ≤ K(μ) · log 2` |
| `MachineEnumeration.lean` | 140 | Generic code/eval enumeration interface |

## Ch 2 → Ch 3 Bridges

| File | Lines | Contents |
|------|-------|----------|
| `UniversalPrediction.lean` | 519 | Core: universal mixture construction, geometric/encode/kpf weight functions |
| `EnumerationBridge.lean` | 105 | Abstract bridge: `PrefixMeasureEnumeration` → dominance → regret |
| `SolomonoffBridge.lean` | 429 | Concrete: M₁ (prefix measures), M₂ (semimeasures); dominance constants are explicit code weights |
| `CompetitorBounds.lean` | 71 | Hook B: dominance → regret for any LSC competitor |

## Conjugate Predictors (Hook B instances)

| File | Lines | Contents |
|------|-------|----------|
| `BetaPredictor.lean` | 358 | Beta-Bernoulli: Laplace (α=β=1), Jeffreys (½), Haldane (improper) |
| `BetaCompetitors.lean` | 111 | Regret bounds for Beta family |
| `MarkovBetaPredictor.lean` | 346 | Markov(1) with independent Beta priors per transition row |
| `MarkovHyperpriorMixture.lean` | 169 | Hyperprior mixture over Markov(1) Beta grid |
| `MarkovDirichletPredictor.lean` | 497 | Markov(1) with Dirichlet priors (finite alphabet) |
| `MarkovExchangeabilityBridge.lean` | 347 | Markov exchangeability ⟹ factorization through transition counts |

## Decision Theory Touchpoint (Ch 4–5)

| File | Lines | Contents |
|------|-------|----------|
| `ThompsonSampling.lean` | 291 | Thompson Sampling = Bayes-optimal agent for bandits; `thompsonSampling_is_bayesOptimal`; connects to `UniversalAI.BayesianAgents` |

## Finite Alphabet (`FiniteAlphabet/`)

Parallel stack for generic finite alphabets (`List α`) rather than
`BinString`. 12 files (~1,700 lines) covering prefix measures, entropy,
enumeration, Hook B composition, Solomonoff bridge, controlled
(action-conditioned) prefix measures, computable mixtures, and a
state-machine `StepModel.lean` template — all for arbitrary `[Fintype α]`,
so new predictor families plug in without boilerplate.

## Formalization status

All 40 `.lean` files in this directory (28 top-level + 12 in `FiniteAlphabet/`,
~13,700 lines) are `sorry`-free. The Chapter-2 enumeration machinery, the
Kraft/summability bound (proven, *not* postulated as an axiom — see `Optimality.lean`
and `HutterV3Kpf.lean`), and the Chapter-3 results cited in the tables above
(Lemma 3.11s, Theorems 3.19, 3.36, 3.48, 3.59, 3.60, 3.63-3.70) are all
kernel-checked. The remaining TODOs noted in the coverage tables (e.g. the cylinder
partition note in `Optimality.lean`) are docstring TODOs, not proof gaps: there are
no `sorry`s in this directory.

**Scope note.** The sibling `Mettapedia/UniversalAI/` directory (Chapters 4-7,
*not* part of this directory's footer count) does contain open `sorry`s — 11 in its
`GrainOfTruth/ROADMAP.lean` and ~10 in `GodelMachine/`, marking planned extensions.
Those are outside this directory; the 0-sorry claim here is about Chapters 2-3 only.

**Trusted base.** There are no source-level `axiom` declarations in this directory
(a source grep, *not* a per-theorem `#print axioms` audit — the development is built
on Mathlib's measure-theory / `Nat.Partrec.Code` machinery, so theorems may inherit
standard Mathlib axioms such as `propext`, `Quot.sound`, and `Classical.choice`
transitively, and several constructions are `noncomputable`). Nothing in this
directory uses `native_decide`, so no `.lean` file here enlarges the trusted base via
compile-time evaluation.

## References

- Marcus Hutter, [*Universal Artificial Intelligence: Sequential Decisions Based on Algorithmic Probability*](https://www.hutter1.net/ai/uaibook.htm) (Springer, 2005) — the primary source; this directory follows Chapters 2-3.
- Ray J. Solomonoff, "A Formal Theory of Inductive Inference, Parts I and II," [*Information and Control* 7, 1964, pp. 1-22](https://doi.org/10.1016/S0019-9958(64)90223-2) and [pp. 224-254](https://raysolomonoff.com/publications/1964pt2.pdf) — the origin of algorithmic probability and universal induction.
- Ming Li & Paul Vitányi, [*An Introduction to Kolmogorov Complexity and Its Applications*](https://link.springer.com/book/10.1007/978-0-387-49820-1) (Springer) — standard reference for the algorithmic-complexity background (prefix-free codes, Kraft inequality, semimeasures).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 40 .lean files, 0 with sorries.*
