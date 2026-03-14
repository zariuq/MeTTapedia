# Universal AI

Lean 4.28 formalization of Hutter's *Universal Artificial Intelligence:
Sequential Decisions Based on Algorithmic Probability* (Springer, 2005),
Chapters 4–7. **71 files, ~27,000 lines. Zero sorry in core chapters
(21 total in auxiliary extensions).**

Companion directory: `Logic/UniversalPrediction/` covers Chapters 2–3
(~12,900 lines, zero sorry).

## Coverage

| Chapter | Topic | Coverage | Lines | Sorries |
|---------|-------|----------|-------|---------|
| Ch 4 — Agents & environments | Action/observation/reward, value functions, AIXI agent | ~95% | ~5,800 | 0 |
| Ch 5 — Optimality of AIXI | Intelligence measure (Legg-Hutter Υ), grain-of-truth, asymptotic optimality | ~85% | ~12,500 | 11 (in `GrainOfTruth/ROADMAP.lean`) |
| Ch 6 — Problem classes | SP, SG, FM, EX reductions to AIXI | ~95% | ~2,000 | 0 |
| Ch 7 — Computation & AIXItl | Levin search, time-bounded AIXI, ε-optimality | ~90% | ~11,900 | 0 |
| Extensions | Multi-agent, self-modification, Gödel machines | WIP | ~5,700 | 10 (GodelMachine) |

## Chapter 4: Bayesian Agents (`BayesianAgents/`)

| File | Lines | Contents |
|------|-------|----------|
| `BayesianAgents.lean` | 2,423 | Agents, environments, rewards, value functions, histories, AIXI agent, Bayesian mixture environments |
| `BayesianAgents/Core.lean` | 753 | Core agent-environment interaction loop |
| `BayesianAgents/CoreCompat.lean` | 116 | Compatibility layer |
| `BayesianAgents/HistoryProbability.lean` | 183 | History probability distributions |
| `BayesianAgents/InfiniteHistoryCompat.lean` | 1,546 | Infinite-history compatibility |
| `BayesianAgents/PosteriorSampling.lean` | 185 | Posterior sampling agents |

## Chapter 5: Intelligence & Grain of Truth

| File | Lines | Contents |
|------|-------|----------|
| `Intelligence/Basic.lean` | 365 | Legg-Hutter intelligence measure Υ(π); proves AIXI maximizes intelligence |

### Grain of Truth (`GrainOfTruth/`, 18 files, ~11,900 lines)

Asymptotic optimality: Thompson sampling convergence to Nash equilibrium
in reflective environments. Includes measure-theoretic infrastructure:

- `GrainOfTruth/Main.lean` — Main theorem (Leike 2016)
- `GrainOfTruth/FixedPoint.lean` — Fixed-point convergence
- `GrainOfTruth/MeasureTheory/HistoryFiltration.lean` (3,047 lines) — History filtrations
- `GrainOfTruth/MeasureTheory/ExpectedTotalVariation.lean` (2,090 lines) — Total variation bounds

## Chapter 6: Problem Classes

| File | Lines | Contents |
|------|-------|----------|
| `ProblemClasses.lean` | 2,045 | All four major classes: **SP** (sequence prediction), **SG** (strategic games), **FM** (function minimization), **EX** (supervised learning) — each reduced to AIXI with optimality theorems |
| `UniversalAIBridge.lean` | 91 | Ch 6 ↔ Ch 7 bridge: AIXItl ε-optimality instantiated to Ch 6 embeddings |
| `UniversalAIBridgeCore.lean` | 142 | FM and EX instantiations |

## Chapter 7: Time-Bounded AIXI (`TimeBoundedAIXI/`)

| File | Lines | Contents |
|------|-------|----------|
| `TimeBoundedAIXI.lean` | 9,099 | Levin search (`LevinSearch`), fastest algorithm M_p* (Thm 7.1), time-bounded semimeasure ξ^tl, `AIXItl` agent, `ValidApproximation`, `aixitl_cycle_eps_optimal` |
| `TimeBoundedAIXI/Core.lean` | 561 | Core definitions |
| `TimeBoundedAIXI/StepCounting.lean` | 188 | Fuel-based execution semantics |
| `TimeBoundedAIXI/ProofSystem.lean` | 163 | Proof system for valid approximations |
| `TimeBoundedAIXI/ProofEnumeration.lean` | 166 | Proof enumeration |
| `TimeBoundedAIXI/CoreToPartrec.lean` | 523 | Connection to `Nat.Partrec.Code` |
| `TimeBoundedAIXI/CodingBits.lean` | 53 | Encoding utilities |
| `TimeBoundedAIXI/CoreProvability.lean` | 124 | Provability results |
| `TimeBoundedAIXI/ProofEnumerationOracle.lean` | 61 | Oracle interface |

## Extensions

### Multi-Agent (`MultiAgent/`, ~2,560 lines, 0 sorries)

Multi-agent value functions, Nash equilibrium, best response —
extending AIXI to multi-agent settings.

### Self-Modification (`SelfModification/`, ~1,640 lines, 0 sorries)

Optimal self-modifying policies, realistic agents, value function
preservation under self-modification.

### Gödel Machines (`GodelMachine/`, ~1,500 lines, 10 sorries)

Schmidhuber's self-referential self-improving agents. `ROADMAP.lean`
marks remaining proof gaps.

## References

- Hutter, M. (2005). *Universal Artificial Intelligence: Sequential
  Decisions Based on Algorithmic Probability*. Springer. (Chapters 4–7)
- Legg, S. & Hutter, M. (2007). "Universal Intelligence: A Definition
  of Machine Intelligence"
- Leike, J. (2016). "Nonparametric General Reinforcement Learning"
