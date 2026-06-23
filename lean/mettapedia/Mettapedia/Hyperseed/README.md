# Hyperseed (Lean 4)

## What this is about

An agent never sees the whole world — only the part of it that its current vantage
point makes *reachable*, *affordable*, and *allowed*. Hyperseed is a small framework
that takes this seriously: from a stream of observations it grows the set of queries
("what could I ask / discover next?") that an agent can actually reach, and it makes
the answer depend explicitly on a **perspective** — a chosen view that restricts which
worlds are observable, which are within budget, and which a guard predicate admits.

Two pieces fit together:

- **A perspective model (the "ultrainfinitism" core).** Observer-relativity is made a
  property of a (possibly infinite) *perspective/regime*, not of a finite observer
  token. A perspective picks a class of signals it takes seriously, a reachability
  relation, and an effort/cost function. From these come three regions: the
  *observable universe* (worlds reachable through admitted signals), the
  *near eurycosm* (worlds within an effort budget), and the *available region* (their
  intersection with an admissibility guard).
- **An observation-ingestion + query-closure layer.** Given observations and a rule
  pool, Hyperseed folds the observations into a world-model (WM) state and closes a
  seed query set under the rules, producing every discoverable query — then filters
  that closure through the active perspective. This layer is a thin packaging of the
  existing PLN-world-model closure/cascade machinery, specialized for OpenClaw-style
  observation flows; it does not introduce a new semantics stack.

## Modules

| File | Contents |
|------|----------|
| `Ultrainfinitism.lean` | the perspective core: `Perspective` / `StatefulPerspective`; `observableUniverse`, `nearEurycosm`, `availableRegion`; monotonicity and subset theorems (incl. `mem_availableRegion_iff`) |
| `Basic.lean` | the Hyperseed front door: `ObservationEnvelope`, the `HyperseedKernel` interface, and trace-seeded helpers `traceSeed` / `closureFromTrace` / `cascadeFromTrace` (perspective-filtered, state-conditioned, and stage-filtered variants) over sufficient-statistic WMs |
| `ObservationTrace.lean` | observation traces as lists plus the `traceState` fold that ingests a trace into WM state; `traceState_append` and the `simp` contracts |
| `Closure.lean` | thin wrappers (`hyperseedClosure`, `hyperseedImmediateIter`, `hyperseedQueryStrength`) over `PLNWorldModelFixpointClosure`, specialized to a `HyperseedKernel` |
| `OpenClawBridge.lean` | the OpenClaw-facing surface: `OpenClawObservation` envelopes and `appendObservation` / `appendObservationTrace`, with the trace-state extension lemma |
| `ConstructionBaseBridge.lean` | re-expresses perspective-filtered discovery in the `ConstructionBase` (FCA) vocabulary, so `thatsAllAt` / `openWorldAt` read directly on Hyperseed examples |
| `Regression.lean` | concrete agent scenario: `AgentObservation` / `AgentQuery`, grounded vs expansive perspectives, regime-sensitive perspective, staged query accessibility (positive: nonempty trace discovers `awareReady`; negative: empty trace does not) |
| `UltrainfinitismRegression.lean` | toy world (`ToyWorld.city` / `forest` / `hidden`): canary theorems for `observableUniverse`, `nearEurycosm`, `availableRegion` under grounded vs expanded perspectives and budget variation |

## Key Results

- **`mem_availableRegion_iff`**: available region = observable ∩ affordable ∩ admitted.
- **`mem_closureFromTrace_iff_mem_cascade_card_of_finite`**: closure and cascade agree
  on finite rule pools.
- **`mem_closureFromTrace_implies_eventualDiscovery_of_finite`**: every query in the
  closure is eventually discovered by the fair cascade.
- **`availableClosureFromTrace_subset_closureFromTrace`**: perspective-filtering only
  removes queries, never adds.
- **`availableClosureFromTrace_subset_availableRegion`**: the filtered closure stays
  inside the available region.
- **Budget monotonicity**: larger budgets weakly enlarge the near eurycosm and the
  available closure.

## Formalization status

All 8 source files are `sorry`-free. No `axiom` declarations appear in this directory
— this is a source-level grep, *not* a per-theorem `#print axioms` audit (a theorem
can still inherit a Mathlib axiom transitively).

**Trusted base.** Nothing here uses `native_decide`, so nothing in this directory
enlarges the trusted base by trusting the compiler.

Reproduce from this directory (raw scans — they also match prose in comments/strings;
the comment-stripped count in the footer below is authoritative):

```bash
# sorry/admit occurrences (raw):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Ben Goertzel, [Hyperseed v2](https://bengoertzel.substack.com/p/hyperseed-v2)
  (Eurykosmotron, 2026) — the Hyperseed semantic-primitive ontology this layer draws on;
  see also [Introducing Hyperseed-1](https://bengoertzel.substack.com/p/introducing-hyperseed-1) (2024).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 8 .lean files, 0 with sorries.*
