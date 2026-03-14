# Hyperseed

Lean 4.28 formalization of the Hyperseed query-expansion framework.
**4 files. Zero sorry.**

## Key Idea

A *Hyperseed* is an observation-driven query generator: given a stream
of observations and a frontier function (which signals are reachable
from an observation), the framework closes that seed set under a WM
rule pool to produce all discoverable queries. Crucially, what is
discoverable depends on a *perspective* — a view of the world that
restricts which worlds are observable, affordable, and admitted by a
guard predicate.

The `Ultrainfinitism` module formalizes the perspective model that
underlies this: an agent need not see the full world, only what lies
within its observable universe (reachable signals), near eurycosm
(affordable region), and admissibility guard.

## Modules

| File | Contents |
|------|----------|
| `Ultrainfinitism.lean` | `Perspective` and `StatefulPerspective`; `observableUniverse`, `nearEurycosm`, `availableRegion`; monotonicity and subset theorems |
| `Basic.lean` | `traceSeed`, `closureFromTrace`, `cascadeFromTrace`; perspective-filtered and state-conditioned variants; stage-filtered variants; cascade–closure correspondences and budget/guard monotonicity |
| `Regression.lean` | Concrete agent scenario: `AgentObservation`/`AgentQuery`, grounded vs expansive perspectives, regime-sensitive perspective, staged query accessibility |
| `UltrainfinitismRegression.lean` | Toy world (`ToyWorld.city`, `ToyWorld.forest`, `ToyWorld.hidden`): canary theorems for `observableUniverse`, `nearEurycosm`, `availableRegion` under grounded vs expanded perspectives and budget variation |

## Key Results

- **`mem_availableRegion_iff`**: available region = observable ∩ affordable ∩ admitted.
- **`mem_closureFromTrace_iff_mem_cascade_card_of_finite`**: closure and cascade agree on finite rule pools.
- **`mem_closureFromTrace_implies_eventualDiscovery_of_finite`**: every query in the closure is eventually discovered by the fair cascade.
- **`availableClosureFromTrace_subset_closureFromTrace`**: perspective-filtering only removes queries, never adds.
- **`availableClosureFromTrace_subset_availableRegion`**: the filtered closure stays inside the available region.
- **Budget monotonicity**: larger budgets weakly enlarge the near eurycosm and available closure.

## Reference

- Goertzel, B. (2024). [Hyperseed v2](https://bengoertzel.substack.com/p/hyperseed-v2)
