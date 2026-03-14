# π-Calculus

Lean 4.28 formalization of the asynchronous, choice-free π-calculus
following Lybech (2022). **19 files, 9,134 lines. Zero sorry.**

Part of `papers/process-calculi.tex` (Section 3).

## Syntax

Six process constructors: nil, par, input, output (async), restriction,
replication (input-guarded). Names are strings.

## Core Semantics

| File | Contents |
|------|----------|
| `Syntax.lean` | Process type, alpha-equivalence, free/bound names |
| `StructuralCongruence.lean` | SC relation (Type-valued); par-comm, par-assoc, scope extrusion |
| `Reduction.lean` | COMM reduction rule, substitution lemmas |
| `MultiStep.lean` | `P =>* Q` reflexive-transitive closure |

## π → ρ Encoding (Lybech 2022)

Full encoding into the ρ-calculus via name-server approach.

| File | Contents |
|------|----------|
| `RhoEncoding.lean` | Encoding function with Lybech-style name server |
| `ForwardSimulation.lean` | Forward simulation for restriction-free fragment |
| `EncodingMorphism.lean` | Encoding as structured `LanguageMorphism` |
| `RhoEncodingCorrectness.lean` | Clean RF forward-correctness surface |
| `NameServerLemmas.lean` | Name server operational lemmas |
| `WeakBisim.lean` | Weak N-restricted barbed bisimilarity |
| `WeakBisimDerived.lean` | Weak bisimilarity with derived reductions |
| `BackwardNormalization.lean` | Normalization helpers |
| `BackwardAdminReflection.lean` | `EncodedSC` predicate; admin trace reflection (2,745 lines) |
| `RhoParTactic.lean` | Custom tactic for rhoPar/rhoSubstitute commutativity |

## Open-Map Bridges

| File | Contents |
|------|----------|
| `BranchingBisim.lean` | Branching bisimilarity via generalized open maps |
| `WeakBisimOpenMapBridge.lean` | Weak bisim ↔ generalized open-map path bisimulation |
| `OpenMapBridgeRegression.lean` | Regression checks |

## Key Results

- Forward simulation for restriction-free π→ρ encoding (Prop 4, Lybech 2022)
- Backward admin reflection with three-branch decomposition
- `calculus_weak_correspondence_full_encode` — weak correspondence via forward + backward
- Weak bisim ↔ open-map path bisimulation bridge
