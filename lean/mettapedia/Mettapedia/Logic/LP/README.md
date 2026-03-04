# LP Kernel

The logic-programming kernel underneath PeTTa and the Prolog layer.
It formalizes first-order terms, substitutions, unification (with MGU
and assumption-free completeness), the $T_P$ operator with least Herbrand
model via Tarski's theorem, and SLD resolution with an executable
search procedure.  Everything builds with zero sorries.

Import via `Mettapedia.Logic.LP` ([LP.lean](../LP.lean)).

## Build

```bash
# from repository root
ulimit -v 6291456
lake build Mettapedia.Logic.LP
```

## Modules

### Core

| Module | What it does |
|--------|-------------|
| [Core.lean](Core.lean) | Terms, atoms, clauses, knowledge bases |
| [Substitution.lean](Substitution.lean) | Substitution application and composition |
| [Matching.lean](Matching.lean) | One-way pattern matching |
| [Semantics.lean](Semantics.lean) | $T_P$ operator, Herbrand interpretations, least Herbrand model |

### Unification

| Module | What it does |
|--------|-------------|
| [Unification.lean](Unification.lean) | Fuel-bounded unification algorithm |
| [UnificationMGU.lean](UnificationMGU.lean) | Most general unifier properties |
| [UnificationComplete.lean](UnificationComplete.lean) | Assumption-free completeness: semantic unifiability implies algorithmic success |

### SLD resolution

| Module | What it does |
|--------|-------------|
| [SLD.lean](SLD.lean) | SLD derivation relation |
| [SLDCompute.lean](SLDCompute.lean) | Executable SLD search with fuel |
| [SLDAll.lean](SLDAll.lean) | All-solutions SLD (collecting all answer substitutions) |
| [SLDCompletenessKit.lean](SLDCompletenessKit.lean) | Completeness infrastructure: SLD finds all LHM members |
| [SLDCompletenessCanaries.lean](SLDCompletenessCanaries.lean) | Canary theorems exercising completeness |
| [UnificationCompletenessCanaries.lean](UnificationCompletenessCanaries.lean) | Canary theorems exercising unification completeness |

### Fragments and extensions

| Module | What it does |
|--------|-------------|
| [FunctionFree.lean](FunctionFree.lean) | Function-free fragment with finite evaluation guarantees |
| [FunctionFreeEvaluation.lean](FunctionFreeEvaluation.lean) | Evaluation in the function-free fragment |
| [FunctionFreePeTTa.lean](FunctionFreePeTTa.lean) | PeTTa-specific function-free specialization |
| [RangeRestriction.lean](RangeRestriction.lean) | Range-restricted clauses and unit-KB LHM characterization |
| [MMMeasure.lean](MMMeasure.lean) | Term-size measure for well-founded recursion |

### Bridges

| Module | What it does |
|--------|-------------|
| [MeTTaILBridge.lean](MeTTaILBridge.lean) | `DeclReduces` implies LHM membership |
| [WorldModelBridge.lean](WorldModelBridge.lean) | LP knowledge base as PLN world-model instance |
| [PathMapBridge.lean](PathMapBridge.lean) | PathMap lattice operations as LP queries |
| [OSLFBridge.lean](OSLFBridge.lean) | OSLF language instance for LP |
| [CertifyingDatalogBridge.lean](CertifyingDatalogBridge.lean) | Bridge to certifying Datalog evaluation |
| [Provenance.lean](Provenance.lean) | Derivation provenance tracking |

### ATP / chainer

| Module | What it does |
|--------|-------------|
| [PropositionalChainer.lean](PropositionalChainer.lean) | Propositional forward/backward chainer |
| [PropositionalConnectionChainer.lean](PropositionalConnectionChainer.lean) | Propositional connection tableau with DFS and witness completeness |
| [FirstOrderConnectionTrace.lean](FirstOrderConnectionTrace.lean) | First-order connection traces with substitutions |

## Related

- [PeTTa layer](../../Languages/MeTTa/PeTTa) — evaluation, effects, OSLF instance
- [Prolog layer](../Prolog) — goal language, cut, ISO conformance
