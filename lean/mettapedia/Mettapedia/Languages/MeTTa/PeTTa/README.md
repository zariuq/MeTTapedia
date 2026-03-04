# PeTTa Evaluation Layer

PeTTa (Prolog-based MeTTa) evaluates MeTTa expressions by compiling them
into Prolog-style goals and resolving them against an LP kernel.  This
directory formalizes that pipeline: from raw MeTTa expressions through
pattern-level evaluation, typed evaluation with error propagation, and
stateful effects (`add-atom`, `remove-atom`, `progn`), down to LP
soundness theorems that connect PeTTa evaluation to least Herbrand model
membership.

Import everything via `Mettapedia.Languages.MeTTa.PeTTa`
([PeTTa.lean](../PeTTa.lean)).

## Build

```bash
# from repository root
ulimit -v 6291456
lake build Mettapedia.Languages.MeTTa.PeTTa
```

## Modules

### Core evaluation

| Module | What it does |
|--------|-------------|
| [Eval.lean](Eval.lean) | `PeTTaEval` — the central pure evaluation relation |
| [MeTTaEval.lean](MeTTaEval.lean) | 4-argument evaluation with bindings, types, and error propagation |
| [Answers.lean](Answers.lean) | Answer-set projection from evaluation derivations |
| [SpaceSemantics.lean](SpaceSemantics.lean) | Atomspace query/match semantics |
| [Effects.lean](Effects.lean) | `PeTTaCmd` — stateful evaluation (`add-atom`, `remove-atom`, `get-atoms`, `progn`, `prog1`) |

### Types and standard library

| Module | What it does |
|--------|-------------|
| [TypeSystem.lean](TypeSystem.lean) | Type annotations, arrow types, special type atoms |
| [TypedEval.lean](TypedEval.lean) | Type-directed evaluation pass-through |
| [StdLib.lean](StdLib.lean) | Standard library derived forms (309 lines) |
| [MinimalInstructions.lean](MinimalInstructions.lean) | Operational instruction semantics |
| [Unit.lean](Unit.lean) | Unit-level evaluation fixtures |

### Bridges

| Module | What it does |
|--------|-------------|
| [LPSoundness.lean](LPSoundness.lean) | LP soundness: `PeTTaEval` rule application implies LHM membership |
| [PrologBridge.lean](PrologBridge.lean) | Wires `EvalOracle` to concrete PeTTa semantics |
| [TranslateExpr.lean](TranslateExpr.lean) | `compileExpr`: MeTTa expressions to Prolog goals, with correctness theorems |
| [GroundedOracle.lean](GroundedOracle.lean) | Grounded oracle interface for built-in operations |
| [OSLFInstance.lean](OSLFInstance.lean) | OSLF language instance with Galois connection and Rust export |
| [GSLTVertex.lean](GSLTVertex.lean) | GSLT forward fiber for categorical integration |

## Related

- [LP kernel](../../../Logic/LP) — unification, SLD resolution, Herbrand semantics
- [Prolog layer](../../../Logic/Prolog) — goal language, cut semantics, ISO conformance
- [Conformance harness](../../../../scripts/prolog) — SWI parity checks and ISO coverage
