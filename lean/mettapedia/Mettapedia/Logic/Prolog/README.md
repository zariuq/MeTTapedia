# Prolog Goal Language

Formalizes a Prolog-style goal language with 14 constructors covering
ISO control predicates (`succeed`, `fail`, `cut`), logical connectives
(`conj`, `disj`, `ite`), determinism and negation-as-failure (`once`,
`neg`), unification (`unify`, `notUnify`), meta-predicates (`findall`,
`isVar`), and MeTTa-specific extensions (`spaceMatch`, `reduceCall`).

The operational semantics (`PrologEval` in [Eval.lean](Eval.lean))
implements backtracking with cut propagation — cut is caught at
disjunction, once, findall, and if-then-else boundaries, matching
standard Prolog behavior.

A 242-theorem fixture corpus ([FixtureCorpus.lean](FixtureCorpus.lean))
proves agreement with ISO Prolog on 63 test IDs drawn from the Logtalk
conformance suite.  An executable harness cross-checks these against
SWI-Prolog.

Import via `Mettapedia.Logic.Prolog.Prolog` ([Prolog.lean](Prolog.lean)).

## Build

```bash
# from repository root
ulimit -v 6291456
lake build Mettapedia.Logic.Prolog.Prolog
```

## Modules

| Module | What it does |
|--------|-------------|
| [Core.lean](Core.lean) | `PrologGoal` inductive (14 constructors), `PEnv` environment, helper functions |
| [Eval.lean](Eval.lean) | `PrologEval` operational semantics with cut-aware control flow |
| [RuntimeErrorSpec.lean](RuntimeErrorSpec.lean) | ISO runtime-error boundary: maps 4 out-of-model ISO IDs to error classes |
| [FixtureCorpus.lean](FixtureCorpus.lean) | 242 proven fixture theorems sourced from Logtalk ISO tests |
| [Prolog.lean](Prolog.lean) | Aggregates all modules; includes architecture diagram |

## Conformance

Two levels of validation:

- **Lean theorem-level** (this directory): 242 proven fixture theorems
  matching ISO Prolog behavior, cross-checked against SWI-Prolog via
  [scripts/prolog](../../../scripts/prolog).
  Run: `scripts/prolog/run_conformance.sh`
- **PeTTa runtime unit suite**: 69 assertions testing the concrete
  interpreter.  Run: `cd hyperon/PeTTa && ./unit/run_petta_unit_69.sh`

## Related

- [LP kernel](../LP) — unification, SLD resolution, Herbrand semantics
- [PeTTa layer](../../Languages/MeTTa/PeTTa) — evaluation, effects, expression compilation
