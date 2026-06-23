# Prolog Goal Language

Prolog runs a program by *searching* for a proof and *backtracking* when a branch
fails — and one operator, the **cut** (`!`), prunes that search by committing to
choices already made. Getting cut right (where it is "caught", what it discards) is
the subtle heart of Prolog's control flow. This directory gives a Prolog-style goal
language a precise operational semantics in Lean 4, including cut, and then *proves*
that the formal semantics agrees with a real ISO Prolog on a corpus of conformance
tests.

The goal language (`PrologGoal` in [Core.lean](Core.lean)) has 14 constructors:
ISO control predicates (`succeed`, `fail`, `cut`), logical connectives (`conj`,
`disj`, `ite`), determinism and negation-as-failure (`once`, `neg`), unification
(`unify`, `notUnify`), meta-predicates (`findall`, `isVar`), and MeTTa-specific
extensions (`spaceMatch`, `reduceCall`).

The operational semantics (`PrologEval` in [Eval.lean](Eval.lean)) is an inductive
relation implementing backtracking with cut propagation — cut is caught at
disjunction, `once`, `findall`, and if-then-else boundaries, matching standard
Prolog behavior.

A 242-theorem fixture corpus ([FixtureCorpus.lean](FixtureCorpus.lean)) proves
agreement with ISO Prolog on 63 ISO test IDs drawn from the Logtalk conformance
suite. An executable harness cross-checks these against SWI-Prolog.

Import via `Mettapedia.Logic.Prolog.Prolog` ([Prolog.lean](Prolog.lean)).

## Build

```bash
# from repository root
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

The Lean theorem-level corpus is cross-checked against a real Prolog by the harness
under [scripts/prolog](../../../scripts/prolog) (run `scripts/prolog/run_conformance.sh`).
Per that harness's own counts:

| Metric | Count |
|--------|------:|
| Lean fixture theorems (`FixtureCorpus.lean`) | 242 |
| SWI-Prolog `lean_aligned` cases | 183 |
| SWI-Prolog `iso_probe` cases | 11 |
| Unique Logtalk ISO IDs covered | 63 |
| Runtime-error boundary probes (`RuntimeErrorSpec.lean`) | 4 |

The four runtime-error boundary cases (`\+ 3`, `\+ G`, `findall(_, G, _)`,
`findall(_, 4, _)`) fall outside the typed `PrologGoal` AST, so they are formalized
as theorem-level error-class declarations in [RuntimeErrorSpec.lean](RuntimeErrorSpec.lean)
rather than executed in `PrologEval`.

## Related

- [LP kernel](../LP) — unification, SLD resolution, Herbrand semantics
- [PeTTa layer](../../Languages/MeTTa/PeTTa) — evaluation, effects, expression compilation

## Formalization status

All 5 `.lean` files in this directory are `sorry`-free. The semantics is an
inductive relation (`PrologEval`); the 242 fixture theorems and the 4 runtime-error
boundary declarations are discharged constructively (many by `rfl`).

**Trusted base.** There are no source-level `axiom` declarations in this directory
(a source grep, *not* a per-theorem `#print axioms` audit — proofs built on Mathlib
may inherit standard Mathlib axioms such as `propext`, `Quot.sound`, and
`Classical.choice` transitively). Nothing in this directory uses `native_decide`, so
no `.lean` file here enlarges the trusted base via compile-time evaluation. The
SWI-Prolog cross-check is an *external* differential test (it runs a separate Prolog
engine); it is evidence of conformance, not part of the Lean kernel guarantee.

## References

- John W. Lloyd, [*Foundations of Logic Programming*](https://link.springer.com/book/10.1007/978-3-642-83189-8) (Springer, 2nd ed. 1987) — the declarative/operational semantics of Horn-clause logic programming underlying Prolog.
- ISO/IEC 13211-1:1995, [Information technology — Programming languages — Prolog — Part 1: General core](https://www.iso.org/standard/21413.html) — the ISO Prolog standard whose control predicates and error classes the fixtures target.
- Paulo Moura, [Logtalk Prolog conformance test suite](https://github.com/LogtalkDotOrg/logtalk3/tree/master/tests/prolog) — the upstream source of the 63 ISO test IDs.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 5 .lean files, 0 with sorries.*
