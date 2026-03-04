import Mettapedia.Logic.Prolog.Core
import Mettapedia.Logic.Prolog.Eval
import Mettapedia.Logic.Prolog.RuntimeErrorSpec
import Mettapedia.Logic.Prolog.FixtureCorpus

/-!
# Prolog Semantics Barrel

Barrel import for the Prolog built-in goal language and its operational semantics.

This module formalizes **Prolog = LP + Built-ins**:
- The LP kernel (pure Horn clauses, SLD resolution) lives in `Mettapedia.Logic.LP`.
- This module adds the **built-in goal constructors** used by PeTTa's `translate_expr`:
  `succeed`, `fail`, `cut`, `conj`, `disj`, `ite`, `once`, `neg`, `isVar`, `unify`, `notUnify`,
  `findall`, `spaceMatch`, `reduceCall`.

## Architecture

```
Mettapedia.Logic.LP           ← pure Horn clauses, SLD resolution (existing)
  ↑ extended by
Mettapedia.Logic.Prolog       ← Prolog built-ins + operational semantics (this module)
  ↑ instantiated by
Mettapedia.Languages.MeTTa.PeTTa.PrologBridge  ← wires reduceCall → PeTTaEval (bridge, TBD)
  ↑ used in
Mettapedia.Languages.MeTTa.PeTTa.TranslateExpr ← translate_expr formalization + correctness (TBD)
```

## File Index

| File | Contents |
|------|----------|
| `Core` | `PrologGoal` (12 constructors), `PEnv`, `Pattern.mkList`, `conjList`, `disjList` |
| `Eval` | `EvalOracle`, `PrologSpace`, `PrologEvalResult` (normal/cutThrown), `PrologEval` (inductive), `PrologConjAll` (derived Prop) |
| `RuntimeErrorSpec` | theorem-level ISO runtime-error boundary map (`instantiation_error`, `type_error(callable, ...)`) |
| `FixtureCorpus` | ISO/Logtalk-sourced fixture theorems (positive + negative constructor-level regressions) |

## Key Design Decisions

- **Pairs-witness pattern** for conjunction/spaceMatch: avoids `mutual inductive` while
  still expressing "run g on each element of a list" inside the `PrologEval` inductive.
- **`EvalOracle`** abstracts `reduceCall` (re-entry into MeTTa evaluator) as a
  `Prop`-valued relation, keeping the Prolog layer standalone and kernel-checkable.
- **Cut semantics**: `cutThrown` is caught by `disj`, `findall`, and `once`; in conjunction,
  g2 runs left-to-right over g1 answers; if a cut is thrown in either g1/g2,
  current-branch answers are kept and suffix branches are pruned.
- **`PrologConjAll`** is a derived `Prop` (not an inductive type), using the pairs witness.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed. (1987)
- Sterling & Shapiro, *The Art of Prolog*, 2nd ed. (1994)
- PeTTa `translator.pl`: `translate_expr/3`, `call_goals/1`, `reduce/2`
-/
