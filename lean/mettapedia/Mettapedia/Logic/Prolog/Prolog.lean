import Mettapedia.Logic.Prolog.Core
import Mettapedia.Logic.Prolog.Eval

/-!
# Prolog Semantics Barrel

Barrel import for the Prolog built-in goal language and its operational semantics.

This module formalizes **Prolog = LP + Built-ins**:
- The LP kernel (pure Horn clauses, SLD resolution) lives in `Mettapedia.Logic.LP`.
- This module adds the **built-in goal constructors** used by PeTTa's `translate_expr`:
  `succeed`, `fail`, `cut`, `conj`, `disj`, `ite`, `once`, `neg`, `unify`, `notUnify`,
  `findall`, `spaceMatch`, `reduceCall`.

## Architecture

```
Mettapedia.Logic.LP           ← pure Horn clauses, SLD resolution (existing)
  ↑ extended by
Mettapedia.Logic.Prolog       ← Prolog built-ins + operational semantics (this module)
  ↑ instantiated by
Mettapedia.OSLF.PeTTa.PrologBridge  ← wires reduceCall → PeTTaEval (bridge, TBD)
  ↑ used in
Mettapedia.OSLF.PeTTa.TranslateExpr ← translate_expr formalization + correctness (TBD)
```

## File Index

| File | Contents |
|------|----------|
| `Core` | `PrologGoal` (12 constructors), `PEnv`, `Pattern.mkList`, `conjList`, `disjList` |
| `Eval` | `EvalOracle`, `PrologSpace`, `PrologEvalResult` (normal/cutThrown), `PrologEval` (inductive), `PrologConjAll` (derived Prop) |

## Key Design Decisions

- **Pairs-witness pattern** for conjunction/spaceMatch: avoids `mutual inductive` while
  still expressing "run g on each element of a list" inside the `PrologEval` inductive.
- **`EvalOracle`** abstracts `reduceCall` (re-entry into MeTTa evaluator) as a
  `Prop`-valued relation, keeping the Prolog layer standalone and kernel-checkable.
- **Cut semantics**: `cutThrown` is caught by `disj`, `findall`, and `once`; it propagates
  through `conj` (when thrown by g1). Cut from g2 in conjunction is deferred.
- **`PrologConjAll`** is a derived `Prop` (not an inductive type), using the pairs witness.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed. (1987)
- Sterling & Shapiro, *The Art of Prolog*, 2nd ed. (1994)
- PeTTa `translator.pl`: `translate_expr/3`, `call_goals/1`, `reduce/2`
-/
