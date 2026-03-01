import Mettapedia.OSLF.PeTTa.Answers
import Mettapedia.OSLF.PeTTa.SpaceSemantics
import Mettapedia.OSLF.PeTTa.Eval
import Mettapedia.OSLF.PeTTa.LPSoundness
import Mettapedia.OSLF.PeTTa.Effects
import Mettapedia.OSLF.PeTTa.TypeSystem
import Mettapedia.OSLF.PeTTa.TypedEval
import Mettapedia.OSLF.PeTTa.MinimalInstructions
import Mettapedia.OSLF.PeTTa.MeTTaEval
import Mettapedia.OSLF.PeTTa.StdLib
import Mettapedia.OSLF.PeTTa.GroundedOracle
import Mettapedia.OSLF.PeTTa.PrologBridge
import Mettapedia.OSLF.PeTTa.TranslateExpr
import Mettapedia.OSLF.PeTTa.OSLFInstance
import Mettapedia.OSLF.PeTTa.GSLTVertex

/-!
# PeTTa Formal Specification

Barrel import for the PeTTa specification module stack.

PeTTa is a Prolog-based implementation of MeTTa. This module formalizes
the **pure, type-free fragment** of PeTTa evaluation in Lean 4, grounded
in the LP kernel (`Mettapedia.Logic.LP`).

## Architecture

```
Layer 0: LP Core + MeTTaIL Pattern/Match/DeclReduces    (done, 0 sorries)
Layer 1: All-solutions SLD (SLDAll)                      (done, 0 sorries)
    │
Layer 2: Atomspace + Answer type                         (done, 0 sorries)
    │
Layer 3: Pure evaluation relation (PeTTaEval)            (done, 0 sorries)
    │
Layer 3b: LP soundness bridge                            (done, 0 sorries)
Layer 4a: Effects + stateful evaluation (PeTTaCmd)       (done, 0 sorries)
Layer 4b: Static type system (MeTTaType)                 (done, 0 sorries)
Layer 4c: Type-gated evaluation (TypedPeTTaEval)         (done, 0 sorries)
Layer 5: Minimal instructions + lambda (MeTTaStep)       (done, 0 sorries)
Layer 6: Full 4-arg eval with binding threading (MeTTaEval) (done, 0 sorries)
Layer 7: StdLib — if/case/let/let* as derived forms         (done, 0 sorries)
Layer 8: Grounded oracle layer (MeTTaEvalG)                 (done, 0 sorries)
Layer 9: Prolog built-in semantics (PrologEval)             (done, 0 sorries)
Layer 10: translate_expr/3 formalization (compileExpr)      (done, 0 sorries)
Layer 11: OSLF type system + Galois + Rust export            (done, 0 sorries)
Layer 12: GSLT forward fiber (unit-indexed)                  (done, 0 sorries)
```

## File Index

| File | Contents |
|------|----------|
| `Answers` | `Answers := List Pattern`, superpose, collapse, emptyAnswer |
| `SpaceSemantics` | `PeTTaSpace`, `spaceMatch`, soundness + completeness |
| `Eval` | `PeTTaEval` inductive relation (pure, type-free fragment) |
| `LPSoundness` | Bridge `PeTTaEval.ruleApp` → `leastHerbrandModel` |
| `Effects` | `EvalState`, `PeTTaCmd` (add-atom, remove-atom, get-atoms, progn, prog1), `notReducible`, `mkEmpty` |
| `TypeSystem` | `MeTTaType` (8 constructors), arrow types, monotonicity |
| `TypedEval` | `TypedPeTTaEval`, `typeCheckPasses`, soundness bridge to `PeTTaEval` |
| `MinimalInstructions` | `MeTTaStep` (11 constructors): eval, chain, unify, decons, cons, lambda, beta, return, empty, evalc |
| `MeTTaEval` | `MeTTaEval` 4-arg judgment with binding threading, error propagation, meta-type dispatch |
| `StdLib` | Standard library derivations: if/case/let/let* as derived forms |
| `GroundedOracle` | `GroundedOracle` structure, `InterpretArgs`, `MeTTaEvalG` extended evaluation |
| `PrologBridge` | `meTTaPrologOracle`, `reduceCall_meTTa_sound`, `pettaEval_to_reduceCall` |
| `TranslateExpr` | `compileExpr : Pattern → PrologGoal`, correctness theorems for fvar/ground/collapse/reduceCall |
| `OSLFInstance` | `pettaOSLF`, `pettaGalois`, `pettaRenderRust`, `pettaWriteRust` |
| `GSLTVertex` | `pettaForwardFiber`, `pettaIdMorphism` (unit-indexed GSLT fiber) |

## Remaining Work

- Dependent types and type-level computation (deferred)
- Multiple named spaces (deferred)
- SLD variable freshening (convention-based, formalization deferred)

## References

- MeTTa spec: `trueagi-io.github.io/hyperon-experimental/metta/`
- PeTTa: `hyperon/PeTTa/transpiler.pl`, `hyperon/PeTTa/spaces.pl`
- LP foundation: `Mettapedia.Logic.LP`
- MeTTaIL Pattern/Match: `Mettapedia.OSLF.MeTTaIL`
-/
