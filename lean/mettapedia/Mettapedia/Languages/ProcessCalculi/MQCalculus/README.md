# MQ-Calculus

Lean 4.28 formalization of the MQ-calculus (Stay & Meredith 2026).
**10 files, 1,433 lines. Zero sorry.**

Part of `papers/process-calculi.tex` (Section 4).

## Key Idea

COMM is quantum measurement: a rendezvous event produces a binary
outcome governed by Born-rule probabilities. Each `MQIn` carries two
continuations — one for outcome zero, one for outcome one — making
branching explicit in the syntax.

## Syntax

Six process constructors with De Bruijn-style wire indices:

```
Process ::= MQNil | MQPar P Q | MQNu P | MQGate spec P | MQOut n | MQIn n P Q
```

`MQIn n P Q` listens on wire `n`; `P` is the zero-outcome continuation,
`Q` the one-outcome continuation.

## Modules

| File | Contents |
|------|----------|
| `Syntax.lean` | Process grammar (`GateOp`, `GateSpec`, `Process`), De Bruijn wire indices |
| `StructuralCongruence.lean` | Par-comm, par-assoc, nu-nil, scope-extrusion |
| `Reduction.lean` | One-step `Reduces` and reflexive-transitive `MultiStep` |
| `CommRule.lean` | COMM with binary `Outcome` type; `comm_both_outcomes` witness |
| `Shift.lean` | Wire-index shifting with equational law proofs |
| `Denotational.lean` | Denotational semantics (Stay & Meredith 2026, Section 6.3) |
| `Backend.lean` | `MQSemanticsBackend` interface: gate application, wire allocation, Born-rule probabilities, post-measurement collapse |
| `Interoperability.lean` | `comm_nondeterminism_iff_mork_binary`: MQ COMM ↔ MORK binary-fold |
| `PaperMap.lean` | Theorem index from the MQ-calculus paper to Lean names |
| `MQCalculus.lean` | Facade module, integration tests, canary theorems |

## Key Results

- **`comm_both_outcomes`**: constructive witness that both COMM outcomes
  are simultaneously derivable.
- **`collapseByOutcome_norm_eq_one_of_raw_pos`**: post-collapse state
  normalization (physical consistency).
- **`comm_nondeterminism_iff_mork_binary`**: MQ's two `CommReduction`
  outcomes biject with MORK's two `FoldPicksSubResult` choices.
- MQ processes form an OSLF `LanguageDef` instance (`HasPar`, `HasNil`,
  `HasNu`, gate application).

## Backend Interface

The denotational semantics is parameterized by `MQSemanticsBackend`,
which provides `branchProb`, `applyGate`, `allocFresh`, and `collapse`.
The `statevectorBackend` instantiation gives executable semantics while
keeping theorem-level invariants clean. Born probabilities and branch
relations are decoupled: the branch inductive is structural; probabilities
are a separate field subject to `branchProb_sum_one`.

## References

- Stay, M. & Meredith, L.G. (2026). "MQ-Calculus"
- Gay, S. & Nagarajan, R. (2005). "Communicating Quantum Processes"
