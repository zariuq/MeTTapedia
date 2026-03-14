# MeTTa-Calculus

Lean 4.28 formalization of the MeTTa-calculus (Meredith 2024).
**9 files, 1,174 lines. Zero sorry.**

Part of `papers/process-calculi.tex` (Section 5).

## Key Idea

A symmetric reflective higher-order concurrent calculus. Two reduction
rules:

- **COMM**: two guarded inputs on the same channel unify their payload
  patterns via first-order unification; each body is continued under
  dot-substitution (bound variables are quoted into names).
- **REFL**: a process inspects its own future via one-step COMM-only
  lookahead, emitting the successor state as a guarded listener.

Names *are* quoted processes (`@(P)`), so the calculus is reflective.

## Syntax

```
P, Q ::= 0 | P | Q | for(t ← x) P | x?P | *x
x    ::= @(P)
t    ::= (P) | true | false | n | s | sym
```

`for(t ← x) P` — guarded input; `x?P` — reflection; `@(P)` — quote;
`*x` — drop (unquote). Two language definitions: `mettaCalc` (COMM + REFL)
and `mettaCalcCommOnly` (COMM only, used inside the REFL premise to
avoid self-reference).

## Modules

| File | Contents |
|------|----------|
| `Syntax.lean` | Grammar as `Pattern` abbreviations; `commSymRule`, `reflRule`; `mettaCalc` / `mettaCalcCommOnly` `LanguageDef` |
| `StructuralCongruence.lean` | `SC` relation (11 constructors): nil, comm, assoc, par-perm, par-cong, QuoteDrop; paper-mapped equivalence theorems |
| `Reduction.lean` | Dot-substitution (`dotBindings`, `applyDot`); fuel-bounded MGU (256 steps, occurs check); `step` function |
| `Premises.lean` | `PremiseProgram` IR: two relations, two builtins; machine-checked stratification and well-formedness |
| `Adequacy.lean` | Premise–runtime adequacy: 4 bridge theorems including `reducesViaPremiseContract_iff_reduces` |
| `Interoperability.lean` | `toRhoSharedProc?` translation; shared-core forward/backward simulation and star-closure bisimulation w.r.t. ρ-calculus |
| `PaperMap.lean` | Theorem index mapping paper clauses to Lean proofs; `paper_shared_to_rho_*` family |
| `Regression.lean` | Positive/negative canaries for COMM and REFL (`paper_comm_positive`, `paper_refl_negative`, …) |
| `RelationNames.lean` | Single source of truth for relation and builtin string identifiers |

## Key Results

- **`comm_both_outcomes`-equivalent canaries**: `paper_comm_positive` /
  `paper_comm_negative` validate the unifier and dot-substitution at the
  kernel level.
- **`reducesViaPremiseContract_iff_reduces`**: the datalog-IR stepping
  function agrees with the direct `step` function.
- **`sharedCore_stepStar_bisimulation`**: combined star-level forward +
  backward shared-core bisimulation between MeTTa-calculus and ρ-calculus
  on the quote/drop/parallel fragment.
- **SC paper map**: all four paper SC clauses verified
  (`paper_equiv_par_nil_left`, `paper_equiv_par_comm`,
  `paper_equiv_par_assoc`, `paper_equiv_quote_drop`).

## References

- Meredith, L.G. (2024). "The MeTTa Calculus"
