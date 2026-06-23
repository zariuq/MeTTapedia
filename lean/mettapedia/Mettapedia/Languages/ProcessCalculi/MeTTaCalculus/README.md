# MeTTa-Calculus (Lean 4)

## What this is about

In ordinary process calculi, channel *names* and the *processes* that run on them
are two different kinds of thing. The **reflective** idea of Meredith's calculi is
to collapse that distinction: a name is just a *quoted process*, `@(P)`. You can
quote a process to get a name, send that name around, and later *unquote* (drop) it
to run the process again. So a program can build, pass, and execute references to
its own code — concurrency and meta-programming from one set of rules.

The **MeTTa-calculus** (Meredith 2024) is a symmetric reflective higher-order
concurrent calculus in this family, tuned to MeTTa's pattern-rewriting flavor. This
directory formalizes it in Lean and proves it lines up, clause by clause, with the
paper — and that, on the shared quote/drop/parallel fragment, it is bisimilar to
the rho-calculus formalized next door.

Two reduction rules drive it:

- **COMM**: two guarded inputs on the same channel unify their payload patterns by
  first-order unification; each body continues under dot-substitution (bound
  variables are quoted into names).
- **REFL**: a process inspects its own future via one-step COMM-only lookahead,
  emitting the successor state as a guarded listener.

Names *are* quoted processes (`@(P)`), which is what makes the calculus reflective.

Part of `../../../../../../papers/process-calculi.tex` (Section 5).

## Syntax

```
P, Q ::= 0 | P | Q | for(t <- x) P | x?P | *x
x    ::= @(P)
t    ::= (P) | true | false | n | s | sym
```

`for(t <- x) P` — guarded input; `x?P` — reflection; `@(P)` — quote;
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
| `Adequacy.lean` | Premise-runtime adequacy: 4 bridge theorems including `reducesViaPremiseContract_iff_reduces` |
| `Interoperability.lean` | `toRhoSharedProc?` translation; shared-core forward/backward simulation and star-closure bisimulation w.r.t. rho-calculus |
| `PaperMap.lean` | Theorem index mapping paper clauses to Lean proofs; `paper_shared_to_rho_*` family |
| `Regression.lean` | Positive/negative canaries for COMM and REFL (`paper_comm_positive`, `paper_refl_negative`, ...) |
| `RelationNames.lean` | Single source of truth for relation and builtin string identifiers |

## Key Results

- **COMM/REFL canaries** (`paper_comm_positive` / `paper_comm_negative`,
  `paper_refl_positive` / `paper_refl_negative`): validate the unifier and
  dot-substitution at the kernel level.
- **`reducesViaPremiseContract_iff_reduces`**: the datalog-IR stepping function
  agrees with the direct `step` function.
- **`sharedCore_stepStar_bisimulation`** (declared in `Interoperability.lean`):
  combined star-level forward + backward shared-core bisimulation between
  MeTTa-calculus and rho-calculus on the quote/drop/parallel fragment.
- **SC paper map**: the four par/nil structural-congruence clauses are verified
  in `PaperMap.lean` — `paper_equiv_par_nil_left`, `paper_equiv_par_nil_right`,
  `paper_equiv_par_comm`, `paper_equiv_par_assoc`. (Quote/drop is carried as the
  `QuoteDrop` constructor of the `SC` relation in `StructuralCongruence.lean`.)

## Formalization status

9 `.lean` files, 1,174 lines, with **0 `sorry`** (comment-stripped). No source-level
`axiom` declarations appear in these files — this is a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a Mathlib axiom
transitively.

**Trusted base — `native_decide`.** 30 `native_decide` invocations remain across 6
of the 9 files — these are the paper-map / regression / adequacy fixtures, which
compile-evaluate rather than kernel-check, so they enlarge the trusted base (they
trust the Lean compiler) and are flagged for migration to kernel `decide`:

- `Regression.lean` — 10
- `Reduction.lean` — 6
- `Adequacy.lean` — 5
- `PaperMap.lean` — 4
- `Interoperability.lean` — 3
- `Premises.lean` — 2

Reproduce from this directory — note the `sorry` regex is a *raw* scan that also
matches prose in comments/strings, so the figure of 0 above is the authoritative
comment-stripped count:

```bash
# sorry occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\bsorry\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (the 30 disclosed above):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Lucius Gregory Meredith (2024). *The MeTTa Calculus*. (Not located under that
  exact title in a public index at the time of writing; cited as the source of the
  calculus and clause numbering formalized here.)
- Lucius Gregory Meredith, Ben Goertzel, Jonathan Warrell, Adam Vandervorst (2023).
  [*Meta-MeTTa: an operational semantics for MeTTa*](https://arxiv.org/abs/2305.17218)
  — the published operational-semantics companion for MeTTa.
- L.G. Meredith & M. Radestock (2005). *A Reflective Higher-Order Calculus*,
  Electronic Notes in Theoretical Computer Science 141(5), 49-67 —
  [DOI:10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016)
  — the origin of the "names are quoted processes" reflective design.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 9 .lean files, 0 with sorries.*
