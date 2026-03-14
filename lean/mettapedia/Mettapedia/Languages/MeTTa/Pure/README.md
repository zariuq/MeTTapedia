# Pure — MeTTa-Pure

Formalization of MeTTa-Pure: a dependently-typed, proof-oriented fragment of
MeTTa with full metatheory. This is the **proof branch** of the two-target
architecture described in `papers/PureMeTTa.tex`:

```
Surface MeTTa → Elaborated MeTTa-Core → ┬─ MeTTa-Pure / PureKernel  (proof target)
                                         └─ RuntimeExec / MORK/MM2    (runtime target)
```

MeTTa-Pure is not a runtime. It is the trusted semantic waist for
kernel-checked certificate generation, canonical normalization, and
definitional equality. Zero sorry, zero axioms beyond Lean's kernel.

## Key Theorems

| Theorem | File | Statement |
|---------|------|-----------|
| Subject Reduction | `SubjectReduction.lean` | `HasType Γ t A → Reduces t t' → HasType Γ t' A` |
| Confluence | `Confluence.lean` | Church-Rosser via parallel reduction |
| Pi/Sigma injectivity | `Confluence.lean` | Under `PureConv` |
| Substitution | `FVarSubst.lean` | `substFVar` preserves typing |

Uses the locally nameless approach (Aydemir et al. 2008) for binders.

## Canonical Normalization Service

`PureNormalizationService.lean` (at `MeTTa/` root) packages the closed
reference normalization service around complete development (`cdev`).
A `CanonicalClosedPureTerm` carries:
- the input closed term
- its canonical development
- a `RedStar` reduction proof to that development
- a `Conv` conversion proof

Service operations: `defEqClosed?`, `asPiClosed?`, `asSigmaClosed?`.

## Proof Branch Chain

MeTTa-Pure → PureKernel → A → B → C1

- **A** — tiny closed executable kernel fragment (`pureOpStep`)
- **B** — kernel theory reduction (`PureKernel.ProfileTheory`)
- **C1** — quoted profile-theory closure (`quoteClosedTm` bridge)

Key bridge theorems:
- `pureClosedTheoryBridge_to_star` — one-step lifts to star by induction
- `profileStepStar_sound` — star closure transports to WM inequalities
- `pureTheoryStep_to_wmStrengthObligation_default` — PureKernel reduction → WM obligation

## Modules

| Module | Contents |
|--------|----------|
| `Reduction.lean` | `PureReduces` (single-step), `PureReducesStar` (transitive closure) |
| `Typing.lean` | Dependent type judgment `PureHasType` |
| `FVarSubst.lean` | Free-variable substitution and typing-preservation lemmas |
| `Confluence.lean` | Parallel reduction, Church-Rosser, Pi/Sigma injectivity |
| `SubjectReduction.lean` | Type preservation under reduction |
| `BinderOps.lean` | Binder open/close (locally nameless) |
| `Fragment.lean` | Expression fragment |
| `Core.lean` | `PureTm`, `mettaPure` dialect definition |
| `TypedLangDef.lean` | Typed language definition |

```bash
ulimit -v 6291456 && lake build Mettapedia.Languages.MeTTa.Pure
```
