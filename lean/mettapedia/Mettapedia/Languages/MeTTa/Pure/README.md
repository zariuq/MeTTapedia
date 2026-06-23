# Pure — MeTTa-Pure

## What this is about

MeTTa, the meta-language of OpenCog Hyperon, is untyped at its core. **MeTTa-Pure**
is the opposite extreme: a small, *dependently typed* fragment with a full
metatheory, meant to be the trustworthy place where you check proofs rather than
run programs. Think of it as MeTTa's "logical kernel" — the part you would point
to and say "if this typechecks, it is correct."

Concretely, MeTTa-Pure is an intensional dependent type theory packaged as an
OSLF `LanguageDef` (`mettaPure`, in `Core.lean`). It has:

- **Pi-types** (dependent functions) and **Sigma-types** (dependent pairs);
- **Id-types** (propositional equality);
- **two Russell-style universes** `U0 : U1`; and
- **three beta-reductions** — for Pi (`App` of `Lam`), Sigma-first (`Fst` of
  `Pair`), Sigma-second (`Snd` of `Pair`) — and **no extensional equations**
  (that is what "intensional" means here).

Because it is the trusted semantic waist for kernel-checked certificate
generation, canonical normalization, and definitional equality, the payoff is
the *metatheory proved about it*: type preservation (subject reduction),
confluence (Church-Rosser), and injectivity of the Pi/Sigma type formers — the
properties a dependent kernel needs to be sound. Terms are represented in the
ambient MeTTa-IL `Pattern` type, with a predicate `PureTmPattern` carving out
the pure fragment and locally nameless binders (Aydemir et al. 2008).

MeTTa-Pure is the **proof branch** of MeTTa's two-target story — surface MeTTa
elaborates to a core, which then heads either toward this proof target
(MeTTa-Pure / PureKernel) or toward a runtime target (MORK / MM2):

```
Surface MeTTa -> Elaborated MeTTa-Core -> +- MeTTa-Pure / PureKernel  (proof target)
                                          +- RuntimeExec / MORK / MM2  (runtime target)
```

## Key Theorems

| Theorem | File | Statement |
|---------|------|-----------|
| Subject reduction | `SubjectReduction.lean` (`mettaPure_subject_reduction`) | `PureHasType Γ t A → PureReduces t t' → PureHasType Γ t' A` |
| Church-Rosser | `Confluence.lean` (`church_rosser_lc`) | confluence of `PureReducesStar` via parallel reduction |
| Pi / Sigma injectivity | `Confluence.lean` (`pi_injectivity`, `sigma_injectivity`) | type-former injectivity under `PureConv` |
| Substitution | `FVarSubst.lean` (`substFVar`) | free-variable substitution and its typing-preservation lemmas |

## Modules

| Module | Contents |
|--------|----------|
| `Core.lean` | `mettaPure` dialect (`LanguageDef`): Pi/Sigma/Id, two universes, three beta-reductions |
| `Reduction.lean` | `PureReduces` (single-step), `PureReducesStar` (transitive closure) |
| `Typing.lean` | dependent type judgment `PureHasType`; conversion relation `PureConv` |
| `FVarSubst.lean` | free-variable substitution `substFVar` and typing-preservation lemmas |
| `Confluence.lean` | parallel reduction, Church-Rosser, Pi/Sigma injectivity |
| `SubjectReduction.lean` | type preservation under reduction |
| `BinderOps.lean` | binder open/close (locally nameless) |
| `Fragment.lean` | the pure term fragment `PureTmPattern` embedded in `Pattern`, with closure/inversion lemmas |
| `TypedLangDef.lean` | typed language definition wiring `mettaPure` to the OSLF type-synthesis interface |

## Canonical normalization service (sibling module)

The closed reference normalization service lives one level up at
`MeTTa/PureNormalizationService.lean` (not in this directory). It packages a
`CanonicalClosedPureTerm`, built around a complete-development normal form
(`cdev`), carrying the input closed term, its canonical development, a `RedStar`
reduction proof to that development, and a `Conv` conversion proof. Companion
checking-service operations (`defEqClosed?`, `asPiClosed?`, `asSigmaClosed?`)
live in `MeTTa/ElaboratedCore.lean` / `MeTTa/PureCheckingService.lean` and act on
the indexed `PureTm` syntax of `PureKernel/`. (This README covers the `Pure/`
metatheory; those modules are part of the broader proof branch around it.)

## Build

```bash
# from the repository root
lake build Mettapedia.Languages.MeTTa.Pure
```

## Formalization status

All 9 `.lean` files in this directory are `sorry`-free: the reduction and typing
relations, free-variable substitution, the confluence/Church-Rosser development
and Pi/Sigma injectivity, and subject reduction. The lone textual occurrence of
"sorry" is the phrase "sorry-free" in a `TypedLangDef.lean` comment, not an
actual `sorry`.

**Trusted base.** No `axiom` declarations appear in this directory's source — a
source-level grep, *not* a per-theorem `#print axioms` audit. These proofs build
on Mathlib, whose standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
may be inherited transitively, so this is a statement about source-level `axiom`
declarations, not a claim of `#print axioms` purity. There is no `native_decide`
anywhere in this directory, so nothing here enlarges the trusted base beyond
Mathlib's standard axioms.

Reproduce from this directory (the `sorry` regex is a *raw* scan that also
matches the "sorry-free" comment in `TypedLangDef.lean`, so the comment-stripped
footer count below is authoritative):

```bash
# sorry/admit occurrences (raw — also matches the "sorry-free" comment):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Brian Aydemir, Arthur Charguéraud, Benjamin C. Pierce, Randy Pollack, Stephanie Weirich, [*Engineering Formal Metatheory*](https://www.chargueraud.org/research/2007/binders/binders_popl_08.pdf) (POPL 2008; [publisher copy](https://repository.upenn.edu/cis_papers/369)) — the locally nameless representation of binders used throughout this development.
- Lucius Gregory Meredith, Ben Goertzel, Jonathan Warrell, Adam Vandervorst, [*Meta-MeTTa: an operational semantics for MeTTa*](https://arxiv.org/abs/2305.17218) (arXiv:2305.17218, 2023) — the MeTTa meta-language this dependent fragment refines.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 9 .lean files, 0 with sorries.*
