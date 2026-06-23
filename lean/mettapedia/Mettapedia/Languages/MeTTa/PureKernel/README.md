# MeTTa PureKernel

## What this is about

A **proof kernel** is the small, trusted core of a system that checks
proofs: keep it tiny and obviously correct, and everything built on top
inherits that trust. PureKernel is exactly that for the dependently typed
fragment of MeTTa (Hyperon's meta-language) — the minimal term syntax,
reduction, typing, and definitional-equality rules that every higher MeTTa
layer must prove against. Nothing enters here unless it belongs to the
intended final kernel design.

The kernel is a dependent type theory in the De Bruijn style (variables are
numeric indices, so there is no name capture to worry about). It provides two
universes `u0 : u1`, dependent functions (Pi), dependent pairs (Sigma), and
identity types — and proves the metatheory a kernel needs: confluence
(Church-Rosser), type preservation under reduction (subject reduction), and a
bidirectional type-checking algorithm.

One design choice is worth flagging up front: **ordinary datatypes like Bool,
Nat, and Unit are not baked into the kernel.** Instead there is a general
*declaration mechanism* — you hand the kernel a list of well-scoped
declarations, and it admits the family, its constructors, and its recursor,
with delta-reduction (definitional unfolding) reading values back out of the
declaration environment. Bool/Nat/Unit are then just the first families built
through that mechanism, included as runnable proofs of concept.

## Term Syntax (`Syntax.lean`)

Dependently typed terms `PureTm n` indexed by De Bruijn depth `n`:

```
PureTm n ::= var (Fin n) | const DeclName | u0 | u1
           | pi A B | sigma A B | id A t u
           | lam B | app f a
           | pair t u | fst p | snd p
           | refl t
```

Two universes (`u0 : u1`), Pi, Sigma, and identity types, with
`DecidableEq`/`Repr`. No inductive families are hard-coded; they arise from the
general declaration mechanism (see below).

## Core Theory

| File | Contents |
|------|----------|
| `Syntax.lean` | `PureTm n` — scoped De Bruijn term type |
| `Renaming.lean` | `Ren`, `wkRen`; renaming action on terms |
| `Substitution.lean` | `Sub`, simultaneous substitution, `inst0` |
| `Reduction.lean` | `Red` — one-step beta/delta/iota reduction |
| `Confluence.lean` | Church-Rosser / confluence for `Red` |
| `Typing.lean` | `HasType Γ t A`; weakening, substitution, context morphisms |
| `DefEq.lean` | `Conv` (reduction-closure equivalence); `cdev` canonical normalizer; `defEqByNormalization?` decision procedure |
| `AlgorithmicTyping.lean` | Bidirectional type-checking algorithm |
| `SubjectReduction.lean` | Type preservation under beta/delta/iota reduction |
| `Context.lean` | `Ctx n` — typing contexts |
| `Parallel.lean` | Parallel reduction relation (for the confluence proof) |

## Declaration Environment

Ordinary type families (Bool, Nat, Unit, ...) are not hard-coded in the kernel.
Instead, they are added via a general declaration mechanism:

| File | Contents |
|------|----------|
| `DeclarationEnv.lean` | `DeclEntry` (type + optional unfolding), `DeclEnv` (name → entry); `Extends` monotonicity; `typeOf?`, `valueOf?` |
| `DeclarationSemantics.lean` | Well-formedness predicate `DeclEnvWellFormed`; semantics of delta-reduction via `valueOf?` |
| `DeclarationSpec.lean` | `DeclSpec` list format; `SignatureWellFormed` / `SignatureWellFormedPrefix`, `PrefixDeclSpecAdmissible`, `envOfSpecs`; lookup-correctness theorems |
| `Telescope.lean` | `Telescope` — sequence of typed binders for constructor/recursor signatures |
| `InductiveDecl.lean` | General inductive-family declaration (`IndDecl`, `CtorSpec`); the `checkIndDecl` admissibility checker with positivity tests (`strictlyPositive`, `occursOnlyPositively`, `targetsFamily`, `namesDistinct`) and good/bad examples (`badNegDecl`, `badTargetDecl`) |
| `RecursorDecl.lean` | Generated recursor declarations and their typing obligations |

## Pilot Families

Bool, Nat, and Unit are instantiated via the general mechanism as runnable
proofs of concept. Each pilot provides: declaration specs, `DeclEnv`
witnesses, typed declaration theorems (`⊢ Bool : u0`, `⊢ Bool.true : Bool`,
...), a delta-reduction witness (`Bool.alias` unfolds to `Bool.true`, e.g.
`valueOf_boolAlias`), and full `DeclEnvWellFormed` and `SignatureWellFormed`
proofs.

| File | Family |
|------|--------|
| `BoolDecl.lean` | Bool (type, `true`, `false`, alias) |
| `NatDecl.lean` | Nat (`zero`, `succ`, alias) |
| `UnitDecl.lean` | Unit (`unit`) |

## Bridges and Integration

| File | Contents |
|------|----------|
| `PatternBridge.lean` | Embedding `PureTm` into the shared `Pattern` AST used by OSLF |
| `PatternBridgeSubst.lean` | Substitution coherence across the bridge |
| `CoreEmbedding.lean` | Embedding PureKernel terms into the broader MeTTa Core layer |
| `HOLToPureIntegrationContract.lean` | Contract linking the HOL layer to PureKernel judgements |
| `TypedLangDef.lean` | PureKernel as an OSLF `TypedLangDef` assembly |
| `ProfileTheory.lean` | Profile-level theory for the kernel |
| `Inst0BridgeProof.lean` / `Inst0BridgeDerived.lean` | `inst0` substitution bridge proofs and derived lemmas |

## Key invariants

- Ordinary families enter through `DeclSpec` lists, not kernel constructors.
- The delta-reduction rule reads `valueOf?` from `DeclEnv`; the kernel never
  hardcodes a family's unfolding.
- `SignatureWellFormedPrefix` enforces that each declaration only mentions
  names declared earlier (no forward references / shadowing).

## Formalization status

All 28 `.lean` files in this directory are `sorry`-free: the De Bruijn syntax,
renaming/substitution, reduction and its confluence, the typing judgment and
bidirectional algorithm, subject reduction, the declaration mechanism and its
well-formedness predicates, and the Bool/Nat/Unit pilots with their typed
declaration theorems.

**Trusted base.** No source-level `axiom` declarations appear in this directory
— a source grep, *not* a per-theorem `#print axioms` audit. Because these proofs
build on Mathlib, the standard Mathlib axioms (`propext`, `Classical.choice`,
`Quot.sound`) may be inherited transitively; this README does not run
`#print axioms`, so it does not claim those are absent, only that the kernel adds
no `axiom` of its own. There is no `native_decide` anywhere in this directory, so
nothing here enlarges the trusted base beyond Mathlib's standard axioms.

Reproduce from this directory (the `sorry` regex is a *raw* scan that would also
match comment/string prose, so the comment-stripped footer count below is
authoritative):

```bash
# sorry/admit occurrences (raw):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Lucius Gregory Meredith, Ben Goertzel, Jonathan Warrell, Adam Vandervorst, [*Meta-MeTTa: an operational semantics for MeTTa*](https://arxiv.org/abs/2305.17218) (arXiv:2305.17218, 2023) — the MeTTa meta-language this dependent kernel underpins.
- Ben Goertzel, [*Reflective Metagraph Rewriting as a Foundation for an AGI "Language of Thought"*](https://arxiv.org/abs/2112.08272) (arXiv:2112.08272, 2021) — MeTTa as Hyperon's meta-language, the setting for a trusted typed kernel.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 28 .lean files, 0 with sorries.*
