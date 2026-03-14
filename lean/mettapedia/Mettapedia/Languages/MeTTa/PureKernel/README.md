# MeTTa PureKernel

Trusted proof kernel for dependently-typed MeTTa Pure.
**28 files. Zero sorry.**

This is the small, stable waist of the Pure MeTTa type theory: the term
syntax, reduction, typing, and definitional equality rules that every
higher-level layer proves against. Nothing enters here unless it belongs
to the intended final kernel design.

## Term Syntax (`Syntax.lean`)

Dependently-typed terms indexed by De Bruijn depth:

```
PureTm n ::= var (Fin n) | const DeclName | U0 | U1
           | pi A B | sigma A B | id A t u
           | lam B | app f a
           | pair t u | fst p | snd p
           | refl t
```

Two universes (`U0 : U1`), Π, Σ, and identity types. No inductive
families are hard-coded; they arise from the general declaration
mechanism (see below).

## Core Theory

| File | Contents |
|------|----------|
| `Syntax.lean` | `PureTm n` — scoped De Bruijn term type |
| `Renaming.lean` | `Ren`, `wkRen`; renaming action on terms |
| `Substitution.lean` | `Sub`, simultaneous substitution, `inst0` |
| `Reduction.lean` | `Red` — one-step β/δ/ι reduction |
| `Confluence.lean` | Church-Rosser / confluence for `Red` |
| `Typing.lean` | `HasType Γ t A`; weakening, substitution, context morphisms |
| `DefEq.lean` | `Conv` (reduction-closure equivalence); `cdev` canonical normalizer; `defEqByNormalization?` decision procedure |
| `AlgorithmicTyping.lean` | Bidirectional type-checking algorithm |
| `SubjectReduction.lean` | Type preservation under β/δ/ι reduction |
| `Context.lean` | `Ctx n` — typing contexts |
| `Parallel.lean` | Parallel reduction relation |

## Declaration Environment

Ordinary type families (Bool, Nat, Unit, …) are not hard-coded in the
kernel. Instead, they are added via a general declaration mechanism:

| File | Contents |
|------|----------|
| `DeclarationEnv.lean` | `DeclEntry` (type + optional unfolding), `DeclEnv` (name → entry); `Extends` monotonicity; `typeOf?`, `valueOf?` |
| `DeclarationSemantics.lean` | Well-formedness predicate `DeclEnvWellFormed`; semantics of δ-reduction via `valueOf?` |
| `DeclarationSpec.lean` | `DeclSpec` list format; `SignatureWellFormed`, `PrefixDeclSpecAdmissible`, `envOfSpecs`; lookup correctness theorems |
| `Telescope.lean` | `Telescope` — sequence of typed binders for constructor/recursor signatures |
| `InductiveDecl.lean` | General inductive family declaration: type, constructors, recursor; `InductiveDeclWellFormed` |
| `RecursorDecl.lean` | Generated recursor declarations and their typing obligations |

## Pilot Families

Bool, Nat, and Unit are instantiated via the general mechanism as
runnable proofs of concept. Each pilot provides: declaration specs,
`DeclEnv` witnesses, typed declaration theorems (`⊢ Bool : U0`, `⊢
Bool.true : Bool`, …), a δ-reduction witness (`Bool.alias` unfolds to
`Bool.true`), and full `DeclEnvWellFormed` and `SignatureWellFormed`
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

## Key Invariants

- **No sorry. No axioms beyond `propext`, `Classical.choice`, `Quot.sound`.**
- Ordinary families enter through `DeclSpec` lists, not kernel constructors.
- The δ-reduction rule reads `valueOf?` from `DeclEnv`; the kernel never hardcodes a family's unfolding.
- `SignatureWellFormedPrefix` enforces that each declaration only mentions names declared earlier.
