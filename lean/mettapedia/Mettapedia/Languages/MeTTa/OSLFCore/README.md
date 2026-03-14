# MeTTa Core

The OSLF-facing representation layer for MeTTa: the canonical `Atom` type,
`Atomspace`, pattern matching, rewrite rules, and the `FullLanguageDef`
OSLF instance. **16 files.**

This directory is **not** the computable HE spec (`HE/`) and **not** the
Prolog evaluation pipeline (`PeTTa/`). It provides the shared algebraic
vocabulary — `Atom`, `Atomspace`, `PatternMatch`, `RewriteRules` — that
OSLF-layer clients and bridges import.

## Modules

### Atom and Space

| File | Contents |
|------|----------|
| `Atom.lean` | 4-constructor `Atom` (Symbol, Variable, Grounded, Expression); `GroundedValue`; `DecidableEq`, `LawfulBEq`; meta-type constants (`atomType`, `symbolType`, …); `typeAnnotation`, `functionType` helpers |
| `Atomspace.lean` | `Atomspace` — noncomputable `Multiset Atom` wrapper; `add`, `remove`, `query`, `empty` |
| `Bindings.lean` | Variable binding maps for pattern matching |
| `Types.lean` | MeTTa type system: `MetaType`, `HasType` judgement, `checkType` decision procedure |

### Pattern Matching and Reduction

| File | Contents |
|------|----------|
| `PatternMatch.lean` | Structural pattern matching with variable capture; binding construction |
| `RewriteRules.lean` | `RewriteRule` type — head pattern + body; rule application |
| `Premises.lean` | Premise queries for the OSLF rewrite IR |
| `MinimalOps.lean` | Minimal built-in operations (arithmetic, comparison, control) |

### State and OSLF Instance

| File | Contents |
|------|----------|
| `State.lean` | Explicit `State` sort: instruction stream + atomspace |
| `FullLanguageDef.lean` | `mettaFull` — first OSLF `LanguageDef` client; explicit `State`/`Instr`/`Atom`/`Space` sorts; premise-driven equation lookup (`eqnLookup`), core instruction branches (Eval, Unify, Chain, Return) |
| `FullPremises.lean` | Premises for the full language def (`typeOf`, `cast`, `groundedCall` hooks) |
| `FullLanguageTests.lean` | Integration tests for the full language def |

### Properties and Bridges

| File | Contents |
|------|----------|
| `Properties.lean` | Properties of atom operations (membership, equality, space laws) |
| `SubjectReduction.lean` | Type preservation under rewrite-rule application |
| `Algebra.lean` | Algebraic properties of atomspace operations |
| `Bridge.lean` | Bridge from `MeTTaCore.Atom` to the shared OSLF `Pattern` AST |

## Relationship to Other Layers

- **vs `HE/`**: HE uses a computable `List Atom` space and directly mirrors
  `interpreter.rs`. Core uses a noncomputable `Multiset` and is designed for
  OSLF proof composition, not executable conformance testing.
- **vs `PeTTa/`**: PeTTa compiles MeTTa expressions into Prolog goals. Core
  provides the atom algebra that PeTTa's `TranslateExpr` and `LPSoundness`
  proofs reason about.
- **vs `PureKernel/`**: PureKernel is a dependently-typed kernel (Pi/Sigma/Id).
  Core is untyped symbolic atoms with a shallow type layer on top.
