# MeTTa Core (OSLF-facing layer)

## What this is about

MeTTa is the meta-language at the heart of OpenCog Hyperon: an
S-expression, homoiconic language whose programs are themselves data, and
whose only computation rule is *nondeterministic pattern-matching rewriting*
over a knowledge base of **atoms** (an "atomspace"). If you have seen Lisp, the
syntax will look familiar; the twist is that MeTTa rewrites against a queryable
space of facts and equations rather than evaluating a fixed program, and a
single query can return many results.

This directory builds the canonical **atom algebra** that the rest of the MeTTa
formalization reasons about, and packages it as an input to **OSLF**
(Operational Semantics in Logical Form, Meredith & Stay): an algorithm that
takes a rewrite system and *synthesizes a type system* for it — types are
`(sort, predicate)` pairs, and modal operators "step-future" (`diamond`) and
"step-past" (`box`) are read off the reduction relation. Concretely, this layer
provides:

- a 4-constructor `Atom` type (Symbol, Variable, Grounded, Expression) with
  decidable equality — the data every other MeTTa layer manipulates;
- an `Atomspace` (a `Multiset Atom`) with `add`/`remove`/`query`;
- structural pattern matching with variable capture, and rewrite rules; and
- `mettaFullLegacy`, an OSLF `LanguageDef` instance giving MeTTa an explicit
  machine `State` and core instructions (Eval, Unify, Chain, Return).

It is deliberately the *proof-composition* representation, not the executable
conformance spec. See "Relationship to Other Layers" below for how it differs
from the computable HE mirror, the PeTTa Prolog pipeline, and the dependently
typed PureKernel.

## Modules

### Atom and Space

| File | Contents |
|------|----------|
| `Atom.lean` | 4-constructor `Atom` (Symbol, Variable, Grounded, Expression); `GroundedValue`; `DecidableEq`, `LawfulBEq`; meta-type constants (`atomType`, `symbolType`, ...); `typeAnnotation`, `functionType` helpers |
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
| `FullLanguageDef.lean` | `mettaFullLegacy` — full-oriented OSLF `LanguageDef` client; explicit `State`/`Instr`/`Atom`/`Space` sorts; premise-driven equation lookup (`eqnLookup`), core instruction branches (Eval, Unify, Chain, Return) |
| `FullPremises.lean` | Premises for the full language def (`typeOf`, `cast`, `groundedCall` hooks) |
| `FullLanguageTests.lean` | Integration tests for the full language def |

### Properties and Bridges

| File | Contents |
|------|----------|
| `Properties.lean` | Properties of atom operations (membership, equality, space laws) |
| `SubjectReduction.lean` | Type preservation under rewrite-rule application |
| `Algebra.lean` | Algebraic properties of atomspace operations |
| `Bridge.lean` | Bridge from `MeTTaCore.Atom` to the shared OSLF/MeTTaIL `Pattern` AST |

## Relationship to Other Layers

- **vs `HE/`**: HE uses a computable `List Atom` space and directly mirrors the
  Hyperon Experimental `interpreter.rs`. Core uses a noncomputable `Multiset`
  and is designed for OSLF proof composition, not executable conformance
  testing.
- **vs `PeTTa/`**: PeTTa compiles MeTTa expressions into Prolog goals. Core
  provides the atom algebra that PeTTa's translation and soundness proofs reason
  about.
- **vs `PureKernel/`**: PureKernel is a dependently-typed kernel (Pi/Sigma/Id).
  Core is untyped symbolic atoms with a shallow type layer on top.

## Formalization status

Every `.lean` file in this directory is `sorry`-free — the atom algebra,
pattern matching, rewrite rules, the `mettaFullLegacy` OSLF instance, and the
subject-reduction and bridge results.

**Trusted base.** No `axiom` declarations appear in this directory's source — a
source-level grep, *not* a per-theorem `#print axioms` audit (a theorem can
still inherit a Mathlib axiom such as `propext`/`Classical.choice`/`Quot.sound`
transitively, since the proofs build on Mathlib). There is no `native_decide`
anywhere here; the only textual mentions of `native_decide` are in
`FullLanguageTests.lean`, where comments explicitly note that the tests are
checked by the Lean kernel and do *not* use it. So nothing in this directory
enlarges the trusted base beyond Mathlib's standard axioms.

Reproduce from this directory — note the `sorry`/`native_decide` regexes are
*raw* scans that also match prose in comments/strings (e.g. the `native_decide`
mentions in `FullLanguageTests.lean`), so the comment-stripped footer count
below is the authoritative figure:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (only comment mentions in FullLanguageTests.lean):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Lucius Gregory Meredith, Ben Goertzel, Jonathan Warrell, Adam Vandervorst, [*Meta-MeTTa: an operational semantics for MeTTa*](https://arxiv.org/abs/2305.17218) (arXiv:2305.17218, 2023) — the operational semantics this atom algebra and `LanguageDef` instance follow.
- Ben Goertzel, [*Reflective Metagraph Rewriting as a Foundation for an AGI "Language of Thought"*](https://arxiv.org/abs/2112.08272) (arXiv:2112.08272, 2021) — MeTTa as Hyperon's metagraph-rewriting meta-language.
- Christian Williams & Michael Stay, [*Native Type Theory*](https://arxiv.org/abs/2102.04672) (arXiv:2102.04672, ACT 2021) — the presheaf-internal-language construction underlying OSLF's "types from a rewrite system".
- [Hyperon Experimental — MeTTa documentation](https://trueagi-io.github.io/hyperon-experimental/metta/) — the reference MeTTa implementation the atom datatype mirrors.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 16 .lean files, 0 with sorries.*
