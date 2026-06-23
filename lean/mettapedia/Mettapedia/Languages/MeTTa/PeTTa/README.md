# PeTTa Evaluation Layer

Upstream: https://github.com/trueagi-io/PeTTa

## What this is about

MeTTa, the meta-language of OpenCog Hyperon, runs programs by
*pattern-matching rewriting* over a space of atoms. **PeTTa** ("Prolog-based
MeTTa") is one way to actually execute that: it compiles each MeTTa expression
into Prolog-style goals and resolves them against a logic-programming (LP)
kernel — so MeTTa's pattern matching becomes Prolog unification, and MeTTa's
nondeterministic results become the answer set of an LP query. If you know
Prolog, the mental picture is "MeTTa equations are clauses; evaluating an
expression is running a goal."

This directory formalizes that pipeline in Lean and *proves it correct*. The
chain runs from raw MeTTa expressions, through a pure pattern-level evaluation
relation, through typed evaluation with error propagation and stateful effects
(`add-atom`, `remove-atom`, `progn`), down to **LP soundness** theorems: when
PeTTa applies a rewrite rule, the result is a member of the **least Herbrand
model** of the compiled clause set. So the executable Prolog story is pinned to
a declarative logical meaning, not just asserted.

The development is laid out as an **audit-first 3-layer spec pack** (pure
declarative core, stateful declarative core, operational minimal-step layer),
with explicit bridge theorems showing the three layers agree. Import everything
via `Mettapedia.Languages.MeTTa.PeTTa` ([PeTTa.lean](../PeTTa.lean)).

## Build

```bash
# from the repository root
lake build Mettapedia.Languages.MeTTa.PeTTa
```

## Modules

### 3-layer spec pack (audit-first)

This PeTTa formalization is organized as a 3-layer spec pack:

1. **Pure declarative core**: `PeTTaEval` / `PureDecl`.
2. **Stateful declarative core**: `PeTTaCmd` / `CoreDecl`.
3. **Operational minimal-step layer**: `MeTTaStep`.

Bridge theorem anchors:
- `pureDecl_iff_pettaEval` ([DeclarativeSpec.lean](DeclarativeSpec.lean))
- `coreDecl_iff_pettaCmd` ([DeclarativeSpec.lean](DeclarativeSpec.lean))
- `evalStep_implies_pettaEval` ([MinimalInstructions.lean](MinimalInstructions.lean))
- `translatePredicate_query_to_pettaEval_match` ([DeclarativeSpec.lean](DeclarativeSpec.lean))
- `catch_fallback_to_pettaEval` ([DeclarativeSpec.lean](DeclarativeSpec.lean))

### Core evaluation

| Module | What it does |
|--------|-------------|
| [Eval.lean](Eval.lean) | `PeTTaEval` — the central pure evaluation relation (`inductive ... : Pattern → Answers → Prop`) |
| [MeTTaEval.lean](MeTTaEval.lean) | 4-argument evaluation with bindings, types, and error propagation |
| [Answers.lean](Answers.lean) | Answer-set projection from evaluation derivations |
| [SpaceSemantics.lean](SpaceSemantics.lean) | Atomspace query/match semantics |
| [Effects.lean](Effects.lean) | `PeTTaCmd` — stateful evaluation (`add-atom`, `remove-atom`, `get-atoms`, `progn`, `prog1`) |

### Types and standard library

| Module | What it does |
|--------|-------------|
| [TypeSystem.lean](TypeSystem.lean) | Type annotations, arrow types, special type atoms |
| [TypedEval.lean](TypedEval.lean) | Type-directed evaluation pass-through |
| [StdLib.lean](StdLib.lean) | Standard library derived forms (309 lines) |
| [MinimalInstructions.lean](MinimalInstructions.lean) | Operational instruction semantics |
| [Unit.lean](Unit.lean) | Unit-level evaluation fixtures |

### Bridges

| Module | What it does |
|--------|-------------|
| [LPSoundness.lean](LPSoundness.lean) | LP soundness: `PeTTaEval` rule application implies least-Herbrand-model membership |
| [PrologBridge.lean](PrologBridge.lean) | Wires `EvalOracle` to concrete PeTTa semantics |
| [TranslateExpr.lean](TranslateExpr.lean) | `compileExpr`: MeTTa expressions to Prolog goals, with correctness theorems against `PeTTaEval` |
| [GroundedOracle.lean](GroundedOracle.lean) | Grounded oracle interface for built-in operations |
| [OSLFInstance.lean](OSLFInstance.lean) | OSLF language instance (`pettaOSLF`) with Galois connection (diamond ⊣ box) and Rust export |
| [GSLTVertex.lean](GSLTVertex.lean) | GSLT forward fiber for categorical integration |

## Formalization status

All 38 `.lean` files in this directory are `sorry`-free — the pure and stateful
evaluation relations, the typed pass, the LP-soundness bridge, the
`compileExpr` translation correctness, and the OSLF instance. The 3-layer spec
pack is sealed by the named bridge theorems above (verified present in
`DeclarativeSpec.lean` and `MinimalInstructions.lean`).

**Trusted base.** No `axiom` declarations appear in this directory's source — a
source-level grep, *not* a per-theorem `#print axioms` audit (a theorem can
still inherit a Mathlib axiom such as `propext`/`Classical.choice`/`Quot.sound`
transitively, since the proofs build on Mathlib). There is no `native_decide`
anywhere in this directory, so nothing here enlarges the trusted base beyond
Mathlib's standard axioms.

Reproduce from this directory (the `sorry` regex is a *raw* scan that would also
match prose in comments/strings, so the comment-stripped footer count below is
authoritative):

```bash
# sorry/admit occurrences (raw):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## Related

- [LP kernel](../../../Logic/LP) — unification, SLD resolution, Herbrand semantics
- [Prolog layer](../../../Logic/Prolog) — goal language, cut semantics, ISO conformance fixtures (proven against the Lean evaluator)
- [Conformance harness](../../../../scripts/prolog) — SWI parity checks and ISO coverage

## References

- Lucius Gregory Meredith, Ben Goertzel, Jonathan Warrell, Adam Vandervorst, [*Meta-MeTTa: an operational semantics for MeTTa*](https://arxiv.org/abs/2305.17218) (arXiv:2305.17218, 2023) — the MeTTa operational semantics this evaluation layer formalizes.
- Ben Goertzel et al., [*OpenCog Hyperon: A Framework for AGI at the Human Level and Beyond*](https://arxiv.org/abs/2310.18318) (arXiv:2310.18318, 2023) — the Hyperon system MeTTa and PeTTa serve.
- [PeTTa (trueagi-io/PeTTa)](https://github.com/trueagi-io/PeTTa) — the upstream Prolog-based MeTTa interpreter this directory formalizes.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 38 .lean files, 0 with sorries.*
