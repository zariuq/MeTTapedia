# HE — Hyperon Experimental Interpreter (Lean 4)

## What this is about

When you want to know "what does this MeTTa program actually do?", the most direct
answer is: *run it the way the reference implementation runs it.* [Hyperon
Experimental](https://trueagi-io.github.io/hyperon-experimental/metta/) (HE) is the
reference MeTTa system, and its evaluator lives in Rust (`interpreter.rs`). This
directory transcribes that evaluator into Lean as a **fuel-bounded, computable
function** — a faithful re-expression of the reference interpreter that Lean can
actually *evaluate* inside proofs.

Why bother re-implementing it in a proof assistant? Because once the interpreter is
a Lean function, you can state and check *conformance* facts: "on this input, the
spec's clause says the result is X" becomes a theorem the kernel verifies by
computation. The spec prose (`metta.md`) and the Rust source agree, and the Lean
copy lets you prove they agree, clause by clause.

**Source precedence:** `interpreter.rs` (ground truth) > `metta.md` (spec prose,
lines 240-552).

## Core

`Eval.lean` — a mutual block of fuel-bounded evaluation functions:

| Function | Role |
|----------|------|
| `evalAtom` | Top-level step; dispatches on expression form |
| `interpretExpression` | Evaluates a single expression |
| `interpretFunction` | Handles function application |
| `interpretArgs` | Evaluates argument lists |
| `interpretTuple` | Evaluates tuple forms |
| `mettaCall` | Calls into the space / rule lookup |

plus `eval`, the fuel-wrapped public entry point (`fuel := 100` by default).

`Types.lean` — `Bindings` (assignments + equalities), `ResultPair`, `ResultSet`,
error codes.

`Conformance.lean` — 48 clause-by-clause conformance theorems (`rfl`/`decide`)
checked against `metta.md`. No source-level `axiom` declarations and no `sorry`
(comment-stripped), and no `native_decide` in this file — the conformance theorems
are kernel-checked.

## Supporting Modules

| Module | Contents |
|--------|----------|
| `Space.lean` | `List Atom` space (computable, unlike `MeTTaCore.Atomspace`'s noncomputable `Multiset`) |
| `Matching.lean` | Pattern matching and binding unification |
| `TypeCheck.lean` | Type-checking pass |
| `CoreFragment.lean` | Core expression fragment |
| `HELanguageDef.lean` | Full OSLF `LanguageDef` with HE dispatch |
| `HEPremises.lean` | Premise specifications |
| `ContractCatalog.lean` | Execution contracts |

## Key semantics

- Symbols -> `typeCast` (not equation lookup)
- Expressions -> `interpretExpression` -> `mettaCall`
- `Bindings`: `assignments : List (String x Atom)` + `equalities : List (String x String)`

## Formalization status

Own scope is 67 `.lean` files with **0 `sorry`** (comment-stripped). No source-level
`axiom` declarations appear in these files — this is a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a Mathlib axiom
transitively.

**Trusted base — `native_decide`.** The clause-by-clause `Conformance.lean` theorems
are kernel-checked (`rfl`/`decide`), but two files carry 12 `native_decide`
invocations that compile-evaluate rather than kernel-check, so they enlarge the
trusted base (they trust the Lean compiler) and are flagged for migration to kernel
`decide`:

- `MatcherBridge.lean` — 11
- `Eval.lean` — 1

Reproduce from this directory — note the `sorry` regex is a *raw* scan that also
matches prose in comments/strings, so the own-scope figure of 0 above is the
authoritative comment-stripped count:

```bash
# build this layer:
lake build Mettapedia.Languages.MeTTa.HE
# sorry occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\bsorry\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (the 12 disclosed above):
rg -n --glob '*.lean' 'native_decide' .
```

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 67 .lean files, 0 with sorries.*
