# Conformance

A formal specification and a running implementation can drift apart: the
spec says one thing, the code does another, and only a test catches it —
if there is one. This directory closes that gap with **machine-checked
conformance proofs**. Each proof takes a concrete input, runs it through
*both* the formal Lean spec and a stand-in for the runtime backend, and
proves the two outputs are the *same term* in Lean's kernel. When that
succeeds, the kernel itself is the test runner, and "spec = code" holds by
definitional equality rather than by a passing test that might not be
re-run.

The directory pins the formal side of Mettapedia against four runtime
surfaces: the `Simple` finite-state backend, the PeTTa engine, the HE
parser/interpreter, and the book's "Maple Court" world-model example.

## Core Idea

A conformance proof takes a concrete input (space + query, or config +
pattern), runs it through both the formal spec and the runtime backend,
and proves the outputs are identical — typically by `rfl` on computable
definitions, or via kernel-checked `decide` on Bool fixtures bridged to
Prop theorems with `decide_eq_true_eq.mp`.

This closes the gap between "the spec says X" and "the implementation
returns X": if both sides reduce to the same normal form in Lean's
kernel, the runtime and spec agree by *definitional* equality. No
external test harness is needed — the kernel *is* the test runner.

## Modules

### `SimpleHE.lean` (322 lines, 9 fixtures + 6 theorem anchors)

Conformance between the `Simple` finite-state backend
(`Algorithms.MeTTa.Simple.Session`) and the formal HE interpreter spec
(`HE.Interpreter`). Tests cover:

- **Basic rewriting**: `f(a) = b` → query `f(a)` → `[b]`
- **Chained rewrites**: `g(a) → f(a) → b`
- **Non-determinism**: multiple rules for one LHS
- **No-reduction**: unknown expressions preserved
- **Pattern variables**: `f(x) = result(x)` with concrete substitution
- **Untyped identity**: `id(x) = x`
- **Duplicate rules**: same rule twice → duplicate outputs
- **Premise relations**: conditional rewrite gated by `allowed(alpha)`
- **Premise builtins**: conditional rewrite gated by `palette(warm)`

Translation layer: `atomToFrozen?` / `frozenToAtom` bridges `Atom`
(spec) ↔ `FrozenHEAtom` (runtime).

### `SimplePeTTa.lean` (1,070 lines, 48 checks + 11 theorems)

Cross-engine equivalence between the PeTTa runtime and the
`OSLF.MeTTaIL.Engine` reference evaluator. The most comprehensive
conformance module:

- **Bidirectional translation** (`Core` ↔ `Spec`) for all MeTTaIL types:
  patterns, equations, rules, language defs — with round-trip proofs
- **Basic evaluation** (3): simple, nested, non-determinism
- **Premise handling** (2): relation facts, builtin facts
- **Space matching** (13): pattern match against facts, multi-fact
  instantiation, shared-variable constraints, conjunction, named spaces
- **Session/state** (4): dynamic `add-atom`, `remove-atom`, nested
  side-effects
- **Intrinsic operations** (4): arithmetic (`+`, `-`, `*`, `%`),
  comparison (`<`), equality (`==`, `!=`)
- **Translation round-trips** (4): pattern, rule, language-def, tuple
- **Profile checksum drift** (5): detect semantic drift between engines

### `HEParserConformance.lean` (108 lines, 9 Bool checks)

Parser conformance for HE syntax profiles (compatibility vs canonical).
Tests that `!name` parses as symbol in compatibility mode but as
`!(eval (name))` in canonical mode; that `(= (f a) b)` → `defineEq`;
that `(: foo Bar)` → `defineType`; that bare `!` is rejected; etc.

### `PeTTaArtifactBridge.lean` (82 lines, 4 theorems)

Frozen `PeTTaConfig` round-trips through formal `PeTTaSpace`: facts and
rewrite rules map correctly both directions. Establishes the artifact
source-of-truth boundary between runtime lowering and formal
verification.

### `PeTTaBackendSpaceCompat.lean` (542 lines, 20+ theorems)

Proves `&mork` space references normalize to `&self` (the only currently
proved default atomspace). Covers normalization of match, get-atoms,
add-atom, remove-atom, collapse, let, chain, let\*, progn, prog1.
Proves normalized queries still satisfy `PeTTaEval`,
`PeTTaSpaceCoreQuery`, and `SpaceEffectFragment` predicates.

### `PeTTaCompatHeadBoundary.lean` (574 lines, 18+ theorems)

Two-phase compat-head lowering architecture:

1. **External witness phase**: grounded oracle evaluation (e.g.
   `is-member` tuple membership check) produces witnesses
2. **Residual MORK phase**: actual MORK source rules fire on the
   workspace using those witnesses

Proves binding-flow soundness: witness bindings instantiate the residual
body the same way MORK's substitution does.
`TupleMembershipOracleContract` grounds the external witness phase.

### `HECoreFiles.lean` (91 lines)

Runs a curated subset of the *actual* CeTTa HE core `.metta` files through
the real `FileRunner` (`Languages.MeTTa.HE.FileRunner`), recording the
current supported lane against real-file pressure rather than overclaiming.
It tracks three lanes explicitly: `supportedCoreFiles` (e.g.
`he_a1_symbols.metta`, `he_b0_chaining_prelim.metta`, `he_b1_equal_chain.metta`,
`he_b3_direct.metta`) run end-to-end with zero errors; a near-frontier file
(`he_a3_twoside.metta`) is one failing assertion away; and a negative-example
file (`he_b2_backchain.metta`) still exposes a missing reasoning capability.

### `MapleCourtConformance.lean` (101 lines)

Bridges the **algebraic** Maple Court model to the **typed rewrite calculus**.
It proves that each Maple Court algebraic operation (revision, extraction) from
`Logic.PLNMapleCourtDemo` corresponds to a WM-calculus rewrite step in
`wmCoreLanguageDef`: the evidence-add law fires as the `RewriteRule`
`ruleEvidenceAdd` via `langReduces`, and batch-vs-sequential sleep
consolidation is witnessed at the rewrite level. The payoff: the same
world-model operations proved algebraically in the `WorldModel` typeclass are
also derivable as typed rewrite steps, so the algebra and the operational
semantics agree.

### `MapleCourtEvidenceConformance.lean` (212 lines)

Kernel-checked verification of the Maple Court *full-day* evidence profile
across three layers: a reflected Nat-arithmetic model (`BinEvN`/`KEv3N` with
`hplus`/`krev`/`dirToBin`/`strength`, checked by `decide`); a bridge proving the
reflected values agree with `mapleCourtEvidence` from `PLNMapleCourtDemo.lean`;
and correspondence to the PeTTa runtime fixture
`artifacts/conformance/maple_court_full_profile.metta`. It also includes
negative-example discrimination tests proving that wrong values are rejected,
so a trivial always-`true` checker would fail.

### `MapleCourtWMConformance.lean` (116 lines)

Proves the WM-calculus core rules correctly rewrite Maple Court terms using the
Ramsey36 reflection pattern: a specialized checker `wmCoreCheck` that the kernel
can reduce directly (one pattern match, no recursion or substitution engine), a
soundness theorem linking the checker to the real engine, and conformance
theorems composing the two. All proofs are kernel-checked.

### Maple Court PeTTa Conformance (`artifacts/conformance/maple_court_simple.metta`)

End-to-end conformance between the PeTTa runtime and the Lean algebraic
world model for the book's running example.  6 tests covering:

- Evidence revision (`evidence-hplus`) = Lean `BinaryEvidence.hplus`
- Strength view = Lean `BinaryEvidence.toStrength`
- Commutativity, zero identity
- Three-way sleep consolidation (batch = sequential)

Run: `cd hyperon/PeTTa && ./run.sh <path>/maple_court_simple.metta --silent`

Lean side: `Logic/PLNMapleCourtDemo.lean` (sorry-free) proves the
same operations algebraically.  The two sides agree by construction —
PeTTa's `pln_evidence.metta` implements the same formulas as Lean's
`BinaryEvidence`.

## Formalization status

All 10 `.lean` files in this directory are `sorry`-free.

**Trusted base.** No `axiom` declarations appear in the source — a
source-level grep, *not* a per-theorem `#print axioms` audit (a theorem can
still inherit a Mathlib axiom transitively). Conformance fixtures are
discharged by `rfl` on computable definitions or by kernel-checked `decide`
on Bool fixtures bridged to Prop with `decide_eq_true_eq.mp`. There is **no
`native_decide`** anywhere in this directory, so nothing here compile-evaluates
rather than kernel-checks; the trusted base is not enlarged. (The matches for
the string `native_decide` in these files all appear inside docstrings/comments
stating that the path is *non*-`native_decide`.)

Reproduce from this directory — the `sorry`/`native_decide` regexes below are
*raw* scans that also match prose in comments/strings, so the per-file
comment-stripped count is the authoritative figure in the footer:

```bash
# sorry occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\bsorry\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (raw — only matches the "non-native_decide" prose):
rg -n --glob '*.lean' 'native_decide' .
```

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 10 .lean files, 0 with sorries.*
