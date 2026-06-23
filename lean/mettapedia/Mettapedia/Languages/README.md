# Formal Languages (Lean 4)

## What this is about

A *language* — whether a programming language, a process calculus, or a fragment of
English — is at heart a set of well-formed expressions plus a rule for what those
expressions *mean* or *do*. Once both halves are written down precisely, a computer can
check claims about the language: that two programs compute the same thing, that a
translation between two languages preserves behaviour, that a grammar accepts exactly the
sentences it should. `Mettapedia/Languages` collects such formalizations and, crucially,
runs them all through one shared back-end (OSLF / Native Type Theory, see `../OSLF/`): you
describe a language as a small-step rewrite system, and the framework synthesizes a modal
type theory and bisimulation theory for it automatically.

The directory spans four very different kinds of language, unified by that common shape:

- **Natural language** — a Lean port of a subset of [Grammatical Framework](https://www.grammaticalframework.org/)
  (GF), which cleanly separates *abstract syntax* (the language-independent meaning skeleton)
  from *concrete syntax* (how each language linearizes it). This is the bridge from English
  or Czech sentences into the world-model / inference stack.
- **Concurrency** — the π- and ρ-process calculi and their relatives, where computation *is*
  message-passing (see `ProcessCalculi/`, which has its own README).
- **The MeTTa language family** — syntax, the dependently-typed pure kernel, the
  Hyperon-Experimental interpreter spec, and the PeTTa runtime (see `MeTTa/`, its own README).
- **Machine and metamathematical languages** — the classic IMP imperative language, a Minsky
  register-machine fragment, and Metamath / Metamath-Zero formalizations.

This top-level README owns the small "glue" layer (the per-language facade modules and the
Metamath / IMP / MinskyLite / MM0 formalizations); the large sub-trees each document
themselves in their own README (linked below).

## Modules

### Grammatical Framework — `GF/` (own README)

A Lean 4 formalization of a GF RGL subset: ~170 abstract function signatures, two concrete
grammars (Czech and English), and a verified semantic bridge
GF → Pattern → Store → QFormula → Evidence → NTT. The Czech grammar covers 14 declension
paradigms plus verb conjugation, adjectives, pronouns, and numerals; the English grammar
covers clause construction with tense, aspect, polarity, do-support, and relative clauses.
A **SUMO repair lane** (`GF/SUMO/`) runs ontology repair through the GF → GSLT → OSLF →
world-model pipeline, comparing SUMO KIF, Enache's SUMO-GF encoding, and a flattened Lean
encoding. Full architecture, file map, and the exact proof/conformance status (including the
`native_decide` use in the US-Constitution diagnostics lane) live in
[`GF/README.md`](GF/README.md).

### Process calculi — `ProcessCalculi/` (own README)

π-calculus (asynchronous, choice-free, after Lybech), ρ-calculus (Meredith & Radestock,
locally nameless, with the spice extension), the MeTTa-calculus, the MQ quantum calculus,
and a MORK execution kernel — with cross-calculus bridges (the π → ρ forward simulation,
open-map bisimulation bridges). See [`ProcessCalculi/README.md`](ProcessCalculi/README.md).

### MeTTa language family — `MeTTa/` (own README)

Syntax, the typed pure metatheory (subject reduction, confluence), the declaration kernel,
the Hyperon-Experimental computable interpreter spec, the PeTTa Prolog-evaluation pipeline,
and the OSLF instance — see [`MeTTa/README.md`](MeTTa/README.md).

### Glue and smaller languages (this README's own scope)

| Module | Files | What it is |
|--------|-------|------------|
| `Metamath/` | 11 | Metamath language: a `LanguageDef`, simulation/acceptance equivalence, and conformance fixtures |
| `IMP/` | 5 | the classic IMP imperative language (states, big-/small-step semantics) |
| `MinskyLite/` | 5 | a Minsky register-machine fragment |
| `MM0.lean`, `MM0Lite.lean` | 2 | Metamath Zero (MM0) |
| `GF.lean`, `MeTTa.lean`, `ProcessCalculi.lean`, `Metamath.lean` | 4 | facade modules re-exporting each sub-tree |
| `OSLFNTTReadout.lean` | 1 | a compact theorem-level "what the NTT lens sees" readout over the live GF and Metamath lanes |

## Formalization status

This README's **own scope** (the glue facades plus `Metamath/`, `IMP/`, `MinskyLite/`, and
the MM0 files — everything not under a sub-tree that has its own README) is **32 `.lean`
files, all `sorry`-free**. There are no source-level `axiom` declarations in this scope
(a source grep, not a per-theorem `#print axioms` audit, so a theorem can still inherit a
standard Mathlib axiom transitively). The sub-trees report their own status:
`GF/`, `MeTTa/`, and `ProcessCalculi/` are likewise `sorry`-free in their own READMEs.

**Trusted base — `native_decide`.** The `Metamath/` lane discharges many of its conformance
and acceptance-equivalence fixtures with `native_decide` (which *compile-evaluates* a
Boolean rather than checking it in the kernel, and therefore trusts the Lean compiler and
enlarges the trusted base). There are **67 `native_decide` invocations in this README's own
scope**, all in fixture/diagnostic files:

- `Metamath/AcceptanceEquivalence.lean` — 30
- `Metamath/Fixtures.lean` — 12
- `Metamath/LanguageDefDSL.lean` — 9
- `Metamath/CommentConformance.lean` — 7
- `Metamath/Simulation.lean` — 5
- `Metamath/CrownJewelFixtures.lean` — 2
- `Metamath/BridgeConformance.lean` — 1
- `OSLFNTTReadout.lean` — 1

These are flagged for migration to kernel-checked `decide`; the structural Metamath results
(the `LanguageDef`, the simulation relation) do not depend on them. (The `GF/`, `MeTTa/`,
and `ProcessCalculi/` sub-trees carry their own `native_decide` invocations, disclosed in
their respective READMEs.)

Reproduce from this directory — the `sorry`/`admit` regex is a *raw* scan that also matches
prose in comments and string literals, so the footer's per-file figure (0) is the
authoritative comment-stripped count:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints the fixtures listed above):
rg -n --glob '*.lean' 'native_decide' .
```

Recursively, the whole `Mettapedia/Languages` tree is 461 `.lean` files (the four
sub-trees, each with its own README, own the remainder).

## References

- Aarne Ranta, [*Grammatical Framework: A Type-Theoretical Grammar Formalism*](https://doi.org/10.1017/S0956796803004738), Journal of Functional Programming 14(2):145–189 (2004) — the GF formalism.
- Aarne Ranta, [*Grammatical Framework: Programming with Multilingual Grammars*](https://www.grammaticalframework.org/gf-book/) (CSLI, 2011).
- Norman Megill & David A. Wheeler, [*Metamath: A Computer Language for Mathematical Proofs*](https://us.metamath.org/downloads/metamath.pdf) (2019) — the Metamath language.
- Mario Carneiro, [*Metamath Zero: Designing a Theorem Prover Prover*](https://doi.org/10.1007/978-3-030-53518-6_5), CICM 2020 — MM0.
- Glynn Winskel, [*The Formal Semantics of Programming Languages*](https://mitpress.mit.edu/9780262731034/the-formal-semantics-of-programming-languages/) (MIT Press, 1993) — IMP-style operational semantics.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 32 .lean files, 0 with sorries.*
