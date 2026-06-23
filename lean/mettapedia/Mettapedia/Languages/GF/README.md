# Grammatical Framework in Lean 4

## What this is about

A grammar normally does two jobs at once; **Grammatical Framework (GF)** pulls
them apart. The *abstract syntax* describes what a sentence *means*, as a typed
tree, in a way that is independent of any one language — "some agent performs
some action on some object." The *concrete syntax*, or *linearization*, says how
that tree is *spelled out* in a particular language: word order, agreement,
morphology, articles. Because the meaning is shared, the same abstract tree can
be linearized into English, into Czech, or into a logical form, and a surface
string can be *parsed* back to the tree. That separation — typed meaning tree on
one side, language-specific surface function on the other — is what makes GF a
*multilingual* grammar formalism rather than a parser for a single language.

This directory formalizes a working subset of GF in Lean 4 and connects it to
Mettapedia's semantic machinery. Concretely it provides:

- an **abstract syntax** — the GF category system and a curated set of RGL
  function signatures;
- two **concrete grammars** — a Czech morphology engine and a broader English
  morphology-plus-clause-construction grammar (each with its own README, in
  `HandCrafted/`);
- a **semantic bridge** — GF abstract trees viewed as an OSLF `LanguageDef`, with
  an evidence-valued denotational semantics, so a parsed sentence can flow all
  the way to a truth/evidence value.

The pipeline it targets is `GF tree → Pattern → (store) → QFormula → Evidence`.

- Primary author: Oruži (AI). Human lead editor: Zar.

## Scope

This is a **strict subset** of GF, not a full RGL port:

- The abstract syntax includes 170 core GF RGL function signatures (`HandCrafted/Abstract.lean`).
- The category system defines 112 named GF categories (`HandCrafted/Core.lean`).
- The Czech concrete grammar is a morphology engine; its sentence-level linearization is partial.
- The English concrete grammar covers morphology and clause construction, with broader syntactic coverage than Czech.
- The semantic bridge targets OSLF evidence semantics.

It deliberately does **not** include the PGF runtime, PMCFG parsing, chart
parsing, full conjunction linearization, or full English numeral linearization.

## Architecture

The reusable core lives in `HandCrafted/`; the GF-top-level files build the OSLF
bridge, the kernel/confluence results, the CNL (controlled-natural-language)
renderers, and several conformance/diagnostic experiments.

```
HandCrafted/Core.lean        GF categories (112 named), AbstractTree, ConcreteForm, Grammar
HandCrafted/Abstract.lean    170 core RGL function signatures and abstract nodes
HandCrafted/Concrete.lean    Inflection tables and morphophonological operations
HandCrafted/English/         English morphology and clause construction (own README)
HandCrafted/Czech/           Czech morphology engine (own README)
Typing.lean                  GF-to-OSLF type checking and compositionality
OSLFBridge.lean              GF abstract syntax as an OSLF LanguageDef
WorldModelSemantics.lean     Evidence-valued denotational semantics for GF trees
KernelConfluence.lean        Confluence (mod the normalization invariant) of the kernel rewrite
LinguisticInvariance.lean    Cross-linguistic / lexical-invariance results, garden-path disambiguation
Examples/                    End-to-end pipeline examples (own README)
USConstitution/              GF-witness conformance experiment on Constitution fragments
SUMO/                        SUMO-ontology controlled-language fragment
Generated/                   Machine-generated PGF witness data
ArchivedLegacy/              Frozen earlier material (kept for reference; not a development target)
```

### Typed-symbol pipeline

- Tree-to-pattern bridge: `GF_tree → Pattern`
- Pattern-to-formula bridge: `Pattern → QFormula`
- Full composition: `GF_tree → Pattern → Store → QFormula → Evidence`

## Key results

- **Kernel confluence** (`KernelConfluence.lean`): `kernel_confluence_mod` — the
  kernel rewrite relation is confluent modulo the normalization invariant,
  supported by a terminating wrapper-count measure.
- **Linguistic invariance** (`LinguisticInvariance.lean`): constructors preserve
  the lexical content of a tree, modification enriches it, and the garden-path
  sentence "The old man the boats" is disambiguated at the lexical level.
- **Roundtrip regression** (`RoundTripRegression.lean`): the curated English and
  Czech corpora — 38 surfaces in total (20 English + 18 Czech, per the
  per-language `RoundTripCorpus.lean` files) — have *no* roundtrip failures
  (`*_Failures_empty`).
- **Worked examples** (`Examples/`) prove the end-to-end pipeline on specific
  sentences.

## Formalization status

No `axiom` declarations appear in the source — a source-level grep, *not* a
per-theorem `#print axioms` audit (a theorem can still inherit a Mathlib axiom
transitively).

**Proof state.** This directory's own scope (the files whose nearest README is
this one — i.e. everything under `GF/` except the `Examples/`,
`HandCrafted/Czech/`, and `HandCrafted/English/` subtrees, which have their own
READMEs) is `sorry`-free: 85 files, 0 with sorries (see the footer).

**Trusted base — `native_decide` disclosure.** This directory's own scope is *not*
free of `native_decide`. Thirty-five `native_decide` invocations remain, all in
the US-Constitution conformance/diagnostic *fixtures*:

- `USConstitution/Diagnostics.lean` — 25 occurrences;
- `USConstitution/GeneratedConformance.lean` — 10 occurrences.

These discharge concrete equalities about generated witness data (e.g.
`allClauseIds.length = 21`, `sourceHash.length = 64`) by *compiling and
evaluating* rather than kernel-checking. `native_decide` trusts the Lean
compiler, so each such use **enlarges the trusted base** beyond the kernel. They
are flagged for migration to kernel-checked `decide`; until then this lane is not
a fully kernel-verified slice. The core grammar/bridge/kernel results above do
not use `native_decide`.

Reproduce from this directory — the `sorry`/`admit` regex is a *raw* scan that
also matches comment/string prose, so the per-file counts in the footer are the
authoritative comment-stripped figures:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (the 35 US-Constitution fixtures above):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Aarne Ranta, [*Grammatical Framework: A Type-Theoretical Grammar Formalism*](https://doi.org/10.1017/S0956796803004738), Journal of Functional Programming 14(2):145–189 (2004) — the core GF reference (abstract/concrete separation).
- Aarne Ranta, [*Grammatical Framework: Programming with Multilingual Grammars*](https://www.grammaticalframework.org/gf-book/) (CSLI Publications, Stanford, 2011) — the book-length GF reference.
- L. Gregory Meredith & Mike Stay, [*Name-free combinators for concurrency*](https://arxiv.org/abs/1703.07054) (arXiv:1703.07054) — background for the OSLF semantic bridge.
- GF Resource Grammar Library — [GitHub source](https://github.com/GrammaticalFramework/gf-rgl).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 85 .lean files, 0 with sorries.*
