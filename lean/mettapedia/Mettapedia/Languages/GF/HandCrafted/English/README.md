# English Morphology and Clause Construction (GF, Lean 4)

## What this is about

A **Grammatical Framework (GF)** grammar separates the *abstract syntax* — the
language-independent meaning of a sentence, as a typed tree — from the *concrete
syntax*, which *linearizes* that tree into a particular language's surface
strings. English carries little inflection but a lot of *syntax*: tense and
aspect are spelled out with auxiliary verbs, questions and negation need
*do-support* ("does he walk?", "he doesn't walk"), word order flips between
declarative and interrogative, and relative clauses extract a noun phrase from
inside a clause. This directory is the Lean 4 formalization of that English
concrete syntax — both the (modest) morphology and the (substantial) clause
construction — ported from the GF Resource Grammar Library (`ResEng.gf`,
`ParadigmsEng.gf`, `SentenceEng.gf`, `RelativeEng.gf`).

It covers more *syntactic* ground than the Czech engine in `../Czech/` (which is
morphology-only): here a full clause is built from a verb plus tense, aspect, and
polarity, with do-support, question inversion, and relative clauses. It remains a
*partial* port of the GF RGL English (see *What's missing*).

## Coverage

### Morphology — `Morphology.lean`
The parameter types: Case (2: Nom/Gen), Number (2), Gender (3), Person (3), Agr
(8 agreement values), VForm (5 verb forms), Tense (4), Anteriority (2), CPolarity
(positive / negative / contracted-negative), Polarity (2), Order
(declarative/interrogative), Degree (3). English is morphologically far simpler
than Czech (4 noun forms vs 14), so most of the work is in syntax.

### Nouns — `Nouns.lean`
The 4-form noun (sg/pl × nom/gen) with pluralization (`addS`), genitive
formation, and the `regN`/`mk2N`/`mk4N`/`compoundN` constructors. Includes the
irregular plurals (man/woman/mouse/foot/tooth/child/ox/sheep), gendered nouns,
and compounds.

### Adjectives — `Adjectives.lean`
Positive/comparative/superlative/adverb forms with both comparison strategies —
synthetic (`-er`/`-est`) and analytic (`more`/`most`) — via regular, compound,
irregular, and invariable paradigms; `compStem` for comparative formation.

### Verbs — `Verbs.lean`
The 5-form verb paradigm (infinitive, present 3sg, past, past participle, present
participle), with regular and irregular (3-form, 4-form) constructors. Full
auxiliary paradigms (be/have/do) with polarity-sensitive forms, and `EnglishV2`
for transitive verbs carrying a complement preposition.

### Syntax — `Syntax.lean`
Full clause construction: tense × anteriority combinations with positive and
negative (contracted and uncontracted) realizations; do-support for questions
and negation; declarative and interrogative word orders; `EnglishVP`,
`EnglishVPSlash` (for extraction), and `EnglishClause`; article selection
(a/an/the) and mass nouns; VP modification (adverbs) and complementation.

### Relative clauses — `Relatives.lean`
`EnglishRP`/`EnglishRCl`/`EnglishRS`/`EnglishClSlash`, with `relVP` (subject
relatives: "who walks"), `relSlash` (object relatives with extraction: "whom she
loves"), and `useRCl` carrying tense/polarity.

### Pronouns and structural words — `Pronouns.lean`
8 personal pronouns with full case forms (I/we/you-sg/you-pl/he/she/it/they),
demonstrative and quantifier determiners, interrogatives (who/what), prepositions,
coordinating `EnglishConj`, and subordinating `EnglishSubj`.

### Linearization — `Linearization.lean` and `Linearization/`
The typed evaluator bridging GF abstract trees to English surface strings:
category-aware lexical leaves, the core compositional constructors (UseN, DetCN,
AdjCN, UseV, PredVP, UseCl, …), tense/polarity transport, and coordination
constructors, with coverage diagnostics against `FunctionSig.allFunctions`.
Unknown constructors still linearize deterministically via a symbolic fallback,
so coverage can grow incrementally without ever returning `∅`. The implementation
is split across the `Linearization/` subdirectory — `Types`, `Compose`, `Render`,
`Coverage`, and `Witnesses` — which has no separate README and counts under this
directory's scope.

## What's proven

- Core morphology and syntax constructors are executable and regression-checked.
- A theorem-backed example suite in `Examples.lean` covers tense, negation,
  questions, irregular verbs, transitive complements, relative clauses,
  subordination, and **garden-path disambiguation** — including the famous
  "The old man the boats" (the `ex_parse2` theorem pins the substantivized-noun
  reading "the old man the boats" by `decide`).
- A **20-surface roundtrip corpus** (`RoundTripCorpus.lean`): `parse_linearize_complete`
  and `parse_sound` prove the parser sound and complete *on this corpus*
  (including the telescope/Anna NP-vs-VP attachment ambiguities) — corpus-
  restricted by design, not a claim of full English parsing.

## What's missing

- Full numeral linearization (type defined but not linearized).
- Conjunction linearization (types defined, no surface generation).
- Passive-voice morphology.
- Comparative/superlative clause-level constructions.
- Many GF RGL functions (Idiom, Extend, Construction modules) not covered.

## Formalization status

No `axiom` declarations appear in the source — a source-level grep, *not* a
per-theorem `#print axioms` audit (a theorem can still inherit a Mathlib axiom
transitively).

**Proof state.** All sixteen files (the eleven top-level files plus the five
under `Linearization/`) are `sorry`-free; the comment-stripped count is 0 (see
the footer). The example and roundtrip theorems are *kernel* checks — surface
strings are pinned by `decide`/`rfl` and the corpus soundness/completeness
results are proven, not asserted.

**Trusted base.** Nothing here uses `native_decide` — a source grep finds zero
occurrences in this directory, so none of these proofs enlarge the trusted base
beyond the Lean kernel.

Reproduce from this directory (the per-file counts in the footer are the
authoritative comment-stripped figures; the regex below is a raw scan):

```bash
# sorry/admit occurrences (raw; prints nothing here):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Aarne Ranta, [*Grammatical Framework: A Type-Theoretical Grammar Formalism*](https://doi.org/10.1017/S0956796803004738), Journal of Functional Programming 14(2):145–189 (2004) — the abstract/concrete (linearization) separation this English grammar instantiates.
- Aarne Ranta, [*Grammatical Framework: Programming with Multilingual Grammars*](https://www.grammaticalframework.org/gf-book/) (CSLI Publications, Stanford, 2011) — the multilingual-grammar reference.
- GF Resource Grammar Library — [English concrete syntax](https://github.com/GrammaticalFramework/gf-rgl/tree/master/src/english) (`ResEng.gf`, `SentenceEng.gf`, `RelativeEng.gf`, the source ported here).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 16 .lean files, 0 with sorries.*
