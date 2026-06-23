# Czech Morphology Engine (GF, Lean 4)

## What this is about

In **Grammatical Framework (GF)** a grammar is split into an *abstract syntax*
(the language-independent meaning, as a typed tree) and a *concrete syntax* (how
that tree is spelled out in one particular language). For a richly inflected
language like Czech, most of the work of the concrete syntax is *morphology*: a
single noun has up to fourteen surface forms (7 cases × 2 numbers), a verb
changes for person and number, and an adjective agrees with its noun in gender,
number, and case. This directory is the Lean 4 formalization of that Czech
*morphological* layer — the inflection tables and the agreement rules — ported
from the GF Resource Grammar Library (`ResCze.gf`, `ParadigmsCze.gf`,
`MorphoCze.gf`).

A recurring theme is **syncretism**: the *compression paradox* that, although a
Czech noun has fourteen theoretical case/number slots, heavy form-sharing means
most paradigms realize fewer than ten *distinct* strings. The proofs here pin
those distinct-form counts exactly, so a change that broke the inflection rules
could not slip through unnoticed.

**This is a morphology engine, not a complete Czech grammar.** It covers
declension, conjugation, and agreement; it does *not* implement full Czech
clause construction. Sentence-/VP-level linearization is partial compared to the
English formalization in `../English/` (see *What's missing* below).

## Coverage

### Nouns — `Declensions.lean`, `Morphology.lean`
Fourteen declension paradigms (`declPAN` … `declSTAVENI`) covering the standard
Czech noun classes:

- Masculine animate: PAN, MUZ, PREDSEDA, SOUDCE
- Masculine inanimate: HRAD, STROJ
- Feminine: ZENA, RUZE, PISEN, KOST
- Neuter: MESTO, KURE, MORE, STAVENI

`Morphology.lean` defines the parameters: 7 cases (Nom/Gen/Dat/Acc/Voc/Loc/Ins),
2 numbers, and the gender system. Each paradigm fills the 7 × 2 = 14-slot table;
distinct-form counts are proven by `decide`.

### Verbs — `Verbs.lean`
A `VerbForms` record with 10 named fields (infinitive; present 1/2/3 sg and pl;
past participle sg/pl; negative present 3sg). Covers the copula `být`, `mít`, and
the productive `-ovat` conjugation class.

### Adjectives — `Adjectives.lean`
Five paradigm types — `mladý` (hard), `jarní` (soft), `otcův` (masc. possessive),
`matčin` (fem. possessive), and invariable. 15 named slots are mapped onto the
full Gender × Number × Case table (56 theoretical combinations collapsed by
syncretism).

### Pronouns — `Pronouns.lean`
Personal pronouns (já/ty/on/ona/ono/my/vy/oni), possessive paradigms
(můj/tvůj/náš/váš/její/jeho/jejich), reflexive possessive (svůj), demonstratives
(ten/ta/to), and the interrogatives kdo/co — with full, clitic, and
prepositional case variants.

### Numerals — `Numerals.lean`
`jeden`, `dva`, `tři`, `čtyři` with full case declension, the 5+ (`Num5`)
pattern that forces the governed noun into the genitive plural, and the
invariable higher numerals.

### Agreement — `Agreement.lean`
The `NumSize`-based case/number selection governing numeral–noun agreement
(Num1 → singular; Num2_4 → plural; Num5 → Nom/Acc redirected to genitive plural).

### Linearization (partial) — `Linearization.lean`
Maps GF abstract categories (CN, NP, Det, VP, S) to Czech concrete types and
proves that abstract equivalence implies linguistic equivalence. Sentence-level
coverage is intentionally partial.

## What's proven

- **Exact distinct-form counts** for all fourteen declension paradigms
  (`Properties.lean`, e.g. `pán_exact_forms : countDistinctForms pán = 10`),
  plus universal syncretism invariants and constructor-coherence checks — each a
  correctness certificate that a broken implementation could not satisfy.
- **String-level regression tests** for the PAN paradigm — every case/number
  slot of the full 7 × 2 table pinned by `decide` (`Tests.lean`).
- An **18-entry roundtrip corpus** (`RoundTripCorpus.lean`): parsing is proved
  sound and complete *on this corpus* of theorem-backed surfaces — corpus-
  restricted by design, not a claim of full Czech parsing.

## What's missing

- Full clause construction (a `SentenceCze.gf` equivalent) — not formalized.
- Verbal aspect pairs — not modeled.
- Sentence-level Czech linearization comparable to the English layer.
- Numeral–noun agreement beyond the basic `NumSize` patterns.

`Tests.lean` also documents two known irregular-stem gaps in the regular
paradigms (e.g. `pes` genitive, `okno` genitive plural) — honest TODOs, not
claimed as covered.

## Formalization status

No `axiom` declarations appear in the source — a source-level grep, *not* a
per-theorem `#print axioms` audit (a theorem can still inherit a Mathlib axiom
transitively).

**Proof state.** All twelve files are `sorry`-free (the comment-stripped count is
0; see the footer). The correctness theorems are *kernel* checks: form counts and
string-equality regressions are closed by `decide`, `rfl`, or explicit lemmas.

**Trusted base.** Nothing here uses `native_decide` — a source grep finds zero
occurrences in this directory, so the morphology proofs do not enlarge the
trusted base beyond the Lean kernel.

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

- Aarne Ranta, [*Grammatical Framework: A Type-Theoretical Grammar Formalism*](https://doi.org/10.1017/S0956796803004738), Journal of Functional Programming 14(2):145–189 (2004) — the abstract/concrete (linearization) separation this engine instantiates for Czech.
- Aarne Ranta, [*Grammatical Framework: Programming with Multilingual Grammars*](https://www.grammaticalframework.org/gf-book/) (CSLI Publications, Stanford, 2011) — the multilingual-grammar reference.
- GF Resource Grammar Library — [Czech concrete syntax](https://github.com/GrammaticalFramework/gf-rgl/tree/master/src/czech) (`ResCze.gf`, the source ported here).
- J. Naughton, *Czech: An Essential Grammar* (Routledge, 2005) — the linguistic reference cited in the paradigm docstrings.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 12 .lean files, 0 with sorries.*
