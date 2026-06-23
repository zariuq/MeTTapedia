# GF Examples — Worked End-to-End Demonstrations

## What this is about

A grammar usually does two jobs at once, and **Grammatical Framework (GF)**
splits them apart. The *abstract syntax* says what a sentence *means* in a
language-independent way — "some agent performs some action on some object" —
as a typed tree. The *concrete syntax* (the *linearization*) says how that tree
is *spelled out* in a particular language, handling word order, agreement, and
morphology. The same abstract tree can be linearized to English, to Czech, or to
a logical formula; conversely a string can be *parsed* back to the tree. That
separation — meaning as a typed tree, surface form as a function of it — is what
makes GF a multilingual grammar formalism rather than a parser for one language.

This directory collects **worked examples** that run that idea end to end inside
Lean and prove the result correct at each stage. They are not the grammar
libraries themselves (those live in `../HandCrafted/` and `../`) — they are
demonstrations that exercise the libraries: take an abstract tree, push it
through linearization or through the OSLF semantic layers, and prove that the
output is exactly what the theory predicts.

Two flavours appear here:

- **Linearization demos** — start from a language-independent semantic tree and
  generate English surface text, with the morphology/agreement machinery
  actually firing (the rendered string is pinned by a `decide` proof).
- **Semantic-pipeline demos** — push GF abstract trees through the OSLF
  layers (visible-action store semantics, the ◇/□ modal layer, and the
  premise-aware logic layer), proving operational steps, store invariants, and
  the resulting evidence values.

## Modules

| File | What it demonstrates |
|------|----------------------|
| `MainReadmeGFPilot.lean` | A small pilot: a language-independent `RepoClaim` tree linearized to English via GF morphology (`linPredVP`, `complV2`, `linUseCl`, tense/agreement). Four `decide` theorems pin the rendered sentences (incl. plural agreement). |
| `AnaphoraBinding.lean` | Cross-sentential anaphora ("John walks. He sleeps.") via the visible layer V3 (referent introduction) + V4 (pronoun binding): valid `VisibleStep`s, store resolution, `functionalBind`/`uniqueRef` invariants, the ⊥→real `BinaryEvidence` transition, and base-vs-visible separation. |
| `EmbeddedScopeDemo.lean` | The grounded GF-witness demo on the real `GFCore.check` / PGF-witness lane: generated English and Czech `PaperAmbiguity` witnesses recover the same abstract trees and check to the same patterns; the syntax-only OSLF lane distinguishes VP- vs NP-attachment readings; the modal boundary is honest (`□` vacuous, no positive `◇` witness because the syntax lane has no rewrites). |
| `ModalLogicComposition.lean` | Composition of the OSLF modal layer with a Datalog logic layer: the ◇ ⊣ □ Galois connection (`langGaloisUsing`) is parametric in the `RelationEnv`, so premise-aware reductions still form a Galois pair; monotonicity, unit/counit, scope-ordering lift, and a GF instantiation. |
| `MainReadmeCompositional.lean` | Compatibility shim — `export`s from the canonical `Mettapedia.DocText.MainReadmeCompositional`. |
| `GFReadmeCompositional.lean` | Compatibility shim — `export`s from `Mettapedia.DocText.GFReadmeCompositional`. |
| `OSLFReadmeCompositional.lean` | Compatibility shim — `export`s from `Mettapedia.DocText.OSLFReadmeCompositional`. |
| `ReadmeGFHelpers.lean` | Compatibility shim — `export`s linearization helpers from `Mettapedia.DocText.ReadmeGFHelpers`. |
| `ReadmeTree.lean` | Compatibility shim — `export`s `ReadmeBlock`/`renderDoc` from `Mettapedia.DocText.ReadmeTree`. |

The five `*Compositional`/`Readme*` shims preserve the old
`Mettapedia.Languages.GF.Examples.*` import paths; the live definitions moved to
`Mettapedia/DocText/`. They contain no proofs of their own — only `export`
re-exports — so the substantive content here is the four demonstration files.

### What is actually proven

- `MainReadmeGFPilot.lean`: the generated English for each `RepoClaim` equals the
  intended sentence, by kernel `decide` — so the morphology/agreement path really
  produces those strings, it is not asserted.
- `AnaphoraBinding.lean`: every stage — the two `VisibleStep`s, store resolution,
  both store invariants at each state, the ⊥→real evidence transition, and the
  two base-separation facts — has a corresponding theorem, with no proof gaps.
- `EmbeddedScopeDemo.lean`: English/Czech tree recovery agreement, the four
  attachment-distinction facts, and the modal boundary are all proven on the real
  `GFCore.check`/PGF-witness lane (no authored semantics smuggled in).
- `ModalLogicComposition.lean`: the Galois connection and its consequences hold
  for *any* `RelationEnv`, so the logic layer composes with the modal layer
  without breaking the adjunction.

## Formalization status

No `axiom` declarations appear in the source — a source-level grep, *not* a
per-theorem `#print axioms` audit (a theorem can still inherit a Mathlib axiom
transitively).

**Proof state.** All nine files are `sorry`-free. The two raw matches for the
word `sorry` in `MainReadmeGFPilot.lean` are *string literals* inside example
sentences (`"... use \`rg \"sorry\"\` in relevant code folders"`), not proof
stubs; the comment-stripped count is 0 across the directory (see the footer).

**Trusted base.** Nothing here uses `native_decide` — a source grep finds zero
occurrences in this directory. The linearization theorems in
`MainReadmeGFPilot.lean` are closed by kernel-checked `decide`, so they do not
enlarge the trusted base.

Reproduce from this directory — note the `sorry`/`admit` regex is a *raw* scan
that also matches the string-literal mentions above, so the comment-stripped
footer count is the authoritative figure:

```bash
# sorry/admit occurrences (raw — also matches the "sorry" string literals):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Aarne Ranta, [*Grammatical Framework: A Type-Theoretical Grammar Formalism*](https://doi.org/10.1017/S0956796803004738), Journal of Functional Programming 14(2):145–189 (2004) — the abstract-syntax / concrete-syntax (linearization) separation that these examples exercise.
- Aarne Ranta, [*Grammatical Framework: Programming with Multilingual Grammars*](https://www.grammaticalframework.org/gf-book/) (CSLI Publications, Stanford, 2011) — the book-length treatment of multilingual GF grammars.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 9 .lean files, 0 with sorries.*
