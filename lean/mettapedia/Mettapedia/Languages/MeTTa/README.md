# MeTTa Language Formalization (Lean 4)

## What this is about

[MeTTa](https://metta-lang.dev/) is a *homoiconic* rewrite language: a program is
just data (atoms in an atomspace), and computation is rewriting that data by
pattern-matching against equations the program itself can read and modify. That
"code is data" character is what makes MeTTa attractive for AI — a system can
inspect and rewrite its own rules — but it also makes "what does this program
*mean*?" a genuinely subtle question, because the same atom can be a value, a
function, or a rewrite rule depending on context.

This directory pins that meaning down in Lean. The same surface language admits
several complementary readings, so it is formalized in **layers**, each with its
own notion of "running a program" and its own trust model:

- a **computable interpreter** that mirrors the reference Rust implementation
  closely enough to check conformance fixtures against it;
- a **typed metatheory** that proves the well-behavedness theorems you expect of
  a calculus (typing is preserved by reduction; reduction is confluent);
- a **Prolog-style evaluation** model that connects MeTTa rewriting to logic
  programming; and
- a full-language **OSLF instance** (the "open sub-language family" presentation
  used elsewhere in Mettapedia), kept as a state-indexed legacy view.

Because these layers describe one language, the root of this directory also holds
integration facades that wire them together into a single surface for the rest of
Mettapedia to import.

This README owns the integration layer and the small modules directly under
`MeTTa/`; the four big layers each have their own README (linked below). Counting
recursively, the whole `MeTTa/` tree is 212 `.lean` files; this README's own
scope (files whose nearest README is this one) is 54.

## Layers

| Layer | Dir | What it is |
|-------|-----|------------|
| Computable spec | `HE/` | Fuel-bounded interpreter from `interpreter.rs` + `metta.md`; 37 conformance theorems (see `HE/README.md`) |
| Pure metatheory | `Pure/` | Typed pure MeTTa; subject reduction (`Pure/SubjectReduction.lean`) and confluence (`Pure/Confluence.lean`) proven |
| Prolog evaluation | `PeTTa/` | PeTTa evaluation pipeline; LP soundness and bridge theorems |
| OSLF instance | `OSLFCore/` | Full-language OSLF `LanguageDef` (state-indexed, legacy) |

Supporting modules and data:
- `PureKernel/` — declaration kernel (inductive types as MeTTa atoms)
- `Translation/` — HE-to-PeTTa lowering and validated-surface conformance fixtures
- `SuiteBase/` — shared test-suite base
- `TensorDSL/` — tensor-operation layer
- `HEPrime/` — `Telescope.lean`, a single telescope-IR module
- `SpecProfiles/` — profile inventories as `.csv`/`.json` data (no Lean code)

Root-level modules (`RuntimeSpec.lean`, `ExecutionContract.lean`,
`ElaboratedCore.lean`, etc.) are integration facades — they wire the layers
together and export a unified surface for the rest of Mettapedia.

## Formalization status

Own scope is 54 `.lean` files with **0 `sorry`** (comment-stripped). No source-level
`axiom` declarations appear in these files — this is a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a Mathlib axiom
transitively. The core layers (`Pure/`, `PureKernel/`, and the HE metatheory) are
kernel-checked.

**Trusted base — `native_decide`.** 49 `native_decide` invocations remain in the
own-scope files, concentrated in the Translation conformance/lowering fixtures plus
a couple of profile/seed proofs. These compile-evaluate rather than kernel-check, so
they enlarge the trusted base (they trust the Lean compiler) and are flagged for
migration to kernel `decide`:

- `Translation/HEPeTTaValidatedSurface.lean` — 31
- `Translation/HEPeTTaNativeLoweringContracts.lean` — 12
- `DTTSeedProofPath.lean` — 4
- `CoreProfile.lean` — 1
- `RuntimeSpec.lean` — 1

Reproduce from this directory — note the `sorry` regex is a *raw* scan that also
matches prose in comments/strings (there is one such mention in
`Translation/HEPeTTaTranslateExamples.lean`), so the own-scope figure of 0 above is
the authoritative comment-stripped count:

```bash
# build this layer:
lake build Mettapedia.Languages.MeTTa
# sorry occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\bsorry\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (the 49 disclosed above):
rg -n --glob '*.lean' 'native_decide' .
```

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 54 .lean files, 0 with sorries.*
