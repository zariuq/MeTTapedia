# Ethics

## What this is about

Ethical theories disagree about *what makes an act right* — a utilitarian counts
consequences, a virtue ethicist asks what a good character would do, a deontic
theory talks about duties and rights. A natural formal question is whether these
are really different *logics* or merely different *vocabularies* over a shared
semantic core. This directory takes the second view seriously: it gives the
competing paradigms a common semantic spine (a `Semantics`/`Theory`/`Entails`
interface) and then proves *bridge* theorems showing that, model for model, a
utilitarian sentence, a virtue-target sentence, and a moral-value sentence can be
made to **entail the same things** — so a choice point is a genuine moral dilemma
under one paradigm exactly when it is under the others.

On top of that translation framework sits the headline worked example:
**Gewirth's Principle of Generic Consistency (PGC)** — the claim that any agent
who acts for a purpose is rationally committed to granting every other purposive
agent the same generic rights to freedom and well-being. The PGC is formalized
here as a sorry-free theorem and then wired into Mettapedia's deontic-logic
(DDLPlus) and OSLF governance layers, so a result from moral philosophy becomes a
governance norm the rest of the system can use.

This is, in spirit, a Lean port and extension of the **FOET** (formal ontology of
ethical theories) semantic core, with the Gewirth lane following the
Fuenmayor-Benzmüller Isabelle/HOL formalization.

## Origin and Attribution

The Gewirth lane is a **direct port** into Lean 4 of the Isabelle/HOL
formalization by David Fuenmayor and Christoph Benzmüller:

> Fuenmayor, D. & Benzmüller, C. (2018).
> *Formalisation and Evaluation of Alan Gewirth's Proof for the Principle
> of Generic Consistency in Isabelle/HOL.*
> Archive of Formal Proofs, October 2018.
> https://isa-afp.org/entries/GewirthPGCProof.html

The original Isabelle development is at `GewirthPGCProof/` (project root).
Our Lean port follows the same proof structure, with one simplification:
the AFP/Isabelle formalization introduces 8 frame conditions as axioms
(`sem_3a`–`sem_5e`); our Lean proof needs only 3 (`sem_5a`, `sem_5b`,
`sem_5e`), dropping 5 as unnecessary (`sem_3a` av-seriality, `sem_4a` av⊆pv,
`sem_4b` pv-reflexivity, `sem_5c` ob-conjunction, `sem_5d` ob-transfer).

Note the distinction: those `sem_*` frame conditions are taken as **axioms in
the Isabelle development**; on the Lean side they are ordinary *hypotheses*
(fields of `PGCAssumptions` / `PGCInterpretation`), discharged by the caller,
not Lean `axiom` declarations — so the PGC results here are honest theorems,
not postulates (see the formalization-status note below). `GewirthTheory.lean`
proves both the minimal route (`entails_PGC_strong`) and the full AFP-aligned
route (`entails_PGC_strong_from_AFPTheory`), confirming the stronger
AFP-aligned assumptions subsume the weaker ones.

## Key Idea

The PGC is Gewirth's (1978) central theorem in moral philosophy: every
purposive agent, by virtue of acting for purposes, implicitly claims
that freedom and well-being are necessary for their action — and is
therefore rationally committed to acknowledging the same right for all
other purposive agents. In short: *Act in accord with the generic
rights of your recipients as well as yourself.*

This directory formalizes the PGC argument in Lean, proves the main
theorem (`PGC_strong`) from explicit assumptions, and bridges it to the
DDLPlus deontic logic layer and the governance norm framework.

## Modules

This directory has 16 `.lean` files in two layers: the **FOET semantic core**
(the cross-paradigm translation framework) and the **Gewirth PGC lane** built on
top of it.

### Gewirth PGC lane

| File | Contents |
|------|----------|
| `GewirthPGC.lean` | The PGC argument: modal operators (□ᴰ, □ₐ, □ₚ, ◇ₐ, ◇ₚ), `Oi` (ideal obligation), `PPA` (purposeful purposive action), `RightTo`, `PGCInterpretation`, `PGCAssumptions`; main theorem `PGC_strong`; helper `CJ_14p`; bundled wrapper `PGC_strong_ofAssumptions` |
| `GewirthBridge.lean` | Connects PGC to the rest of Mettapedia: `PGCFullFrame` → `DDLPlusFrame` → `GovFrame`; `pgc_is_governance_norm` — the PGC conclusion is a governance norm in the DDLPlus framework |
| `GewirthTheory.lean` | Theory-level presentation: `PGCAssumptionTheory`, `pgcSemantics`, `entails_PGC_strong`; AFP-aligned route `entails_PGC_strong_from_AFPTheory` matching the Carmo-Jones DDL embedding |

### FOET semantic core (cross-paradigm translation framework)

| File | Contents |
|------|----------|
| `Core.lean` | Semantic infrastructure: `Semantics`, `Entails`, `DeonticAttribute`, `MoralValueAttribute`, `ModalSentence`, `DeonticSemantics`, `ValueSemantics` (ported from `foet/Foet/EthicsCore.lean`) |
| `Theory.lean` | `Theory` operations: `map`, `EntailsUnder`, `Satisfiable`, and `entails_map_iff`-style transport lemmas across relabelings |
| `Translation.lean` | `TranslationRel`, `Translates`, `Witnessed`, and `witnessed_to_translates` — the relational-translation backbone |
| `FOETCore.lean` | Aggregator/primer for the FOET semantic spine (theory + translation infra, utility/virtue bridges, structured sentences, choice points) — the semantic core, not the full SUMO-facing FOET stack |
| `UtilitarianToValue.lean` | `utilityToMoralValue` / `moralValueToUtility` round-trip; `UtilityAssignmentSentence/Theory.toValue`, `UtilityAssignmentSemantics` |
| `VirtueToValue.lean` | `VirtueAspect`, virtue↔moral-value round-trip, `VirtueDesireSentence`/`VirtueTargetSentence`, virtue theories |
| `UtilitarianToVirtue.lean` | `toVirtueTarget` translation and `entails_utilitarian_iff_entails_virtueTarget` (utilitarian ⇔ virtue-target entailment) |
| `ChoicePoint.lean` | `ChoicePoint` and the four dilemma notions (value/deontic/utilitarian/virtue-target) with their equivalence lemmas (`deonticMoralDilemma_iff_valueMoralDilemma`, etc.) |
| `StructuredSentence.lean` | `StructuredSentence` inductive, `map`/`Sat`/`semantics`, and `relLift`/`witnessedLift` plus `sat_map_iff` transport |
| `StructuredParadigms.lean` | Structured imperative↔value atoms and `entails_structuredImperative_iff_entails_structuredValue` |
| `CredalValueAttributionCaseTable.lean` | Reusable case-table interface for moral-value attribution over the credal concept-formation surface |
| `CredalValueAttributionExample.lean` | Small worked example: lenient vs strict acceptance gates yield one stable attribution and one genuinely ambiguous one |
| `Dignity.lean` | Placeholder only — no formal dignity theory is exported yet (earlier toy `True`/`False` definitions were deliberately removed as over-signaling); reserved for a future nontrivial formalization |

## Key Results

- **`PGC_strong`**: from the PGC assumptions (`sem_5ab`, `CJ_14p`, `PPA`,
  `RightTo` instantiation, and the DDLPlus frame conditions), every
  purposive agent is ideally obligated to respect the generic rights of
  all other purposive agents. Zero sorry.
- **`pgc_is_governance_norm`**: the PGC conclusion holds as a
  governance norm in the DDLPlus/`GovFrame` framework — connecting
  moral philosophy directly to the OSLF governance layer.
- **`entails_PGC_strong`**: semantic entailment: any model satisfying
  the PGC assumption theory satisfies `PGC_strong`.
- **`entails_PGC_strong_from_AFPTheory`**: AFP-aligned route using the
  full CJDDLplus frame conditions, compatible with the Isabelle companion.

Cross-paradigm bridges in the FOET core:

- **`entails_utilitarian_iff_entails_virtueTarget`** and
  **`entails_structuredImperative_iff_entails_structuredValue`**: a utilitarian
  theory entails a sentence exactly when its virtue-target (resp. structured
  value) translation entails the translated sentence — the formal sense in which
  the paradigms agree model-for-model.
- **`*MoralDilemma_iff_valueMoralDilemma`** (`deontic`, `utilitarian`,
  `virtueTarget`): a choice point is a moral dilemma under one paradigm iff it is
  under the value paradigm.

## Formalization status

All 16 `.lean` files in this directory are `sorry`-free and `admit`-free. There
are **no source-level `axiom` declarations** in our Lean — a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a Mathlib axiom
(typically `propext`, `Classical.choice`, `Quot.sound`) transitively. The Gewirth
frame conditions `sem_*` are Lean *hypotheses* (structure fields), not Lean
`axiom`s; the only place "8 frame axioms" appears is in the description of the
external Isabelle/HOL companion (above), where they genuinely are axioms.

**Trusted base.** There is **no `native_decide` anywhere in this directory**, so
nothing here compile-evaluates in place of kernel checking; nothing in this lane
enlarges the trusted base beyond Mathlib's own.

Reproduce from this directory (all three print nothing; the comment-stripped
footer counts are authoritative):

```bash
# sorry/admit occurrences:
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations:
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*(noncomputable\s+)?axiom\s' .
# native_decide occurrences:
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Alan Gewirth, [*Reason and Morality*](https://press.uchicago.edu/ucp/books/book/chicago/R/bo3618471.html)
  (University of Chicago Press, 1978) — the source of the PGC.
- David Fuenmayor & Christoph Benzmüller, [*Formalisation and Evaluation of Alan
  Gewirth's Proof for the Principle of Generic Consistency in
  Isabelle/HOL*](https://www.isa-afp.org/entries/GewirthPGCProof.html) (Archive of
  Formal Proofs, October 2018) — the Isabelle/HOL formalization this lane ports.
- David Fuenmayor & Christoph Benzmüller, [*Harnessing Higher-Order (Meta-)Logic
  to Represent and Reason with Complex Ethical Theories*](https://arxiv.org/abs/1903.09818)
  (arXiv:1903.09818, 2019) — the methodology behind the shallow semantic embedding.
- José Carmo & Andrew J. I. Jones, ["Deontic Logic and
  Contrary-to-Duties"](https://doi.org/10.1007/978-94-010-0387-2_4), in *Handbook
  of Philosophical Logic*, vol. 8 (Kluwer/Springer, 2002), pp. 265-343 — the
  Carmo-Jones DDL the DDLPlus embedding follows.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 16 .lean files, 0 with sorries.*
