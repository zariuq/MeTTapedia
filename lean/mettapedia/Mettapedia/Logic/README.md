# Probabilistic Logic Networks (PLN) in Lean 4

## What this is about

Classical logic asks whether a statement is *true*. Real reasoning — a scientist weighing
evidence, an agent acting on incomplete information — needs more: *how strongly* do I
believe it, and *how much evidence* is that belief based on? **Probabilistic Logic Networks
(PLN)** answer this by attaching to every statement a truth value carrying both a *strength*
and a *confidence*, and giving inference rules (deduction, induction, abduction, revision)
that combine such values as evidence accumulates. `Mettapedia/Logic` is the Lean
formalization of PLN, together with the surrounding logic it connects to.

The organizing discovery of this directory is that PLN's evidence-counting truth values are
not an ad-hoc gadget: the *same* `(positive, negative)` evidence object can be read
simultaneously as

- a point of a **quantale** (an ordered algebra with a tensor product) — this is what makes
  PLN's chaining rules associative and monotone;
- a valuation in a **Heyting frame** — so PLN strictly generalizes intuitionistic truth
  rather than collapsing to Boolean true/false;
- a **Beta statistic** — the conjugate-prior summary of a sequence of binary trials;
- and the **collapse of an exchangeable binary Solomonoff mixture** — tying PLN to universal
  prediction (de Finetti's theorem says exchangeable beliefs *are* a mixture over evidence
  frequencies).

Building all four views and the bridges between them in Lean turns "PLN unifies these
frameworks" from a slogan into checked theorems. On top of that core sit first-order and
fuzzy quantifiers, Bayesian-network inference, deontic/governance reasoning, a PLN↔NARS
comparison, and a work-in-progress universal-hyperprior lane for second-order uncertainty.

Most of this directory's files sit directly under `Logic/`; several focused sub-areas have
their own READMEs (linked below).

## Map

| Area | Where | Status |
|------|-------|--------|
| Core PLN inference rules | top-level `PLN*.lean` | sorry-free |
| Weight / confidence | `PLNConfidenceWeight.lean`, … | sorry-free |
| Bounds / consistency | `PLNFrechetBounds.lean`, … | sorry-free |
| Algebraic structure (quantale/Heyting) | `EvidenceQuantale.lean`, `HeytingValuationOnEvidence.lean`, `PLNQuantaleSemantics/` | sorry-free |
| Solomonoff / exchangeability | `SolomonoffExchangeable.lean`, `DeFinetti.lean` | sorry-free |
| First-order & fuzzy quantifiers | `PLNFirstOrder/` (own README) | sorry-free |
| Logic programming | `LP/`, `Prolog/` (own READMEs) | sorry-free |
| Governance / deontic | `GovernanceReasoning/`, `DDLPlus/` | sorry-free |
| Concept ontology / Mizar benchmark | `ConceptOntology/` | sorry-free (uses `native_decide`, see below) |
| Universal prediction (Hutter Ch 2–3) | `UniversalPrediction/` (own README) | sorry-free |
| Bayesian-network inference | `PLNBayesNetInference.lean`, `PLN*BNLocalMarkov*.lean` | sorry-free |
| Higher-order / measure-theoretic PLN | `HigherOrder/`, `MeasureTheoreticPLN/` | sorry-free |
| **Universal hyperprior (2nd-order uncertainty)** | `UniversalHyperprior/` + `UniversalHyperprior.lean` | **work in progress — open sorries** |

Other subdirectories: `Archive/` (frozen — do not build on), `BDD/`, `Bridges/`,
`Comparison/` (3), `Convergence/` (4), `HOL/`, `Metaphysics/`, `StratifiedPLN/`.

## The unification thesis

PLN evidence `(n⁺, n⁻)` flows through all four readings:

```
PLN Evidence (n⁺, n⁻)
  → Quantale (tensor / chaining)
  → Heyting frame (intuitionistic valuation)
  → Beta statistic (conjugate summary)
  → Solomonoff exchangeable binary collapse (de Finetti)
```

Anchor theorems (files all verified present):

| Result | File |
|--------|------|
| Fréchet bounds / PLN consistency | `PLNFrechetBounds.lean` |
| Weight-space minimization | `PLNConfidenceWeight.lean` |
| Evidence is not Boolean | `HeytingValuationOnEvidence.lean` |
| Quantale transitivity | `EvidenceQuantale.lean` |
| Solomonoff collapse | `SolomonoffExchangeable.lean` |
| De Finetti | `DeFinetti.lean` |

The PLN evidence object is further shown to recover **Naive Bayes**
(`PLN_tensorStrength_eq_nbPosterior`, in `PLNBayesNetInference.lean`) and **k-NN relevance**
(`PLN_hplusPos_eq_knnRelevance`, in `PremiseSelectionKNN_PLNBridge.lean`), and a
consolidated **PLN↔NARS** comparison lives in `PLNNARSRuleCorrespondence.lean`.

## Chapter regressions (one-command build targets)

Several book chapters are tracked by dedicated regression targets with positive *and*
negative ("canary") fixtures, so a semantic regression fails the build. From the project
root (`Mettapedia/lean/mettapedia`):

```bash
# Ch 11 — quantifier / fuzzy / ITV bridges
lake build Mettapedia.Logic.PLNFirstOrder.QuantifierRegression
# Ch 12 — intensional inheritance
lake build Mettapedia.Logic.PLNIntensionalRegression
# Ch 13 — inference control (premise selection)
lake build Mettapedia.Logic.PLNInferenceControlRegression
# Ch 8 — neighborhood consequence + categorical endpoints
lake build Mettapedia.Logic.PLNWorldModelNeighborhoodConsequence \
             Mettapedia.Logic.PLNWorldModelCategoricalRegression
# Ch 9 — Bayesian-network positive path
lake build Mettapedia.Logic.PLNSelectorRewriteThresholdRegression
```

Matching shell checkers live under `scripts/` (`check_ch11_quantifiers.sh`,
`check_ch12_intensional.sh`, `check_ch13_inference_control.sh`,
`check_ch8_neighborhood.sh`, `check_ch9_positive.sh`).

## Open-map bridge

PLN's bisimulation/observation bridges connect to the generalized-open-map machinery in
`../CategoryTheory/GeneralizedOpenMaps.lean`:

- `WeightedOpenMaps.lean` — `weightedBisim_iff_gopen_span`
- `OSLFOpenMapBridge.lean` — `pathBisim_implies_bisimilar`, `fullOpenWitness_implies_obsEq`,
  `fullOpenWitness_not_distinguished`
- `OpenMapBridgeRegression.lean` — regression checks for the above
- π/ρ side: `../Languages/ProcessCalculi/PiCalculus/WeakBisimOpenMapBridge.lean`
  (`weakRestrictedBisim_iff_pathBisim`)

## Formalization status

This README's **own scope** (files whose nearest-ancestor README is `Logic/` — i.e.
everything except the `LP/`, `Prolog/`, `PLNFirstOrder/`, `GovernanceReasoning/`, and
`UniversalPrediction/` sub-trees, which have their own READMEs) is **668 `.lean` files**.
Of these, **5 files carry open `sorry`s, all in the work-in-progress `UniversalHyperprior/`
lane** (a Normal-Normal universal-hyperprior development whose computability and dyadic
real-arithmetic obligations are not yet discharged); every other lane is `sorry`-free. There
are no source-level `axiom` declarations in this scope (a source grep, *not* a per-theorem
`#print axioms` audit, so a theorem can still inherit a standard Mathlib axiom transitively).

**Trusted base — `native_decide`.** `ConceptOntology/MizarBenchmarkEndpoint.lean` uses
`native_decide` for **7** finite-cardinality / sum-counting fixtures (e.g.
`Fintype.card MizarFamilyPilotArticle = 13`). `native_decide` compile-evaluates rather than
kernel-checks, so it trusts the Lean compiler and enlarges the trusted base; these are
flagged for migration to kernel `decide`. No other file in this scope uses it.

Reproduce from this directory — the `sorry` regex is a *raw* scan that also matches prose in
comments/strings, so the footer's per-file figures are the authoritative comment-stripped
counts (every real hit is under `UniversalHyperprior/`):

```bash
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .   # prints nothing
rg -n --glob '*.lean' 'native_decide' .                 # ConceptOntology/MizarBenchmarkEndpoint.lean
```

Recursively (including the sub-README sub-trees) the whole `Mettapedia/Logic` tree is
797 `.lean` files.

## References

- Ben Goertzel, Matthew Iklé, Izabela Goertzel & Ari Heljakka, [*Probabilistic Logic Networks: A Comprehensive Framework for Uncertain Inference*](https://doi.org/10.1007/978-0-387-76872-4) (Springer, 2008).
- Bruno de Finetti, "La prévision: ses lois logiques, ses sources subjectives," *Annales de l'Institut Henri Poincaré* 7 (1937); modern treatment in Olav Kallenberg, [*Probabilistic Symmetries and Invariance Principles*](https://doi.org/10.1007/0-387-28861-9) (Springer, 2005).
- Ray Solomonoff, [*A Formal Theory of Inductive Inference*](https://doi.org/10.1016/S0019-9958(64)90223-2), Information and Control 7 (1964) — the universal-prediction connection.
- Jasmin Blanchette, Cezary Kaliszyk, Lawrence Paulson & Josef Urban, [*Hammering towards QED*](https://doi.org/10.6092/issn.1972-5787/4593), Journal of Formalized Reasoning 9(1) (2016) — premise selection, cited by the inference-control lane.
- Jan Jakubův et al., [*MizAR 60 for Mizar 50*](https://doi.org/10.4230/LIPIcs.ITP.2023.19), ITP 2023 — the Mizar benchmark referenced by `ConceptOntology/`.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 668 .lean files, 5 with sorries.*
- `UniversalHyperprior.lean` — 5 sorries
- `UniversalHyperprior/ApproximationBounds.lean` — 6 sorries
- `UniversalHyperprior/Computability.lean` — 12 sorries
- `UniversalHyperprior/DyadicArithmetic.lean` — 4 sorries
- `UniversalHyperprior/DyadicRealization.lean` — 1 sorry
