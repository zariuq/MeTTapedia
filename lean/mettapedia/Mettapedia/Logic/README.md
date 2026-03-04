# Mettapedia logic module

Mettapedia Logic formalizes probabilistic logic networks with theorem-level bridges.
The module connects probability theory, Heyting semantics, quantales, and Solomonoff-style prediction.

## Overview

```
| Category | Files | Status |
|----------|-------|--------|
| Core PLN Inference | 9 | Complete |
| Weight/Confidence | 2 | Complete |
| Bounds/Consistency | 2 | Complete |
| Algebraic Structure | 8 | Complete |
| Solomonoff/Exchangeability | 6 | Complete |
| Convergence/ | 4 | Complete |
| Comparison/ | 3 | Complete |
| MeasureTheoreticPLN/ | 3 | Complete |
| PLNQuantaleSemantics/ | 4 | Complete |
| UniversalPrediction/ | 21 | WIP |
| Foundations/ | 90+ | Embedded |
| System Bridges | 4 | Complete |
```

## Semantics tree

- The semantics decision tree is `Mettapedia/Logic/SemanticsDecisionTree.lean`.

- `Mettapedia/Logic/SemanticsDecisionTree.lean`

## Generalized open-map bridge map

- The generalized-open-map core lives in `Mettapedia/CategoryTheory/GeneralizedOpenMaps.lean`.
- Weighted bridge file: `Mettapedia/Logic/WeightedOpenMaps.lean`
  - theorem: `weightedBisim_iff_gopen_span`
- OSLF bridge file: `Mettapedia/Logic/OSLFOpenMapBridge.lean`
  - theorems: `pathBisim_implies_bisimilar`, `fullOpenWitness_implies_obsEq`,
    `fullOpenWitness_not_distinguished`
- Regression file: `Mettapedia/Logic/OpenMapBridgeRegression.lean`
  - theorem checks: `weighted_equiv_regression`,
    `pathBisim_to_bisimilar_regression`,
    `fullOpenWitness_obsEq_regression`,
    `fullOpenWitness_not_distinguished_regression`
- Pi/ρ bridge location: `Mettapedia/Languages/ProcessCalculi/PiCalculus/WeakBisimOpenMapBridge.lean`
  - theorem: `weakRestrictedBisim_iff_pathBisim`

## Chapter-11 quantifier regression

- Chapter 11 quantifier regression is a one-command build target.
- Chapter 11 quantifier regression includes `check_ch11_quantifiers.sh` and `check_ch11_fuzzy_syllogism.sh`.
- Chapter 11 quantifier regression tracks primary modules for quantifier, fuzzy, and ITV bridges.
- Chapter 11 quantifier regression tracks a broad canary.

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNFirstOrder.QuantifierRegression
```

```bash
cd /home/zar/claude/lean-projects/mettapedia
./scripts/check_ch11_quantifiers.sh
./scripts/check_ch11_fuzzy_syllogism.sh
```

- `Mettapedia/Logic/PLNFirstOrder/QuantifierSemantics.lean`
- `Mettapedia/Logic/PLNFirstOrder/FuzzyQuantifierSemantics.lean`
- `Mettapedia/Logic/PLNFirstOrder/FuzzyITVBridge.lean`
- `Mettapedia/Logic/PLNFirstOrder/QuantifierCanary.lean`
- `Mettapedia/Logic/PLNFirstOrder/QuantifierWorkedExamples.lean`

## Chapter-12 intensional inheritance regression

- Chapter 12 intensional inheritance regression is a one-command build target.
- Chapter 12 intensional inheritance regression includes selector-specialized one-call final-bundle wrappers with mixed-policy non-equivalence canaries.

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNIntensionalRegression
```

```bash
cd /home/zar/claude/lean-projects/mettapedia
./scripts/check_ch12_intensional.sh
```

- `Mettapedia/Logic/PLNIntensionalWorldModel.lean`
- `Mettapedia/Logic/IntensionalInheritanceSolomonoffBridge.lean`
- `Mettapedia/Logic/PLNCanonicalAPI.lean`
- `Mettapedia/Logic/PLNIntensionalCanary.lean`
- `Mettapedia/Logic/PLNIntensionalRegression.lean`

## Chapter-13 inference-control regression

- Chapter 13 inference-control regression is a one-command build target.
- Chapter 13 inference-control regression includes selector, ranking, and coverage theorems with composed core modules and positive and negative canaries.

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNInferenceControlRegression
```

```bash
cd /home/zar/claude/lean-projects/mettapedia
./scripts/check_ch13_inference_control.sh
```

- `Mettapedia/Logic/PremiseSelectionSelectorSpec.lean`
- `Mettapedia/Logic/PremiseSelectionOptimality.lean`
- `Mettapedia/Logic/PremiseSelectionRankingStability.lean`
- `Mettapedia/Logic/PremiseSelectionCoverage.lean`
- `Mettapedia/Logic/PLNInferenceControlCore.lean`
- `Mettapedia/Logic/PLNInferenceControlCanary.lean`
- `Mettapedia/Logic/PLNInferenceControlRegression.lean`

## Chapter-8 neighborhood consequence regression

- Chapter 8 neighborhood consequence regression checks state-indexed WM consequence rules,
  neighborhood modal/deontic lifts, and governance formula translation preservation.

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNWorldModelNeighborhoodConsequence
```

```bash
cd /home/zar/claude/lean-projects/mettapedia
./scripts/check_ch8_neighborhood.sh
```

- `Mettapedia/Logic/PLNWorldModelNeighborhoodConsequence.lean`
- `scripts/check_ch8_neighborhood.sh`

## Chapter-9 positive regression

- Chapter 9 positive regression tracks the non-counterexample path:
  class-packaged BN side-condition discharge plus one-call selector→rewrite→threshold composition.

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNSelectorRewriteThresholdRegression
```

```bash
cd /home/zar/claude/lean-projects/mettapedia
./scripts/check_ch9_positive.sh
```

- `Mettapedia/Logic/PLNChainBNLocalMarkovPackage.lean`
- `Mettapedia/Logic/PLNForkBNLocalMarkovPackage.lean`
- `Mettapedia/Logic/PLNColliderBNLocalMarkovPackage.lean`
- `Mettapedia/Logic/PLNBNLocalMarkovPackages.lean`
- `Mettapedia/Logic/PLNSelectorRewriteThresholdExamples.lean`
- `Mettapedia/Logic/PLNSelectorRewriteThresholdRegression.lean`

## Unification thesis

- The unification thesis states PLN evidence unifies quantale, Heyting, and Bayesian views.
- The unification thesis states exchangeable binary Solomonoff prediction collapses to evidence counts.

```
PLN Evidence (n+, n-)
  -> Quantale (tensor)
  -> Heyting frame
  -> Beta statistic
  -> Solomonoff exchangeable binary collapse
```

## Critical proven theorem

- The critical theorem section summarizes Frechet bounds, quantale transitivity, De Finetti, and Solomonoff collapse.

```
| Theorem | File |
|---------|------|
| Frechet bounds | PLNFrechetBounds.lean |
| PLN consistency | PLNFrechetBounds.lean |
| Weight-space min | PLNConfidenceWeight.lean |
| Evidence not boolean | HeytingValuationOnEvidence.lean |
| Quantale transitivity | EvidenceQuantale.lean |
| Solomonoff collapse | SolomonoffExchangeable.lean |
| De Finetti | DeFinetti.lean |
```

## Proof for PLN covering NB and k-NN

- `PLN_tensorStrength_eq_nbPosterior` is the Naive Bayes bridge theorem.
- `PLN_hplusPos_eq_knnRelevance` is the k-NN bridge theorem.
- Premise-selection ranking transfer is a theorem family in `PremiseSelectionOptimality.lean`.
- Tier A-to-B composition is a proven spine in `PLNXiDerivedBNRules.lean`.
- Collider abduction caveat is a formalized approximation warning.
- MeTTa formula parity is tracked with theorem anchors and a checklist.

- `Mettapedia/Logic/PLNBayesNetInference.lean:296`
- `Mettapedia/Logic/PremiseSelectionKNN_PLNBridge.lean:111`
- `Mettapedia/Logic/PremiseSelectionOptimality.lean:333`
- `Mettapedia/Logic/PLNBNCompilation.lean:161`
- `Mettapedia/Logic/PLNXiDerivedBNRules.lean:464`
- `Mettapedia/Logic/PLNXiDerivedBNRules.lean:1172`
- `Mettapedia/Implementation/MettaVerification.lean:77`
- `Mettapedia/Implementation/PLNParityChecklist.lean:66`

## Proof for PLN↔NARS rule comparison

- `PLNNARSRuleCorrespondence.lean` is the consolidated PLN↔NARS comparison package.
- The PLN↔NARS package bundles confidence transforms, rule correspondences, revision coherence, and informativeness adjunction.

- `Mettapedia/Logic/PLNNARSRuleCorrespondence.lean`

## Subdirectories

- Subdirectories are cataloged with scope and file counts.

```
Comparison/ (3 files)
Convergence/ (4 files)
Foundations/ (90+ files)
MeasureTheoreticPLN/ (3 files)
PLNQuantaleSemantics/ (4 files)
UniversalPrediction/ (21 files)
```

## Index by purpose

- The file index is grouped by purpose.

```
PLN core, inference rules, weight/confidence, bounds/consistency,
algebraic structure, Solomonoff/exchangeability, system bridges,
analysis/comparison, and other files are indexed by purpose.
```

## Dependency graph

- The dependency graph section is available with bridge and submodule highlights.

```
Foundations -> Core inference -> Algebraic semantics -> Bridges
                      \-> Quantifier regression -> Chapter 11 canaries
                      \-> Intensional regression -> Chapter 12 canaries
                      \-> Inference-control regression -> Chapter 13 canaries
```

## Key insight

- The key insight distinguishes evidence-valued PLN from interval probability semantics.

### Weight-space fix

- The weight-space bug fix is documented with corrected formulas.

## Build

- The build section lists core, quantifier, and full-build commands.

```bash
cd /home/zar/claude/lean-projects/mettapedia
# Quantifier regression
lake build Mettapedia.Logic.PLNFirstOrder.QuantifierRegression
# Intensional inheritance regression
lake build Mettapedia.Logic.PLNIntensionalRegression
# Inference-control regression
lake build Mettapedia.Logic.PLNInferenceControlRegression
# Core files
lake build Mettapedia.Logic.PLNBayesNetInference Mettapedia.Logic.PremiseSelectionKNN_PLNBridge
# Build all (slow)
lake build
```

## References

- The references section lists references.

```
Blanchette et al. (2016) Hammering towards QED
Goertzel et al. Probabilistic Logic Networks
Jakubuv & Urban (2023) Mizar60
```
