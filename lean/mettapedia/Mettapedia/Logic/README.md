# Mettapedia Logic Module

Formalizing probabilistic logic networks (PLN) and their connections to
probability theory, imprecise probability, Heyting algebras, quantales, and Solomonoff induction.

## Module Overview

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
| Foundations/ | 90+ | Embedded (separate project) |
| System Bridges | 4 | Complete |
| Other/Misc | 8+ | Various |

**Total**: 49 top-level files + 6 subdirectories

---

## The Unification Thesis

PLN Evidence `(n+, n-)` unifies multiple mathematical frameworks:

```
                     PLN Evidence (n+, n-)
                            |
       +--------------------+--------------------+
       |                    |                    |
       v                    v                    v
   Quantale            Heyting Frame       Beta Statistic
   (tensor x)         (non-Boolean)        (conjugacy)
       |                    |                    |
       v                    v                    v
  PLN Deduction        Bounds [L, U]       Bayesian Update
  A->B, B->C => A->C   with gap            (hplus = add params)
       |                    |                    |
       +--------------------+--------------------+
                            |
                            v
              +-----------------------------+
              | Solomonoff on Exchangeable  |
              | Binary = Evidence (n+, n-)  |
              +-----------------------------+
```

**Key Insight**: Restricted Solomonoff prediction on exchangeable binary sequences
collapses to PLN Evidence counts!

---

## Critical Proven Theorems

| Theorem | File | Statement |
|---------|------|-----------|
| Frechet Upper | `PLNFrechetBounds.lean` | P(A n B) <= min(P(A), P(B)) |
| Frechet Lower | `PLNFrechetBounds.lean` | max(0, P(A)+P(B)-1) <= P(A n B) |
| PLN Consistency | `PLNFrechetBounds.lean` | Consistency <-> Frechet bounds |
| Weight-Space Min | `PLNConfidenceWeight.lean` | min in weight space, NOT confidence |
| Evidence Not Boolean | `HeytingValuationOnEvidence.lean` | a v ~a != T for some a |
| Quantale Transitivity | `EvidenceQuantale.lean` | (A->B) x (B->C) <= (A->C) |
| Solomonoff Collapse | `SolomonoffExchangeable.lean` | Exchangeable -> depends on counts only |
| De Finetti | `DeFinetti.lean` | Exchangeable <-> Bernoulli mixture |

---

## Subdirectories

### Comparison/ (3 files)
Error analysis and optimality comparisons between PLN variants.
- `ErrorCharacterization.lean` - Error analysis between fast/complete PLN
- `OptimalityTheorems.lean` - Optimality results
- `StructuralAdvantages.lean` - Structural advantages of PLN

### Convergence/ (4 files)
Probabilistic convergence theory for PLN evidence semantics.
- `ConfidenceConvergence.lean` - Confidence converges with evidence
- `IIDBernoulli.lean` - IID Bernoulli convergence properties
- `LawOfLargeNumbers.lean` - LLN for Evidence
- `RateOfConvergence.lean` - Asymptotic rates

### Foundations/ (90+ files) - EMBEDDED SEPARATE PROJECT
Self-contained formal logic library with its own README, CLAUDE.md, LICENSE.
Covers propositional, first-order, modal, and provability logic.
**Note**: This is NOT part of PLN formalization proper.

### MeasureTheoreticPLN/ (3 files)
Bridge between PLN and measure theory.
- `Basic.lean` - Measure-theoretic foundations
- `BetaMeasure.lean` - Beta measure connection
- `EvidenceSemantics.lean` - Measure semantics of Evidence

### PLNQuantaleSemantics/ (4 files)
Quantale-valued semantics and soundness framework.
- `CDLogic.lean` - Conditional Doxastic Logic
- `PBit.lean` - Probabilistic bit
- `PLNModel.lean` - Model theory for PLN
- `Soundness.lean` - Soundness proofs

### UniversalPrediction/ (21 files)
Formalization of Hutter's Universal AI (AIXI) prediction theory.
Largest subdirectory (~420 KB). Includes:
- Entropy, distances, chain rule
- Convergence criteria and error bounds
- Hutter enumeration theorems
- Beta/Dirichlet predictors
- Thompson sampling
- Solomonoff bridge

---

## File Index by Purpose

### PLN Core Foundation

| File | Description | Sorries |
|------|-------------|---------|
| `EvidenceQuantale.lean` | Evidence structure (n+, n-), quantale ops (x, +) | 0 |

### PLN Inference Rules

| File | Description | Sorries |
|------|-------------|---------|
| `PLNDeduction.lean` | Deduction: A->B, B->C => A->C | 0 |
| `PLNDerivation.lean` | Induction, abduction, Bayes inversion | 0 |
| `PLNInferenceRules.lean` | Similarity, modus ponens/tollens | 0 |
| `PLNConjunction.lean` | Hypergeometric distribution, mode bounds | 0 |
| `PLNDisjunction.lean` | De Morgan, inclusion-exclusion | 0 |
| `PLNNegation.lean` | Evidence swap (n+, n-) -> (n-, n+) | 0 |
| `PLNRevision.lean` | Evidence aggregation = hplus | 0 |
| `PLNImplicantConjunction.lean` | A->C, B->C => (A^B)->C | 0 |

### Weight-Space and Confidence

| File | Description | Sorries |
|------|-------------|---------|
| `PLNConfidenceWeight.lean` | **CRITICAL**: min in weight space, not confidence | 0 |
| `ConfidenceCompoundingTheorem.lean` | Confidence propagation | 0 |

### Bounds and Consistency

| File | Description | Sorries |
|------|-------------|---------|
| `PLNFrechetBounds.lean` | Frechet bounds <-> PLN consistency | 0 |
| `EvidenceIntervalBounds.lean` | Strength intervals, incomparability | 0 |

### Algebraic Structure

| File | Description | Sorries |
|------|-------------|---------|
| `EvidenceQuantale.lean` | Commutative quantale instance | 0 |
| `HeytingValuationOnEvidence.lean` | Non-Boolean, credal sets | 0 |
| `EvidenceBeta.lean` | Beta distribution connection | 0 |
| `EvidenceDirichlet.lean` | Dirichlet-Multinomial generalization | 0 |
| `EvidenceKSBridge.lean` | Knuth-Skilling plausibility space | 0 |
| `EvidenceSTVBijection.lean` | Truth value bijection | 0 |
| `EvidenceIntuitionisticProbability.lean` | Intuitionistic semantics | 0 |
| `ResidualDeductionFormula.lean` | Residuation in quantale | 0 |

### Solomonoff and Exchangeability

| File | Description | Sorries |
|------|-------------|---------|
| `SolomonoffExchangeable.lean` | Solomonoff -> Evidence collapse | 0 |
| `Exchangeability.lean` | Exchangeable sequences, count sufficiency | 0 |
| `DeFinetti.lean` | De Finetti representation theorem | 0 |
| `SolomonoffPrior.lean` | Solomonoff prior formalization | 0 |
| `SolomonoffMeasure.lean` | Measure-theoretic Solomonoff | 0 |
| `SolomonoffInduction.lean` | Solomonoff induction analysis | 0 |

### System Bridges

| File | Description | Sorries |
|------|-------------|---------|
| `NuEvidenceQuantaleBridge.lean` | nuPLN <-> Evidence quantale | 0 |
| `NARSEvidenceBridge.lean` | NARS <-> Evidence bridge | 0 |
| `PLN_KS_Bridge.lean` | PLN <-> Knuth-Skilling bridge | 0 |
| `EvidenceKSBridge.lean` | Evidence as PlausibilitySpace | 0 |

### Analysis and Comparison

| File | Description | Sorries |
|------|-------------|---------|
| `PLNBugAnalysis.lean` | Historical bug analysis | 0 |
| `CompletePLN.lean` | Exact Bayesian inference in logical form | 0 |
| `SoundnessCompleteness.lean` | Soundness/completeness analysis | 0 |

### Other Files

| File | Description | Sorries |
|------|-------------|---------|
| `PLNDistributional.lean` | Distributional properties | -- |
| `PLNTemporal.lean` | Temporal PLN (skeleton) | -- |
| `PLNEnrichedCategory.lean` | Enriched category structure | -- |
| `PLNQuantaleConnection.lean` | Quantale connection | -- |
| `PLNQuantaleSemantics.lean` | Semantic re-export | -- |
| `PLNConsistencyLemmas.lean` | Consistency helpers | -- |
| `PLNDeductionComposition.lean` | Deduction composition | -- |
| `PLNDerivedFromEvidence.lean` | Derivation from Evidence | -- |
| `PLNMettaTruthFunctions.lean` | MeTTa truth formulas | -- |
| `NARSMettaTruthFunctions.lean` | NARS truth formulas | -- |
| `TemporalQuantale.lean` | Temporal quantale structures | -- |
| `MarkovExchangeability.lean` | Markov chain exchangeability | -- |
| `MomentSequences.lean` | Completely monotone sequences | -- |
| `HausdorffMoment.lean` | Hausdorff moment problem (81 KB) | -- |
| `IntensionalInheritance.lean` | Information-theoretic unification (POC) | -- |
| `UniversalPrediction.lean` | Re-export for UniversalPrediction/ | -- |

---

## Dependency Graph

```
EvidenceQuantale.lean (Foundation: Evidence structure, quantale ops)
       |
       +-- EvidenceQuantale.lean (quantale instance)
       |        +-- evidence_tensor_transitivity
       |
       +-- HeytingValuationOnEvidence.lean (Heyting, non-Boolean)
       |        +-- evidence_not_boolean
       |        +-- credalGap_singleton
       |
       +-- EvidenceBeta.lean (Beta conjugacy)
       |        +-- EvidenceDirichlet.lean (k-ary generalization)
       |
       +-- PLNDeduction.lean (core deduction rule)
       |        +-- PLNDerivation.lean (induction, abduction, Bayes)
       |                 +-- PLNInferenceRules.lean (similarity, modus ponens)
       |
       +-- PLNConjunction.lean (hypergeometric)
       |        +-- PLNConfidenceWeight.lean (weight-space operations)
       |        +-- PLNDisjunction.lean (De Morgan)
       |
       +-- PLNNegation.lean (evidence swap)
       +-- PLNRevision.lean (= hplus)
       +-- PLNImplicantConjunction.lean (A->C, B->C => A^B->C)
       |
       +-- PLNFrechetBounds.lean (Frechet <-> consistency)
       +-- EvidenceIntervalBounds.lean (strength intervals)
       |
       +-- Exchangeability.lean (count sufficiency)
                +-- SolomonoffExchangeable.lean (Solomonoff collapse)
                +-- DeFinetti.lean (representation theorem)
```

---

## Key Insight: PLN Evidence vs Interval Probability

PLN Evidence `(n+, n-)` is **richer** than interval probabilities:

| Interval Probability | PLN Evidence |
|---------------------|--------------|
| Bounds [a, b] | Actual counts (n+, n-) |
| "What we know" | "How we know it" |
| Point in [0,1]^2 | Extra dimension: weight |

The extra dimension (total count = weight) enables:
1. **Confidence**: Higher weight -> higher confidence
2. **Correct inference**: min/max in **weight space**, not confidence space!
3. **Beta conjugacy**: Evidence = sufficient statistic for Beta posterior

### The Weight-Space Bug Fix

**WRONG** (causes 10-50% underestimation):
```
w2c(min(c1, c2))  -- treats confidences as weights
```

**CORRECT**:
```
w2c(min(c2w(c1), c2w(c2)))  -- converts to weight space first
```

This is formalized in `PLNConfidenceWeight.lean`.

---

## Build

```bash
cd lean-projects/mettapedia

# Core files
lake build Mettapedia.Logic.EvidenceQuantale
lake build Mettapedia.Logic.PLNDeduction
lake build Mettapedia.Logic.PLNFrechetBounds
lake build Mettapedia.Logic.EvidenceQuantale

# New files
lake build Mettapedia.Logic.PLNConfidenceWeight
lake build Mettapedia.Logic.PLNConjunction
lake build Mettapedia.Logic.SolomonoffExchangeable
lake build Mettapedia.Logic.DeFinetti

# Build all (slow)
export LAKE_JOBS=3 && nice -n 19 lake build Mettapedia.Logic
```

---

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- Goertzel et al., "Probabilistic Logic Networks" (2008)
- Knuth & Skilling, "Foundations of Inference" (2012)
- Frechet, M. (1935) "Generalisation du theoreme des probabilites totales"
- Hutter, "Universal Artificial Intelligence" (2005)
- Nil's nuPLN.tex (internal document on PLN formalization)
