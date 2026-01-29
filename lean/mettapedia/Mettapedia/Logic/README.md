# Mettapedia Logic Module

This module formalizes probabilistic logic networks (PLN) and their connections to
probability theory, imprecise probability, Heyting algebras, quantales, and Solomonoff induction.

## The Unified Architecture

```
                     PLN Evidence (n⁺, n⁻)
                            │
       ┌────────────────────┼────────────────────┐
       │                    │                    │
       ▼                    ▼                    ▼
   Quantale            Heyting Frame       Beta Statistic
   (tensor ⊗)         (non-Boolean)        (conjugacy)
       │                    │                    │
       ▼                    ▼                    ▼
  PLN Deduction        Bounds [L, U]       Bayesian Update
  A→B, B→C ⊢ A→C      with gap            (hplus = add params)
       │                    │                    │
       └────────────────────┼────────────────────┘
                            │
                            ▼
              ┌─────────────────────────────┐
              │ Solomonoff on Exchangeable  │
              │ Binary = Evidence (n⁺, n⁻) │
              └─────────────────────────────┘
```

## Key Theorems and Connections

### 1. Fréchet Bounds (Proven)

File: `PLNFrechetBounds.lean`

| Theorem | Statement | Status |
|---------|-----------|--------|
| `frechet_upper_bound` | P(A ∩ B) ≤ min(P(A), P(B)) | ✅ Proven |
| `frechet_lower_bound` | max(0, P(A) + P(B) - 1) ≤ P(A ∩ B) | ✅ Proven |
| `frechet_bounds_iff_consistency` | PLN consistency ↔ Fréchet bounds | ✅ Proven |

### 2. Hypergeometric Mode Bounds (Proven)

File: `PLNConjunction.lean`

| Theorem | Statement | Status |
|---------|-----------|--------|
| `hypergeometricMode_in_range` | mode ≤ min(a, b) | ✅ Proven |
| Lower bound | max(0, a+b-n) ≤ mode | Documented (proof sketch) |

**Connection**: Fréchet bounds on probabilities correspond to hypergeometric bounds on cardinalities:
- P(A) = a/n, P(B) = b/n in finite universe
- P(A ∩ B) ∈ [max(0, a+b-n)/n, min(a,b)/n]

### 3. Weight-Space Operations (Proven)

File: `PLNConfidenceWeight.lean` (NEW)

| Theorem | Statement | Status |
|---------|-----------|--------|
| `evidence_combination_bounded` | mode ≤ min(a, b) justifies min in weight space | ✅ Proven |
| `w2c_le_one` | Confidence bounded by 1 | ✅ Proven |
| `combineCorrect_comm` | Correct formula is symmetric | ✅ Proven |

**Critical Insight**: The hypergeometric operates on COUNTS (weights), not confidences!
- **WRONG**: `w2c(min(c₁, c₂))` — treats confidences as weights
- **CORRECT**: `w2c(min(c2w(c₁), c2w(c₂)))` — converts to weight space first

### 4. Quantale Structure (Proven)

File: `EvidenceQuantale.lean`

| Theorem | Statement | Status |
|---------|-----------|--------|
| `Evidence.isQuantale` | Evidence with tensor is a quantale | ✅ Proven |
| `IsCommQuantale Evidence` | Commutative quantale | ✅ Proven |
| `evidence_tensor_transitivity` | (A→B) ⊗ (B→C) ≤ (A→C) | ✅ Proven |
| `confidence_monotone_in_total` | More evidence → higher confidence | ✅ Proven |

### 5. Heyting/Non-Boolean Structure (Proven)

File: `HeytingValuationOnEvidence.lean`

| Theorem | Statement | Status |
|---------|-----------|--------|
| `evidence_not_boolean` | Evidence has no Boolean complement | ✅ Proven |
| `credalGap_singleton` | Point probabilities have zero gap | ✅ Proven |
| `evidence_richer_than_strength` | Evidence > intervals | ✅ Proven |
| `strength_fiber_infinite` | Infinitely many Evidence per strength | ✅ Proven |

### 6. Solomonoff Connection (Proven)

File: `SolomonoffExchangeable.lean`

| Theorem | Statement | Status |
|---------|-----------|--------|
| `semimeasureExchangeable_same_counts` | Exchangeable → depends only on counts | ✅ Proven |
| `mu_same_counts` | Restricted Solomonoff depends on (n⁺, n⁻) | ✅ Proven |

**Key Insight**: Solomonoff prediction restricted to exchangeable binary sequences
collapses to Evidence (n⁺, n⁻)!

### 7. De Finetti Representation (Proven)

File: `DeFinetti.lean`

The full measure-theoretic de Finetti representation theorem is proven,
establishing that exchangeable sequences have Bernoulli mixture representations.

## File Index

### Core PLN

| File | Description | Sorries |
|------|-------------|---------|
| `PLNEvidence.lean` | Evidence structure, quantale operations (⊗, ⊕) | 0 |
| `PLNDeduction.lean` | PLN deduction rules | 0 |
| `PLNDerivation.lean` | Induction, abduction, Bayes inversion | 0 |
| `PLNInferenceRules.lean` | Similarity, modus ponens/tollens | 0 |

### Conjunction/Disjunction/Negation

| File | Description | Sorries |
|------|-------------|---------|
| `PLNConjunction.lean` | Hypergeometric distribution, mode bounds | 0 |
| `PLNDisjunction.lean` | De Morgan, inclusion-exclusion | 0 |
| `PLNNegation.lean` | Evidence swap | 0 |
| `PLNImplicantConjunction.lean` | A→C, B→C ⊢ A∧B→C | 0 |
| `PLNRevision.lean` | Evidence aggregation = hplus | 0 |

### Weight-Space and Confidence

| File | Description | Sorries |
|------|-------------|---------|
| `PLNConfidenceWeight.lean` | **NEW** Min in weight space theorem | 0 |
| `ConfidenceCompoundingTheorem.lean` | Confidence propagation | 0 |

### Bounds and Consistency

| File | Description | Sorries |
|------|-------------|---------|
| `PLNFrechetBounds.lean` | Fréchet bounds ↔ PLN consistency | 0 |
| `EvidenceIntervalBounds.lean` | Strength intervals, incomparability | 0 |

### Algebraic Structure

| File | Description | Sorries |
|------|-------------|---------|
| `EvidenceQuantale.lean` | Commutative quantale instance | 0 |
| `HeytingValuationOnEvidence.lean` | Non-Boolean, credal sets | 0 |
| `EvidenceBeta.lean` | Beta distribution connection | 0 |

### Solomonoff and Exchangeability

| File | Description | Sorries |
|------|-------------|---------|
| `SolomonoffExchangeable.lean` | Solomonoff → Evidence collapse | 0 |
| `Exchangeability.lean` | Exchangeable sequences | 0 |
| `DeFinetti.lean` | De Finetti representation theorem | 0 |

## Key Insight: PLN Evidence ↔ Credal Sets ↔ Interval Probability

PLN represents beliefs as **Evidence** pairs `(n⁺, n⁻)` where:
- `n⁺` = positive evidence (support for proposition)
- `n⁻` = negative evidence (support against proposition)

The **strength** is `s = n⁺ / (n⁺ + n⁻)` ∈ [0,1].
The **weight** is `w = n⁺ + n⁻` (total evidence count).
The **confidence** is `c = w / (w + k)` for prior weight k.

**Key Theorem**: Evidence forms a **partial order** where two values can be
**incomparable**. This incomparability represents **epistemic uncertainty**!

### Why Evidence is Richer than Intervals

| What intervals capture | What PLN Evidence adds |
|------------------------|------------------------|
| Probability bounds [a, b] | Actual evidence counts |
| "What we know" | "How we know it" |
| Point in [0,1]² | Extra dimension: weight |

The extra dimension (total count = weight) enables:
1. **Confidence**: Higher weight → higher confidence
2. **Correct inference**: min/max in weight space, not confidence space!
3. **Beta conjugacy**: Evidence = sufficient statistic for Beta posterior

## Build

```bash
cd lean-projects/mettapedia
lake build Mettapedia.Logic.PLNConfidenceWeight  # New file
lake build Mettapedia.Logic.PLNFrechetBounds     # Fréchet bounds
lake build Mettapedia.Logic.EvidenceQuantale     # Quantale structure
```

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- Goertzel et al., "Probabilistic Logic Networks" (2008)
- Knuth & Skilling, "Foundations of Inference" (2012)
- Fréchet, M. (1935) "Généralisation du théorème des probabilités totales"
- Nil's nuPLN.tex (internal document on PLN formalization)
