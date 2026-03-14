# PLN First-Order Quantifiers

Formalization of PLN first-order quantifier semantics via Goertzel's
weakness theory and fuzzy quantifier algebra (QFM).
**40 files, ~6,774 lines. Zero sorry.**

Companion text: `papers/wm-pln-book.tex`, Chapter 11 (Quantifiers).

## Key Idea

First-order quantifiers are **weakness of the diagonal relation** on a
satisfying set: ∀μ(S) = weakness(μ, diag(S)). Under uniform weights
this reduces to |S|²/|U|². The existential is the De Morgan dual.
Fuzzy quantifiers ("most", "few", "about half") extend this with
witness-fraction predicates and QFM composition operators.

## Core Quantifier Semantics

| File | Contents |
|------|----------|
| `Basic.lean` | Re-exports from EvidenceQuantale and QuantaleWeakness |
| `SatisfyingSet.lean` | `SatisfyingSet` (frame-valued predicates), `diagonal`, `complementDiagonal` |
| `QuantifierSemantics.lean` | `forAllEval`, `thereExistsEval` (De Morgan); extensional views via lattice meet/join |
| `WeaknessConnection.lean` | `forAll_is_weakness_of_diagonal` — the central theorem |
| `Soundness.lean` | 5 main theorems: weakness identity, monotonicity, De Morgan, functoriality |

## Infinite-Domain Layer

| File | Contents |
|------|----------|
| `Infinite.lean` | `WeightFunctionInf`, `SatisfyingSetInf` for arbitrary domains |
| `InfiniteSoundness.lean` | Infinite-domain analogs of the 5 main theorems |
| `InfiniteCanary.lean` | Natural number fixtures for infinite-domain validation |

## Fuzzy Quantifier Semantics (QFM)

| File | Contents |
|------|----------|
| `FuzzyQuantifierSemantics.lean` | `FuzzyQuantifierParams` (ε, L, U, θ); `nearOne`/`nearZero`; witness fraction; QFM composition (multiplicative, minimum, Łukasiewicz, probabilistic sum) |
| `FuzzyMeasureCore.lean` | `FuzzyCapacity`, `IsNormalized`; Sugeno/Choquet support |
| `FuzzyQuantifierSemanticsInf.lean` | Infinite-domain fuzzy cuts and scores |
| `FuzzyQuantifierSoundnessInf.lean` | Infinite fuzzy soundness theorems |
| `FuzzyITVBridge.lean` | ITV coordinate mapping (lower/upper/credibility profiles) |

## Graded Quantifiers (Sugeno / Choquet)

| File | Contents |
|------|----------|
| `GradedQuantifierSpecialization.lean` | `GradedQuantifierSemantics` generic interface; Sugeno and Choquet instances |
| `SugenoIntegral.lean` | Level-cut computation; `sugenoIntegral_in_unit`, monotonicity |
| `ChoquetQuantifierSemantics.lean` | Choquet level cuts, integrands, monotonicity |
| `FuzzyDomainQuantifiers.lean` | Domain-restricted variants for all three families |

## Syllogisms and Worked Examples

| File | Contents |
|------|----------|
| `FuzzySyllogismCanary.lean` | QFM syllogisms: `qfm_syllogism_interval`, Zadeh syllogisms, composition variants |
| `QuantifierWorkedExamples.lean` | Ch.11 parameter fixtures (a_few, many, most, almost_all, …) |
| `QuantifierAlgorithmTheorems.lean` | Parameter scaling, relaxation, witness counting |

## Canary and Regression Tests

10 canary files and 5 regression files covering finite, infinite, fuzzy,
graded, syllogism, and domain-restriction correctness on concrete
domains (Bool, Fin n, ℕ).

## Third-Order Extension

| File | Contents |
|------|----------|
| `ThirdOrderQuantifierSemantics.lean` | `SecondOrderUncertainty`, `ThirdOrderQuantifierModel`; theory-observation gap theorem |
| `FoundationBridge.lean` | `PLNSemiformula` syntax bridge to Foundation logic |
