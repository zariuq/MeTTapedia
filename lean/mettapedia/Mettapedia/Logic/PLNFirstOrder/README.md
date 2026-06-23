# PLN First-Order Quantifiers

Classical logic gives you "for all" and "there exists" as a crisp yes/no. But
real reasoning needs *graded* quantifiers: not just "all swans are white" but
"**most** swans are white," "**about half** of the patients improved," "**few**
trials failed." This directory formalizes PLN's account of quantifiers — both the
classical pair and the fuzzy family — as *uncertain truth values* you can compute
with, proving the central identities rather than asserting them.

The starting observation is a clean one. In PLN, an evidence-graded truth value
lives in a *quantale* (an ordered algebra of evidence), and there is an operation
called **weakness** that measures how strongly one predicate is contained in
another. The key idea here is that the universal quantifier is *exactly* the
weakness of a satisfying set against the diagonal relation:

> ∀μ(S) = weakness(μ, diag(S)),   which under uniform weights reduces to |S|²/|U|².

The existential is its De Morgan dual. Fuzzy quantifiers ("most", "few", "about
half") extend this with witness-fraction predicates and QFM (quantifier
fuzzification mechanism) composition operators (multiplicative, minimum,
Łukasiewicz, probabilistic-sum), and the graded layer adds Sugeno- and
Choquet-integral semantics over fuzzy capacities.

Built via Goertzel's weakness theory (`Mettapedia.Algebra.QuantaleWeakness`) and
the evidence quantale (`Mettapedia.Logic.EvidenceQuantale`).

Companion text: `../../../../../papers/wm-pln-book.tex`, Chapter 11 (Quantifiers).

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

8 `*Canary*.lean` files and 8 `*Regression*.lean` files covering finite,
infinite, fuzzy, graded, syllogism, and domain-restriction correctness on
concrete domains (Bool, Fin n, ℕ).

## Third-Order Extension

| File | Contents |
|------|----------|
| `ThirdOrderQuantifierSemantics.lean` | `SecondOrderUncertainty`, `ThirdOrderQuantifierModel`; theory-observation gap theorem |
| `FoundationBridge.lean` | `PLNSemiformula` syntax bridge to Foundation logic |

## Formalization status

All 40 `.lean` files in this directory are `sorry`-free (~6,800 lines total). The
central identity `forAll_is_weakness_of_diagonal` (`WeaknessConnection.lean`) holds
*by construction*; the soundness lane (`Soundness.lean`, `InfiniteSoundness.lean`)
proves monotonicity, De Morgan duality, and functoriality, mirrored in the
infinite-domain layer; the Sugeno/Choquet graded layer proves the integrands
monotone/antitone and the scores in `[0,1]`.

**Trusted base.** There are no source-level `axiom` declarations in this directory
(a source grep, *not* a per-theorem `#print axioms` audit — the quantifier
evaluators are `noncomputable` and built on Mathlib's order/real machinery, so
theorems may inherit standard Mathlib axioms such as `propext`, `Quot.sound`, and
`Classical.choice` transitively). Nothing in this directory uses `native_decide`,
so no `.lean` file here enlarges the trusted base via compile-time evaluation.

## References

- Ben Goertzel, Matthew Iklé, Izabela Freire Goertzel & Ari Heljakka, [*Probabilistic Logic Networks: A Comprehensive Framework for Uncertain Inference*](https://link.springer.com/book/10.1007/978-0-387-76872-4) (Springer, 2008) — PLN truth values, the weakness/quantale account of quantifiers, and the source of Chapter 11's quantifier theory.
- Lotfi A. Zadeh, "A Computational Approach to Fuzzy Quantifiers in Natural Languages," [*Computers & Mathematics with Applications* 9(1), 1983, pp. 149-184](https://www.sciencedirect.com/science/article/pii/0898122183900135) — the fuzzy-quantifier ("most", "few", "about half") tradition behind the QFM layer.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 40 .lean files, 0 with sorries.*
