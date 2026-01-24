# Knuth-Skilling Foundations of Inference

Lean 4 formalization of Knuth & Skilling's "Foundations of Inference" (2012).

## Overview

The **Knuth-Skilling representation theorem** shows that any algebraic structure
satisfying natural axioms (associativity, monotonicity, and a separation
property) embeds into `(ℝ, +)`. This provides a foundational justification for
probability theory without assuming additivity, continuity, or differentiability.

**Key insight**: K&S works on **distributive lattices**, not just Boolean algebras.
This means no negation/complements are required—a genuine generalization of
classical probability.

## Primary Assumption: NoAnomalousPairs (NAP)

The **canonical proof path** uses `NoAnomalousPairs` from the 1950s ordered-semigroup
literature (Alimov 1950, Fuchs 1963), formalized via Eric Luap's OrderedSemigroups library.

**Why NAP is primary**:
- Historical precedent: NAP (1950s) predates K&S's `KSSeparation` (2012) by 60+ years
- Strictly weaker: NAP is identity-free; `KSSeparation` requires identity
- The relationship: `KSSeparation + IdentIsMinimum ⇒ NoAnomalousPairs` (proven)

See `Additive/Main.lean` for the canonical assumption hierarchy.

## Two Proof Approaches

We formalize **both** proofs of the representation theorem:

1. **Hölder/Alimov embedding** (`Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean`):
   Uses `NoAnomalousPairs` — **CANONICAL PATH**
   Direct embedding via Eric Luap's OrderedSemigroups library.

2. **Dedekind cuts** (`Additive/Proofs/DirectCuts/Main.lean`):
   Uses `KSSeparationStrict` — alternative path
   Classical Dedekind cuts construction.

3. **Grid induction** (`Additive/Proofs/GridInduction/Main.lean`):
   Uses `KSSeparationStrict` — K&S paper's original approach
   Most complex; kept for historical fidelity.

The Hölder/Alimov approach is modeled on Alimov (1950) and Hölder (1901),
adapted for ordered semigroups without identity.

## Main Result (Representation Theorem; Appendix A in the paper)

```lean
theorem associativity_representation
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [RepresentationGlobalization α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧   -- Order embedding
      Θ ident = 0 ∧                        -- Identity maps to 0
      ∀ x y : α, Θ (op x y) = Θ x + Θ y    -- Operation maps to addition
```

In practice, the globalization class `RepresentationGlobalization` is provided automatically from the
induction pipeline once `KSSeparationStrict` is available; and `KSSeparationStrict` is derived from
`KSSeparation` under a mild “density above `ident`” hypothesis (e.g. `[DenselyOrdered α]`).

## Axiom System

### Our Approach: Base + Separation

We use a minimal base with separation as the key regularity condition:

**Base axioms (`KnuthSkillingAlgebraBase`)**:
- Linear order on α
- Associative operation `op : α → α → α`
- Identity element `ident`
- Strict monotonicity (both sides)
- Positivity (`ident ≤ x` for all x)

**Plus separation (`KSSeparation`)**:
- For any `a > ident` and `x < y`, there exist `m, n` such that `x^m < a^n ≤ y^m`

**What we DERIVE (not assume!)**:
- **Commutativity**: `op x y = op y x` — proven in `Additive/Axioms/SandwichSeparation.lean`
- **Archimedean property**: no infinitesimals — proven in `Additive/Axioms/SandwichSeparation.lean`

### Comparison with Other Expositions

Some treatments assume commutativity and Archimedean up front. Our approach is
more economical: separation implies both.

### Why Separation is Necessary

`KSSeparation` is **not derivable** from the base axioms alone. Counterexamples:
- `Counterexamples/SemidirectNoSeparation.lean`: Archimedean ordered associative monoid
  that is noncommutative and fails separation
- `Counterexamples/ProductFailsSeparation.lean`: Commutative ordered monoid with
  infinitesimals (ℕ×ℕ lexicographic) that fails separation

```lean
-- KSSeparation: For any a > ident and x < y, there exist m, n such that x^m < a^n ≤ y^m
class KSSeparation (α : Type*) [KnuthSkillingAlgebraBase α] : Prop where
  separation :
    ∀ {a x y : α},
      KnuthSkillingAlgebraBase.ident < a →
      KnuthSkillingAlgebraBase.ident < x →
      KnuthSkillingAlgebraBase.ident < y →
      x < y →
      ∃ n m : ℕ, 0 < m ∧
        KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
        KnuthSkillingAlgebra.iterate_op a n ≤ KnuthSkillingAlgebra.iterate_op y m
```

## Directory Structure

```
KnuthSkilling/
├── README.md                    # This file
├── FoundationsOfInference.lean  # Reviewer entrypoint (imports Core + Appendices A/B/C)
├── Core/                        # Core axiom hierarchy
│   ├── Basic.lean               # PlausibilitySpace, Valuation, KSSemigroupBase
│   ├── Algebra.lean             # iterate_op, KSSeparation, NoAnomalousPairs
│   └── ScaleCompleteness.lean   # σ-additivity bridge
├── Additive/                    # Appendix A: additive representation
│   ├── Main.lean                # Public API: HasRepresentationTheorem
│   ├── Axioms/                  # Axiom definitions
│   │   ├── AnomalousPairs.lean  # NoAnomalousPairs (NAP) - PRIMARY
│   │   └── SandwichSeparation.lean  # KSSeparation ⇒ Commutativity + Archimedean
│   └── Proofs/                  # Three proof paths
│       ├── OrderedSemigroupEmbedding/  # Hölder path (NAP) - CANONICAL
│       ├── DirectCuts/          # Dedekind cuts (KSSeparationStrict)
│       └── GridInduction/       # K&S induction (KSSeparationStrict)
├── Multiplicative/              # Appendix B: product operation
│   ├── Main.lean                # Public entry point
│   └── Proofs/                  # Proof alternatives
├── Variational/                 # Appendix C: Cauchy/log equation
│   └── Main.lean                # Variational theorem
├── Probability/                 # Derived probability calculus
│   ├── ProbabilityCalculus.lean # Canonical interface for end-results
│   └── ProbabilityDerivation.lean
├── Information/                 # K&S Section 6/8: entropy/KL
│   └── Main.lean
├── ShoreJohnson/                # Shore-Johnson (1980) formalization
│   └── Main.lean                # SJ entrypoint (first-class, import explicitly)
├── Examples/                    # Concrete examples
│   ├── CoinDie.lean             # Full pipeline: coin/die → ℝ
│   └── PreciseVsImpreciseGrounded.lean  # K&S → credal sets, decision theory
├── Counterexamples/             # Why axioms matter
└── Literature/                  # Reference: Aczél, Hölder, Cox
```

## Key Files

| File | Description |
|------|-------------|
| `FoundationsOfInference.lean` | **Reviewer entrypoint**: imports Core + Appendices A/B/C |
| `Core/Basic.lean` | Core definitions: `KSSemigroupBase`, `KnuthSkillingMonoidBase` |
| `Additive/Axioms/AnomalousPairs.lean` | **NoAnomalousPairs (NAP)**: primary assumption |
| `Additive/Axioms/SandwichSeparation.lean` | **Key derivations**: `KSSeparation` ⇒ Commutativity + Archimedean |
| `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean` | **Appendix A (Hölder)**: NAP → representation — CANONICAL |
| `Additive/Proofs/DirectCuts/Main.lean` | **Appendix A (cuts)**: KSSeparationStrict → representation |
| `Additive/Main.lean` | **Appendix A API**: `HasRepresentationTheorem` |
| `Multiplicative/Main.lean` | **Appendix B**: product theorem |
| `Variational/Main.lean` | **Appendix C**: variational/Cauchy theorem |
| `Probability/ProbabilityCalculus.lean` | **Canonical interface**: sum rule, product rule, Bayes |
| `Examples/CoinDie.lean` | **Full pipeline example**: coin/die → ℝ |
| `Examples/PreciseVsImpreciseGrounded.lean` | **Decision theory**: K&S → credal sets → EU vs maximin |

## The Hypercube Connection

The K&S foundations fit naturally into the **Stay-Wells hypercube framework**
for generating type systems:

| Hypercube Concept | K&S Interpretation |
|-------------------|-------------------|
| Lambda Theory | KnuthSkillingAlgebra with `op`, `ident` |
| Modal Types | Separation sets A(d,u), B(d,u), C(d,u) |
| Sort Slots | Precision levels: ∗ = intervals, □ = points |
| Equational Center | Structures where Θ representation exists |
| Hypercube Vertices | Different probability theories |

The **spectrum of probability foundations** forms a hypercube where:
- **Axes**: Commutativity, Completeness, Precision profile
- **Vertices**: Different probability theories (imprecise → classical)
- **Paths**: Refinement processes (interval bounds → point values)

See `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Connection.lean` for the full development.

Note: the hypercube-related K&S analysis files now live under:
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Connection.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Neighbors.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Proofs.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Theory.lean`

For the hypercube’s “weakness preorder” + quantale-semantics layer, see:
- `Mettapedia/ProbabilityTheory/Hypercube/WeaknessOrder.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/QuantaleSemantics.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/ThetaSemantics.lean`
- `Mettapedia/ProbabilityTheory/Hypercube/DensityAxisStory.lean`

## Build

```bash
cd lean-projects/mettapedia
export LAKE_JOBS=3
nice -n 19 lake build Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
```

## Status

**Appendix A (Representation Theorem): COMPLETE** (2026-01-11)
- Full representation theorem proven (no `sorry`)
- Two proof approaches: K&S induction AND direct Dedekind cuts
- Separation ⇒ commutativity + Archimedean (see `Additive/Axioms/SandwichSeparation.lean`)
- Faithful representation ⇒ separation (see `AxiomSystemEquivalence.lean`)
- Builds warning-free

**Appendix B (Product Theorem): COMPLETE** (2026-01-14)
- **No `sorry`, no `axiom`, no smuggling** - all ProductTheorem files are clean
- Two Lean routes:
  1. **Main.lean**: assumes `AdditiveOrderIsoRep PosReal tensor` + `DistributesOverAdd`
  2. **AczelTheorem.lean**: assumes only `TensorRegularity` + `DistributesOverAdd`
- `TensorRegularity` = associativity + injectivity; **injectivity is DERIVED** from distributivity + commutativity via `TensorRegularity.of_assoc_of_distrib_of_comm`

### WARNING: Circular Reasoning Anti-Pattern

A previous file `EventBridge.lean` was **DELETED** because it contained circular reasoning.
It defined `mulTensor := multiplication` and then "proved" multiplication equals scaled
multiplication. **This proves nothing!**

**DO NOT** try to "bridge" event-level to scalar-level by:
```lean
abbrev mulTensor := mulPos  -- WRONG: assumes tensor IS multiplication
```

The **correct approach** (what `AczelTheorem.lean` does):
1. Start with an ABSTRACT tensor `⊗` satisfying K&S Axioms 3-4
2. Prove that ANY such tensor must equal scaled multiplication
3. The tensor's identity is derived, not assumed

## Open Gaps

### 1. Event Lattice → Plausibility Scale Connection ✅ RESOLVED

**Implemented** in `Model.lean`:

```lean
structure KSModel (E S : Type*)
    [PlausibilitySpace E] [KnuthSkillingAlgebraBase S] where
  v : E → S
  mono : Monotone v
  v_bot : v ⊥ = ident
  v_sup_of_disjoint : ∀ {a b : E}, Disjoint a b → v (a ⊔ b) = op (v a) (v b)
```

This follows GPT-5 Pro's suggestion: keep the scale S already equipped with its
K&S algebra structure. The bridge is the single axiom `v(a ⊔ b) = v(a) ⊕ v(b)`.

**Also includes**:
- `KSModelWithRepresentation`: Composition with the representation theorem (Θ : S → ℝ)
- `instKSAlgebraNNReal`: NNReal with addition forms a `KnuthSkillingAlgebraBase`
- `Three'.threeKSModel`: Concrete example on the 3-element chain with NNReal scale

### 2. Non-Boolean Examples

K&S claims to work on distributive lattices without complements.

The `Examples/` directory contains concrete examples demonstrating K&S applied to finite lattices:
- `CoinDie.lean`: Full pipeline coin/die → ℝ
- `PreciseVsImpreciseGrounded.lean`: K&S → credal sets → decision theory
- `ImpreciseOn7Element.lean`: Imprecise probability on 7-element lattice

Counterexamples showing why axioms matter are in `Additive/Counterexamples/`.

### 3. Decision Theory Example ✅ COMPLETE (2026-01-21)

**Implemented** in `Examples/PreciseVsImpreciseGrounded.lean` (910 lines, 0 sorry):

Demonstrates the complete pipeline from K&S axioms to decision theory:
- **K&S grounding**: Actual `Θ : Event → ℝ` satisfying modularity/monotonicity/non-negativity
- **Probability extraction**: `P(a) = Θ(a) / Θ(⊤)` via `KSBooleanRepresentation.probability`
- **Credal sets**: Sets of K&S representations for imprecise probability (epistemic uncertainty)
- **Hypercube positioning**: Formal connection to `PrecisionAxis.precise` vs `.imprecise`
- **Decision rules**: Expected utility (von Neumann-Morgenstern) vs maximin (Gilboa-Schmeidler)

**Key theorems**:
- Connection: probability distributions arise from K&S representations (not ad-hoc)
- Completeness: when K&S axioms fail to uniquely determine probabilities → credal sets
- Independence: decision theory axioms (vNM, G-S) are ADDITIONAL to K&S probability
- Decisions differ: EU and maximin give opposite recommendations under uncertainty

Axiom stack is honest: clearly separates what K&S derives (probability calculus) from what requires additional axioms (decision rules).

### 4. Cauchy's Functional Equation

Appendix B exponential characterization needs:
```lean
theorem continuous_additive_is_linear (f : ℝ → ℝ)
    (h_cont : Continuous f) (h_add : ∀ x y, f(x+y) = f(x) + f(y)) :
    ∃ c, ∀ x, f(x) = c * x
```
Not in Mathlib. Classical result but requires density argument.

## Countermodels (why the extra axioms matter)

- `Additive/Counterexamples/SemidirectNoSeparation.lean`: an Archimedean ordered associative monoid
  which is noncommutative and fails `KSSeparation` (so "Archimedean semigroup ⇒ commutative" is
  false).
- `Additive/Counterexamples/ProductFailsSeparation.lean`: a commutative ordered monoid with
  infinitesimals (lexicographic product), failing the sandwich separation axiom `KSSeparation`
  even though addition is commutative (and in particular it is not Archimedean, so it is not a
  `KnuthSkillingAlgebra`).
- `Additive/Counterexamples/KSSeparationNotDerivable.lean`: proves NAP must be postulated, not derived.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Hölder, "Die Axiome der Quantität und die Lehre vom Mass" (1901) — ordered group embeddings
- Alimov (1950) — ordered semigroup embeddings
- Klain & Rota, "Introduction to Geometric Probability" — valuations on distributive lattices
- Aczél, "Lectures on Functional Equations" — rational homogeneity
- Stay & Wells, "Generating Hypercubes of Type Systems"

## Paper

See `paper/ks-formalization.tex` for a detailed writeup of the formalization.
