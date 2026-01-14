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

## Two Proof Approaches

We formalize **both** proofs of the representation theorem:

1. **K&S-style induction** (`RepresentationTheorem/Main.lean`):
   Grid-based inductive extension via `RepresentationGlobalization`.

2. **Direct Dedekind cuts** (`RepresentationTheorem/Alternative/Main.lean`):
   Hölder-style construction adapting classical ordered group embeddings.
   More concise and direct.

The direct cuts approach is modeled on Hölder (1901) and Alimov (1950),
adapted for ordered monoids. The separation axiom—adopted following a
suggestion by B. Goertzel—provides the density condition making this work.

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
- **Commutativity**: `op x y = op y x` — proven in `Separation/SandwichSeparation.lean`
- **Archimedean property**: no infinitesimals — proven in `Separation/SandwichSeparation.lean`

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
├── Basic.lean                   # PlausibilitySpace, Valuation, KnuthSkillingAlgebraBase
├── Algebra.lean                 # iterate_op, basic lemmas
├── Model.lean                   # KSModel: Events → Scale bridge, NNReal instance
├── Separation/                  # Separation machinery
│   ├── SandwichSeparation.lean  # KSSeparation ⇒ Commutativity + Archimedean (DERIVED!)
│   └── Derivation.lean          # WIP derivation of KSSeparation from weaker hypotheses
├── AxiomSystemEquivalence.lean  # Separation ⇔ representation equivalences
├── RepresentationTheorem/       # Appendix A: main formalization
│   ├── Main.lean                # Public API: associativity_representation
│   ├── Alternative/             # Direct Dedekind cuts proof (Hölder-style)
│   │   ├── Main.lean            # associativity_representation_cuts
│   │   └── DirectCuts.lean      # The construction
│   ├── Globalization.lean       # RepresentationGlobalization typeclass
│   ├── Core/                    # K&S-style induction machinery
│   └── Counterexamples/         # Why separation is necessary
├── ProductTheorem/              # Appendix B: product operation (WIP)
│   ├── Main.lean                # Public entry point
│   ├── Basic.lean               # Product equation from distributivity
│   ├── FunctionalEquation.lean  # Product equation → exponential
│   └── AczelTheorem.lean        # TensorRegularity hypothesis bundle
├── ProductTheorem.lean          # Import facade
├── Examples/                    # Concrete examples
│   ├── CoinFlip.lean            # Full pipeline: coin flip → NNReal → ℝ (Durrett 1.6.12)
│   ├── ThreeElementChain.lean   # Non-Boolean: 3-element chain (⊥ < mid < ⊤)
│   └── OpenSets.lean            # Non-Boolean: open sets of ℝ with topology
└── Literature/                  # Reference: Aczél, Hölder, Cox
```

## Key Files

| File | Description |
|------|-------------|
| `Basic.lean` | Core definitions: `PlausibilitySpace`, `Valuation`, `KnuthSkillingAlgebraBase` |
| `Model.lean` | **KSModel**: Events → Scale bridge, NNReal instance, Three' example |
| `Separation/SandwichSeparation.lean` | **Key derivations**: `KSSeparation` ⇒ Commutativity + Archimedean |
| `RepresentationTheorem/Main.lean` | **Appendix A (K&S proof)**: `associativity_representation` |
| `RepresentationTheorem/Alternative/Main.lean` | **Appendix A (cuts proof)**: `associativity_representation_cuts` |
| `AxiomSystemEquivalence.lean` | Representation ⇔ separation equivalence |
| `ProductTheorem/Main.lean` | **Appendix B (WIP)**: product operation |
| `Counterexamples/ProductFailsSeparation.lean` | NatProdLex: why separation is necessary |
| `Examples/CoinFlip.lean` | **Full pipeline example**: coin flip → NNReal → ℝ (Durrett 1.6.12) |
| `Examples/ThreeElementChain.lean` | **Non-Boolean example**: minimal 3-element chain with `Valuation` |
| `Examples/OpenSets.lean` | **Non-Boolean example**: open sets of ℝ (connects to Lebesgue measure) |

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
- Separation ⇒ commutativity + Archimedean (see `Separation/SandwichSeparation.lean`)
- Faithful representation ⇒ separation (see `AxiomSystemEquivalence.lean`)
- Builds warning-free

**Appendix B (Product Theorem): PROVED (scalar theorem), integration WIP** (2026-01-14)
- Two Lean routes: product equation (`ProductTheorem/Main.lean`) and direct `TensorRegularity` route (`ProductTheorem/AczelTheorem.lean`)
- `TensorRegularity` hypothesis bundle (not new axioms): Axiom 4 + injectivity of `t ↦ 1 ⊗ t` (no `ident_le`; injectivity is derivable from an additive order-isomorphism representation)
- **Gap**: event-level bridge from direct products to a `tensor` satisfying these hypotheses

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

### 2. Non-Boolean Examples ✅ RESOLVED

K&S claims to work on distributive lattices without complements.

**Demonstrated** in `Examples/`:
- `ThreeElementChain.lean`: Minimal 3-element chain (⊥ < mid < ⊤) with `Valuation`
- `OpenSets.lean`: Natural example using open sets of ℝ (topological, no complements)

Both files prove their respective lattices are NOT Boolean (no complement operation exists).

### 3. Cauchy's Functional Equation

Appendix B exponential characterization needs:
```lean
theorem continuous_additive_is_linear (f : ℝ → ℝ)
    (h_cont : Continuous f) (h_add : ∀ x y, f(x+y) = f(x) + f(y)) :
    ∃ c, ∀ x, f(x) = c * x
```
Not in Mathlib. Classical result but requires density argument.

## Countermodels (why the extra axioms matter)

- `RepresentationTheorem/Counterexamples/SemidirectNoSeparation.lean`: an Archimedean ordered associative monoid
  which is noncommutative and fails `KSSeparation` (so “Archimedean semigroup ⇒ commutative” is
  false).
- `RepresentationTheorem/Counterexamples/ProductFailsSeparation.lean`: a commutative ordered monoid with
  infinitesimals (lexicographic product), failing the sandwich separation axiom `KSSeparation`
  even though addition is commutative (and in particular it is not Archimedean, so it is not a
  `KnuthSkillingAlgebra`).

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Hölder, "Die Axiome der Quantität und die Lehre vom Mass" (1901) — ordered group embeddings
- Alimov (1950) — ordered semigroup embeddings
- Klain & Rota, "Introduction to Geometric Probability" — valuations on distributive lattices
- Aczél, "Lectures on Functional Equations" — rational homogeneity
- Stay & Wells, "Generating Hypercubes of Type Systems"

## Paper

See `paper/ks-formalization.tex` for a detailed writeup of the formalization.
