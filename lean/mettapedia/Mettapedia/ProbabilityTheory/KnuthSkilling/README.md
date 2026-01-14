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

## Axiom Systems

### Bundle: Explicit Commutativity + Archimedean

Some expositions assume commutativity and an Archimedean property up front:
- **Strict monotonicity** (both sides)
- **Associativity**
- **Commutativity** (`x ⊕ y = y ⊕ x`)
- **Archimedean** (no infinitesimals)

### Bundle: Iterate/Power “Sandwich” Separation (`KSSeparation`)

This development also supports a (stronger, but often implicit) separation assumption:
- **Strict monotonicity** (both sides)
- **Associativity**
- **Sandwich separation** (`KSSeparation`)

The key insight is that `KSSeparation` forces both commutativity and an Archimedean-style
unboundedness property (see `Separation/SandwichSeparation.lean` and
`AxiomSystemEquivalence.lean`).

Importantly, `KSSeparation` is **not derivable** from the bare `KnuthSkillingAlgebra` axioms: there
are ordered associative Archimedean noncommutative monoids (semidirect products) that satisfy the
base axioms but fail `KSSeparation` (see `RepresentationTheorem/Counterexamples/KSSeparationNotDerivable.lean`).

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
├── Basic.lean                   # PlausibilitySpace, Valuation, KnuthSkillingAlgebra
├── Algebra.lean                 # iterate_op, basic lemmas
├── Separation/                  # Separation machinery
│   ├── SandwichSeparation.lean  # Sandwich separation: commutativity + Archimedean consequences
│   └── Derivation.lean          # WIP derivation of `KSSeparation` (packages `LargeRegimeSeparationSpec`)
├── AxiomSystemEquivalence.lean  # Relationship between separation and commutativity/representation bundles
├── ProductTheorem/              # Appendix B (product equation + product rule)
│   ├── FunctionalEquation.lean   # Appendix B solver: product equation → exponential
│   ├── Basic.lean                # Derive product equation from axioms 3–4 + Θ(x⊗t)=Θx+Θt
│   ├── DirectProduct.lean        # Lattice-level bookkeeping for direct products of independent lattices
│   └── Main.lean                 # Conclude `⊗` is multiplication (up to a scale constant)
├── ProductTheorem.lean          # Public entry point for Appendix B
├── RepresentationTheorem/       # The main formalization (see RepresentationTheorem/README.md)
│   ├── Main.lean                # Public API: representation theorem + corollaries
│   ├── Globalization.lean       # Globalization construction (`RepresentationGlobalization`)
│   ├── Core/                    # Induction machinery (see Core/README.md)
│   └── ...
└── Literature/                  # Reference material (Aczél functional equations)
```

## Key Files

| File | Description |
|------|-------------|
| `Basic.lean` | Core definitions: `PlausibilitySpace`, `KnuthSkillingAlgebra`, `iterate_op` |
| `Algebra.lean` | Basic lemmas about `iterate_op`, monotonicity, Archimedean bounds |
| `Separation/SandwichSeparation.lean` | Sandwich separation: `KSSeparation` ⇒ Commutativity + Archimedean-style consequences |
| `AxiomSystemEquivalence.lean` | Separation consequences + “representation ⇒ separation” via rational density |
| `RepresentationTheorem/Main.lean` | **Main theorem**: `associativity_representation` |
| `ProductTheorem/Main.lean` | **Appendix B**: product equation ⇒ exponential ⇒ product rule for `⊗` |
| `ProductTheorem/DirectProduct.lean` | Lattice-level direct product `×` (canonical `Set` model) |

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

**Appendix B (Product Theorem): WIP** (2026-01-14)
- Product equation framework in `ProductTheorem/`
- `TensorRegularity` hypothesis bundle (not new axioms)
- **Gap**: Need to justify ⊗ satisfies K&S conditions (issue: `ident_le` fails for multiplication)

## Open Gaps

### 1. Event Lattice → Plausibility Scale Connection

We have two disconnected pieces:
- `PlausibilitySpace`: Distributive lattice of events
- `KnuthSkillingAlgebra`: Linearly ordered plausibility scale with ⊕

**Missing**: Formal connection showing how a valuation `v : Events → Scale`
induces K&S algebra structure on `range(v)`.

### 2. Non-Boolean Examples

K&S claims to work on distributive lattices without complements, but our
examples mostly use Boolean lattices (`Set Bool`, etc.).

**Needed**: Concrete non-Boolean distributive lattice with K&S valuation.

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
