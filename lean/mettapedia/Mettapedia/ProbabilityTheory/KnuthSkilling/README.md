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
├── ProductTheorem/              # Appendix B: product operation
│   ├── Main.lean                # Public entry point: tensor_coe_eq_mul_div_const
│   ├── Basic.lean               # Product equation from distributivity
│   ├── FunctionalEquation.lean  # Product equation → exponential (no sorry)
│   ├── AczelTheorem.lean        # TensorRegularity hypothesis bundle
│   ├── FibonacciProof.lean      # K&S's actual Appendix B proof (WIP, has sorries)
│   └── DirectProduct.lean       # Lattice-level event product structure
├── ProductTheorem.lean          # Import facade
├── Examples/                    # Concrete examples
│   ├── CoinFlip.lean            # Full pipeline: coin flip → NNReal → ℝ (Durrett 1.6.12)
│   ├── ThreeElementChain.lean   # Non-Boolean: 3-element chain (⊥ < mid < ⊤)
│   ├── OpenSets.lean            # Non-Boolean: open sets of ℝ with topology
│   └── PreciseVsImpreciseGrounded.lean  # K&S → credal sets, EU vs maximin, hypercube positioning
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
| `ProductTheorem/Main.lean` | **Appendix B**: product theorem (tensor → scaled multiplication) |
| `ProductTheorem/FunctionalEquation.lean` | **Appendix B**: Cauchy equation solver (no sorry!) |
| `ProductTheorem/AczelTheorem.lean` | **Appendix B**: TensorRegularity → scaled multiplication |
| `ProductTheorem/FibonacciProof.lean` | **Appendix B**: K&S's actual proof (Fibonacci + golden ratio, WIP) |
| `Counterexamples/ProductFailsSeparation.lean` | NatProdLex: why separation is necessary |
| `Examples/CoinFlip.lean` | **Full pipeline example**: coin flip → NNReal → ℝ (Durrett 1.6.12) |
| `Examples/ThreeElementChain.lean` | **Non-Boolean example**: minimal 3-element chain with `Valuation` |
| `Examples/OpenSets.lean` | **Non-Boolean example**: open sets of ℝ (connects to Lebesgue measure) |
| `Examples/PreciseVsImpreciseGrounded.lean` | **Decision theory example**: K&S representations → credal sets → EU vs maximin (0 sorry) |

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

### 2. Non-Boolean Examples ✅ RESOLVED

K&S claims to work on distributive lattices without complements.

**Demonstrated** in `Examples/`:
- `ThreeElementChain.lean`: Minimal 3-element chain (⊥ < mid < ⊤) with `Valuation`
- `OpenSets.lean`: Natural example using open sets of ℝ (topological, no complements)

Both files prove their respective lattices are NOT Boolean (no complement operation exists).

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
