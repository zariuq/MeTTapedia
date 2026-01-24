# Mettapedia - Encyclopedia of Formalized Mathematics

A comprehensive formalization of mathematics across multiple domains, inspired by Wikipedia's breadth and Metamath's rigor.

## Project Structure

```
Mettapedia/
├── GraphTheory/         # Graph theory (Bondy & Murty, Diestel)
├── ProbabilityTheory/   # Probability theory (Kolmogorov, Billingsley, Durrett)
├── SetTheory/           # Set theory foundations
├── Combinatorics/       # Combinatorial mathematics
├── NumberTheory/        # Number theory
├── Topology/            # Topological spaces
├── Algebra/             # Algebraic structures
├── Logic/               # Mathematical logic
└── Analysis/            # Real and complex analysis
```

## Tools

- **Lean 4.25.0**: Theorem prover
- **LeanHammer**: ATP integration with Zipperposition prover
- **Mathlib v4.25.0**: Lean's standard math library

## Setup

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Git

### Installation

```bash
# Clone the repository (if not already done)
git clone <repository-url> mettapedia
cd mettapedia

# Update dependencies (downloads LeanHammer, mathlib, and cache)
lake update

# Get precompiled mathlib cache (avoids hours of compilation)
lake exe cache get

# Build the project
lake build
```

Note: this repository contains multiple subprojects; see **Build Status** below for
known-good targets.

## Development Workflow

### Building

```bash
# Build with limited parallelism (easier on system resources)
export LAKE_JOBS=3
nice -n 19 lake build
```

### Suggested Build Targets

```bash
cd lean-projects/mettapedia
export LAKE_JOBS=3
ulimit -Sv 6291456

nice -n 19 lake build Mettapedia.ProbabilityTheory.KnuthSkilling.FoundationsOfInference
nice -n 19 lake build Mettapedia.ProbabilityTheory.Hypercube
```

## Build Status (last checked 2026-01-24)

- ✅ `lake build Mettapedia.ProbabilityTheory.KnuthSkilling.FoundationsOfInference` — clean
- ✅ `lake build Mettapedia.ProbabilityTheory.Hypercube` — clean
- ⚠️ `lake build Mettapedia` — builds, but unverified modules have gaps (e.g. `GraphTheory/`, `UniversalAI/`)

### Using LeanHammer

LeanHammer provides automated theorem proving via the Zipperposition ATP:

```lean
import Hammer

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  hammer
```

See [LeanHammer documentation](https://github.com/JOSHCLUNE/LeanHammer) for more details.

### Cache Management

```bash
# Download precompiled mathlib (do this after lake update)
lake exe cache get

# Clean build artifacts (if needed)
lake clean

# Check cache location and size
du -sh ~/.cache/mathlib
```

## Knuth-Skilling Formalization (Flagship Project)

The **Knuth-Skilling Foundations of Inference** formalization is the flagship subproject,
with the core theorems (Appendices A, B, C) **fully verified**.

### Papers

| Paper | Description |
|-------|-------------|
| `paper/ks-formalization-walkthrough.pdf` | **Formalization Walkthrough**: Step-by-step guide through the Lean code |
| `paper/ks-foundations-math.pdf` | **Foundations of Probability (Math Focus)**: Compares K&S with Cox, Kolmogorov, de Finetti |
| `paper/ks-foi-review.pdf` | **FOI Review**: Constructive review of K&S (2012), noting gaps found and resolved |

### Verification Status

| Component | Status | Notes |
|-----------|--------|-------|
| **K&S Appendix A** (Representation Theorem) | ✅ Verified | NAP → additive embedding Θ : α → ℝ |
| **K&S Appendix B** (Product Theorem) | ✅ Verified | Tensor = scaled multiplication |
| **K&S Appendix C** (Variational Theorem) | ✅ Verified | Cauchy/log solution |
| **Probability Calculus** | ✅ Verified | Sum rule, product rule, Bayes derived |
| **Shore-Johnson** | ✅ Verified | Import explicitly via `ShoreJohnson/Main.lean` |
| **Cox Theorem** | 🔬 Experimental | Not on main import path |

## Other Subprojects (Not Formally Verified)

The following subprojects exist as **skeletons** or **works-in-progress** and have
**not** been formally verified:

### Graph Theory (`GraphTheory/Basic.lean`)
- [ ] Chapter 1: Graphs and Subgraphs
- [ ] Chapter 2: Trees
- [ ] Chapter 3: Connectivity
- [ ] Chapter 4: Euler Tours and Hamilton Cycles
- [ ] Chapter 5: Matchings
- [ ] Chapter 6: Tree-Search Algorithms (DFS/BFS)
- [ ] Chapter 7: Flows in Networks
- [ ] Chapter 10: Vertex Colourings
- [ ] Chapter 12: Edge Colourings
- [ ] Chapter 14: Random Graphs
- [ ] Chapter 16: Ramsey Theory
- [ ] Chapter 17: Planar Graphs

### Probability Theory (`ProbabilityTheory/Basic.lean`) — Skeleton Only
- [ ] σ-algebras
- [ ] Probability measures (Kolmogorov axioms)
- [ ] Basic properties (monotonicity, complement, union bound)
- [ ] Finite additivity
- [ ] Conditional probability
- [ ] Independence
- [ ] Bayes' theorem
- [ ] Total probability

> **Note**: The Kolmogorov-style skeleton above is **not verified**. For verified
> probability foundations, see the **K&S formalization** which *derives* these
> rules from symmetry principles rather than axiomatizing them.

### Probability Theory Subprojects

| Subproject | Status | Location |
|------------|--------|----------|
| **Knuth-Skilling FOI** | ✅ Verified | `ProbabilityTheory/KnuthSkilling/README.md` |
| Probability Hypercube | ✅ Verified | `ProbabilityTheory/Hypercube/README.md` |
| Cox Theorem | 🔬 Experimental | `ProbabilityTheory/Cox/` |

## Knuth-Skilling Directory Structure (FOI Formalization)

**Primary Assumption**: The canonical proof path uses **`NoAnomalousPairs`** (NAP) from the 1950s
ordered-semigroup literature (Alimov 1950, Fuchs 1963). NAP is identity-free and strictly weaker
than K&S's `KSSeparation`. See `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean`.

**Stable entrypoints:**
- `Mettapedia/ProbabilityTheory/KnuthSkilling/FoundationsOfInference.lean` — FOI core
- `Mettapedia/InformationTheory/ShannonEntropy/Main.lean` — Shannon/Faddeev entrypoint

```
Mettapedia/ProbabilityTheory/KnuthSkilling/
├── FoundationsOfInference.lean    # Curated FOI entrypoint (Core + Appendix A/B/C + Probability + Information)
├── Core.lean                      # Stable facade re-exporting core hierarchy + main theorems
├── Core/
│   ├── Basic.lean                 # Axiom hierarchy: KSSemigroupBase → KnuthSkillingMonoidBase → KnuthSkillingAlgebraBase
│   ├── Algebra.lean               # Iteration + separation axioms (KSSeparation*)
│   ├── Interfaces.lean            # Import guide / main outputs documentation
│   ├── SymmetricalFoundation.lean # K&S quantum/2D-algebra (Section 4)
│   └── ScaleCompleteness.lean     # σ-completeness axioms + σ-additivity theorem
│
├── Additive/
│   ├── Main.lean                  # Appendix A entrypoint (typeclass interface + instances)
│   ├── Representation.lean        # Appendix A representation interfaces (identity-free default)
│   ├── Axioms/
│   │   ├── AnomalousPairs.lean
│   │   ├── SandwichSeparation.lean   # Archimedean + commutativity from KSSeparation
│   │   └── OpIsAddition.lean
│   ├── Proofs/
│   │   ├── OrderedSemigroupEmbedding/
│   │   │   └── HolderEmbedding.lean  # Canonical: NoAnomalousPairs → additive Θ to ℝ
│   │   ├── DirectCuts/               # Dedekind cuts alternative
│   │   └── GridInduction/            # K&S-style globalization (heavy; opt-in)
│   └── Counterexamples/              # Appendix A-specific countermodels
│
├── Multiplicative.lean               # Appendix B entrypoint (imports both proof paths)
├── Multiplicative/
│   ├── Main.lean                     # K&S Appendix B pipeline
│   ├── ScaledMultRep.lean            # Output interface: tensor = (x*y)/C
│   ├── Basic.lean                    # Derives product equation from distributivity
│   ├── FunctionalEquation.lean       # Product equation solver
│   └── Proofs/Direct/DirectProof.lean  # Alternative proof path (bypasses Appendix A)
│
├── Variational/
│   └── Main.lean                     # Appendix C variational theorem → entropy form
│
├── Probability/
│   ├── ProbabilityDerivation.lean    # FOI main derivation chain
│   ├── ProbabilityCalculus.lean      # End-results: sum/product/Bayes/complement
│   └── ConditionalProbability/Basic.lean  # K&S Section 7 lattice path
│
├── Information/
│   ├── Main.lean                     # Sections 6+8 entrypoint
│   ├── Divergence.lean
│   └── InformationEntropy.lean       # KL + Shannon on ProbDist
│
├── Bridges/
│   └── MathlibProbability.lean       # Bridge to mathlib Measure/ProbabilityMeasure
│
├── Counterexamples/                  # General KS counterexamples
├── Examples/                         # Worked examples (CoinDie, PreciseVsImprecise)
├── Literature/                       # Bibliographic references
└── ShoreJohnson/                     # First-class; import explicitly

Mettapedia/InformationTheory/
└── ShannonEntropy/
    ├── Main.lean                     # Shannon/Faddeev entrypoint
    └── Faddeev.lean                  # Axiomatic entropy derivation
```

### Import Rules

| Goal | Import |
|------|--------|
| FOI core (no WIP) | `KnuthSkilling/FoundationsOfInference.lean` |
| Appendix A (sum-side) | `KnuthSkilling/Additive/Main.lean` |
| Appendix B (product-side) | `KnuthSkilling/Multiplicative.lean` |
| Appendix C (variational) | `KnuthSkilling/Variational/Main.lean` |
| Probability end-results | `KnuthSkilling/Probability/ProbabilityCalculus.lean` |
| σ-additivity extension | `KnuthSkilling/Core/ScaleCompleteness.lean` |
| Shore-Johnson (first-class) | `KnuthSkilling/ShoreJohnson/Main.lean` |
| **Experimental** | `Cox/` |

## References

### Graph Theory
- Bondy & Murty, "Graph Theory" (GTM 244, 2007)
- Diestel, "Graph Theory" (5th edition)

### Probability Theory
- Kolmogorov, "Foundations of the Theory of Probability" (1933)
- Billingsley, "Probability and Measure" (3rd edition)
- Durrett, "Probability: Theory and Examples" (5th edition)

## Comparison with Megalodon

This project runs in parallel with the [Megalodon formalization](../megalodon/) of the same material:

| Feature | Mettapedia (Lean 4) | Megalodon |
|---------|---------------------|-----------|
| **Prover** | Lean 4.25.0 | Megalodon |
| **Foundation** | CIC (Calculus of Inductive Constructions) | Church-encoded HOL + ZF |
| **Library** | Mathlib (~800k LOC) | Egal theory |
| **ATP** | LeanHammer (Zipperposition) | E-prover, Vampire |
| **Tactic language** | Lean tactics | Megalodon proof terms |
| **Verification** | Interactive + ATP | Interactive + ATP |

The goal is to compare formalization approaches and determine which system is more suitable for large-scale mathematical formalization.

## Contributing

When adding new definitions or theorems:

1. **Avoid `sorry`**: When unavoidable, use an explicit `sorry` with a detailed TODO/proof strategy (do not replace proofs with “Prop-as-proof” placeholders)
2. **No axioms**: Do not introduce `axiom`/unjustified assumptions; keep foundations explicit
3. **Document sources**: Include references to textbooks and page numbers
4. **Test compilation**: Run `lake build` frequently
5. **Follow style**: Match existing patterns in the codebase

## License

TBD
