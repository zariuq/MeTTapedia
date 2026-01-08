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

Note: `lake build` currently fails for some parts of the repo; see **Build Status** below for
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

nice -n 19 lake build Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
nice -n 19 lake build Mettapedia.ProbabilityTheory.Hypercube
```

## Build Status (last checked 2026-01-06)

- ✅ `lake build Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA` (0 sorries; linter warnings in `Mettapedia/ProbabilityTheory/KnuthSkilling/Algebra.lean`)
- ✅ `lake build Mettapedia.ProbabilityTheory.Hypercube` (0 sorries; see `Mettapedia/ProbabilityTheory/Hypercube/README.md`)
- ❌ `lake build` (full) currently fails in `Mettapedia/UniversalAI/TimeBoundedAIXI.lean`

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

## Current Status

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

### Probability Theory (`ProbabilityTheory/Basic.lean`)
- [ ] σ-algebras
- [ ] Probability measures (Kolmogorov axioms)
- [ ] Basic properties (monotonicity, complement, union bound)
- [ ] Finite additivity
- [ ] Conditional probability
- [ ] Independence
- [ ] Bayes' theorem
- [ ] Total probability

### Probability Theory Subprojects

- Knuth–Skilling Appendix A: `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA.lean` (see also `reports/ks_appendixA_formalization/ks_appendixA_formalization.pdf`)
- Probability Hypercube: `Mettapedia/ProbabilityTheory/Hypercube/README.md`
- Reflective Oracles (archived axiomatic attempt): `Mettapedia/UniversalAI/ReflectiveOracles/_archive/2025-12-29_axiom_based/README.md`

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

1. **No sorries**: Prefer `admit` or `axiom` with clear TODO comments
2. **Document sources**: Include references to textbooks and page numbers
3. **Test compilation**: Run `lake build` frequently
4. **Use hammer**: Try LeanHammer before writing manual proofs
5. **Follow style**: Match existing patterns in the codebase

## License

TBD
