/-
# Probability Theory Hypercube

A 5-axis hypercube framework for classifying probability theories based on their
operational semantics and structural properties.

## Axes

1. **Commutativity**: commutative vs non-commutative operations
2. **Distributivity**: Boolean vs orthomodular vs general lattices
3. **Precision**: precise vs imprecise (interval) valuations
4. **Ordering**: linear vs partial order
5. **Additivity**: additive vs subadditive measures

## Key Theories as Vertices

- **Kolmogorov**: commutative, Boolean, precise, linear, additive
- **Dempster-Shafer**: commutative, Boolean, imprecise, linear, subadditive
- **Knuth-Skilling**: commutative, distributive, precise, linear, additive
- **Quantum**: non-commutative, orthomodular, precise, linear, additive

## Novel Theories

Three unexplored vertices with potential applications:
- **Imprecise K&S**: K&S with interval-valued plausibilities
- **Quantum D-S**: D-S on orthomodular lattices
- **Partial Classical**: Classical probability with partial ordering
-/

import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.Hypercube.CentralQuestionCounterexample
import Mettapedia.ProbabilityTheory.Hypercube.NeighborTheories
import Mettapedia.ProbabilityTheory.Hypercube.NovelTheories
import Mettapedia.ProbabilityTheory.Hypercube.OperationalSemantics
import Mettapedia.ProbabilityTheory.Hypercube.StayWellsConstruction
import Mettapedia.ProbabilityTheory.Hypercube.Taxonomy
import Mettapedia.ProbabilityTheory.Hypercube.UnifiedTheory
