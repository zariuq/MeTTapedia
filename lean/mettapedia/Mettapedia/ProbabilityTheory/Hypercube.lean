/-
# Probability Theory Hypercube

A multi-axis hypercube framework for classifying probability theories based on their
operational semantics, algebraic structure, and choice of value space.

## Axes (high level)

The master list of axes is defined in `Mettapedia/ProbabilityTheory/Hypercube/Basic.lean`
and currently includes, among others:

- commutativity, distributivity, precision, orderAxis
- density, completeness, separation
- additivity, invertibility
- determinism, support, regularity
- independence

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
import Mettapedia.ProbabilityTheory.Hypercube.DensityAxisStory
import Mettapedia.ProbabilityTheory.Hypercube.NeighborTheories
import Mettapedia.ProbabilityTheory.Hypercube.NovelTheories
import Mettapedia.ProbabilityTheory.Hypercube.OperationalSemantics
import Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics
import Mettapedia.ProbabilityTheory.Hypercube.ScaleDichotomy
import Mettapedia.ProbabilityTheory.Hypercube.StayWellsConstruction
import Mettapedia.ProbabilityTheory.Hypercube.Taxonomy
import Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics
import Mettapedia.ProbabilityTheory.Hypercube.UnifiedTheory
import Mettapedia.ProbabilityTheory.Hypercube.OrthomodularVertex
import Mettapedia.ProbabilityTheory.Hypercube.WeaknessOrder
