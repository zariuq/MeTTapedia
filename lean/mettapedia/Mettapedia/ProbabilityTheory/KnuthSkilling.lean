/-
# Knuth-Skilling Foundations of Probability

Derive probability theory from lattice-theoretic principles following:
- Knuth & Skilling, "The Symmetrical Foundation of Measure, Probability and Quantum theories"

Key insight: Probability DERIVED from symmetry, not axiomatized!

## Module Structure

- **Basic.lean**: Core definitions (PlausibilitySpace, Valuation, KnuthSkillingAlgebra, KSSeparation)
- **Algebra.lean**: Basic operations (iterate_op, commutativity lemmas)
- **Separation/**: Separation machinery
  - `Separation/Derivation.lean`: work-in-progress proof sketch toward `KSSeparation` from K-S axioms
  - `Separation/SandwichSeparation.lean`: sandwich separation ⇒ commutativity + Archimedean-style consequences
- **RepresentationTheorem.lean**: **MAIN ENTRYPOINT** - Appendix A representation theorem (proof under `RepresentationTheorem/`)
- **ProductTheorem.lean**: Appendix B product theorem (product equation → exponential → product rule)

## Layer Structure

The formalization uses a two-layer design to avoid circular dependencies:
- **Layer A (RepresentationTheorem)**: Assumes `[KSSeparation α]`, proves representation + commutativity
- **Layer B (Separation/Derivation)**: Intended to provide `instance : KSSeparation α` (currently not completed)

## Countermodels (opt-in)
- Counterexamples clarifying which hypotheses are required live under
  `Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/`.
  They are intentionally not imported by the main proof chain; import them explicitly when needed.
-/

-- Import all submodules
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.GoertzelGroupFix
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Independence

-- Countermodels are parked under CounterModels/ and not imported by default.
