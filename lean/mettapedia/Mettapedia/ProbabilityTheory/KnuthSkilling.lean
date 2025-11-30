/-
# Knuth-Skilling Foundations of Probability

Derive probability theory from lattice-theoretic principles following:
- Knuth & Skilling, "The Symmetrical Foundation of Measure, Probability and Quantum theories"

Key insight: Probability DERIVED from symmetry, not axiomatized!

## Module Structure

- **Basic.lean**: Core definitions (PlausibilitySpace, Valuation, KnuthSkillingAlgebra)
- **Counterexamples.lean**: Proofs that LinearOrder and Archimedean are necessary
- **Algebra.lean**: Basic operations (iterate_op, commutativity lemmas)
- **RepTheorem.lean**: The main representation theorem (Θ : α → ℝ construction)
- **CoxConsistency.lean**: Cox-Jaynes consistency conditions and probability rules
- **Independence.lean**: Independence definitions and XOR counterexample
-/

-- Import all submodules
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.CoxConsistency
import Mettapedia.ProbabilityTheory.KnuthSkilling.Independence
