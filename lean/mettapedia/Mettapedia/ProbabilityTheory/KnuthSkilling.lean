/-
# Knuth-Skilling Foundations of Probability

Derive probability theory from lattice-theoretic principles following:
- Knuth & Skilling, "The Symmetrical Foundation of Measure, Probability and Quantum theories"

Key insight: Probability DERIVED from symmetry, not axiomatized!

## Module Structure

- **Basic.lean**: Core definitions (PlausibilitySpace, Valuation, KnuthSkillingAlgebra, KSSeparation)
- **Algebra.lean**: Basic operations (iterate_op, commutativity lemmas)
- **SeparationProof.lean**: Proof that KSSeparation holds from K-S axioms
- **RepTheorem.lean**: Representation theorem (assumes KSSeparation)
- **AppendixA.lean**: **MAIN FILE** - K&S representation theorem proof
  - `Theta_eq_swap`: Θ(x⊕y) = Θ(y⊕x)
  - `op_comm_of_KS`: Commutativity x⊕y = y⊕x
  - `KS_representation_theorem`: Full representation (strict mono + additive)
- **ProbabilityDerivation.lean**: Probability calculus (Sum/Product rules) derived from K&S
- **Independence.lean**: Independence definitions and XOR counterexample

## Layer Structure

The formalization uses a two-layer design to avoid circular dependencies:
- **Layer A (RepTheorem)**: Assumes `[KSSeparation α]`, proves representation
- **Layer B (SeparationProof)**: Proves `instance : KSSeparation α` from K-S axioms

## Archived (in _archive/)
- **Counterexamples.lean**: Proofs that LinearOrder and Archimedean are necessary
-/

-- Import all submodules
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.SeparationProof  -- Provides instance : KSSeparation α
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Independence
-- Counterexamples and no-go theorems
import Mettapedia.ProbabilityTheory.KnuthSkilling.CounterExamples
import Mettapedia.ProbabilityTheory.KnuthSkilling.NoGo
