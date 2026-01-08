/-
# Knuth-Skilling Foundations of Probability

Derive probability theory from lattice-theoretic principles following:
- Knuth & Skilling, "The Symmetrical Foundation of Measure, Probability and Quantum theories"

Key insight: Probability DERIVED from symmetry, not axiomatized!

## Module Structure

- **Basic.lean**: Core definitions (PlausibilitySpace, Valuation, KnuthSkillingAlgebra, KSSeparation)
- **Algebra.lean**: Basic operations (iterate_op, commutativity lemmas)
- **SeparationProof.lean**: Work-in-progress proof sketch toward `KSSeparation` from K-S axioms
- **RepTheorem.lean**: Representation theorem (assumes `[KSSeparation α]`)
- **AppendixA.lean**: **MAIN FILE** - K&S representation theorem proof
  - `Theta_eq_swap`: Θ(x⊕y) = Θ(y⊕x)
  - `op_comm_of_KS`: Commutativity x⊕y = y⊕x
  - `KS_representation_theorem`: Full representation (strict mono + additive)

## Layer Structure

The formalization uses a two-layer design to avoid circular dependencies:
- **Layer A (RepTheorem)**: Assumes `[KSSeparation α]`, proves representation
- **Layer B (SeparationProof)**: Intended to provide `instance : KSSeparation α` (currently not completed)

## Countermodels (opt-in)
- See `CounterModels/` for FreeMonoid2 constructions and no-go theorems. These are
  intentionally not imported by the main proof chain.

## Archived (not imported)
- `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/Counterexamples.lean`: Proofs that LinearOrder and Archimedean are necessary
- `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/legacy/`: historical snapshots (may not compile)
  - `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/legacy/RepTheorem_before_layering.lean`
  - `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/legacy/RepTheorem_backup_before_refactor.lean`
  - `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/legacy/SeparationProof_backup_before_filling.lean`
  - `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/legacy/NoGo_BACKUP.lean`
  - `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/legacy/KnuthSkilling_lean_gemini_attempt.bak`
- `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/ProofDraft.lean`: archived monolithic Appendix A draft
- `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/_archive/AppendixA_experimental_20251201.lean`: older experimental Appendix A attempt
- `Mettapedia/ProbabilityTheory/_archive/AssociativityTheorem_Aczel_backup.lean`: Aczél-style exploratory file
-/

-- Import all submodules
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.SeparationProof
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
import Mettapedia.ProbabilityTheory.KnuthSkilling.GoertzelGroupFix
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Independence

-- Countermodels are parked under CounterModels/ and not imported by default.
