/-
# Knuth-Skilling Foundations of Probability

Derive probability theory from lattice-theoretic principles following:
- Knuth & Skilling, "The Symmetrical Foundation of Measure, Probability and Quantum theories"

Key insight: Probability DERIVED from symmetry, not axiomatized!

## Two Formalizations of K&S Content

This formalization provides **two complete paths** to probability calculus, both from K&S's paper:

### Path 1: K&S Appendices A & B (Scalar Framework)
- **RepresentationTheorem**: Appendix A (⊕ → additive order isomorphism Θ)
- **ProductTheorem.Main**: Appendix B (⊗ → scaled multiplication via AdditiveOrderIsoRep)
- **ProbabilityDerivation**: Full probability calculus via `CoxConsistency` structure

### Path 2: K&S Section 7 (Lattice/Conditional Framework)
- **ProductTheorem.Alternative.DirectProof**: Direct proof of Appendix B (same result, different technique)
- **ConditionalProbability.Basic**: K&S Section 7 via `Bivaluation` + `ChainingAssociativity`

**Important clarifications**:
- Both paths formalize K&S's paper - they're not competing approaches (like Cox vs K&S)
- `DirectProof.lean` is NOT "Aczél's derivation of probability" - it's just a direct algebraic
  proof of K&S's Appendix B theorem that avoids "apply Appendix A again"
- `ProbabilityDerivation` and `ConditionalProbability/Basic` formalize DIFFERENT K&S content:
  - `ProbabilityDerivation`: scalar-valued plausibility functions (`CoxConsistency`)
  - `ConditionalProbability/Basic`: conditional plausibility on lattice pairs (`Bivaluation`)
- Both derive Bayes' theorem and product rules, but from different K&S axiom structures

## Canonical Interface (Use This!)

**`ProbabilityCalculus.lean`** provides the single source of truth for end-results:
- `ProbabilityCalculus.sumRule`: P(A ∨ B) = P(A) + P(B) for disjoint events
- `ProbabilityCalculus.productRule`: P(A ∧ B) = P(A|B) · P(B)
- `ProbabilityCalculus.bayesTheorem`: P(A|B) · P(B) = P(B|A) · P(A)
- `ProbabilityCalculus.complementRule`: P(B) = 1 - P(A) for complements

Import `ProbabilityCalculus` for these canonical theorems. Don't use the
path-specific versions in `ProbabilityDerivation` or `ConditionalProbability/Basic` directly.

## Module Structure

- **Basic.lean**: Core definitions (PlausibilitySpace, Valuation, KnuthSkillingAlgebra, KSSeparation)
- **Algebra.lean**: Basic operations (iterate_op, commutativity lemmas)
- **Separation/**: Separation machinery
  - `Separation/Derivation.lean`: work-in-progress proof sketch toward `KSSeparation` from K-S axioms
  - `Separation/SandwichSeparation.lean`: sandwich separation ⇒ commutativity + Archimedean-style consequences
- **RepresentationTheorem.lean**: **MAIN ENTRYPOINT** - Appendix A representation theorem (proof under `RepresentationTheorem/`)
- **ProductTheorem.lean**: Appendix B product theorem (product equation → exponential → product rule)
  - `ProductTheorem/Main.lean`: **K&S path** (uses AdditiveOrderIsoRep from Appendix A)
  - `ProductTheorem/Alternative/DirectProof.lean`: **Alternative path** (direct derivation)
- **ProbabilityDerivation.lean**: K&S's full derivation (Appendix A → B → probability calculus)
- **ProbabilityCalculus.lean**: **CANONICAL INTERFACE** - single source of truth for end-results
- **VariationalTheorem.lean**: Appendix C variational theorem (Cauchy/log solution; Lagrange-multiplier motivation)
- **Divergence.lean**: K&S Section 6 divergence (per-atom and finite-vector forms)
- **ConditionalProbability/**: K&S Section 7 on conditional probability (uses alternative path)
  - `ConditionalProbability/Basic.lean`: Axiom 5 (Chaining Associativity), chain-product rule, Bayes' theorem
- **InformationEntropy.lean**: K&S Section 8 information/entropy (KL divergence, Shannon entropy, basic Shannon properties)

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
import Mettapedia.ProbabilityTheory.KnuthSkilling.VariationalTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.Divergence
import Mettapedia.ProbabilityTheory.KnuthSkilling.DivergenceMathlib
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonKL
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonBridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonInference
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonConstraints
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonPathC
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixKL
import Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropyMathlib
import Mettapedia.ProbabilityTheory.KnuthSkilling.GoertzelGroupFix
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityCalculus
import Mettapedia.ProbabilityTheory.KnuthSkilling.Independence
import Mettapedia.ProbabilityTheory.KnuthSkilling.ConditionalProbability
import Mettapedia.ProbabilityTheory.KnuthSkilling.SymmetricalFoundation

-- Countermodels are parked under CounterModels/ and not imported by default.
