/-
# Knuth-Skilling Foundations of Probability

Derive probability theory from lattice-theoretic principles following:
- Knuth & Skilling, "The Symmetrical Foundation of Measure, Probability and Quantum theories"

Key insight: Probability DERIVED from symmetry, not axiomatized!

## Two Formalizations of K&S Content

This formalization provides **two complete paths** to probability calculus, both from K&S's paper:

### Path 1: K&S Appendices A & B (Scalar Framework)
- **Additive/Main**: Appendix A (⊕ → additive order isomorphism Θ)
- **Multiplicative/Main**: Appendix B (⊗ → scaled multiplication via AdditiveOrderIsoRep)
- **Probability/ProbabilityDerivation**: Full probability calculus via `CoxConsistency` structure

### Path 2: K&S Section 7 (Lattice/Conditional Framework)
- **Multiplicative/Proofs/Direct/DirectProof.lean**: Direct proof of Appendix B (same result, different technique)
- **Probability/ConditionalProbability/Basic.lean**: K&S Section 7 via `Bivaluation` + `ChainingAssociativity`

**Important clarifications**:
- Both paths formalize K&S's paper - they're not competing approaches (like Cox vs K&S)
- `Multiplicative/Proofs/Direct/DirectProof.lean` is NOT "Aczél's derivation of probability" - it's just a direct algebraic
  proof of K&S's Appendix B theorem that avoids "apply Appendix A again"
- `Probability/ProbabilityDerivation` and `Probability/ConditionalProbability/Basic` formalize DIFFERENT K&S content:
  - `Probability/ProbabilityDerivation`: scalar-valued plausibility functions (`CoxConsistency`)
  - `Probability/ConditionalProbability/Basic`: conditional plausibility on lattice pairs (`Bivaluation`)
- Both derive Bayes' theorem and product rules, but from different K&S axiom structures

## Canonical Interface (Use This!)

**`ProbabilityCalculus.lean`** provides the single source of truth for end-results:
- `ProbabilityCalculus.sumRule`: P(A ∨ B) = P(A) + P(B) for disjoint events
- `ProbabilityCalculus.productRule`: P(A ∧ B) = P(A|B) · P(B)
- `ProbabilityCalculus.bayesTheorem`: P(A|B) · P(B) = P(B|A) · P(A)
- `ProbabilityCalculus.complementRule`: P(B) = 1 - P(A) for complements

Import `ProbabilityCalculus` for these canonical theorems. Don't use the
path-specific versions in `Probability/ProbabilityDerivation` or `Probability/ConditionalProbability/Basic` directly.

## Module Structure

- **Core/Basic.lean**: Core definitions (PlausibilitySpace, Valuation, KnuthSkillingAlgebra, KSSeparation)
- **Core/Algebra.lean**: Basic operations (iterate_op, commutativity lemmas)
- **Additive/Axioms/**: Separation machinery (sandwich separation, anomalous pairs)
- **Additive/Main.lean**: **MAIN ENTRYPOINT** - Appendix A representation theorem
  - `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean`: canonical Hölder path
  - `Additive/Proofs/GridInduction/`: grid/induction path (globalization + core)
  - `Additive/Proofs/DirectCuts/`: Dedekind cuts alternative
- **Multiplicative/Main.lean**: Appendix B product theorem (product equation → exponential → product rule)
  - `Multiplicative/Proofs/Direct/DirectProof.lean`: **Alternative path** (direct derivation)
- **Probability/ProbabilityDerivation.lean**: K&S's full derivation (Appendix A → B → probability calculus)
- **Probability/ProbabilityCalculus.lean**: **CANONICAL INTERFACE** - single source of truth for end-results
- **Variational.lean**: Appendix C variational theorem (Cauchy/log solution; Lagrange-multiplier motivation)
- **Information/Divergence.lean**: K&S Section 6 divergence (per-atom and finite-vector forms)
- **Probability/ConditionalProbability/**: K&S Section 7 on conditional probability (uses alternative path)
  - `Probability/ConditionalProbability/Basic.lean`: Axiom 5 (Chaining Associativity), chain-product rule, Bayes' theorem
- **Information/InformationEntropy.lean**: K&S Section 8 information/entropy (KL divergence, Shannon entropy, basic Shannon properties)

## Layer Structure

The formalization uses a two-layer design to avoid circular dependencies:
- **Layer A (Additive/Proofs/*)**: Assumes `[KSSeparation α]`, proves representation + commutativity
- **Layer B (_archive/Separation/Derivation.lean)**: Intended to provide `instance : KSSeparation α` (currently not completed)

## Countermodels (opt-in)
- Counterexamples clarifying which hypotheses are required live under
  `Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Counterexamples/`.
  They are intentionally not imported by the main proof chain; import them explicitly when needed.
-/

-- Import all submodules
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative
import Mettapedia.ProbabilityTheory.KnuthSkilling.Variational.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.DivergenceMathlib
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnson
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonKL
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonBridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonInference
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonObjective
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonConstraints
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonPathC
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonAppendixKL
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropyMathlib
import Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges.GoertzelGroupFix
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityDerivation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityCalculus
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.Independence
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ConditionalProbability
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.SymmetricalFoundation

-- Countermodels are parked under CounterModels/ and not imported by default.
