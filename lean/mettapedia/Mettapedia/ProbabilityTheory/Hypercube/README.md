# Probability Hypercube Formalization

Lean 4 formalization of the **Probability Hypercube** framework, which unifies multiple probability theories through lattice-theoretic axiomatizations.

## Overview

The probability hypercube is a geometric framework for understanding relationships between different probability theories. Each vertex represents a distinct probability theory characterized by which lattice axioms it satisfies:

- **Kolmogorov (Classical)**: Boolean algebra (distributive orthomodular lattice)
- **Dempster-Shafer**: Non-distributive, uses belief functions on power sets
- **Fuzzy Probability**: Different handling of conjunction
- **Quantum Probability**: Orthomodular lattice (non-distributive)
- **Imprecise Probability**: Interval-valued

**Key Insight**: The presence or absence of **commutativity** in orthomodular lattices determines the classical/quantum boundary. Commuting elements generate Boolean (classical) sublattices within the quantum structure.

## Primary References

### Knuth-Skilling Framework
- **Knuth, K. & Skilling, J. (2012)**. "Foundations of Inference." *Axioms* 1(1), 38-73.
  - [https://doi.org/10.3390/axioms1010038](https://doi.org/10.3390/axioms1010038)
  - Derives probability calculus from lattice symmetries without continuity assumptions

- **Skilling, J. & Knuth, K. (2019)**. "A Symmetrical Foundation for Quantum Theory." *AIP Conference Proceedings* 2131, 020003.
  - Extension to quantum theory via orthomodular lattices

### Orthomodular Lattice Theory
- **Foulis, D.J. (1962)**. "A note on orthomodular lattices." *Portugaliae Math.* 21(1), 65-72.
  - Proves commuting elements generate distributive sublattices

- **Kalmbach, G. (1983)**. *Orthomodular Lattices*. Academic Press.
  - Standard reference for OML theory, exchange property

- **Beran, L. (1985)**. *Orthomodular Lattices, Algebraic Approach*. D. Reidel.
  - Symmetry of commutativity, detailed proofs

### Dempster-Shafer Theory
- **Dempster, A.P. (1967)**. "Upper and lower probabilities induced by a multivalued mapping." *Ann. Math. Statist.* 38(2), 325-339.

- **Shafer, G. (1976)**. *A Mathematical Theory of Evidence*. Princeton University Press.

- **Smets, P. & Kennes, R. (1994)**. "The transferable belief model." *Artificial Intelligence* 66(2), 191-234.
  - Generalization to arbitrary lattices

## File Organization

### Core Theory Files

#### `NovelTheories.lean` (43 KB)
Orthomodular lattice foundations and quantum probability structures:
- **`OrthomodularLattice` class**: Axiomatization with orthomodular law, de Morgan laws, complementation
- **Orthogonality → Disjointness** `inf_eq_bot_of_le_compl`: `a ≤ bᶜ → a ⊓ b = ⊥`
- **Important Note on Disjointness vs Orthogonality**: Documents that in general OML, `a ⊓ b = ⊥` does NOT imply `a ≤ bᶜ` (with Hilbert space counterexample)
- **Commutativity Predicate** `commutes`: Defines when elements behave classically
- **`QuantumMassFunction`**: Mass functions on finite orthomodular lattices
- **`QuantumState`**: Probability measures on OMLs (orthoadditive, normalized)

**Key Mathematical Insight**:
The "quasi-distributivity" property `(a ⊔ b) ⊓ aᶜ ≤ b` is **FALSE** in general OML!
Counterexample in Hilbert lattice of ℂ²: `a = span{(1,0)}, b = span{(1,1)}` gives
`(a ⊔ b) ⊓ aᶜ = span{(0,1)} ⊈ span{(1,1)} = b`. This asymmetry is fundamental to quantum logic.

#### `NeighborTheories.lean` (52 KB)
Commutativity theory and the classical/quantum boundary:
- **Commutativity Lemmas**:
  - `commutes_symm`: Symmetry of commutativity
  - `commutes_compl`: Preservation under complement
  - `commutes_self`, `commutes_top`, `commutes_bot`: Basic cases
  - `commutes_of_le_compl`: Orthogonality implies commutativity
- **Exchange Property (Bidirectional)**:
  - `exchange_of_commutes`: `a C b → a ⊓ (aᶜ ⊔ b) = a ⊓ b`
  - `commutes_of_exchange`: Converse direction
  - `commutes_iff_exchange`: Full characterization
- **Foulis-Holland Theorem (Complete!)**:
  - `commutes_inf`: `a C b ∧ a C c → a C (b ⊓ c)`
  - `commutes_sup`: `a C b ∧ a C c → a C (b ⊔ c)`
- **Quantum Logic Note**: Disjunctive syllogism does *not* hold in general OMLs; `NeighborTheories.lean`
  deliberately avoids an unconditional `oml_disjunctive_syllogism` lemma.
- **Orthocomplement Uniqueness**: recorded as a statement `oml_orthocomplement_unique_statement`
  (no proof yet; needs the correct compatibility hypotheses).

**Novel Contributions**:
- **Complete Foulis-Holland theorem**: Commuting elements are closed under ⊓ and ⊔
- Bidirectional exchange characterization (first rigorous formalization)
- De Morgan duality proof for `commutes_sup` via `commutes_inf`

#### `Basic.lean` (46 KB)
Classical Dempster-Shafer theory on power sets:
- **`MassFunction`**: Basic mass assignment on `Finset Ω`
- **Belief Functions**: `belief`, `plausibility`, `commonality`
- **Dempster's Rule**: `dempsterCombine` with normalization
- **Key Theorems**:
  - Belief/plausibility duality
  - Möbius inversion formulas
  - Dempster's rule properties

#### `Taxonomy.lean` (17 KB)
Classification of probability theories by lattice axioms:
- Defines `ProbabilityTheoryClass` structure
- Classifies Kolmogorov, Dempster-Shafer, Quantum, Fuzzy theories
- Documents which axioms each theory satisfies

#### `UnifiedTheory.lean` (10 KB)
Abstract framework for lattice-based probability:
- Generic `LatticeProbability` structure
- Unifies classical, quantum, and imprecise probability
- Shows Kolmogorov as special case

### Advanced Constructions

#### `StayWellsConstruction.lean` (19 KB)
Stey-Wells embedding of classical D-S into quantum:
- Embeds `Finset Ω` into orthomodular lattices
- Preserves belief function semantics
- Shows classical D-S as quantum special case

#### `OperationalSemantics.lean` (12 KB)
Dynamic epistemic update rules:
- Bayesian conditioning
- Jeffrey's rule
- Dempster-Shafer update

### Examples and Counterexamples

#### `CentralQuestionCounterexample.lean` (1.3 KB)
Minimal counterexample showing `quantaleAnd` ≠ lattice meet in general

## Key Theoretical Results

### 1. Disjointness vs Orthogonality (Important Discovery!)
In Boolean algebras: `a ⊓ b = ⊥ ↔ a ≤ bᶜ` (disjointness = orthogonality)

**In general OML: `a ≤ bᶜ → a ⊓ b = ⊥` but NOT the converse!**

The "quasi-distributivity" property `(a ⊔ b) ⊓ aᶜ ≤ b` is **FALSE** in general OML.
Counterexample in ℂ²: `a = span{(1,0)}, b = span{(1,1)}` gives `(a ⊔ b) ⊓ aᶜ = span{(0,1)} ⊈ b`.

This asymmetry is fundamental to quantum logic and distinguishes it from classical logic.

### 2. Exchange Property (Bidirectional Characterization)
**Theorem** `commutes_iff_exchange`: `a C b ↔ a ⊓ (aᶜ ⊔ b) = a ⊓ b`

From Kalmbach (1983). This is THE key property distinguishing commuting (classical-like) from non-commuting (quantum) pairs of events. We proved both directions rigorously.

### 3. Foulis-Holland Theorem (Complete!)
**Theorem** `commutes_inf`: If `a C b` and `a C c`, then `a C (b ⊓ c)`
**Theorem** `commutes_sup`: If `a C b` and `a C c`, then `a C (b ⊔ c)`

Commuting elements are closed under lattice operations. Distributivity for commuting triples is
recorded as `commuting_distributive` (statement; proof TODO). This is part of the standard story
of why classical probability emerges from quantum probability when measuring compatible observables.

**Proof Strategy**:
- For `commutes_inf`: Use exchange characterization. Since `b ⊓ c ≤ b, c`, the exchange bounds combine to give `a ⊓ (aᶜ ⊔ (b ⊓ c)) = a ⊓ b ⊓ c`.
- For `commutes_sup`: De Morgan duality. `b ⊔ c = (bᶜ ⊓ cᶜ)ᶜ`, apply `commutes_inf` to complements, then `commutes_compl`.

## Building the Formalization

```bash
cd lean-projects/mettapedia
export LAKE_JOBS=3
ulimit -Sv 6291456
nice -n 19 lake build Mettapedia.ProbabilityTheory.Hypercube
```

**Dependencies**:
- Lean 4.25.0
- Mathlib v4.25.0

## Current Status

### Build (last checked 2026-01-06)

`lake build Mettapedia.ProbabilityTheory.Hypercube` succeeds with **0** `sorry`s.

### Completed (sorry-free)
- ✅ Orthomodular lattice axiomatization + basic quantum structures (`NovelTheories.lean`)
- ✅ Classical Dempster–Shafer on `Finset Ω` (`Basic.lean`)
- ✅ Neighbor investigations (`NeighborTheories.lean`) are `sorry`-free (open items are explicit `Prop` statements)
- ✅ Hypercube taxonomy order (`Taxonomy.lean`) is `sorry`-free

### Corrected Misconceptions
- ❌ ~~OML fundamental lemma (quasi-distributivity)~~ - **FALSE in general OML!**
- ❌ ~~Bidirectional orthogonality criterion~~ - Only forward direction holds

### In Progress
- ⚠️ `commuting_distributive`: distributivity for commuting triples (Kalmbach/Beran; statement recorded, proof TODO)
- ⚠️ Infinite lattice case for quantum beliefs (requires measure theory)

## Relationship to Other Formalizations

### Knuth-Skilling Appendix A (`../KnuthSkilling/`)
Parallel formalization of K-S Appendix A (representation theorem):
- Different focus: derives real-valued probability from abstract lattice symmetries
- This directory: concrete instantiations (classical, quantum, D-S)

### Common Foundations (`../Common/`)
Shared infrastructure:
- `Lattice.lean`: Basic lattice utilities
- `Valuation.lean`: Abstract valuation functions
- `LatticeValuation.lean`: Normalized valuations, orthoadditive valuations
- `LatticeSummation.lean`: Summation over lattice principal ideals
- `MobiusFunction.lean`: Möbius inversion on lattices

### Belief Functions (`../BeliefFunctions/`)
Extended Dempster-Shafer theory:
- `Basic.lean`: Full D-S calculus with combination rules
- Bridges to hypercube formalization

## Design Philosophy

1. **No `sorry`**: open research lemmas are explicitly recorded as `Prop` statements (not placeholder proofs)
2. **Source Attribution**: Every theorem cites original papers
3. **Modular Structure**: Each theory in separate file
4. **Computational Content**: Definitions executable on finite lattices
5. **Mathlib Integration**: Uses standard mathlib lattice theory where possible

## Future Work

1. ~~**Complete Foulis-Holland**~~ ✅ DONE: `commutes_inf`, `commutes_sup` proven
2. **Distributive Sublattices**: Prove `commuting_distributive`
3. **Hypercube Edges**: Formalize all 12 edges (theory transformations)
4. **Measure Theory Bridge**: Extend finite quantum beliefs to σ-algebras
5. **Concrete Examples**: MO5 lattice, projective geometries
6. **Decision Procedures**: Automated reasoning about commutativity

## Contact

Part of the Mettapedia project formalizing mathematical foundations of inference, probability, and universal AI.

For questions about this formalization, see `lean-projects/mettapedia/CLAUDE.md`.

## Literature

See `literature/KS_codex/README.md` for complete bibliography including:
- Knuth-Skilling papers
- Cox's theorem proofs
- Ordered semigroup embeddings (Hölder, Alimov)
- Functional equations (Aczél)
- Orthomodular lattice theory (Kalmbach, Beran, Foulis)
