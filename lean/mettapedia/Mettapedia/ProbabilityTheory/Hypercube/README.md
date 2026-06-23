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

## Domains: Knowing Which Reasoning Applies

The hypercube is not just a taxonomy of "probability theories"; it is a way to keep track of which
*properties of your domain* are required for which styles of reasoning.

### The Totality / Linear-Order Gate (Why Point-Valued Probability Needs Comparability)

If you want a **faithful point-valued representation** (a map `Θ : α → ℝ` that preserves *and
reflects* `≤`), then your plausibility order must already be **total**: every pair must be
comparable. Otherwise, no such `Θ` can exist, because `ℝ` is linearly ordered.

This is formalized in:
- `Mettapedia/Logic/PLNTruthTower.lean`:
  - `no_pointRepresentation_with_incomparables` (incomparables rule out any faithful `Θ : α → ℝ`)

Interpretation: **Linear order is not cosmetic** in the K&S-style representation theorems; it is
exactly the condition that makes point-valued (precise) semantics possible.

### Evidence/Quantale Semantics (PLN) Lives on the "Partial-Order" Face

PLN’s evidence-count carrier `Evidence := (n⁺, n⁻)` has a natural **partial order**
(coordinatewise `≤`). It contains incomparable elements (e.g. "more positive evidence but less
negative evidence"), so it cannot admit a faithful point-valued embedding into `ℝ`.

In this setting:
- you should *not* expect a point-valued Kolmogorov calculus to be valid "for free";
- projections like `toStrength : Evidence → [0,1]` are intentionally **non-faithful** (they collapse
  distinct evidence states), so they should be treated as a *view* or *forgetful map*, not an
  identification of theories.

See:
- `Mettapedia/Logic/EvidenceQuantale.lean` (evidence counts, Heyting/Frame structure, `toStrength`)

### Practical Takeaway

When you choose a reasoning calculus, you are choosing (often implicitly) what structure you
assume about the domain:

- Domains with **total comparability** support **precise point-valued** probability (and hence the
  usual Bayes/product/sum calculus).
- Domains with **incomparability** naturally lead to **imprecise / interval** semantics (credal
  sets) or **evidence-valued** semantics (PLN-style), rather than point probabilities.

This is exactly what the `orderAxis` / `precision` axes in `Basic.lean` are for: they make the
"domain gate" explicit and machine-checkable.

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
- **Orthocomplement Uniqueness (Safe Form)**:
  - `orthocomplement_unique_of_commutes`: complements are unique *among commuting candidates*

**Results in this file**:
- Foulis-Holland theorem: Commuting elements are closed under ⊓ and ⊔
- Bidirectional exchange characterization
- De Morgan duality proof for `commutes_sup` via `commutes_inf`

#### `Basic.lean` (54 KB)
The **master probability hypercube**:
- Defines all hypercube axes (e.g. `CommutativityAxis`, `DistributivityAxis`, …)
- Defines `ProbabilityVertex` (one record holding all axes)
- Defines named theories as vertices (`kolmogorov`, `cox`, `knuthSkilling`, `dempsterShafer`, `quantum`, …)
- Defines basic navigation (`isNaturalEdge`, `hammingDistance`, `isMoreGeneral`, …)

Note: this file classifies Dempster–Shafer/quantum/etc as vertices, but it does *not* implement
full belief-function combination rules; those belong in separate developments.

#### `KnuthSkilling.lean` + `KnuthSkilling/` (slice modules)
K&S-focused modules that situate the Appendix A development inside the master hypercube:
- `KnuthSkilling/Connection.lean`: conceptual bridge to the master `ProbabilityVertex` view
- `KnuthSkilling/Neighbors.lean`: local neighbor analysis around the `knuthSkilling` vertex
- `KnuthSkilling/Proofs.lean`: small fully-checked “shape lemmas” (toy derivation graph)
- `KnuthSkilling/Theory.lean`: K&S-centered theory notes (interval/ℚ/ℝ viewpoints)

#### `Taxonomy.lean` (17 KB)
**Weakness / generality ordering** for the full hypercube:
- Defines `≤` on each axis (as a `PartialOrder`), with `⊥` = most constrained and `⊤` = most permissive
- Gives the product `PartialOrder` on `ProbabilityVertex` (so the hypercube becomes a genuine poset)
- Proves equivalence to `Basic.lean`’s manual `isMoreGeneral` predicate (`le_iff_isMoreGeneral`)
- Provides “thin-category” perspective: vertices + weakening maps form a preorder/poset

#### `WeaknessOrder.lean` (3 KB)
Goertzel-style weakness preorder (as an opposite category):
- Defines `V ≼ W` as `isMoreGeneral V W`
- Packages the weakness relation as `ProbabilityVertexᵒᵈ` (a preorder-category)
- Provides `Nonempty (V ⟶ W) ↔ (V ≼ W)` in the preorder-category

#### `QuantaleSemantics.lean` (25 KB)
Uniform **quantale semantics** and morphisms for all `QuantaleType` cases:
- Concrete carriers for commutative / interval / noncommutative / free / boolean / monotone cases
- A `semanticsOfQuantaleType` “picker” (avoids global instance clashes)
- Canonical `QuantaleHom`s into `BoolQuantale` / `CommQuantale`
- `QuantaleHom.map_weakness` can transport Goertzel’s weakness measure along these maps

#### `ThetaSemantics.lean` (5 KB)
Abstract “Θ-family ⇒ credal/interval semantics” API:
- `intervalOfFamily` builds lower/upper envelopes from a set of completions
- `Subsingleton` families collapse to point semantics (`lower = upper`)

#### `ScaleDichotomy.lean` and `DensityAxisStory.lean` (5 KB total)
Formal bridge from “density axis” to the subgroup dichotomy:
- Additive subgroups in archimedean ordered groups are either dense or `ℤ•g`
- Packages `AddSubgroup.dense_or_cyclic` into hypercube-friendly lemmas

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
recorded as `commuting_distributive` (proved). This is part of the standard story
of why classical probability emerges from quantum probability when measuring compatible observables.

**Proof Strategy**:
- For `commutes_inf`: Use exchange characterization. Since `b ⊓ c ≤ b, c`, the exchange bounds combine to give `a ⊓ (aᶜ ⊔ (b ⊓ c)) = a ⊓ b ⊓ c`.
- For `commutes_sup`: De Morgan duality. `b ⊔ c = (bᶜ ⊓ cᶜ)ᶜ`, apply `commutes_inf` to complements, then `commutes_compl`.

## Building the Formalization

```bash
cd Mettapedia/lean/mettapedia
export LAKE_JOBS=3
nice -n 19 lake build Mettapedia.ProbabilityTheory.Hypercube
```

## Current Status

This directory is `sorry`-free (23 `.lean` files; see the comment-stripped footer count
below). There are no source-level `axiom` declarations here (a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a standard Mathlib axiom
transitively), and nothing here uses `native_decide`.

### Completed (sorry-free)
- Orthomodular lattice axiomatization (`NovelTheories.lean`)
- Classical Dempster-Shafer on `Finset Ω` (`Basic.lean`)
- Neighbor investigations (`NeighborTheories.lean`)
- Hypercube taxonomy order (`Taxonomy.lean`)
- Weakness preorder as a category (`WeaknessOrder.lean`)
- Quantale semantics + morphisms (`QuantaleSemantics.lean`)
- Θ-family interval semantics API (`ThetaSemantics.lean`)
- Dense-vs-cyclic scale dichotomy (`ScaleDichotomy.lean`, `DensityAxisStory.lean`)

### Corrected Misconceptions
- OML "quasi-distributivity" is FALSE in general (counterexample in code)
- Bidirectional orthogonality criterion: only forward direction holds

### Open
- Infinite lattice case for quantum beliefs (requires measure theory)

## Relationship to Other Formalizations

### Knuth-Skilling Appendix A (`KnuthSkilling/`, inside this directory)
The K&S Appendix A representation-theorem development lives in `KnuthSkilling.lean` plus the
`KnuthSkilling/` slice modules *under this directory* (there is no separate top-level
`KnuthSkilling/` directory):
- Different focus: derives real-valued probability from abstract lattice symmetries
- The rest of this directory: concrete instantiations (classical, quantum, D-S)

### Common Foundations (`../Common/`)
Shared infrastructure (files verified present in `../Common/`):
- `Lattice.lean`: Basic lattice utilities
- `LatticeValuation.lean`: Normalized valuations, orthoadditive valuations
- `LatticeSummation.lean`: Summation over lattice principal ideals
- `MobiusFunction.lean`: Möbius inversion on lattices
- `FrechetBounds.lean`, `CombinationRule.lean`: Fréchet bounds and combination rules

### Belief Functions (`../BeliefFunctions/`)
Extended Dempster-Shafer theory:
- `Basic.lean`: Full D-S calculus with combination rules
- Bridges to hypercube formalization

## Design Philosophy

1. **No `sorry`**: files in this directory build without `sorry`; open directions live in comments/README, not as “Prop-as-proof” placeholders
2. **Source Attribution**: Every theorem cites original papers
3. **Modular Structure**: Each theory in separate file
4. **Computational Content**: Definitions executable on finite lattices
5. **Mathlib Integration**: Uses standard mathlib lattice theory where possible

## Future Work

- Connect `WeaknessOrder.lean` to `QuantaleSemantics.lean` morphisms
- Formalize more hypercube edges (theory transformations) as explicit morphisms
- Extend finite quantum beliefs to σ-algebras (measure theory)
- Concrete examples: MO5 lattice, projective geometries
- Automated reasoning about commutativity

## Contact

Part of the Mettapedia project formalizing mathematical foundations of inference, probability, and universal AI.

## Literature

The bibliography underlying this lane spans:
- Knuth-Skilling papers (see "Primary References" above);
- Cox's theorem proofs;
- ordered-semigroup embeddings (Hölder, Alimov);
- functional equations (Aczél);
- orthomodular lattice theory (Kalmbach, Beran, Foulis — see "Primary References" above).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 23 .lean files, 0 with sorries.*
