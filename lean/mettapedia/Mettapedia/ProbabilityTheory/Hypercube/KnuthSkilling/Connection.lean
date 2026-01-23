import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.CredalSets
import Mettapedia.ProbabilityTheory.Hypercube.Basic

/-!
# K&S Probability via the Hypercube Framework

This file connects the Knuth-Skilling probability foundations to the Stay-Wells hypercube
construction for type systems.

## Overview

The K&S axiom spectrum and credal sets fit naturally into the hypercube framework:

### The Connection

| Hypercube Concept | K&S Interpretation |
|-------------------|-------------------|
| **Lambda Theory** | KnuthSkillingAlgebra with op, ident |
| **Base Rewrite** | x ⊕ y → result (associative combination) |
| **Modal Types** | Separation sets A(d,u), B(d,u), C(d,u) |
| **Sort Slots** | Precision levels: ∗ = intervals, □ = points |
| **Σ-Gating** | Which parameters require precise values? |
| **Equational Center** | Structures where Θ representation exists |
| **Spatial Types** | Atom family decomposition μ(F, r) |
| **Hypercube Vertices** | Different probability theories |

## Key Insight

The **spectrum of probability foundations** forms a hypercube where:
- **Axes**: many semantic axes (see `Mettapedia.ProbabilityTheory.Hypercube.Basic`)
- **Vertices**: Different probability theories (imprecise → classical)
- **Paths**: Refinement processes (interval bounds → point values)

## References

- Stay & Wells, "Generating Hypercubes of Type Systems" (hypercube.pdf)
- Knuth & Skilling, "Foundations of Inference" Appendix A
- Mettapedia/CategoryTheory/Hypercube.lean (PLN instance)
-/

namespace Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Connection

open Mettapedia.ProbabilityTheory.KnuthSkilling
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.Hypercube

/-! ## Section 1: K&S as a Lambda Theory

The KnuthSkillingAlgebra structure fits the lambda theory framework:

**Base Types**:
- Pr = α (the process type = algebra elements)

**Operations**:
- op : α → α → α (the combining operation ⊕)
- ident : α (the identity element)
- iterate_op : α → ℕ → α (x^n = x ⊕ x ⊕ ... ⊕ x)

**Propositions**:
- x ≤ y (order relation)
- x ⊕ y = z (equality)

**Base Rewrite** (conceptually):
- (x ⊕ y) ⊕ z ⇝ x ⊕ (y ⊕ z)   [associativity]
- x ⊕ ident ⇝ x                [identity]
-/

/-! ## Section 2: Modal Types = Separation Statistics

The K&S separation sets are **rely-possibly modal types**!

### A-Statistics (Below d^u)

The set A(d, u) = {r | μ(r) < d^u} has modal type semantics:

  ⟨C_<⟩_{d::Positive, u::ℕ₊} Below

where:
- Context C_< = "compare with d^u"
- Rely: d is positive, u > 0
- Possibly: reach a state "μ(r) < d^u" (Below)

In the rely-possibly formula:
  r :: ⟨C_<⟩ Below  ⟺  ∀d,u. (d > ident ∧ u > 0) ⇒ μ(r) < iterate_op d u

### B-Statistics (Equal to d^u)

The set B(d, u) = {r | μ(r) = d^u} has modal type:

  ⟨C_=⟩_{d::Positive, u::ℕ₊} Equal

### C-Statistics (Above d^u)

The set C(d, u) = {r | μ(r) > d^u} has modal type:

  ⟨C_>⟩_{d::Positive, u::ℕ₊} Above

**Key Property**: The separation statistics θ(r)/u are behavioral types!
-/

/-! ## Section 3: Sort Slots = Precision Levels

The hypercube framework has two sorts at each carrier:
- ∗ (star) = term level = types
- □ (box) = kind level = higher types

**In the K&S context**, this maps to precision:
- ∗ = **Imprecise** (credal intervals [lower, upper])
- □ = **Precise** (point values in ℝ)

### The Credal Algebra Has ∗-Slots

From CredalSets.lean, a CredalAlgebra uses:
- μ : α → Interval (interval-valued, not point-valued)
- Containment: μ(x ⊕ y) ⊆ μ(x) + μ(y)
- Order on lower bounds only

This corresponds to ALL slots being ∗ (imprecise).

### The Classical K&S Has □-Slots

The main K&S representation theorem produces:
- Θ : α → ℝ (point-valued, not interval-valued)
- Equality: Θ(x ⊕ y) = Θ(x) + Θ(y)
- Completeness: Uses sSup to extract limits

This corresponds to ALL slots being □ (precise).

### Mixed Precision Models

Intermediate vertices of the hypercube have MIXED precision:
- Some parameters are intervals (∗-slots)
- Others are points (□-slots)

Example: "We know μ(x) precisely, but μ(y) only to within [a, b]"
-/

/-! ## Section 4: Σ-Gating = Precision Requirements

The Σ-gating mechanism determines which combinations of ∗/□ are admissible.

### No Constraints (Equation-Free)

In the absence of equations (CredalSets.lean Sections 3-4):
- ALL sort assignments are valid
- The hypercube is the full product S^Slot

### Completeness Constraint

**Theorem** (CredalSets.collapse_theorem): Refined credal algebras with shrinking intervals
yield point values via completeness (sSup).

This is an **Σ-constraint**: To get □-slots (precise values), you need the completeness axiom.

  Σ_credal: all slots → ∗  (no completeness needed)
  Σ_classical: all slots → □  (requires completeness!)

### Commutativity Constraint

The K&S representation theorem DERIVES commutativity:
  x ⊕ y = y ⊕ x  (from Θ(x ⊕ y) = Θ(x) + Θ(y) and commutativity of +)

This is an **equational constraint** on the hypercube!

In the toy free monoid (`Hypercube/KnuthSkilling/ToyFreeMonoid2.lean`), we have:
- Associativity ✓
- (a ⊕ b)² ≠ a² ⊕ b² (no commutativity)
- Therefore: NO Θ representation exists

This free monoid is OUTSIDE the equational center Z!
-/

/-! ## Section 5: The Equational Center = Representation Compatibility

**Definition** (hypercube.pdf Section 5.1): The equational center Z ⊆ S^Slot is:

  Z = {Σ : Slot → S | t^S = u^S for every equation t = u}

where t^S, u^S are the sort-level operations induced by Σ.

### K&S Equational Center

For KnuthSkillingAlgebra, the equations are:
1. Associativity: (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)
2. Identity: x ⊕ ident = x, ident ⊕ x = x
3. **Representation-induced**: If Θ exists, then commutativity x ⊕ y = y ⊕ x follows

The equational center Z_KS consists of:

  Z_KS = {structures where the Θ representation exists and respects all equations}

### A small K&S proof slice (not the master hypercube)

The master hypercube of probability theories is `ProbabilityVertex` in
`Mettapedia.ProbabilityTheory.Hypercube.Basic`.

The table below is a **coarse local picture** used only for bookkeeping in the K&S proof story:
it keeps most master axes fixed to `knuthSkilling` and informally tracks only whether we are
working with credal (interval) semantics vs point-valued semantics, and whether a Θ-representation
exists. In particular, “Completeness” here refers to an additional *model* hypothesis used to
collapse intervals via `sSup`; it is not (currently) an axis of `ProbabilityVertex`.

| Vertex | Commutativity | Completeness | Precision | Theory |
|--------|--------------|--------------|-----------|---------|
| V₀ | ✗ | ✗ | all ∗ | Free monoid (no probability) |
| V₁ | ✗ | ✓ | all ∗ | Noncommutative credal sets |
| V₂ | ✓ | ✗ | all ∗ | Commutative credal sets |
| V₃ | ✓ | ✓ | all □ | Classical probability (Kolmogorov) |

V₀ is OUTSIDE Z_KS (no representation).
V₁ is INSIDE Z_KS but unlikely (commutativity usually follows from order).
V₂ is in Z_KS (CredalSets.lean).
V₃ is the K&S target (Main.lean).
-/

/-! ## Section 6: Spatial Types = Atom Family Structure

Spatial types (hypercube.pdf Section 4) classify terms by AST root constructor.

For operation f : X₁ × ⋯ × Xₙ → Y, the spatial type is:
  f♯(A₁, ..., Aₙ) = {y : Y | ∃(xᵢ : Xᵢ). y = f(x₁,...,xₙ) ∧ ∧ᵢ xᵢ :: Aᵢ}

### K&S Atom Families

In K&S Appendix A, μ(F, r) depends on:
- F: an atom family {a₁, ..., aₖ}
- r: a multiplicity vector (r₁, ..., rₖ)

The formula is:
  μ(F, r) = a₁^{r₁} ⊕ ⋯ ⊕ aₖ^{rₖ}

This is a **spatial type**:
  μ♯(F₁,...,Fₖ) = {x : α | ∃(rᵢ : ℕ). x = μ(F, (r₁,...,rₖ)) ∧ ∧ᵢ Fᵢ is an atom}

The spatial type classifies elements by which atoms they combine!

### Slot Families for Spatial Types

The slot family for μ♯ includes:
- One slot for each atom carrier (∗/□ precision for each atom)
- One slot for the result (∗/□ precision for the combined value)

The Σ-gating determines: Can we have precise atoms but imprecise combinations?
-/

/-! ## Section 7: The K&S Probability Hypercube

Putting it all together:

```
                        Foundational Axioms
                              ↓
                    KnuthSkillingAlgebra
                    (associativity, order, ident)
                         /          \
                    [Equations]  [No commutativity]
                       /              \
                Repr exists        Free monoid
                      |              (V₀: outside Z_KS)
                 Commutativity
                      |
                  /       \
           [Completeness] [No completeness]
              /               \
         Classical         Credal sets
         (V₃: all □)      (V₂: all ∗)
            |                  |
      Kolmogorov          Imprecise
      probability         probability
```

### The Hypercube Dimensions

1. **Commutativity axis**: Does x ⊕ y = y ⊕ x hold?
   - No: Free monoid (outside Z_KS)
   - Yes: K&S probability structures

2. **Completeness axis**: Can we use sSup to collapse intervals?
   - No: Credal sets (intervals)
   - Yes: Classical probability (points)

3. **Precision axes**: For each atom/parameter, ∗ or □?
   - All ∗: Pure intervals
   - All □: Pure points
   - Mixed: Partial uncertainty

### Paths in the Hypercube

**Refinement path**: V₂ → V₃ (credal → classical)
- Start: Interval bounds [lower, upper]
- Process: Shrink intervals via RefinedCredalAlgebra
- End: Point value = sSup{lower bounds} (requires completeness!)

This is formalized in CredalSets.collapse_theorem!

**Derivation path**: V₀ → V₂ (noncommutative → commutative)
- Start: Free monoid (associative only)
- Process: Add order + Archimedean + separation
- End: Representation exists → commutativity emerges

This is the K&S Appendix A construction!
-/

/-! ## Section 8: Rely-Possibly Semantics for K&S

The modal types have rely-possibly semantics (hypercube.pdf Section 3.2.4):

  t :: ⟨Cⱼ⟩_{xₖ::Aₖ} B  ⟺  ∀(xₖ). (∧ₖ xₖ :: Aₖ) ⇒ ∃p. Cⱼ[t] ⇝ p ∧ p :: B

### K&S Rely-Possibly for Separation Statistics

For the A-statistic separation set:

  r :: ⟨compare_<⟩_{d::Positive, u::ℕ₊} Below

means:

  "For all positive d and u > 0, if we rely on d > ident and u ∈ ℕ₊,
   then it's possible to verify that μ(r) < d^u in one comparison step"

### The Θ-Grid as Rely-Possibly Types

The Θ_grid in K&S Appendix A Core (MultiGrid.lean) is a rely-possibly type!

For r in the k-grid:
  Θ_grid⟨r, proof⟩ :: ⟨grid_comparison⟩_{ordering_rely} ℝ

This says:
  "Given the ordering properties we rely on, the grid element r maps to a real value"

The modal elimination rule (hypercube.pdf Section 3.2.3) corresponds to:
  "To use Θ_grid(r), prove the property for any r satisfying the grid ordering"

This is EXACTLY how the K&S induction works!
-/

/-! ## Section 9: Heyting Negation and Empty B-Sets

The hypercube framework includes Heyting negation (hypercube.pdf Section 3.2.4):

  ⟨Cⱼ⟩_{xₖ::Aₖ} ⊥ = ¬(∃(xₖ). ∧ₖ xₖ :: Aₖ)

This is **exactly** the K&S B-empty condition!

### B-Empty as Modal Negation

When hB_empty: ∀r u, 0 < u → r ∉ B(d, u), this says:

  ⟨exact_equality⟩_{d::Positive, u::ℕ₊} ⊥ = True

"For all positive d and u, there is **no witness** r with μ(r) = d^u exactly"

This is the **Heyting negation** of the B-witness proposition!

### The Inaccessible δ

The delta_cut_tight property (DeltaShift.lean) says:
  "δ is a tight Dedekind cut - A-statistics approach it from below, C from above"

In modal terms:
  ⟨approach_from_below⟩ ⊥  (no A-statistic equals δ)
  ⟨approach_from_above⟩ ⊥  (no C-statistic equals δ)

The δ value is **inaccessible** - it lives in the gap!

This explains why the B-empty strict-gap step was hard in the Appendix A development:
the boundary case must be excluded in a way compatible with the "no witnesses" hypothesis.

**Status (2026-01-08)**: This blocker is now **fully resolved**. The `KSSeparationStrict` axiom
provides the strict gap, and the proof machinery in `Goertzel.lean` derives all necessary
properties automatically via `appendixA34Extra_of_KSSeparationStrict`.
-/

/-! ## Section 10: Summary - The Hypercube Perspective

The K&S probability foundations form a **hypercube of theories**:

### What the Hypercube Framework Provides

1. **Systematic organization**: Probability theories as vertices of a hypercube
2. **Precision spectrum**: From intervals (credal) to points (classical)
3. **Modal interpretation**: Separation statistics as rely-possibly types
4. **Structural decomposition**: Atom families as spatial types
5. **Equational constraints**: Commutativity emerges, completeness is independent
6. **Negation semantics**: B-empty as Heyting negation of witnesses

### The Main Theorems

- **Stay-Wells**: Hypercube construction from operational semantics
- **K&S**: Representation theorem from associativity + order
- **Connection**: K&S is an instance of the hypercube construction!

The vertices are:
- **V₀**: Free monoid (no representation, outside Z_KS)
- **V₂**: Credal sets (intervals, no completeness, in Z_KS)
- **V₃**: Classical probability (points, with completeness, target of K&S)

The paths are:
- **Derivation**: V₀ → V₂ via K&S Appendix A (order induces commutativity)
- **Refinement**: V₂ → V₃ via CredalSets.collapse_theorem (completeness shrinks intervals)

### Philosophical Insight

The **hypercube perspective** reveals that:

1. Probability is not unique - it's a family of theories
2. Classical probability requires TWO additional axioms:
   - Commutativity (derivable from K&S axioms)
   - Completeness (foundational choice, NOT derivable)
3. The "natural" theory is credal sets (V₂)
4. Point values (V₃) require assuming ℝ is complete

This resolves the apparent tension in CredalSets.lean: K&S didn't make an error,
they just worked in a foundational setting (Lean/ZFC) where completeness is already assumed.
The hypercube shows BOTH credal and classical are valid, just at different vertices!
-/

end Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Connection
