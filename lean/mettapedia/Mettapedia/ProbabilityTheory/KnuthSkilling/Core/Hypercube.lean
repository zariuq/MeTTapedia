/-
# The Hypercube of Probability Theories

## Overview

Different structural assumptions lead to different probability theories.
We can visualize these as vertices of a "hypercube" with axes:

1. **Logic Axis**: Boolean vs Heyting (complement behavior)
2. **Representation Axis**: Point-valued vs 2D/Bounds-valued
3. **Prior Axis**: Fixed prior vs Universal prior (Solomonoff)

## The Correct Gate: Complement Behavior

The key distinction between Boolean and Heyting K&S is NOT about
"incomparable elements forcing interval overlap" (that claim was false).

The REAL gate is the **complement behavior**:
- **Boolean**: ν(a) + ν(¬a) = 1 (equality)
- **Heyting**: ν(a) + ν(¬a) ≤ 1 (inequality - there's slack!)

This creates natural bounds: [ν(a), 1 - ν(¬a)]
- In Boolean algebras: bounds collapse to points (equality)
- In Heyting algebras: bounds have positive width (the excluded middle gap)

## Key Vertices

- **Boolean + Point**: Classical K&S probability (standard Bayesian)
- **Boolean + 2D**: Standard probability with uncertainty quantification
- **Heyting + Point**: K&S on Heyting algebras (negation gives slack bounds)
- **Heyting + 2D**: Explicit positive/negative evidence tracking (PLN-style)

## References

- See HeytingBounds.lean for the correct Boolean vs Heyting characterization
- See HeytingValuation.lean for the modularity axiom foundation
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingValuation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingBounds

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Hypercube

open Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting

/-! ## The Hypercube Axes -/

/-- The logic axis: Boolean vs Heyting algebra.
    The key difference is complement behavior. -/
inductive LogicAxis
  | boolean  -- ν(a) + ν(¬a) = 1 (classical complement)
  | heyting  -- ν(a) + ν(¬a) ≤ 1 (pseudocomplement inequality)
  deriving DecidableEq, Repr

/-- The representation axis: point-valued vs bounds/2D-valued.
    Independent of the logic axis! -/
inductive RepresentationAxis
  | point   -- Single value ν(a) ∈ [0,1]
  | bounds  -- Interval [lower(a), upper(a)] or 2D (n⁺, n⁻)
  deriving DecidableEq, Repr

/-- A vertex in the hypercube of probability theories. -/
structure HypercubeVertex where
  logic : LogicAxis
  representation : RepresentationAxis
  deriving DecidableEq, Repr

/-! ## The Complement Gate Theorem -/

/-- In Boolean algebras, the complement rule gives ν(a) + ν(¬a) = 1. -/
theorem boolean_complement_equality {α : Type*} [BooleanAlgebra α]
    (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ = 1 :=
  ModularValuation.boolean_complement_rule ν a

/-- In Heyting algebras, we only have ν(a) + ν(¬a) ≤ 1. -/
theorem heyting_complement_inequality {α : Type*} [HeytingAlgebra α]
    (ν : ModularValuation α) (a : α) :
    ν.val a + ν.val aᶜ ≤ 1 :=
  heyting_not_boolean_complement ν a

/-! ## The Excluded Middle Gap -/

/-- The excluded middle gap measures how far a ⊔ ¬a is from ⊤.
    - Zero for Boolean algebras
    - Potentially positive for Heyting algebras -/
theorem boolean_em_gap_zero {α : Type*} [BooleanAlgebra α]
    (ν : ModularValuation α) (a : α) :
    excludedMiddleGap ν a = 0 := by
  unfold excludedMiddleGap
  simp only [sup_compl_eq_top, ν.val_top, sub_self]

/-- In Heyting algebras, the gap is always non-negative. -/
theorem heyting_em_gap_nonneg {α : Type*} [HeytingAlgebra α]
    (ν : ModularValuation α) (a : α) :
    excludedMiddleGap ν a ≥ 0 :=
  excludedMiddleGap_nonneg ν a

/-! ## Vertex Classification -/

/-- Standard Bayesian probability sits at the Boolean + Point vertex. -/
def classicalProbability : HypercubeVertex :=
  ⟨.boolean, .point⟩

/-- PLN-style evidence tracking sits at the Heyting + 2D vertex. -/
def plnEvidence : HypercubeVertex :=
  ⟨.heyting, .bounds⟩

/-- Imprecise probability on Boolean events uses Boolean + Bounds. -/
def impreciseProbability : HypercubeVertex :=
  ⟨.boolean, .bounds⟩

/-- K&S on Heyting algebras with point valuations. -/
def heytingPointKS : HypercubeVertex :=
  ⟨.heyting, .point⟩

/-! ## The Heyting Bounds Construction

The natural way to get bounds from a Heyting point valuation is:
- lower(a) := ν(a)
- upper(a) := 1 - ν(¬a)

This follows from the negation inequality and gives exactly
the excluded middle gap as the interval width. -/

/-- The Heyting bounds width equals the excluded middle gap. -/
theorem heyting_bounds_width_eq_em_gap {α : Type*} [HeytingAlgebra α]
    (ν : ModularValuation α) (a : α) :
    heytingWidth ν a = excludedMiddleGap ν a :=
  heytingWidth_eq_em_gap ν a

/-- Boolean algebras have zero width (points). -/
theorem boolean_bounds_collapse {α : Type*} [BooleanAlgebra α]
    (ν : ModularValuation α) (a : α) :
    upperBound ν a = lowerBound ν a :=
  boolean_collapse ν a

/-! ## Summary: The Correct Hypercube Story

The hypercube has two main axes that matter for K&S:

1. **Logic Axis** (Boolean vs Heyting):
   - Determines the complement behavior
   - Boolean: ν(a) + ν(¬a) = 1
   - Heyting: ν(a) + ν(¬a) ≤ 1 (slack exists)

2. **Representation Axis** (Point vs Bounds/2D):
   - Point: single value ν(a)
   - Bounds: interval [lower(a), upper(a)] or 2D (n⁺, n⁻)

Key insight: These axes are INDEPENDENT!
- You can have Boolean + Bounds (imprecise probability)
- You can have Heyting + Point (K&S on Heyting algebras)

The "gate" is NOT about incomparability forcing intervals.
The gate is about complement behavior determining whether
the natural bounds [ν(a), 1 - ν(¬a)] collapse to a point.

PLN BinaryEvidence sits at Heyting + 2D because:
- BinaryEvidence is NOT Boolean (incomparable states exist)
- The 2D representation (n⁺, n⁻) tracks positive/negative evidence separately
- Collapsing to 1D loses the non-Boolean structure
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Hypercube
