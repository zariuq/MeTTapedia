import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityDerivation

/-!
# Probability Calculus: Common Interface for End-Results

This file provides a **single source of truth** for the probability calculus results
derived from K&S. All downstream code should use these canonical definitions.

## Design Principle

Like `AdditiveOrderIsoRep` for Appendix A, this file provides:
1. A common interface (`ProbabilityCalculus`) capturing the key properties
2. Canonical theorem statements that don't depend on proof path
3. The main K&S path (`ProbabilityDerivation`) provides the implementation

## Key Results (Canonical Definitions)

- `sumRule`: P(A ∨ B) = P(A) + P(B) for disjoint A, B
- `productRule`: P(A ∧ B) = P(A|B) · P(B)
- `bayesTheorem`: P(A|B) · P(B) = P(B|A) · P(A)
- `complementRule`: P(Aᶜ ∧ t) = 1 - P(A) (in context t)

## Usage

Import this file for probability calculus results. Don't import
`ProbabilityDerivation` or `ConditionalProbability/Basic` directly for end-results.

```lean
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityCalculus

-- Use the canonical theorems:
#check Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityCalculus.sumRule
#check Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityCalculus.bayesTheorem
```
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityCalculus

open Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## Canonical End-Results

These are the official probability calculus theorems from K&S.
They are re-exported from `ProbabilityDerivation` which provides the main K&S derivation.
-/

/-- **Sum Rule** (Canonical): For disjoint events, probability is additive.

`P(A ∨ B) = P(A) + P(B)` when `A` and `B` are disjoint.

This is derived from K&S's representation theorem (Appendix A) and the
`CoxConsistency` axioms in `ProbabilityDerivation.lean`. -/
abbrev sumRule := @Mettapedia.ProbabilityTheory.KnuthSkilling.sum_rule

/-- **Product Rule** (Canonical): Probability of conjunction factors through conditioning.

`P(A ∧ B) = P(A|B) · P(B)`

This follows from the definition of conditional probability. -/
abbrev productRule := @Mettapedia.ProbabilityTheory.KnuthSkilling.product_rule_ks

/-- **Bayes' Theorem** (Canonical): The fundamental theorem of rational inference.

`P(A|B) · P(B) = P(B|A) · P(A)`

Or equivalently: `P(A|B) = P(B|A) · P(A) / P(B)`

This follows from the commutativity of conjunction (A ∧ B = B ∧ A). -/
abbrev bayesTheorem := @Mettapedia.ProbabilityTheory.KnuthSkilling.bayes_theorem_ks

/-- **Complement Rule** (Canonical): Probability of complement.

`P(B) = 1 - P(A)` when A and B are complementary (disjoint and A ∨ B = ⊤).

This follows from the sum rule and normalization. -/
abbrev complementRule := @Mettapedia.ProbabilityTheory.KnuthSkilling.complement_rule

/-! ## Interface Class

For code that needs to abstract over probability systems, use this class.
The main K&S derivation provides an instance via `CoxConsistency`. -/

/-- A `ProbabilityCalculus` captures the key properties of a probability measure.

This is the common interface that any probability derivation should satisfy.
The canonical instance comes from K&S's `CoxConsistency` + representation theorem. -/
class ProbabilityCalculusClass (α : Type*) [PlausibilitySpace α] [ComplementedLattice α]
    (v : Valuation α) where
  /-- Sum rule for disjoint events -/
  sum_rule' : ∀ {a b : α}, Disjoint a b → v.val (a ⊔ b) = v.val a + v.val b
  /-- Complement rule -/
  complement_rule' : ∀ {a b : α}, Disjoint a b → a ⊔ b = ⊤ → v.val b = 1 - v.val a

namespace ProbabilityCalculusClass

variable {α : Type*} [PlausibilitySpace α] [ComplementedLattice α] {v : Valuation α}
variable [ProbabilityCalculusClass α v]

/-- Sum rule from the class -/
theorem sum_rule_class {a b : α} (h : Disjoint a b) :
    v.val (a ⊔ b) = v.val a + v.val b :=
  ProbabilityCalculusClass.sum_rule' h

/-- Complement rule from the class -/
theorem complement_rule_class {a b : α} (h_disj : Disjoint a b) (h_top : a ⊔ b = ⊤) :
    v.val b = 1 - v.val a :=
  ProbabilityCalculusClass.complement_rule' h_disj h_top

end ProbabilityCalculusClass

/-- The canonical instance: `CoxConsistency` provides `ProbabilityCalculusClass`. -/
instance instProbabilityCalculusOfCoxConsistency
    {α : Type*} [PlausibilitySpace α] [ComplementedLattice α]
    {v : Valuation α} (hC : CoxConsistency α v) :
    ProbabilityCalculusClass α v where
  sum_rule' := fun h => sum_rule v hC h
  complement_rule' := fun h_disj h_top => complement_rule v hC _ _ h_disj h_top

end Mettapedia.ProbabilityTheory.KnuthSkilling.ProbabilityCalculus
