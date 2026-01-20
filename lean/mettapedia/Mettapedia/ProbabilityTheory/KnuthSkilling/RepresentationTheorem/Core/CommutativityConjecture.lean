import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.GrowthRateTheory
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.SeparationImpliesCommutative

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core

open Classical KnuthSkillingAlgebra

/-!
# KSSeparation Implies Commutativity (Historical Notes)

This file originally recorded an *open* conjecture that `KSSeparation` implies commutativity.

## Status: RESOLVED

There is a complete Lean proof:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Separation/SandwichSeparation.lean`

The main “Core/” entry point for this fact is:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Core/SeparationImpliesCommutative.lean`

## What IS Proven (See Other Files)

1. **Representable → Commutative** (OneDimensional.lean)
   - IF an algebra embeds in ℝ, THEN it's commutative
   - Complete proof, no sorries

2. **A commutative product model fails the sandwich axiom** (ProductFailsSeparation.lean)
   - `natProdLex_fails_KSSeparation`: `ℕ ×ₗ ℕ` (lex order, componentwise addition) fails
     the sandwich axiom `KSSeparation`
   - (This model is also non-Archimedean, so it is not a `KnuthSkillingAlgebra`, but it shows the
     sandwich axiom is genuinely additional structure.)

3. **Growth rate theory** (GrowthRateTheory.lean)
   - Base monotonicity: a < b ⟹ a^k < b^k
   - Exponent monotonicity: for a > ident, m < n ⟹ a^m < a^n
   - Separation constraints and impossibility results
   - Complete proofs, no sorries

## Approaches Attempted

All failed due to fundamental obstacles:

1. **Hölder Construction**: Circular - proving φ is additive requires commutativity
2. **Direct Separation**: Can derive constraints but not contradictions
3. **Archimedean Argument**: k=0 case contradicts, but k>0 case is consistent
4. **Growth Rate Comparison**: Base ordering doesn't force exponent impossibilities
5. **Counterexample Construction**: Every structure tried fails KSSeparation

This file now serves only as a record of auxiliary constraints that were useful when
trying to prove commutativity directly.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-- `KSSeparation` forces global commutativity. -/
theorem separation_implies_commutative [KSSeparation α] : ∀ x y : α, op x y = op y x := by
  intro x y
  exact op_comm_of_KSSeparation (α := α) x y

/-!
## Constraints We CAN Derive (Proven)

Without assuming commutativity, we can still prove some constraints about a hypothetical
noncommutativity witness `x⊕y < y⊕x`.
-/

/-- If x⊕y < y⊕x, the gap persists in all powers -/
theorem gap_in_powers (x y : α) (_hx : ident < x) (_hy : ident < y)
    (hlt : op x y < op y x) (k : ℕ) (hk : 0 < k) :
    iterate_op (op x y) k < iterate_op (op y x) k :=
  gap_persists_in_powers x y hlt k hk

/-- If x⊕y < y⊕x, then x < x⊕y < y⊕x -/
theorem ordering_chain (x y : α) (hx : ident < x) (hy : ident < y)
    (hlt : op x y < op y x) :
    x < op x y ∧ op x y < op y x :=
  noncommutativity_gives_constraints x y hx hy hlt

section WithSeparation

variable [KSSeparation α]

/-- Using separation with (x⊕y) as base gives exponent constraint -/
theorem separation_constraint_from_self (x y : α)
    (hx : ident < x) (hy : ident < y) (hlt : op x y < op y x) :
    ∃ n m : ℕ, 0 < m ∧ m < n ∧
    iterate_op (op x y) n ≤ iterate_op (op y x) m :=
  separation_self_base (op x y) (op y x)
    (by calc ident < x := hx
          _ < op x y := (noncommutativity_gives_constraints x y hx hy hlt).1)
    (by calc ident < x := hx
          _ < op x y := (noncommutativity_gives_constraints x y hx hy hlt).1
          _ < op y x := hlt)
    hlt

/-!
## Historical note

Earlier formalization attempts got “stuck” at the final contradiction step. The mass-counting proof
fills this gap using a “mass counting” argument that compares `(x⊕y)^n` and `(y⊕x)^m` when `n > m`
without introducing logarithms.
-/

end WithSeparation

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core
