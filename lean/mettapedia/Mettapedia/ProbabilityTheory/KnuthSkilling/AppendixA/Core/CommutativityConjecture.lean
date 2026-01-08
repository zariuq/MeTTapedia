import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.GrowthRateTheory

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core

open Classical KnuthSkillingAlgebra

/-!
# Conjecture: KSSeparation Implies Commutativity

This file CONJECTURES that KSSeparation implies commutativity.

## Status: OPEN PROBLEM

After extensive formalization attempts (~500 lines of code across multiple files),
we have been UNABLE to complete this proof.

## What IS Proven (See Other Files)

1. **Representable → Commutative** (OneDimensional.lean)
   - IF an algebra embeds in ℝ, THEN it's commutative
   - Complete proof, no sorries

2. **Product algebras fail KSSeparation** (ProductFailsSeparation.lean)
   - Multi-dimensional structures violate separation
   - Complete proof, no sorries

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

## The Conjecture

We conjecture (but cannot prove) the following:
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-
CONJECTURE (UNPROVEN):
If KSSeparation holds, then the algebra is commutative.

This would complete the chain:
  KSSeparation → Commutativity → Representable (via Hölder)

WITHOUT this result, we must treat commutativity as an independent axiom.
-/

/-- Conjecture (UNPROVEN): `KSSeparation` implies commutativity.

This is recorded as a `Prop` (not an `axiom`) so that importing this file does not silently add a
new assumption to the theory. -/
def separation_implies_commutative_UNPROVEN : Prop :=
  ∀ x y : α, op x y = op y x

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
## Why We Cannot Derive Contradiction (Informal Analysis)

The constraints above seem contradictory:
- We have (x⊕y)^k < (y⊕x)^k for ALL k > 0 (base ordering)
- We have (x⊕y)^n ≤ (y⊕x)^m where m < n (separation constraint)

Intuitively, these should be incompatible: the smaller base (x⊕y) with larger exponent (n)
cannot beat the larger base (y⊕x) with smaller exponent (m).

BUT we cannot formalize this without a theory of growth rates or logarithms!

In ℝ, we'd prove: log(x⊕y) < log(y⊕x), so n·log(x⊕y) < m·log(y⊕x) requires n/m < small,
contradicting m < n. But we have no logarithms in the pure algebra.

## Recommendation

Treat commutativity (`NewAtomCommutes` in Basic.lean) as an **explicit, independent axiom**.

This is what Codex does, and appears to be necessary despite K&S's claim it's derivable.
-/

end WithSeparation

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core
