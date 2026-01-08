import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.OneDimensional

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core

open Classical KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

/-!
# What We Actually Know (Proven Solidly)

This file contains ONLY results that are fully proven, no handwaving.

## Summary

✓ PROVEN: Representable ⟹ Commutative
✓ PROVEN: Multi-dimensional structures fail KSSeparation
✗ OPEN: KSSeparation ⟹ Representable
✗ OPEN: KSSeparation ⟹ Commutative (directly)

## The Gap

We cannot prove KSSeparation → Commutativity without additional techniques or axioms.
This is the same gap that exists in Goertzel's proof (Lemma 7).
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
## Theorem 1: If Representable, Then Commutative (FULLY PROVEN)

This is proven in OneDimensional.lean with NO sorries.
-/

theorem representable_implies_commutative_reference [Representable α] :
    ∀ x y : α, op x y = op y x := by
  exact representable_implies_commutative (α := α)

/-!
## Theorem 2: Powers Preserve Inequality (FULLY PROVEN)

If a < b, then a^k < b^k for all k > 0.
This is a basic fact about strictly monotone functions.
-/

theorem iterate_op_preserves_lt {a b : α} (hab : a < b) (k : ℕ) (hk : 0 < k) :
    iterate_op a k < iterate_op b k := by
  induction k with
  | zero => exact absurd hk (Nat.not_lt_zero 0)
  | succ k ih =>
    cases Nat.eq_zero_or_pos k with
    | inl hzero =>
      subst hzero
      simp [iterate_op_one]
      exact hab
    | inr hpos =>
      have : iterate_op a k < iterate_op b k := ih hpos
      calc iterate_op a (k + 1)
          = op a (iterate_op a k) := rfl
        _ < op a (iterate_op b k) := op_strictMono_right a this
        _ < op b (iterate_op b k) := op_strictMono_left (iterate_op b k) hab
        _ = iterate_op b (k + 1) := rfl

/-!
## Theorem 3: Separation Gives Specific Constraints (FULLY PROVEN)

If KSSeparation holds and x⊕y < y⊕x, we CAN apply separation.
This gives us constraints, but not yet a contradiction.
-/

theorem separation_gives_constraints [KSSeparation α]
    (x y : α) (hx : ident < x) (hy : ident < y) (hlt : op x y < op y x) :
    ∃ n m : ℕ, 0 < m ∧
    iterate_op (op x y) m < iterate_op (op x y) n ∧
    iterate_op (op x y) n ≤ iterate_op (op y x) m := by
  -- Prove x⊕y > ident
  have hxy : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op x ident := op_strictMono_left ident hx
         _ = x := op_ident_right x
         _ < op x y := by
           calc x = op x ident := (op_ident_right x).symm
                _ < op x y := op_strictMono_right x hy

  -- Prove y⊕x > ident
  have hyx : ident < op y x := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op y ident := op_strictMono_left ident hy
         _ = y := op_ident_right y
         _ < op y x := by
           calc y = op y ident := (op_ident_right y).symm
                _ < op y x := op_strictMono_right y hx

  -- Apply KSSeparation with base a = (x⊕y)
  exact KSSeparation.separation hxy hxy hyx hlt

/-!
## What We CANNOT Prove

The following is the missing link. We cannot prove it without additional insights:

**Conjecture**: The constraints from Theorem 3 lead to a contradiction.

**Why we're stuck**: To derive the contradiction, we need to know how (x⊕y)^m
relates to x^m and y^m. Without commutativity, we can't establish this relationship.

**Possible approaches that failed**:
1. Growth rate arguments - can't formalize "growth rate" without representation
2. Hölder construction - hits circularity when proving additivity
3. Independence formalization - can't define "direction" without product structure
4. Direct combinatorial - can't rearrange (x⊕y)^m without commutativity

**Conclusion**: Either
- There's a sophisticated proof technique we haven't found, OR
- Commutativity genuinely needs to be an independent axiom
-/

/-!
## The Honest Assessment

After extensive attempts:

**PROVEN RESULTS**:
1. ✓ Multi-dimensional algebras fail KSSeparation (ProductFailsSeparation.lean)
2. ✓ Representable algebras are commutative (OneDimensional.lean)
3. ✓ Attempted counterexamples all fail at separation

**UNPROVEN (OPEN QUESTIONS)**:
1. ✗ Does KSSeparation imply representability?
2. ✗ Does KSSeparation directly imply commutativity?

**PRACTICAL RECOMMENDATION**:
- Treat NewAtomCommutes as an EXPLICIT axiom (like Codex does)
- Document that derivability from KSSeparation is an open question
- Note this is the same gap in Goertzel's proof

**MATHEMATICAL STATUS**:
This appears to be a genuinely difficult problem that may require:
- Model-theoretic techniques
- Representation theory (beyond classical Hölder)
- Order-theoretic methods we haven't found
- OR acceptance that it's truly independent
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core
