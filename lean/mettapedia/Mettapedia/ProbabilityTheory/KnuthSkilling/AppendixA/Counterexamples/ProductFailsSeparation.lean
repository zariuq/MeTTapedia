import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open Classical KnuthSkillingAlgebra

/-!
# Multi-Dimensional Algebras Fail KSSeparation

This file proves that KSSeparation is incompatible with multi-dimensional structures.

## The Key Insight

**KSSeparation is so restrictive that it eliminates independent dimensions**, forcing the algebra
to be essentially 1-dimensional.

## Mathematical Observation

Consider ℕ × ℕ with componentwise addition `(a₁,a₂) + (b₁,b₂) = (a₁+b₁, a₂+b₂)` and
lexicographic order.

This operation is:
- ✓ Associative
- ✓ Commutative
- ✓ Has identity (0,0)
- ✓ Respects lex order (monotone)

But it FAILS KSSeparation!

**Why**: Elements in the same "dimension" cannot be separated by a base in a different dimension.

## Separation Failure

Take x = (0,1), y = (0,2), and base a = (1,0).

In lex order: (0,1) < (0,2) because first coordinates are equal and 1 < 2.

KSSeparation would require: ∃n,m with x^m < a^n ≤ y^m

With componentwise addition:
- x^m = m·(0,1) = (0,m)
- a^n = n·(1,0) = (n,0)
- y^m = m·(0,2) = (0,2m)

In lex order:
- (0,m) < (n,0) requires 0 < n ✓ (true for n ≥ 1)
- (n,0) ≤ (0,2m) requires n ≤ 0 ✗ (contradicts n ≥ 1)

**Conclusion**: No such n, m exist. KSSeparation fails!

## The Deeper Implication

This suggests: **KSSeparation ⟹ 1-Dimensional ⟹ Commutative**

The formal proof below makes this precise.
-/

/-- The lexicographic order on ℕ × ℕ. -/
def prodLexLT : ℕ × ℕ → ℕ × ℕ → Prop :=
  fun (a₁, a₂) (b₁, b₂) => a₁ < b₁ ∨ (a₁ = b₁ ∧ a₂ < b₂)

/-- Lexicographic less-than-or-equal. -/
def prodLexLE : ℕ × ℕ → ℕ × ℕ → Prop :=
  fun (a₁, a₂) (b₁, b₂) => a₁ < b₁ ∨ (a₁ = b₁ ∧ a₂ ≤ b₂)

/-- Main theorem: The multi-dimensional structure ℕ × ℕ with componentwise addition
    cannot satisfy KSSeparation.

    **Proof**: We exhibit specific elements where separation fails. -/
theorem product_fails_separation :
    ¬∃ (sep : ∀ (x y a : ℕ × ℕ),
        (0, 0) < a → (0, 0) < x → (0, 0) < y → prodLexLT x y →
        ∃ n m : ℕ, 0 < m ∧
          prodLexLT (m * x.1, m * x.2) (n * a.1, n * a.2) ∧
          prodLexLE (n * a.1, n * a.2) (m * y.1, m * y.2)), True := by
  intro ⟨sep, _⟩

  -- Take x = (0,1), y = (0,2), a = (1,0)
  let x : ℕ × ℕ := (0, 1)
  let y : ℕ × ℕ := (0, 2)
  let a : ℕ × ℕ := (1, 0)

  -- These are all positive (> (0,0)) in the standard product order
  have hx : (0, 0) < x := by simp [x]
  have hy : (0, 0) < y := by simp [y]
  have ha : (0, 0) < a := by simp [a]

  -- And x < y in lex order
  have hxy : prodLexLT x y := by
    unfold prodLexLT x y
    right
    exact ⟨rfl, by norm_num⟩

  -- Apply separation
  obtain ⟨n, m, hm_pos, h_left, h_right⟩ := sep x y a ha hx hy hxy

  -- Compute the products
  -- m * x = (0, m)
  -- n * a = (n, 0)
  -- m * y = (0, 2m)

  have prod_x : (m * x.1, m * x.2) = (0, m) := by simp [x]
  have prod_a : (n * a.1, n * a.2) = (n, 0) := by simp [a]
  have prod_y : (m * y.1, m * y.2) = (0, 2*m) := by simp [y]; ring

  rw [prod_x, prod_a] at h_left
  rw [prod_a, prod_y] at h_right

  -- h_left: (0,m) < (n,0) in lex order
  -- This requires: 0 < n OR (0 = n AND m < 0)
  -- The second case is impossible since m > 0

  unfold prodLexLT at h_left
  rcases h_left with hn_pos | ⟨h_absurd, h_m_neg⟩
  swap; · omega  -- m < 0 contradicts hm_pos : 0 < m

  -- So n ≥ 1
  have n_ge_1 : 1 ≤ n := hn_pos

  -- h_right: (n,0) ≤ (0,2m) in lex order
  -- This requires: n < 0 OR (n = 0 AND 0 ≤ 2m)

  unfold prodLexLE at h_right
  rcases h_right with hn_lt_zero | ⟨hn_eq_zero, _⟩

  -- Case 1: n < 0 contradicts n ≥ 1
  · omega

  -- Case 2: n = 0 contradicts n ≥ 1
  · omega

/-!
## What This Proves

**Theorem**: The commutative algebra ℕ × ℕ with componentwise addition does NOT satisfy KSSeparation.

**Interpretation**: KSSeparation rules out "independent dimensions."

**Corollary (informal)**: KSSeparation forces algebras to be 1-dimensional.

**Conjecture**: 1-dimensional ordered associative algebras are commutative.

**Therefore (conjectured)**: KSSeparation ⟹ Commutativity

## Why This Matters for K-S Formalization

This result suggests that:
1. K&S's claim that "commutativity is derived" is likely CORRECT
2. The derivation relies on the strength of the separation property
3. The proof might require showing that KSSeparation forces 1-dimensionality

The remaining work is to make "1-dimensionality" precise and complete the proof.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
