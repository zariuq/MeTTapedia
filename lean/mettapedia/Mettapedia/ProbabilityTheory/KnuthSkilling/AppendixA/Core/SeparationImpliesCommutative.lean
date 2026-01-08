import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core

open Classical KnuthSkillingAlgebra

/-!
# Proof: KSSeparation Implies Commutativity

This file contains a direct proof that KSSeparation forces commutativity.

## Strategy

The key insight: if x ⊕ y ≠ y ⊕ x, use separation with (x⊕y) as the base to separate
(x⊕y) from (y⊕x). This leads to a constraint on growth rates that's impossible to satisfy.

## The Core Lemma

If a < b, then for all k: a^k < b^k (by strict monotonicity).
This means the "ratio" b^k / a^k is > 1 for all k.
If a^n ≤ b^m with n > m, this violates growth rate constraints.
-/

variable {α : Type*} [KnuthSkillingAlgebra α] [KSSeparation α]

/-!
## Lemma 1: Powers Preserve Strict Inequality

If a < b, then a^k < b^k for all k > 0.
-/

theorem iterate_op_lt_iterate_op {a b : α} (hab : a < b) (k : ℕ) (hk : 0 < k) :
    iterate_op a k < iterate_op b k := by
  induction k with
  | zero => exact absurd hk (Nat.not_lt_zero 0)
  | succ k ih =>
    cases Nat.eq_zero_or_pos k with
    | inl h =>
      -- k = 0, so k+1 = 1
      subst h
      simp [iterate_op_one]
      exact hab
    | inr hk_pos =>
      -- k > 0, use IH
      calc iterate_op a (k + 1)
          = op a (iterate_op a k) := rfl
        _ < op a (iterate_op b k) := by
            apply op_strictMono_right
            exact ih hk_pos
        _ < op b (iterate_op b k) := by
            apply op_strictMono_left
            exact hab
        _ = iterate_op b (k + 1) := rfl

/-!
## Lemma 2: Reverse Inequality in Powers

If we have a < b and a^n ≤ b^m with n > m, we can derive useful constraints.

Key idea: Since a < b, we have a^m < b^m.
Also, since n > m, we have a^m < a^n.
Combined with a^n ≤ b^m, we get a^m < a^n ≤ b^m.

But we also have a^m < b^m, so we're squeezing a^n between a^m and b^m.
-/

theorem power_inequality_squeeze {a b : α} (hab : a < b) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnm : m < n)
    (h : iterate_op a n ≤ iterate_op b m) :
    iterate_op a n < iterate_op b n := by
  -- Since a < b and n > 0, we have a^n < b^n
  exact iterate_op_lt_iterate_op hab n hn

/-!
## Lemma 3: Growth Rate Constraint

If a < b and 0 < m < n, then a^n cannot be ≤ b^m.

Proof:
- a^m < b^m (by Lemma 1)
- a^m < a^n (by strict monotonicity of iterate_op)
- b^m < b^n (by strict monotonicity of iterate_op)

So: a^m < min(a^n, b^m) < max(a^n, b^m) < b^n

If a^n ≤ b^m, then a^n ≤ b^m < b^n, so a^n < b^n ✓

But we also have: a^n > a^m and b^m > a^m
For a^n ≤ b^m with n > m, we need...

Hmm, this isn't obviously contradictory yet. Let me think harder.
-/

/-!
## Alternative Approach: Use Specific Element Separation

Instead of trying to prove a general growth rate lemma, let's use the specific
structure of x⊕y vs y⊕x.

If x⊕y < y⊕x, apply separation with different bases and derive constraints.
-/

theorem separation_self_base (x y : α) (hx : ident < x) (hy : ident < y)
    (hne : op x y ≠ op y x) (hlt : op x y < op y x) :
    ∃ n m : ℕ, 0 < m ∧
    iterate_op (op x y) m < iterate_op (op x y) n ∧
    iterate_op (op x y) n ≤ iterate_op (op y x) m := by
  -- Use KSSeparation with base a = (x⊕y) to separate (x⊕y) from (y⊕x)
  have hxy : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op x ident := op_strictMono_left ident hx
         _ = x := op_ident_right x
         _ < op x y := by
           calc x = op x ident := (op_ident_right x).symm
                _ < op x y := op_strictMono_right x hy

  have hyx : ident < op y x := by
    calc ident = op ident ident := (op_ident_left ident).symm
         _ < op y ident := op_strictMono_left ident hy
         _ = y := op_ident_right y
         _ < op y x := by
           calc y = op y ident := (op_ident_right y).symm
                _ < op y x := op_strictMono_right y hx

  exact KSSeparation.separation hxy hxy hyx hlt

/-!
## The Main Theorem

**Theorem**: KSSeparation implies commutativity.

**Proof**:
Assume x ⊕ y ≠ y ⊕ x for some x, y > ident.
WLOG x ⊕ y < y ⊕ x.

Apply separation with base a = (x⊕y):
∃n,m: (x⊕y)^m < (x⊕y)^n ≤ (y⊕x)^m

From (x⊕y)^m < (x⊕y)^n: m < n (by strictMono)

From x⊕y < y⊕x: (x⊕y)^k < (y⊕x)^k for all k > 0

Taking k = n: (x⊕y)^n < (y⊕x)^n

But we also have (x⊕y)^n ≤ (y⊕x)^m where m < n.

Since m < n, by strictMono: (y⊕x)^m < (y⊕x)^n

So: (x⊕y)^n ≤ (y⊕x)^m < (y⊕x)^n

This gives: (x⊕y)^n < (y⊕x)^n ✓ (consistent)

But now use separation again with base a = (y⊕x):
∃n',m': (x⊕y)^m' < (y⊕x)^n' ≤ (y⊕x)^m'

Wait, that's (y⊕x)^n' ≤ (y⊕x)^m', which requires n' ≤ m'.
But from (x⊕y)^m' < (y⊕x)^n', we need m' < n' (roughly).

Hmm, not quite a contradiction...

Let me try yet another approach.
-/

/-!
## Alternative: Use Both x and y as Bases

Apply separation with base x to separate (x⊕y) from (y⊕x):
∃n₁,m₁: (x⊕y)^m₁ < x^n₁ ≤ (y⊕x)^m₁

Apply separation with base y to separate (x⊕y) from (y⊕x):
∃n₂,m₂: (x⊕y)^m₂ < y^n₂ ≤ (y⊕x)^m₂

Now, x^n₁ and y^n₂ are both "between" (x⊕y)^m and (y⊕x)^m for appropriate m.

Can we derive a constraint from this?

Actually, let me think about what we know about x^k vs (x⊕y)^k...

We have: x < x⊕y (since y > ident and op is strictly monotone)
So: x^k < (x⊕y)^k for all k > 0

Similarly: y < y⊕x
So: y^k < (y⊕x)^k for all k > 0

From (x⊕y)^m₁ < x^n₁:
We have (x⊕y)^m₁ < x^n₁ but x^n₁ < (x⊕y)^n₁

So we need m₁ and n₁ such that (x⊕y)^m₁ < x^n₁ < (x⊕y)^n₁

But can this happen if x < x⊕y?

If x < x⊕y, then x^k < (x⊕y)^k for all k.
So x^n₁ < (x⊕y)^n₁ ✓

But for (x⊕y)^m₁ < x^n₁, we need the smaller base (x) with bigger power (n₁)
to beat the bigger base (x⊕y) with smaller power (m₁).

This CAN happen! If n₁ >> m₁, then x^n₁ can beat (x⊕y)^m₁.

So this doesn't give a contradiction either...

I'm stuck. Let me try to think of a completely different approach.
-/

/-!
## Last Attempt: Direct Combinatorial Argument

Maybe I need to actually analyze the structure of (x⊕y)^2 vs (y⊕x)^2.

(x⊕y)^2 = (x⊕y) ⊕ (x⊕y) = x ⊕ (y ⊕ x) ⊕ y (by associativity)
(y⊕x)^2 = (y⊕x) ⊕ (y⊕x) = y ⊕ (x ⊕ y) ⊕ x (by associativity)

If x ⊕ y < y ⊕ x, what can we say about these?

By monotonicity:
x ⊕ (y ⊕ x) ⊕ y vs y ⊕ (x ⊕ y) ⊕ x

Hmm, the middle terms are swapped. Can we use this?

Actually, I realize I need commutativity to rearrange terms, which is circular.

The fundamental issue: without commutativity, I can't manipulate the expressions
(x⊕y)^k in a useful way.
-/

  /-!
  ## Open Problem (Recorded as a `Prop`)

  Despite many partial constraints obtainable from `KSSeparation`, we do not currently have a
  complete Lean proof that `KSSeparation` forces commutativity. The main obstruction is turning
  inequalities about iterates `(x ⊕ y)^k` into contradictions without already assuming the ability
  to rearrange/reassociate those iterates.

  To keep this file `sorry`-free, we record the target statement as a `Prop`. -/

  /-- Conjecture: `KSSeparation` implies commutativity. -/
  def SeparationImpliesCommutative : Prop :=
    ∀ x y : α, op x y = op y x

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core
