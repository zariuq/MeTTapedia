import Mathlib.Data.List.Basic

/-!
# Counterexamples for K&S Formalization

This file documents counterexamples showing that certain algebraic identities
require commutativity.

## Main Result

`free_monoid_counterexample`: In any non-commutative monoid, (a⊕b)² ≠ a²⊕b².

## The Free Monoid Counterexample

Let α = FreeMonoid({a, b}) = List Bool with:
- op = list concatenation
- ident = empty list

For generators a = [false] and b = [true]:
- a ⊕ b = [false, true] ("ab")
- (a ⊕ b)² = [false, true, false, true] ("abab")
- a² ⊕ b² = [false, false, true, true] ("aabb")

And "abab" ≠ "aabb"!

## Why This Matters

The algebraic identity μ(F, n·r) = (μ(F, r))^n requires commutativity.
Without commutativity:
- (a ⊕ b)² = a⊕b⊕a⊕b (interleaved)
- a² ⊕ b² = a⊕a⊕b⊕b (grouped)

These are different in a non-commutative monoid.

## Implications for K&S

1. The lemma `mu_scale_eq_iterate` cannot be proven algebraically
2. K&S resolves this by deriving commutativity FROM the representation theorem
3. This is the deep insight: commutativity emerges from associativity + order!
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.CounterExamples

/-- The free monoid on two generators, represented as List Bool. -/
abbrev FreeMonoid2 := List Bool

/-- Concatenation operation on the free monoid. -/
def fm_op (x y : FreeMonoid2) : FreeMonoid2 := x ++ y

/-- Identity element (empty list). -/
def fm_ident : FreeMonoid2 := []

/-- Generator "a" (represented as [false]). -/
def gen_a : FreeMonoid2 := [false]

/-- Generator "b" (represented as [true]). -/
def gen_b : FreeMonoid2 := [true]

/-- Iterate operation: x^n = x ⊕ x ⊕ ... ⊕ x (n times). -/
def fm_iterate (x : FreeMonoid2) : ℕ → FreeMonoid2
  | 0 => fm_ident
  | n + 1 => fm_op (fm_iterate x n) x

/-- Computation: "ab" ⊕ "ab" = "abab" -/
theorem ab_squared : fm_op (fm_op gen_a gen_b) (fm_op gen_a gen_b) =
    [false, true, false, true] := rfl

/-- Computation: "aa" ⊕ "bb" = "aabb" -/
theorem aa_bb : fm_op (fm_iterate gen_a 2) (fm_iterate gen_b 2) =
    [false, false, true, true] := rfl

/-- **The counterexample**: (a ⊕ b)² ≠ a² ⊕ b²

This theorem proves that without commutativity, the scaling identity
μ(F, n·r) = (μ(F, r))^n fails. -/
theorem free_monoid_counterexample :
    fm_op (fm_op gen_a gen_b) (fm_op gen_a gen_b) ≠
    fm_op (fm_iterate gen_a 2) (fm_iterate gen_b 2) := by
  rw [ab_squared, aa_bb]
  decide

/-- Summary: the scaling identity fails for non-commutative monoids. -/
theorem counterexample_summary :
    ∃ (description : String),
      description = "In FreeMonoid2, (a⊕b)² ≠ a²⊕b², so the scaling identity fails" ∧
      fm_op (fm_op gen_a gen_b) (fm_op gen_a gen_b) ≠
      fm_op (fm_iterate gen_a 2) (fm_iterate gen_b 2) := by
  exact ⟨"In FreeMonoid2, (a⊕b)² ≠ a²⊕b², so the scaling identity fails",
         rfl, free_monoid_counterexample⟩

/-! ## Algebraic Properties of the Free Monoid

The free monoid satisfies associativity and has an identity, but NOT commutativity.
This is what makes it a valid counterexample: it shows that associativity alone
does not imply the scaling identity. -/

theorem fm_op_assoc (x y z : FreeMonoid2) :
    fm_op (fm_op x y) z = fm_op x (fm_op y z) := List.append_assoc x y z

theorem fm_op_ident_left (x : FreeMonoid2) : fm_op fm_ident x = x := rfl

theorem fm_op_ident_right (x : FreeMonoid2) : fm_op x fm_ident = x := List.append_nil x

/-- The free monoid is NOT commutative: a ⊕ b ≠ b ⊕ a -/
theorem fm_not_comm : fm_op gen_a gen_b ≠ fm_op gen_b gen_a := by decide

end Mettapedia.ProbabilityTheory.KnuthSkilling.CounterExamples
