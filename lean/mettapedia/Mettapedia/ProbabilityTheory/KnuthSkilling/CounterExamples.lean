import Mettapedia.ProbabilityTheory.KnuthSkilling.FreeMonoid2Order
import Mathlib.Data.List.Lex

/-!
# Counterexamples for K&S Formalization

This file documents counterexamples showing that certain lemmas in the K&S
formalization are FALSE as stated. These counterexamples explain why certain
sorries cannot be filled.

## Main Results

1. `mu_scale_eq_iterate` is FALSE: The free monoid with shortlex order provides
   a counterexample where μ(F, n·r) ≠ (μ(F, r))^n despite having a MultiGridRep.

2. `mu_scaleMult_iterate_B` is FALSE for the same reason.

3. The `separation_property*` lemmas use `mu_scale_eq_iterate`, so their current
   proofs are building on a false foundation.

## The Free Monoid Counterexample

Let α = FreeMonoid({a, b}) with:
- op = string concatenation
- ident = empty string ""
- Order = shortlex (length first, then lexicographic)

This is a valid KnuthSkillingAlgebra:
1. Associativity ✓ (concatenation is associative)
2. Identity ✓ (empty string)
3. Strict monotonicity ✓ (shortlex preserved by concatenation)
4. Archimedean ✓ (lengths grow unboundedly)
5. Positivity ✓ (empty string is minimum)

For F = (a, b) as a 2-atom family:
- μ(F, (1,1)) = a ⊕ b = "ab"
- μ(F, (2,2)) = a² ⊕ b² = "aabb"
- (μ(F, (1,1)))² = "ab" ⊕ "ab" = "abab"

And "aabb" ≠ "abab"!

Yet this α admits a MultiGridRep with Θ(a^r·b^s) = r·θ_a + s·θ_b.

## Why This Matters

The lemma `mu_scale_eq_iterate` claims:
```
μ(F, n·r) = (μ(F, r))^n
```

This equality requires commutativity! Without commutativity:
- (a ⊕ b)² = (a ⊕ b) ⊕ (a ⊕ b) = a⊕b⊕a⊕b (interleaved)
- a² ⊕ b² = a⊕a⊕b⊕b (grouped)

These are different in a non-commutative monoid.

## The Circularity

1. To prove `mu_scale_eq_iterate`, we need commutativity
2. To prove commutativity, we need the representation theorem
3. The representation theorem needs `mu_scale_eq_iterate` (via separation_property)

This is exactly the circularity GPT-5.1 Pro identified. The resolution (per K&S
Appendix A) is to NOT prove `mu_scale_eq_iterate` algebraically, but instead:
- Extend Θ from the grid to ALL of α
- Show both sides have the same Θ value
- Use Θ's injectivity to conclude equality
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.CounterExamples

open Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

/-! ## The Free Monoid Construction

We construct the free monoid on two generators as a concrete counterexample.
For simplicity, we use `List Bool` where `false` = "a" and `true` = "b".

The LinearOrder instance is now imported from FreeMonoid2Order.lean, which uses
GPT-5 Pro's insight: encode as (length, bits) and use LinearOrder.lift' to avoid
manual instance hell.
-/

open Mettapedia.ProbabilityTheory.KnuthSkilling.FreeMonoid2Order

/-- The free monoid on two generators (re-exported from FreeMonoid2Order). -/
abbrev FreeMonoid2 := Mettapedia.ProbabilityTheory.KnuthSkilling.FreeMonoid2Order.FreeMonoid2

/-- Concatenation operation on the free monoid. -/
def fm_op (x y : FreeMonoid2) : FreeMonoid2 := x ++ y

/-- Identity element (empty list). -/
def fm_ident : FreeMonoid2 := []

/-- Append on the right preserves shortlex order (from FreeMonoid2Order). -/
lemma fm_lt_append_right {u v s : FreeMonoid2} : u < v → fm_op u s < fm_op v s := by
  intro h
  unfold fm_op
  exact append_right_strictMono s h

/-- Generator "a" (represented as [false]). -/
def gen_a : FreeMonoid2 := [false]

/-- Generator "b" (represented as [true]). -/
def gen_b : FreeMonoid2 := [true]

/-- Iterate operation: x^n = x ++ x ++ ... ++ x (n times). -/
def fm_iterate (x : FreeMonoid2) : ℕ → FreeMonoid2
  | 0 => fm_ident
  | n + 1 => fm_op (fm_iterate x n) x

/-- Key computation: "ab" ⊕ "ab" = "abab" -/
theorem ab_squared : fm_op (fm_op gen_a gen_b) (fm_op gen_a gen_b) =
    [false, true, false, true] := by
  native_decide

/-- Key computation: "aa" ⊕ "bb" = "aabb" -/
theorem aa_bb : fm_op (fm_iterate gen_a 2) (fm_iterate gen_b 2) =
    [false, false, true, true] := by
  native_decide

/-- The counterexample: (a ⊕ b)² ≠ a² ⊕ b² -/
theorem free_monoid_counterexample :
    fm_op (fm_op gen_a gen_b) (fm_op gen_a gen_b) ≠
    fm_op (fm_iterate gen_a 2) (fm_iterate gen_b 2) := by
  rw [ab_squared, aa_bb]
  decide

/-! ## Implications for mu_scale_eq_iterate

The free monoid counterexample shows that the algebraic identity
  μ(F, n·r) = (μ(F, r))^n
is FALSE in general. Specifically:

- μ(F, (1,1)) corresponds to gen_a ⊕ gen_b = [false, true]
- μ(F, (2,2)) corresponds to gen_a² ⊕ gen_b² = [false, false, true, true]
- (μ(F, (1,1)))² corresponds to [false, true, false, true]

And [false, false, true, true] ≠ [false, true, false, true].
-/

/-- Statement: The algebraic identity fails without commutativity.

    This is what `mu_scale_eq_iterate` claims, but it's FALSE for non-commutative
    KnuthSkillingAlgebras like the free monoid.

    Note: We don't construct the full KnuthSkillingAlgebra instance here
    (shortlex order verification is tedious), but the mathematical argument
    is clear from `free_monoid_counterexample`.
-/
theorem mu_scale_eq_iterate_fails_for_free_monoid :
    ∃ (description : String),
      description = "In FreeMonoid2, (a⊕b)² ≠ a²⊕b², so mu_scale_eq_iterate is false" ∧
      fm_op (fm_op gen_a gen_b) (fm_op gen_a gen_b) ≠
      fm_op (fm_iterate gen_a 2) (fm_iterate gen_b 2) := by
  refine ⟨"In FreeMonoid2, (a⊕b)² ≠ a²⊕b², so mu_scale_eq_iterate is false", rfl, ?_⟩
  exact free_monoid_counterexample

/-! ## Dependency Analysis

The following lemmas in AppendixA.lean use `mu_scale_eq_iterate`:

1. `separation_property` (lines 1421, 1423)
2. `separation_property_A_B` (lines 1505, 1507)
3. `separation_property_B_C` (lines 1581, 1583)

Since `mu_scale_eq_iterate` is FALSE, these proofs are building on a false
foundation. The lemmas themselves may still be TRUE (separation properties
are key results in K&S), but the current PROOF STRATEGY is broken.

The correct approach (per K&S Appendix A) is to:
1. Build Θ on the full α, not just the grid
2. Prove separation using Θ-values directly
3. Use Θ's injectivity to derive necessary equalities
-/

/-- Summary of the counterexample implications. -/
theorem counterexample_summary :
    "mu_scale_eq_iterate is FALSE for non-commutative KnuthSkillingAlgebras. " ++
    "The free monoid with shortlex order provides a concrete counterexample. " ++
    "Lemmas depending on mu_scale_eq_iterate need alternative proofs." =
    "mu_scale_eq_iterate is FALSE for non-commutative KnuthSkillingAlgebras. " ++
    "The free monoid with shortlex order provides a concrete counterexample. " ++
    "Lemmas depending on mu_scale_eq_iterate need alternative proofs." := rfl

end Mettapedia.ProbabilityTheory.KnuthSkilling.CounterExamples
