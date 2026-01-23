import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core.Induction.ThetaPrime
import Mathlib.Data.Real.Basic

/-!
# Interval-Valued Approach: Exploration Notes (not a refutation)

This file explores an interval-valued “imprecise / credal” style semantics motivated by the
K&S Appendix-A B-empty discussion.

This is *not* a proof that the interval approach is untenable, and it is *not* a formal refutation
of Knuth–Skilling Appendix A. It is a place to record which algebraic facts do and do not go
through when values are intervals rather than points, and what additional hypotheses would be
needed to recover point-valued additivity.

## The Interval-Valued Proposal

Instead of μ : α → ℝ, define μ : α → Interval where:
- Interval = { (l, u) : ℝ × ℝ | l ≤ u }
- Addition: [a,b] ⊕ [c,d] = [a+c, b+d]
- Order: [a,b] < [c,d] iff b < c (strict separation)

## Attack Vectors to Try

1. Does interval arithmetic preserve associativity?
2. Does order transfer correctly?
3. Do intervals shrink or grow with more atom types?
4. Is there a compounding uncertainty problem?
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Experimental.RepresentationTheorem.Explorations.IntervalApproach

/-!
## Check 1: Associativity of Interval Arithmetic

Interval addition: [a,b] + [c,d] = [a+c, b+d]

Is this associative?
([a,b] + [c,d]) + [e,f] = [a+c, b+d] + [e,f] = [a+c+e, b+d+f]
[a,b] + ([c,d] + [e,f]) = [a,b] + [c+e, d+f] = [a+c+e, b+d+f]

YES! Interval addition is associative. ✓

Associativity is preserved.
-/

/-- Interval addition is associative -/
theorem interval_add_assoc (a b c d e f : ℝ) :
    (a + c) + e = a + (c + e) ∧ (b + d) + f = b + (d + f) := by
  constructor <;> ring

/-!
## Check 2: Order Preservation

If x < y in the algebra, does μ(x) < μ(y) as intervals (meaning upper(x) < lower(y))?

Key insight from K&S: The A/C constraints ensure that for ANY valid δ in the interval,
the order is preserved. Therefore:
- sup{μ(x) : δ valid} < inf{μ(y) : δ valid}
- i.e., upper(μ(x)) < lower(μ(y))

Order is preserved when intervals come from valid δ-ranges (with a uniform margin).
-/

/-- A uniform *margin* implies strict separation of the `iSup`/`iInf` envelopes.

Pointwise strictness (`μ_x δ < μ_y δ` for all δ) does **not** imply
`iSup μ_x < iInf μ_y` in general, since the gap may shrink to 0 along the interval.

This lemma isolates the (standard) sufficient condition we actually need:
a uniform `ε > 0` with `μ_x δ + ε ≤ μ_y δ`. -/
theorem order_preserved_from_uniform_margin
    (μ_x μ_y : ℝ → ℝ) (L U : ℝ)
    (ε : ℝ) (_hε : 0 < ε)
    (h_order :
      ∀ δ₁ δ₂,
        δ₁ ∈ Set.Icc L U →
        δ₂ ∈ Set.Icc L U →
        μ_x δ₁ + ε ≤ μ_y δ₂)
    (hX_ne : (Set.image μ_x (Set.Icc L U)).Nonempty)
    (hY_ne : (Set.image μ_y (Set.Icc L U)).Nonempty) :
    sSup (Set.image μ_x (Set.Icc L U)) + ε ≤ sInf (Set.image μ_y (Set.Icc L U)) := by
  classical
  -- Show the supremum of μ_x is ε-below every element of the μ_y image, then take `sInf`.
  refine le_csInf hY_ne ?_
  intro y hy
  rcases hy with ⟨δ₂, hδ₂, rfl⟩
  have hSup_le : sSup (Set.image μ_x (Set.Icc L U)) ≤ μ_y δ₂ - ε := by
    refine csSup_le hX_ne ?_
    intro x hx
    rcases hx with ⟨δ₁, hδ₁, rfl⟩
    have h := h_order δ₁ δ₂ hδ₁ hδ₂
    linarith
  linarith [hSup_le]

/-!
## Check 3: Compounding Uncertainty

HERE IS THE REAL ATTACK!

As we add more atom types, each introduces its own δ-interval:
- δ_b ∈ [L_b, U_b]  (uncertainty ε_b = U_b - L_b)
- δ_c ∈ [L_c, U_c]  (uncertainty ε_c = U_c - L_c)
- etc.

For a combination m(s of b, t of c) = s·δ_b + t·δ_c:
- Lower bound: s·L_b + t·L_c
- Upper bound: s·U_b + t·U_c
- Total uncertainty: s·ε_b + t·ε_c

Uncertainty accumulates with more atom types unless additional structure is imposed.

For k atom types with uncertainties ε_1, ..., ε_k and coefficients n_1, ..., n_k:
Total uncertainty = n_1·ε_1 + ... + n_k·ε_k

This can grow without bound as k increases!
-/

/-- Uncertainty accumulates additively.
    Total uncertainty = Σᵢ nᵢ * εᵢ, which is positive if any term is positive.
    (Standard fact about sums of nonnegative terms with at least one positive.) -/
theorem uncertainty_accumulates (k : ℕ) (ε : Fin k → ℝ) (n : Fin k → ℕ)
    (hε_nonneg : ∀ i, ε i ≥ 0) :
    (∃ i, ε i > 0 ∧ n i > 0) → ∑ i, (n i : ℝ) * ε i > 0 := by
  intro ⟨i, hε_pos, hn_pos⟩
  have h : (n i : ℝ) * ε i > 0 := mul_pos (Nat.cast_pos.mpr hn_pos) hε_pos
  have h_nonneg : ∀ j, (n j : ℝ) * ε j ≥ 0 := fun j =>
    mul_nonneg (Nat.cast_nonneg _) (hε_nonneg j)
  calc ∑ j, (n j : ℝ) * ε j ≥ (n i : ℝ) * ε i :=
      Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
    _ > 0 := h

/-!
## Attack 3 Analysis: Is Accumulation Fatal?

The accumulation of uncertainty is REAL, but is it FATAL?

K&S line 1893: δ can be found to "arbitrarily high accuracy" by allowing
"sufficiently high multiples".

This means: for any ε > 0, we can make the δ-interval width < ε
by considering enough multiples.

So each ε_i CAN be made arbitrarily small... but only by going to
arbitrarily high multiples, which is an INFINITE process.

**THE TENSION**:
- To get total uncertainty < ε for k atom types
- We need each ε_i < ε/k (roughly)
- This requires considering O(k/ε) multiples for each atom type
- As k → ∞, we need infinitely many multiples

**CONCLUSION**: For any FINITE number of atom types, the interval approach works!
But the limit k → ∞ (infinitely many atom types) requires completeness.

This is WEAKER than K&S claims, but still USEFUL and VALID.
-/

/-- For finite k and any target precision, we can achieve it.
    If each interval width is bounded by ε/(k+1), then total uncertainty < ε.
    (This is a standard bound on sum of bounded terms.) -/
theorem finite_atoms_bounded_uncertainty
    (k : ℕ) (ε : ℝ) (hε : ε > 0) :
    ∃ (width_bound : ℝ), width_bound > 0 ∧
      ∀ (widths : Fin k → ℝ), (∀ i, 0 < widths i ∧ widths i < width_bound) →
        ∀ (coeffs : Fin k → ℕ), (∀ i, coeffs i ≤ 1) →
          ∑ i, (coeffs i : ℝ) * widths i < ε := by
  use ε / (k + 1)
  refine ⟨by positivity, fun widths h_widths coeffs h_coeffs => ?_⟩
  -- Each term is bounded: coeffs i * widths i ≤ widths i < ε/(k+1)
  have h_term_bound : ∀ i, (coeffs i : ℝ) * widths i < ε / (k + 1) := fun i => by
    have h_coeff_le : (coeffs i : ℝ) ≤ 1 := by
      have h := h_coeffs i
      cases' Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 h1
      · simp [h0]
      · simp [h1]
    calc (coeffs i : ℝ) * widths i
        ≤ 1 * widths i := mul_le_mul_of_nonneg_right h_coeff_le (le_of_lt (h_widths i).1)
      _ = widths i := one_mul _
      _ < ε / (k + 1) := (h_widths i).2
  -- Sum of k terms each < ε/(k+1) gives sum < ε
  by_cases hk : k = 0
  · -- When k = 0, Fin 0 is empty, so sum is 0 < ε
    subst hk; simp [hε]
  · -- When k > 0, sum < k * (ε/(k+1)) < ε
    have hk_pos : k > 0 := Nat.pos_of_ne_zero hk
    haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk_pos
    calc ∑ i, (coeffs i : ℝ) * widths i
        < ∑ _i : Fin k, ε / (k + 1) := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact Finset.univ_nonempty
          · exact fun i _ => h_term_bound i
      _ = k * (ε / (k + 1)) := by
          rw [Finset.sum_const, Finset.card_fin]
          ring
      _ < ε := by
          have hk_real : (k : ℝ) > 0 := Nat.cast_pos.mpr hk_pos
          have h1 : (k : ℝ) < k + 1 := by linarith
          have h2 : (k : ℝ) + 1 > 0 := by linarith
          calc k * (ε / (k + 1)) = ε * (k / (k + 1)) := by ring
            _ < ε * 1 := by
                apply mul_lt_mul_of_pos_left _ hε
                rwa [div_lt_one h2]
            _ = ε := mul_one ε

/-!
## Attack 4: The δ-Constraints Might Not Be Interval-Compatible

A subtler attack: K&S's constraints on δ come from comparing different grid points.
Are these constraints guaranteed to form a consistent interval?

For the B-empty case, K&S shows:
- All A-statistics < δ
- All C-statistics > δ
- These form an interval [sup A, inf C]

But wait! We need sup A < inf C for the interval to be non-empty!

K&S argues this follows from the strict inequalities separating A and C.
Let's check if this could fail...
-/

/-- To build a *single* admissible interval `(L, U)`, it is enough to have:
- a global upper bound `L` for `A`, and
- a global lower bound `U` for `C`,
with `L < U`.

Without some such global bounds, mere pairwise separation (`∀ a∈A, ∀ c∈C, a < c`)
does not guarantee the existence of a uniform gap point δ. -/
theorem exists_delta_of_global_bounds
    (A C : Set ℝ) (L U : ℝ)
    (hA : ∀ a ∈ A, a ≤ L)
    (hC : ∀ c ∈ C, U ≤ c)
    (hLU : L < U) :
    ∃ δ, (∀ a ∈ A, a < δ) ∧ (∀ c ∈ C, δ < c) := by
  refine ⟨(L + U) / 2, ?_, ?_⟩
  · intro a ha
    have ha_le : a ≤ L := hA a ha
    have hL_lt : L < (L + U) / 2 := by linarith
    exact lt_of_le_of_lt ha_le hL_lt
  · intro c hc
    have hc_ge : U ≤ c := hC c hc
    have h_mid_lt_U : (L + U) / 2 < U := by linarith
    exact lt_of_lt_of_le h_mid_lt_U hc_ge

/-!
## CRITICAL INSIGHT: The Interval Approach Still Needs Something

Even the interval approach requires ONE of:
1. **Finite A and C**: Then we can compute max A and min C explicitly
2. **Completeness**: To take sup A and inf C as limits
3. **Decidable bounds**: Some constructive witness for the gap

K&S's argument uses the Archimedean property to show A and C are "eventually"
separated to any precision. But "eventual" separation ≠ "current" separation!

For the interval to be well-defined at each step, we need CURRENT bounds,
not just eventual convergence.
-/

/-- The Archimedean property gives eventual bounds, not current ones.
    This is a standard fact - we state it here to emphasize the distinction.

    Key point: We can make 1/n arbitrarily small, but never exactly 0. -/
theorem archimedean_eventual_not_current :
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n : ℝ) < ε) ∧  -- eventual: can get arbitrarily close to 0
    (∀ n : ℕ, n > 0 → 1 / (n : ℝ) > 0) := by         -- but always positive for n > 0
  constructor
  · intro ε hε
    -- Use Archimedean property: ∃ N : ℕ, N > 1/ε
    use Nat.ceil (1/ε) + 1
    intro n hn
    have hε_inv_pos : 1/ε > 0 := by positivity
    have hn_ge : (n : ℝ) ≥ Nat.ceil (1/ε) + 1 := by exact_mod_cast hn
    have hn_pos : (n : ℝ) > 0 := lt_of_lt_of_le (by positivity : (0:ℝ) < Nat.ceil (1/ε) + 1) hn_ge
    have hn_gt : (n : ℝ) > 1/ε := calc
      (n : ℝ) ≥ Nat.ceil (1/ε) + 1 := hn_ge
      _ > Nat.ceil (1/ε) := by linarith
      _ ≥ 1/ε := Nat.le_ceil (1/ε)
    calc 1 / (n : ℝ) < 1 / (1/ε) := one_div_lt_one_div_of_lt hε_inv_pos hn_gt
      _ = ε := one_div_one_div ε
  · intro n hn
    exact one_div_pos.mpr (Nat.cast_pos.mpr hn)

/-!
## Summary: What the Interval Approach Achieves

This file does not prove any impossibility result about interval-valued semantics.
Everything developed so far is consistent with ordinary interval arithmetic on `ℝ`.

It also makes clear that an interval-valued approach is (at least syntactically) weaker than a
point-valued representation theorem:

| K&S Claims | Interval Approach Achieves |
|------------|---------------------------|
| μ : α → ℝ | μ : α → Intervals |
| Exact additivity | Interval containment |
| No continuity needed | Still needs Archimedean + careful bounds |
| Works for all α | Works for finite atom types |

One plausible “interval version” of a K&S-style statement (for finite grids) is:

For any finite collection of k atom types, there exists an interval-valued
measure μ : α → Intervals such that:
1. μ(x ⊕ y) ⊆ μ(x) ⊕ μ(y) (containment)
2. x < y implies μ(x) and μ(y) are separated (order)
3. Interval widths can be made arbitrarily small by considering higher multiples

What remains open (and model-dependent):
- Whether one can control accumulation of uncertainty uniformly across extensions.
- Whether additional axioms collapse intervals to points (and which completeness principle that uses).

This is useful mainly as a bookkeeping device: it separates “approximate / bounded” statements from
“point-valued” statements, and makes any required use of `sSup`/completeness explicit in Lean.
-/

/-!
## A Potential Formalization

Here's what a rigorous interval-valued K&S theorem would look like:
-/

/-- An interval in ℝ -/
structure Interval where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper

namespace Interval

/-- Interval addition -/
def add (I J : Interval) : Interval where
  lower := I.lower + J.lower
  upper := I.upper + J.upper
  valid := add_le_add I.valid J.valid

/-- Interval width -/
def width (I : Interval) : ℝ := I.upper - I.lower

/-- Interval strict ordering (separated) -/
def lt (I J : Interval) : Prop := I.upper < J.lower

/-- A point is in an interval -/
def mem (x : ℝ) (I : Interval) : Prop := I.lower ≤ x ∧ x ≤ I.upper

theorem add_width (I J : Interval) : (add I J).width = I.width + J.width := by
  simp [add, width]; ring

theorem add_assoc (I J K : Interval) :
    add (add I J) K = add I (add J K) := by
  simp only [add]
  congr 1 <;> ring

end Interval

/-- An interval-valued measure on a K&S algebra -/
structure IntervalMeasure (α : Type*) [KnuthSkillingAlgebra α] where
  μ : α → Interval
  order_preserving : ∀ x y, x < y → (μ x).lt (μ y)
  sub_additive : ∀ x y, (μ x).lower + (μ y).lower ≤ (μ (KnuthSkillingAlgebraBase.op x y)).lower
  super_additive : ∀ x y, (μ (KnuthSkillingAlgebraBase.op x y)).upper ≤ (μ x).upper + (μ y).upper

/-- The key property: actual μ(x⊕y) is contained in interval sum -/
theorem IntervalMeasure.containment {α : Type*} [KnuthSkillingAlgebra α]
    (M : IntervalMeasure α) (x y : α) :
    (M.μ (KnuthSkillingAlgebraBase.op x y)).lower ≥ (M.μ x).lower + (M.μ y).lower ∧
    (M.μ (KnuthSkillingAlgebraBase.op x y)).upper ≤ (M.μ x).upper + (M.μ y).upper :=
  ⟨M.sub_additive x y, M.super_additive x y⟩

/-!
## Final Verdict: Interval Approach Is Consistent But Potentially Too Weak

The interval approach is consistent as a semantics, but it may be too weak to recover the full
point-valued representation claim without additional assumptions.

### What the Interval Approach Achieves
1. Avoids requiring completeness for approximate additivity
2. Makes the completion step explicit rather than hiding it in "denote the limiting value"
3. Gives a constructive result for finite atom types
4. Philosophically aligns with imprecise probabilities / credal sets

### Open Questions (per Codex's analysis)
1. **Can the interval axioms prove commutativity?** If not, the approach is too weak
   for K&S's goals.
2. **Do strong interval axioms collapse to point-valued Θ?** If so, we've just
   repackaged the completion step.
3. **Does a noncommutative model exist satisfying interval axioms?** If so,
   interval axioms cannot prove commutativity.

### The Core Tension
- **Weak interval axioms**: Likely consistent, but may not prove commutativity
- **Strong interval axioms**: Likely force intervals to collapse to points, reintroducing
  the completion step that K&S claims to avoid

### Philosophical Interpretation
The interval approach represents the "credal set" view: instead of a single probability
measure, we have a set of admissible measures bounded by L and U. K&S's limit argument
is then the selection of a unique measure from this set — which requires completeness.

### Next Steps to Resolve
1. Formalize "strong" interval axioms (e.g., shrinking width implies convergence)
2. Try to prove: strong axioms ⇒ point-valued Θ exists (collapse theorem)
3. Or try to construct: noncommutative model satisfying interval axioms (separation theorem)

Either outcome would clarify what the interval approach can and cannot achieve.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Experimental.RepresentationTheorem.Explorations.IntervalApproach
