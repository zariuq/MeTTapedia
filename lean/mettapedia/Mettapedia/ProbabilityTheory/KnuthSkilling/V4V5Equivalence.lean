/-
# Goertzel v4 ↔ v5 Axiom Equivalence

This file establishes the precise equivalence between the v4 and v5 axiom systems
for the Knuth-Skilling representation theorem.

## Axiom Systems

**v4 Axioms** (assumes commutativity):
- A1a, A1b: Strict monotonicity
- A2: Associativity
- A3: Commutativity (x ⊕ y = y ⊕ x)
- A4: Archimedean property

**v5 Axioms** (derives commutativity):
- A1a, A1b: Strict monotonicity
- A2: Associativity
- A3: KSSeparation (replaces A3 + A4)

## Main Results

1. **v5 → v4**: `KSSeparation` implies both Archimedean and Commutativity
   - `ksSeparation_implies_archimedean`: KSSeparation → Archimedean
   - `ksSeparation_implies_comm`: KSSeparation → Commutativity

2. **v4 + Representation → v5**: If we have an additive order isomorphism Θ : α ≃o ℝ,
   then KSSeparation holds automatically (because ℝ has rational density).
   - `ksSeparation_of_additiveOrderIsoRep`: AdditiveOrderIsoRep → KSSeparation

## Equivalence Theorem

The axiom systems are equivalent in the presence of a faithful representation:

```
v5 (KSSeparation) ⟺ v4 (Comm + Arch) + faithful Θ : α ≃o ℝ exists
```

More precisely:
- v5 → v4: Direct (commutativity derived from separation)
- v4 → v5: Via the representation theorem (which v4 proves)

-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.GoertzelV5Separation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.FunctionalEquations

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical

/-! ## Direction 1: v5 → v4

This is already proven in `GoertzelV5Separation.lean`:
- `GoertzelV5.KSSeparationWeak.op_archimedean_of_separation`
- `GoertzelV5.ThetaAdditivity.ksSeparation_implies_comm`

Here we provide convenient wrappers in the main namespace.
-/

namespace V4V5Equivalence

open KnuthSkillingAlgebra
open GoertzelV5

/-! ### Archimedean from KSSeparation -/

/-- **v5 → v4 (Archimedean)**: KSSeparation implies the Archimedean property. -/
theorem archimedean_of_ksSeparation
    {α : Type*} [LinearOrder α] [KnuthSkillingAlgebraWeak α] [KSSeparationWeak α]
    (a x : α) (ha : KnuthSkillingAlgebraWeak.ident < a) :
    ∃ n : ℕ, x < Nat.iterate (KnuthSkillingAlgebraWeak.op a) n a :=
  KSSeparationWeak.op_archimedean_of_separation a x ha

/-! ### Commutativity from KSSeparation -/

/-- **v5 → v4 (Commutativity)**: KSSeparation implies commutativity. -/
theorem comm_of_ksSeparation
    {α : Type*} [LinearOrder α] [KnuthSkillingAlgebraWeak α] [KSSeparationWeak α]
    (x y : α) (hx : KnuthSkillingAlgebraWeak.ident < x) (hy : KnuthSkillingAlgebraWeak.ident < y) :
    KnuthSkillingAlgebraWeak.op x y = KnuthSkillingAlgebraWeak.op y x :=
  ThetaAdditivity.ksSeparation_implies_comm x y hx hy

/-! ## Direction 2: v4 + Representation → v5

If we have an additive order isomorphism Θ : α ≃o ℝ (i.e., an `AdditiveOrderIsoRep`),
then KSSeparation holds automatically.

**Key insight**: In ℝ with addition, separation is a consequence of rational density:
For any 0 < x < y and base a > 0, we can find n, m such that m·x < n·a ≤ m·y.
This is essentially the Archimedean property of ℝ plus density of rationals.
-/

/-- The separation property holds in (ℝ, +) due to rational density.

For any a, x, y > 0 with x < y, there exist n, m ∈ ℕ⁺ such that m·x < n·a ≤ m·y.

Proof idea: Choose m large enough that m·(y - x) > a, then find n with m·x < n·a ≤ m·y. -/
theorem real_separation (a x y : ℝ) (ha : 0 < a) (_hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧ (m : ℝ) * x < (n : ℝ) * a ∧ (n : ℝ) * a ≤ (m : ℝ) * y := by
  -- The gap y - x is positive
  have hgap : 0 < y - x := sub_pos.mpr hxy
  -- Choose m large enough that m * (y - x) > a (Archimedean)
  obtain ⟨m, hm⟩ := exists_nat_gt (a / (y - x))
  have hm_pos : 0 < m := by
    by_contra h
    push_neg at h
    interval_cases m
    simp at hm
    exact not_lt.mpr (le_of_lt (div_pos ha hgap)) hm
  -- m * (y - x) > a, so m * y - m * x > a
  have hm_gap : a < (m : ℝ) * (y - x) := by
    have : a / (y - x) < m := hm
    calc a = (a / (y - x)) * (y - x) := by field_simp
      _ < m * (y - x) := by
        apply mul_lt_mul_of_pos_right this hgap
  -- Rearranged: m * x + a < m * y
  have hm_ineq : (m : ℝ) * x + a < (m : ℝ) * y := by
    calc (m : ℝ) * x + a < (m : ℝ) * x + (m : ℝ) * (y - x) := by linarith
      _ = (m : ℝ) * y := by ring
  -- Use floor function: n' = floor(m * y / a)
  -- Then n' * a ≤ m * y by definition of floor
  let n' := Nat.floor ((m : ℝ) * y / a)
  have hn'_upper : (n' : ℝ) * a ≤ (m : ℝ) * y := by
    have h1 : (n' : ℝ) ≤ (m : ℝ) * y / a := Nat.floor_le (by positivity)
    calc (n' : ℝ) * a ≤ ((m : ℝ) * y / a) * a := mul_le_mul_of_nonneg_right h1 (le_of_lt ha)
      _ = (m : ℝ) * y := by field_simp
  -- Also: (n' + 1) * a > m * y by definition of floor
  have hn'_floor_upper : (m : ℝ) * y < ((n' : ℝ) + 1) * a := by
    have := Nat.lt_floor_add_one ((m : ℝ) * y / a)
    calc (m : ℝ) * y = ((m : ℝ) * y / a) * a := by field_simp
      _ < (↑(Nat.floor ((m : ℝ) * y / a)) + 1) * a := mul_lt_mul_of_pos_right this ha
  -- Check if n' works (i.e., m * x < n' * a)
  by_cases hn'_works : (m : ℝ) * x < (n' : ℝ) * a
  · exact ⟨n', m, hm_pos, hn'_works, hn'_upper⟩
  · -- n' doesn't work: n' * a ≤ m * x
    -- Then (n' + 1) * a > m * x (since the gap is a)
    -- But we need (n' + 1) * a ≤ m * y, i.e., not > m * y
    -- This is impossible: n' * a ≤ m * x and (n' + 1) * a > m * y together with
    -- m * x + a < m * y gives a contradiction
    push_neg at hn'_works
    exfalso
    -- From hn'_works: n' * a ≤ m * x
    -- From hm_ineq: m * x + a < m * y
    -- So: n' * a + a < m * y, i.e., (n' + 1) * a < m * y
    have h1 : ((n' : ℝ) + 1) * a < (m : ℝ) * y := by linarith
    -- But hn'_floor_upper says (n' + 1) * a > m * y. Contradiction!
    linarith

/-- **v4 + Representation → v5**: An additive order isomorphism implies KSSeparation.

If Θ : α ≃o ℝ is an order isomorphism with Θ(x ⊕ y) = Θ(x) + Θ(y), then KSSeparation holds.
This is because the separation property holds in ℝ (rational density). -/
theorem ksSeparation_of_additiveOrderIsoRep
    {α : Type*} [LinearOrder α] {op : α → α → α}
    (h : Literature.AdditiveOrderIsoRep α op)
    (ident : α)
    (h_ident_zero : h.Θ ident = 0)
    (iterate_op : α → ℕ → α)
    (h_iterate_zero : ∀ x, iterate_op x 0 = ident)
    (h_iterate_succ : ∀ x n, iterate_op x (n + 1) = op x (iterate_op x n)) :
    ∀ {a x y : α}, ident < a → ident < x → ident < y → x < y →
      ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  intro a x y ha hx hy hxy
  -- Map to ℝ using Θ
  have ha' : 0 < h.Θ a := by
    calc 0 = h.Θ ident := h_ident_zero.symm
      _ < h.Θ a := h.Θ.strictMono ha
  have hx' : 0 < h.Θ x := by
    calc 0 = h.Θ ident := h_ident_zero.symm
      _ < h.Θ x := h.Θ.strictMono hx
  have hy' : 0 < h.Θ y := by
    calc 0 = h.Θ ident := h_ident_zero.symm
      _ < h.Θ y := h.Θ.strictMono hy
  have hxy' : h.Θ x < h.Θ y := h.Θ.strictMono hxy
  -- Θ(iterate_op z k) = k * Θ(z)
  have h_iterate_Theta : ∀ z : α, ∀ k : ℕ, h.Θ (iterate_op z k) = k * h.Θ z := by
    intro z k
    induction k with
    | zero => simp [h_iterate_zero, h_ident_zero]
    | succ n ih =>
      rw [h_iterate_succ, h.map_op, ih]
      simp only [Nat.cast_succ]
      ring
  -- Use real separation
  obtain ⟨n, m, hm_pos, h_lower, h_upper⟩ := real_separation (h.Θ a) (h.Θ x) (h.Θ y) ha' hx' hy' hxy'
  refine ⟨n, m, hm_pos, ?_, ?_⟩
  · -- iterate_op x m < iterate_op a n
    apply h.Θ.lt_iff_lt.mp
    simp only [h_iterate_Theta]
    exact h_lower
  · -- iterate_op a n ≤ iterate_op y m
    apply h.Θ.le_iff_le.mp
    simp only [h_iterate_Theta]
    exact h_upper

/-! ## The Full Equivalence Theorem

The axiom systems are equivalent modulo the representation theorem:

- **Forward (v5 → v4)**: KSSeparation directly implies Archimedean + Commutativity
- **Backward (v4 → v5)**: v4 axioms prove the representation theorem, which gives
  an additive order isomorphism Θ, from which KSSeparation follows

Thus v4 and v5 are *equivalent* as axiomatic foundations for the K&S representation theorem.
-/

/-- **Equivalence Theorem (informal statement)**:

The following are equivalent for a Knuth-Skilling algebra:

1. (v5) The KSSeparation axiom holds
2. (v4) Commutativity + Archimedean + faithful representation Θ : α ≃o ℝ exists

The forward direction (1 → part of 2) is `comm_of_ksSeparation` and `archimedean_of_ksSeparation`.
The backward direction (2 → 1) is `ksSeparation_of_additiveOrderIsoRep`.

The "faithful representation exists" part of (2) is exactly what the representation theorem proves,
so v4 is self-supporting: its axioms prove the representation theorem, which then implies
KSSeparation, closing the equivalence loop.
-/
theorem v4_v5_equivalence_doc : True := trivial

end V4V5Equivalence

end Mettapedia.ProbabilityTheory.KnuthSkilling
