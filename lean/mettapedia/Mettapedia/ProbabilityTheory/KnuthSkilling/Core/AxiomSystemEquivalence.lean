/-
# Axiom-System Equivalence: Separation vs (Comm+Arch)+Representation

This file records a clean relationship between two axiom bundles that show up when
formalizing Knuth–Skilling Appendix A–style representation arguments:

1. The iterate/power “sandwich” separation axiom `KSSeparation` (over the core
   structure `KnuthSkillingAlgebraBase`).
2. A faithful additive order representation into ℝ (an order isomorphism `Θ : α ≃o ℝ`
   satisfying `Θ(op x y) = Θ x + Θ y`), which implies the sandwich axiom by rational density.

Paper cross-reference:
- `paper/ks-formalization.tex`, Section “Commutativity from Separation” (label `sec:commutativity`).
  The paper states the “separation (sandwich) ⇒ commutativity” direction; this file additionally
  records a clean reverse direction via a faithful additive order representation.

## Contents

### Direction 1: Separation ⇒ (Archimedean consequences + commutativity)

This is already proven in `Additive/Axioms/SandwichSeparation.lean`.

### Direction 2: Representation ⇒ Separation

If we have an additive order isomorphism Θ : α ≃o ℝ, then the sandwich axiom holds
automatically (because ℝ has rational density).

-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.FunctionalEquations

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical

namespace AxiomSystemEquivalence

open KnuthSkillingMonoidBase
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation

/-! ## Direction 1: Separation consequences

These are already proven in `Additive/Axioms/SandwichSeparation.lean`; we provide small wrappers
in the main K&S namespace.
-/

/-- `KSSeparation` gives an Archimedean-style bound: `x < a^n` for some `n`. -/
theorem archimedean_of_ksSeparation
    {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparation α]
    (a x : α) (ha : ident < a) :
    ∃ n : ℕ, x < Nat.iterate (op a) n a :=
  SandwichSeparation.SeparationToArchimedean.op_archimedean_of_separation (α := α) a x ha

/-- `KSSeparation` forces commutativity on the positive cone. -/
theorem comm_pos_of_ksSeparation
    {α : Type*} [KnuthSkillingMonoidBase α] [KSSeparation α]
    (x y : α) (hx : ident < x) (hy : ident < y) :
    op x y = op y x :=
  SandwichSeparation.ThetaAdditivity.ksSeparation_implies_comm (α := α) x y hx hy

/-- `KSSeparation` forces global commutativity of `op`. -/
theorem comm_of_ksSeparation
    {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α] (x y : α) :
    op x y = op y x :=
  SandwichSeparation.ksSeparation_implies_commutative (α := α) x y

/-! ## Direction 2: Representation ⇒ Separation

If we have an additive order isomorphism Θ : α ≃o ℝ (i.e., an `AdditiveOrderIsoRep`),
then the separation sandwich holds automatically.

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

/-- An additive order isomorphism implies the separation sandwich.

If Θ : α ≃o ℝ is an order isomorphism with Θ(x ⊕ y) = Θ(x) + Θ(y), then the separation sandwich holds.
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

/- ## Summary (informal)

- `KSSeparation` already implies commutativity (and an Archimedean-style consequence) over the
  core K&S structure.
- Any faithful additive order representation into ℝ implies `KSSeparation` by rational density.
-/

end AxiomSystemEquivalence

end Mettapedia.ProbabilityTheory.KnuthSkilling
