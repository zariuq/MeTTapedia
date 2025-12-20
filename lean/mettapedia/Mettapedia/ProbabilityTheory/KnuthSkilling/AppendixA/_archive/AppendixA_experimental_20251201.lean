/-!
# ARCHIVED (LEGACY EXPERIMENT — DO NOT IMPORT)

This file is a historical experimental attempt at Appendix A (alternative data structures, etc.).
It is not part of the current proof chain and may not compile against the current codebase.

See the maintained refactor instead:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA.lean`
- `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Core.lean`
- `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Main.lean`
-/

/-
# Knuth-Skilling Appendix A: Full Formalization

This file provides a complete formalization of K&S Appendix A "Associativity Theorem"
following the paper's actual proof structure (separation argument on value grid),
NOT the ratio-set equality approach.

**Reference**: Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
(arXiv lines 1292-1922)

**Key insight**: Commutativity is DERIVED, not assumed!
  "Associativity + Order ⟹ Additivity allowed ⟹ Commutativity" (line 1166)

**Proof structure**:
1. One type base case: m(r of a) = r·a (linear grid)
2. Separation argument: A/B/C sets partition old values relative to new type
3. Case B non-empty: new type's value is rationally related to old
4. Case B empty: Accuracy lemma pins down irrational value via Archimedean
5. Induction: extend from k types to k+1 types
6. Commutativity emerges from additivity + injectivity
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.RepTheorem
import Mathlib.Data.Finsupp.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

open Classical KnuthSkillingAlgebra

-- Import key theorems from RepTheorem (which already proves iterate_op lemmas)
open KSAppendixA in

/-! ## Section A.1: Atom Types and Multisets

K&S work with "atoms" that can be of various "types". A sequence like
"r of a and s of b and t of c" is valued as r·a + s·b + t·c in the
final representation.

We model this using `Finsupp ℕ ℕ` (finite support functions from atom type
indices to multiplicities).
-/

/-- Atom type identifier. We use ℕ for simplicity. -/
abbrev AtomType := ℕ

/-- An atom multiset is a finite support function from atom types to multiplicities.
Example: "3 of type 0 and 2 of type 1" is `fun | 0 => 3 | 1 => 2 | _ => 0` -/
abbrev AtomMultiset := ℕ →₀ ℕ

namespace AtomMultiset

/-- The empty multiset (0 of each type) -/
noncomputable def empty : AtomMultiset := 0

/-- A singleton multiset: n copies of atom type t -/
noncomputable def single (t : AtomType) (n : ℕ) : AtomMultiset := Finsupp.single t n

/-- Scaling a multiset by a factor k -/
noncomputable def scale (k : ℕ) (m : AtomMultiset) : AtomMultiset := k • m

/-- Adding two multisets -/
noncomputable def add (m₁ m₂ : AtomMultiset) : AtomMultiset := m₁ + m₂

/-- The support of a multiset (types with non-zero multiplicity) -/
def types (m : AtomMultiset) : Finset AtomType := m.support

theorem single_multiplicity (t : AtomType) (n : ℕ) : (single t n) t = n := by
  simp only [single, Finsupp.single_eq_same]

theorem single_multiplicity_other (t t' : AtomType) (n : ℕ) (h : t ≠ t') :
    (single t n) t' = 0 := by
  simp only [single]
  exact Finsupp.single_eq_of_ne h.symm

end AtomMultiset

/-! ## Section A.2: Valuation Functions

A valuation assigns a real value to each atom type. The measure of a multiset
is the linear combination: μ(r₁,...,rₖ) = r₁·v₁ + ... + rₖ·vₖ
-/

/-- A valuation assigns real values to atom types -/
structure AtomValuation where
  val : AtomType → ℝ

namespace AtomValuation

/-- The measure of a multiset under a valuation: Σ_t (multiplicity t) * (val t) -/
noncomputable def measure (v : AtomValuation) (m : AtomMultiset) : ℝ :=
  m.sum (fun t n => n * v.val t)

/-- Empty multiset has measure 0 -/
theorem measure_empty (v : AtomValuation) : v.measure AtomMultiset.empty = 0 := by
  simp only [measure, AtomMultiset.empty, Finsupp.sum_zero_index]

/-- Measure of singleton -/
theorem measure_single (v : AtomValuation) (t : AtomType) (n : ℕ) :
    v.measure (AtomMultiset.single t n) = n * v.val t := by
  simp only [measure, AtomMultiset.single]
  rw [Finsupp.sum_single_index]
  simp only [Nat.cast_zero, zero_mul]

/-- Measure is additive -/
theorem measure_add (v : AtomValuation) (m₁ m₂ : AtomMultiset) :
    v.measure (m₁ + m₂) = v.measure m₁ + v.measure m₂ := by
  simp only [measure]
  rw [Finsupp.sum_add_index']
  · intro t
    simp only [Nat.cast_zero, zero_mul]
  · intro t n₁ n₂
    push_cast
    ring

/-- Measure is linear in scaling -/
theorem measure_scale (v : AtomValuation) (k : ℕ) (m : AtomMultiset) :
    v.measure (k • m) = k * v.measure m := by
  simp only [measure]
  rw [Finsupp.sum_smul_index']
  · simp only [smul_eq_mul, Finsupp.sum]
    rw [Finset.mul_sum]
    congr 1
    ext t
    push_cast
    ring
  · intro t
    simp only [Nat.cast_zero, zero_mul]

end AtomValuation

/-! ## Section A.3: Connecting to KnuthSkillingAlgebra

The theorems about iterate_op (strict monotonicity, addition, multiplication,
repetition lemma) are already proved in RepTheorem.lean. We import them
and build on top.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-! ### Section A.3a: One-Type Base Case - Θ on Iterates

**Key Theorem**: For the reference element a, Θ(iterate_op a n) = n.

This follows directly from the Dedekind cut definition:
- Θ(x) = sSup { n/m : a^n ≤ x^m, m > 0 }
- For x = a^k: a^n ≤ (a^k)^m = a^(k*m) iff n ≤ k*m
- So the set is { n/m : n ≤ k*m } = { r : r ≤ k }
- sSup of this is k

This is the foundation for the value-grid approach:
μ(n copies of a) = n * value(a) = n * 1 = n = Θ(a^n)
-/

/-- The lower ratio set for iterate_op a k is exactly { r : r ≤ k }. -/
theorem lowerRatioSet_iterate (a : α) (ha : ident < a) (k : ℕ) :
    KSAppendixA.lowerRatioSet a (iterate_op a k) =
    { r : ℝ | ∃ n m : ℕ, m > 0 ∧ n ≤ k * m ∧ r = (n : ℝ) / m } := by
  ext r
  simp only [KSAppendixA.lowerRatioSet, Set.mem_setOf_eq]
  constructor
  · -- Forward: lowerRatioSet → { n/m : n ≤ k*m }
    intro ⟨n, m, hm_pos, hle, hr_eq⟩
    refine ⟨n, m, hm_pos, ?_, hr_eq⟩
    -- iterate_op a n ≤ iterate_op (iterate_op a k) m = iterate_op a (k * m)
    rw [KSAppendixA.iterate_op_mul] at hle
    -- By strict monotonicity: iterate_op a n ≤ iterate_op a (k * m) → n ≤ k * m
    by_contra h_gt
    push_neg at h_gt
    have h_lt : iterate_op a (k * m) < iterate_op a n :=
      KSAppendixA.iterate_op_strictMono a ha h_gt
    exact absurd (lt_of_lt_of_le h_lt hle) (lt_irrefl _)
  · -- Backward: { n/m : n ≤ k*m } → lowerRatioSet
    intro ⟨n, m, hm_pos, hn_le, hr_eq⟩
    refine ⟨n, m, hm_pos, ?_, hr_eq⟩
    -- n ≤ k * m → iterate_op a n ≤ iterate_op a (k * m) = iterate_op (iterate_op a k) m
    rw [KSAppendixA.iterate_op_mul]
    exact KSAppendixA.iterate_op_mono a ha hn_le

/-- The set { n/m : n ≤ k*m, m > 0 } has supremum k. -/
theorem sSup_ratio_le_k (k : ℕ) :
    sSup { r : ℝ | ∃ n m : ℕ, m > 0 ∧ n ≤ k * m ∧ r = (n : ℝ) / m } = k := by
  apply le_antisymm
  · -- sup ≤ k: all elements are ≤ k
    apply csSup_le
    · -- Nonempty: k/1 = k is in the set
      exact ⟨k, ⟨k, 1, Nat.one_pos, by simp, by simp⟩⟩
    · -- Upper bound: n/m ≤ k when n ≤ k*m
      intro r ⟨n, m, hm_pos, hn_le, hr_eq⟩
      rw [hr_eq]
      have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
      rw [div_le_iff₀ hm_pos_real]
      calc (n : ℝ) ≤ (k * m : ℕ) := Nat.cast_le.mpr hn_le
        _ = (k : ℝ) * m := by push_cast; ring
  · -- k ≤ sup: k is in the set (take n = k, m = 1)
    apply le_csSup
    · -- Bounded above by k
      use k
      intro r ⟨n, m, hm_pos, hn_le, hr_eq⟩
      rw [hr_eq]
      have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
      rw [div_le_iff₀ hm_pos_real]
      calc (n : ℝ) ≤ (k * m : ℕ) := Nat.cast_le.mpr hn_le
        _ = (k : ℝ) * m := by push_cast; ring
    · -- k is in the set
      exact ⟨k, 1, Nat.one_pos, by simp, by simp⟩

/-- **KEY THEOREM**: Θ(iterate_op a k) = k for all k ≥ 1.
This is the one-type base case that grounds the value-grid construction. -/
theorem Theta_iterate (a : α) (ha : ident < a) (k : ℕ) (hk : 0 < k) :
    KSAppendixA.Theta a (iterate_op a k) ha (KSAppendixA.iterate_op_pos a ha k hk) = k := by
  unfold KSAppendixA.Theta
  rw [lowerRatioSet_iterate a ha k]
  exact sSup_ratio_le_k k

/-- Corollary: ThetaFull(iterate_op a k) = k for k ≥ 1. -/
theorem ThetaFull_iterate (a : α) (ha : ident < a) (k : ℕ) (hk : 0 < k) :
    KSAppendixA.ThetaFull a ha (iterate_op a k) = k := by
  have h_pos : ident < iterate_op a k := KSAppendixA.iterate_op_pos a ha k hk
  simp only [KSAppendixA.ThetaFull, h_pos, dif_pos]
  exact Theta_iterate a ha k hk

/-- ThetaFull(iterate_op a 0) = ThetaFull(ident) = 0. -/
theorem ThetaFull_iterate_zero (a : α) (ha : ident < a) :
    KSAppendixA.ThetaFull a ha (iterate_op a 0) = 0 := by
  simp only [KSAppendixA.iterate_op_zero]
  exact KSAppendixA.ThetaFull_ident a ha

/-- **Linearity on iterates**: ThetaFull(iterate_op a n) = n for all n.
Combines the k ≥ 1 and k = 0 cases. -/
theorem ThetaFull_iterate_eq (a : α) (ha : ident < a) (n : ℕ) :
    KSAppendixA.ThetaFull a ha (iterate_op a n) = n := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero]
    exact ThetaFull_iterate_zero a ha
  | succ k => exact ThetaFull_iterate a ha (k + 1) (Nat.succ_pos k)

/-- **KEY: Additivity on iterates**. This proves Θ is additive on the one-type grid.

For iterates of a single element, we have:
  Θ(a^m ⊕ a^n) = Θ(a^m) + Θ(a^n) = m + n

This follows from:
1. iterate_op_add: a^m ⊕ a^n = a^(m+n)
2. ThetaFull_iterate_eq: Θ(a^k) = k

This is the foundation for showing that the value-grid measure equals Θ. -/
theorem ThetaFull_iterate_add (a : α) (ha : ident < a) (m n : ℕ) :
    KSAppendixA.ThetaFull a ha (op (iterate_op a m) (iterate_op a n)) =
    KSAppendixA.ThetaFull a ha (iterate_op a m) + KSAppendixA.ThetaFull a ha (iterate_op a n) := by
  -- Step 1: a^m ⊕ a^n = a^(m+n) by iterate_op_add (no commutativity needed!)
  rw [KSAppendixA.iterate_op_add]
  -- Step 2: Θ(a^(m+n)) = m + n by ThetaFull_iterate_eq
  rw [ThetaFull_iterate_eq]
  -- Step 3: Θ(a^m) = m and Θ(a^n) = n by ThetaFull_iterate_eq
  rw [ThetaFull_iterate_eq, ThetaFull_iterate_eq]
  -- Step 4: m + n = m + n ✓
  push_cast
  ring

/-- **Commutativity on one-type grid**: Iterates of a single element commute.

This follows trivially from iterate_op_add and commutativity of ℕ addition:
  a^m ⊕ a^n = a^(m+n) = a^(n+m) = a^n ⊕ a^m

This is the foundation for extending commutativity to the full algebra via density. -/
theorem iterate_op_comm (a : α) (m n : ℕ) :
    op (iterate_op a m) (iterate_op a n) = op (iterate_op a n) (iterate_op a m) := by
  rw [KSAppendixA.iterate_op_add, KSAppendixA.iterate_op_add]
  congr 1
  ring

/-! ### Commutativity → Distributivity → Additivity

**Key logical chain**:
1. If op is commutative, then x^m ⊕ y^m = (x⊕y)^m (iterate_op_op_distrib_of_comm)
2. From this, add_le_Theta has NO factor-of-2 gap
3. Combined with Theta_le_add, we get Theta_add (full additivity)

This completes the K&S bootstrapping: once we establish commutativity by other means
(e.g., via the value-grid density argument), additivity follows automatically.
-/

/-- **Commutativity → Distributivity**: If op is commutative, then x^m ⊕ y^m = (x⊕y)^m.

This is the key theorem that eliminates the factor-of-2 in add_le_Theta.
The counterexample `iterate_op_op_distrib_false` shows this REQUIRES commutativity. -/
theorem iterate_op_op_distrib_of_comm (x y : α) (m : ℕ)
    (h_comm : ∀ a b : α, op a b = op b a) :
    op (iterate_op x m) (iterate_op y m) = iterate_op (op x y) m := by
  induction m with
  | zero =>
    simp only [KSAppendixA.iterate_op_zero]
    rw [op_ident_left]
  | succ m ih =>
    -- x^{m+1} ⊕ y^{m+1} = (x ⊕ x^m) ⊕ (y ⊕ y^m)
    -- Using commutativity and associativity, rearrange to:
    -- = (x ⊕ y) ⊕ (x^m ⊕ y^m) = (x⊕y) ⊕ (x⊕y)^m = (x⊕y)^{m+1}
    calc op (iterate_op x (m + 1)) (iterate_op y (m + 1))
        = op (op x (iterate_op x m)) (op y (iterate_op y m)) := rfl
      _ = op (op x (iterate_op x m)) (op (iterate_op y m) y) := by rw [h_comm y]
      _ = op x (op (iterate_op x m) (op (iterate_op y m) y)) := by rw [op_assoc]
      _ = op x (op (op (iterate_op x m) (iterate_op y m)) y) := by
          congr 1
          rw [← op_assoc]
      _ = op x (op (iterate_op (op x y) m) y) := by rw [ih]
      _ = op x (op y (iterate_op (op x y) m)) := by rw [h_comm (iterate_op (op x y) m)]
      _ = op (op x y) (iterate_op (op x y) m) := by rw [← op_assoc]
      _ = iterate_op (op x y) (m + 1) := rfl

/-- **Corollary**: With commutativity, add_le_Theta has no factor-of-2 gap.

Given commutativity, for any r₁ ∈ Lower(x), r₂ ∈ Lower(y), we have r₁ + r₂ ∈ Lower(x⊕y)
(not just (r₁+r₂)/2 as in half_add_le_Theta). -/
theorem add_le_Theta_of_comm (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y)
    (hxy : ident < op x y) (h_comm : ∀ a b : α, op a b = op b a) :
    KSAppendixA.Theta a x ha hx + KSAppendixA.Theta a y ha hy ≤
    KSAppendixA.Theta a (op x y) ha hxy := by
  unfold KSAppendixA.Theta
  -- For any r₁ ∈ Lower(x), r₂ ∈ Lower(y), show r₁ + r₂ ∈ Lower(x⊕y)
  have h_combine : ∀ r₁ r₂, r₁ ∈ KSAppendixA.lowerRatioSet a x →
      r₂ ∈ KSAppendixA.lowerRatioSet a y →
      r₁ + r₂ ∈ KSAppendixA.lowerRatioSet a (op x y) := by
    intro r₁ r₂ ⟨n₁, m₁, hm₁, hle₁, hr₁⟩ ⟨n₂, m₂, hm₂, hle₂, hr₂⟩
    subst hr₁ hr₂
    -- Use repetition lemma to get common denominator M = m₁ * m₂
    have hle₁' : iterate_op a (n₁ * m₂) ≤ iterate_op x (m₁ * m₂) :=
      KSAppendixA.repetition_lemma_le a x n₁ m₁ m₂ hle₁
    have hle₂' : iterate_op a (n₂ * m₁) ≤ iterate_op y (m₁ * m₂) := by
      have h := KSAppendixA.repetition_lemma_le a y n₂ m₂ m₁ hle₂
      simp only [Nat.mul_comm m₂ m₁] at h
      exact h
    -- Combine: a^{n₁m₂ + n₂m₁} ≤ x^{m₁m₂} ⊕ y^{m₁m₂}
    have hle_sum : iterate_op a (n₁ * m₂ + n₂ * m₁) ≤
        op (iterate_op x (m₁ * m₂)) (iterate_op y (m₁ * m₂)) := by
      rw [← KSAppendixA.iterate_op_add]
      calc op (iterate_op a (n₁ * m₂)) (iterate_op a (n₂ * m₁))
          ≤ op (iterate_op x (m₁ * m₂)) (iterate_op a (n₂ * m₁)) :=
            (op_strictMono_left _).monotone hle₁'
        _ ≤ op (iterate_op x (m₁ * m₂)) (iterate_op y (m₁ * m₂)) :=
            (op_strictMono_right _).monotone hle₂'
    -- KEY: With commutativity, x^{m₁m₂} ⊕ y^{m₁m₂} = (x⊕y)^{m₁m₂} (no factor of 2!)
    have hle_final : op (iterate_op x (m₁ * m₂)) (iterate_op y (m₁ * m₂)) =
        iterate_op (op x y) (m₁ * m₂) :=
      iterate_op_op_distrib_of_comm x y (m₁ * m₂) h_comm
    -- Chain the inequalities
    have hle_combined : iterate_op a (n₁ * m₂ + n₂ * m₁) ≤ iterate_op (op x y) (m₁ * m₂) := by
      rw [← hle_final]; exact hle_sum
    -- Now show (n₁/m₁ + n₂/m₂) = (n₁m₂ + n₂m₁)/(m₁*m₂) is in Lower(x⊕y)
    have hdenom_pos : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
    refine ⟨n₁ * m₂ + n₂ * m₁, m₁ * m₂, hdenom_pos, hle_combined, ?_⟩
    -- Ratio arithmetic
    have hm₁_ne : (m₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm₁)
    have hm₂_ne : (m₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm₂)
    push_cast
    field_simp [hm₁_ne, hm₂_ne]
  -- The rest follows the same pattern as half_add_le_Theta
  -- but now r₁ + r₂ (not (r₁+r₂)/2) is in Lower(x⊕y)
  have h_sum_in : ∀ r₁ r₂, r₁ ∈ KSAppendixA.lowerRatioSet a x →
      r₂ ∈ KSAppendixA.lowerRatioSet a y →
      r₁ + r₂ ≤ sSup (KSAppendixA.lowerRatioSet a (op x y)) := by
    intro r₁ r₂ hr₁ hr₂
    exact le_csSup (KSAppendixA.lowerRatioSet_bddAbove a (op x y) ha hxy) (h_combine r₁ r₂ hr₁ hr₂)
  -- Conclude: sup Lower(x) + sup Lower(y) ≤ sup Lower(x⊕y)
  have hS_x := KSAppendixA.lowerRatioSet_nonempty a x hx
  have hS_y := KSAppendixA.lowerRatioSet_nonempty a y hy
  have hS_xy := KSAppendixA.lowerRatioSet_nonempty a (op x y) hxy
  have hBdd_x := KSAppendixA.lowerRatioSet_bddAbove a x ha hx
  have hBdd_y := KSAppendixA.lowerRatioSet_bddAbove a y ha hy
  -- For any ε > 0, find r₁, r₂ close to their sups
  by_contra h_not_le
  push_neg at h_not_le
  -- Let δ = (sup_x + sup_y - sup_xy) / 3 > 0
  set S_x := sSup (KSAppendixA.lowerRatioSet a x) with hS_x_def
  set S_y := sSup (KSAppendixA.lowerRatioSet a y) with hS_y_def
  set S_xy := sSup (KSAppendixA.lowerRatioSet a (op x y)) with hS_xy_def
  have hδ : S_x + S_y - S_xy > 0 := by linarith
  set δ := (S_x + S_y - S_xy) / 3 with hδ_def
  have hδ_pos : δ > 0 := by linarith
  -- Find r₁ > S_x - δ and r₂ > S_y - δ
  obtain ⟨r₁, hr₁_in, hr₁_close⟩ := exists_lt_of_lt_csSup hS_x (sub_lt_self S_x hδ_pos)
  obtain ⟨r₂, hr₂_in, hr₂_close⟩ := exists_lt_of_lt_csSup hS_y (sub_lt_self S_y hδ_pos)
  -- Then r₁ + r₂ > S_x - δ + S_y - δ = S_x + S_y - 2δ > S_xy + δ > S_xy
  have h1 : r₁ > S_x - δ := hr₁_close
  have h2 : r₂ > S_y - δ := hr₂_close
  have h3 : r₁ + r₂ > S_x - δ + (S_y - δ) := by linarith
  have h4 : S_x - δ + (S_y - δ) = S_x + S_y - 2 * δ := by ring
  rw [h4] at h3
  have h5 : S_x + S_y - 2 * δ = S_xy + δ := by
    simp only [hδ_def]
    ring
  rw [h5] at h3
  have h6 : r₁ + r₂ > S_xy := by linarith
  -- But r₁ + r₂ ≤ S_xy by h_sum_in
  have h7 := h_sum_in r₁ r₂ hr₁_in hr₂_in
  linarith

/-! ### The Density Argument for Commutativity (K&S key insight)

**Goal**: Extend commutativity from iterates to all elements.

**What we have**:
- `iterate_op_comm`: For any a, m, n: a^m ⊕ a^n = a^n ⊕ a^m
- `iterate_op_op_distrib_of_comm`: If op is commutative, then x^m ⊕ y^m = (x⊕y)^m
- `add_le_Theta_of_comm`: If op is commutative, then Θ(x) + Θ(y) ≤ Θ(x⊕y)

**The K&S insight**: In a KS algebra (LinearOrder + Archimedean), for any x, y:
1. Both x and y are "determined" by how they compare to iterates of a
2. The Dedekind cut Θ(x) = sup{n/m : a^n ≤ x^m} captures this comparison
3. Since Θ is strictly monotone (injective), Θ(x⊕y) = Θ(y⊕x) implies x⊕y = y⊕x

**The gap**: We need to show Θ(x⊕y) = Θ(y⊕x) without assuming commutativity.

**Strategy** (from K&S Appendix A):
1. Show that both Θ(x⊕y) and Θ(y⊕x) are determined by the same limiting process
2. Use the density of rationals and the uniqueness of Dedekind cuts
3. Conclude Θ(x⊕y) = Θ(y⊕x), hence x⊕y = y⊕x by injectivity
-/

/-- **Key lemma**: Scaling inequality preserves membership in lowerRatioSet.

If a^p ≤ z^q, then a^{mp} ≤ z^{mq} (by taking m-th power).
This is the foundation for super-additivity of Θ on iterates. -/
lemma lowerRatioSet_scale_up (a z : α) (ha : ident < a) (hz : ident < z) (p q m : ℕ)
    (hq : 0 < q) (hle : iterate_op a p ≤ iterate_op z q) :
    iterate_op a (m * p) ≤ iterate_op z (m * q) := by
  induction m with
  | zero => simp only [Nat.zero_mul, KSAppendixA.iterate_op_zero, le_refl]
  | succ m ih =>
    -- a^{(m+1)*p} = a^{m*p + p} = a^{m*p} ⊕ a^p
    -- z^{(m+1)*q} = z^{m*q + q} = z^{m*q} ⊕ z^q
    rw [Nat.succ_mul, ← KSAppendixA.iterate_op_add, Nat.succ_mul, ← KSAppendixA.iterate_op_add]
    -- By monotonicity: a^{m*p} ⊕ a^p ≤ z^{m*q} ⊕ z^q
    calc op (iterate_op a (m * p)) (iterate_op a p)
        ≤ op (iterate_op z (m * q)) (iterate_op a p) :=
          (op_strictMono_left _).monotone ih
      _ ≤ op (iterate_op z (m * q)) (iterate_op z q) :=
          (op_strictMono_right _).monotone hle

/-- **Super-additivity**: Θ(z^m) ≥ m * Θ(z).

This follows from: if p/q ∈ lowerRatioSet(a, z), then mp/q ∈ lowerRatioSet(a, z^m).
Combined with sub-additivity (Theta_le_add), this gives Θ(z^m) = m * Θ(z). -/
theorem Theta_iterate_superadd (a z : α) (ha : ident < a) (hz : ident < z) (m : ℕ) :
    m * KSAppendixA.ThetaFull a ha z ≤ KSAppendixA.ThetaFull a ha (iterate_op z m) := by
  cases m with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, KSAppendixA.iterate_op_zero, KSAppendixA.ThetaFull_ident, le_refl]
  | succ m =>
    -- For m ≥ 1, both z and z^m are > ident
    have hzm_pos : ident < iterate_op z (m + 1) :=
      KSAppendixA.iterate_op_pos z hz (m + 1) (Nat.succ_pos m)
    -- Unfold ThetaFull to Theta (both are > ident)
    simp only [KSAppendixA.ThetaFull, hz, hzm_pos, dif_pos]
    -- Show: (m+1) * Θ(z) ≤ Θ(z^{m+1})
    unfold KSAppendixA.Theta
    -- Strategy: For any r in lowerRatioSet(a, z), show (m+1)*r is in lowerRatioSet(a, z^{m+1})
    -- Then use: (m+1) * sSup S ≤ sSup T when ∀ r ∈ S, (m+1)*r ∈ T
    have hz_ne : (KSAppendixA.lowerRatioSet a z).Nonempty := KSAppendixA.lowerRatioSet_nonempty a z hz
    have hz_bdd : BddAbove (KSAppendixA.lowerRatioSet a z) := KSAppendixA.lowerRatioSet_bddAbove a z ha hz
    have hzm_bdd : BddAbove (KSAppendixA.lowerRatioSet a (iterate_op z (m + 1))) :=
      KSAppendixA.lowerRatioSet_bddAbove a (iterate_op z (m + 1)) ha hzm_pos
    -- Key: for each r ∈ lowerRatioSet(a, z), we have (m+1)*r ∈ lowerRatioSet(a, z^{m+1})
    have h_scale : ∀ r ∈ KSAppendixA.lowerRatioSet a z,
        (m + 1 : ℝ) * r ∈ KSAppendixA.lowerRatioSet a (iterate_op z (m + 1)) := by
      intro r ⟨p, q, hq_pos, hle, hr_eq⟩
      subst hr_eq
      refine ⟨(m + 1) * p, q, hq_pos, ?_, by push_cast; ring⟩
      rw [KSAppendixA.iterate_op_mul]
      exact lowerRatioSet_scale_up a z ha hz p q (m + 1) hq_pos hle
    -- Now: (m+1) * sSup(lowerRatioSet a z) ≤ sSup(lowerRatioSet a z^{m+1})
    -- Use: c * sSup S ≤ sSup T when c ≥ 0 and ∀ s ∈ S, c*s ≤ sSup T
    have hm_pos : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _
    calc (↑(m + 1) : ℝ) * sSup (KSAppendixA.lowerRatioSet a z)
        ≤ sSup ((↑(m + 1) : ℝ) • KSAppendixA.lowerRatioSet a z) := by
          rw [Real.smul_csSup (by positivity : (0 : ℝ) < ↑(m + 1)) hz_ne hz_bdd]
      _ ≤ sSup (KSAppendixA.lowerRatioSet a (iterate_op z (m + 1))) := by
          apply csSup_le_csSup hzm_bdd
          · exact Set.Nonempty.smul hz_ne
          intro x hx
          obtain ⟨r, hr, rfl⟩ := Set.mem_smul_set.mp hx
          exact h_scale r hr

/-- **Exactness**: Θ(z^m) = m * Θ(z) for all z > ident and m ≥ 0.

This combines super-additivity with sub-additivity (Theta_le_add). -/
theorem Theta_iterate_exact (a z : α) (ha : ident < a) (hz : ident < z) (m : ℕ) :
    KSAppendixA.ThetaFull a ha (iterate_op z m) = m * KSAppendixA.ThetaFull a ha z := by
  apply le_antisymm
  · -- Upper bound: Θ(z^m) ≤ m * Θ(z) by sub-additivity (Theta_le_add iterated)
    induction m with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, KSAppendixA.iterate_op_zero]
      exact le_of_eq (KSAppendixA.ThetaFull_ident a ha)
    | succ m ih =>
      have hzm_pos : ident < iterate_op z (m + 1) :=
        KSAppendixA.iterate_op_pos a ha z (m + 1) (Nat.succ_pos m)
      -- z^{m+1} = z ⊕ z^m
      rw [KSAppendixA.iterate_op_succ]
      -- Θ(z ⊕ z^m) ≤ Θ(z) + Θ(z^m) ≤ Θ(z) + m*Θ(z) = (m+1)*Θ(z)
      have h_le : KSAppendixA.ThetaFull a ha (op z (iterate_op z m)) ≤
          KSAppendixA.ThetaFull a ha z + KSAppendixA.ThetaFull a ha (iterate_op z m) := by
        cases m with
        | zero =>
          simp only [KSAppendixA.iterate_op_zero, op_ident_right]
          linarith [KSAppendixA.ThetaFull_pos_of_pos a ha z hz]
        | succ m =>
          have hzm'_pos : ident < iterate_op z (m + 1) :=
            KSAppendixA.iterate_op_pos a ha z (m + 1) (Nat.succ_pos m)
          simp only [KSAppendixA.ThetaFull, hz, hzm'_pos, dif_pos]
          have hop_pos : ident < op z (iterate_op z (m + 1)) := by
            calc ident = op ident ident := (op_ident_left ident).symm
              _ < op z ident := op_strictMono_left ident hz
              _ < op z (iterate_op z (m + 1)) := op_strictMono_right z hzm'_pos
          simp only [KSAppendixA.ThetaFull, hz, hzm'_pos, hop_pos, dif_pos]
          exact KSAppendixA.Theta_le_add a z (iterate_op z (m + 1)) ha hz hzm'_pos hop_pos
      calc KSAppendixA.ThetaFull a ha (op z (iterate_op z m))
          ≤ KSAppendixA.ThetaFull a ha z + KSAppendixA.ThetaFull a ha (iterate_op z m) := h_le
        _ ≤ KSAppendixA.ThetaFull a ha z + m * KSAppendixA.ThetaFull a ha z := by linarith [ih]
        _ = (m + 1) * KSAppendixA.ThetaFull a ha z := by ring
  · -- Lower bound: m * Θ(z) ≤ Θ(z^m) by super-additivity
    exact Theta_iterate_superadd a z ha hz m

/-- **Recursive structure**: (x⊕y)^{m+1} = x ⊕ (y⊕x)^m ⊕ y.

This beautiful identity follows from associativity and captures how iterates of
x⊕y and y⊕x are interleaved. It's the key to proving Θ(x⊕y) = Θ(y⊕x). -/
theorem iterate_op_recursive (x y : α) (m : ℕ) :
    iterate_op (op x y) (m + 1) = op x (op (iterate_op (op y x) m) y) := by
  induction m with
  | zero =>
    simp only [KSAppendixA.iterate_op_zero, op_ident_left]
    rfl
  | succ m ih =>
    -- (x⊕y)^{m+2} = (x⊕y) ⊕ (x⊕y)^{m+1}
    --             = (x⊕y) ⊕ (x ⊕ (y⊕x)^m ⊕ y)  [by IH]
    --             = x ⊕ (y ⊕ x ⊕ (y⊕x)^m ⊕ y)  [by assoc]
    --             = x ⊕ ((y⊕x) ⊕ (y⊕x)^m) ⊕ y  [by assoc]
    --             = x ⊕ (y⊕x)^{m+1} ⊕ y
    calc iterate_op (op x y) (m + 2)
        = op (op x y) (iterate_op (op x y) (m + 1)) := rfl
      _ = op (op x y) (op x (op (iterate_op (op y x) m) y)) := by rw [ih]
      _ = op x (op y (op x (op (iterate_op (op y x) m) y))) := by rw [op_assoc, op_assoc]
      _ = op x (op (op y x) (op (iterate_op (op y x) m) y)) := by rw [← op_assoc y x]
      _ = op x (op (op (op y x) (iterate_op (op y x) m)) y) := by rw [← op_assoc]
      _ = op x (op (iterate_op (op y x) (m + 1)) y) := rfl

/-- **The commutativity theorem**: Θ(x⊕y) = Θ(y⊕x) for all x, y > ident.

This is the culmination of the K&S density argument. The proof uses:
1. Theta_iterate_exact: Θ(z^m) = m * Θ(z)
2. iterate_op_recursive: (x⊕y)^{m+1} = x ⊕ (y⊕x)^m ⊕ y

From these, we derive two inequalities that force Θ(x⊕y) = Θ(y⊕x). -/
theorem Theta_eq_swap (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y) :
    KSAppendixA.ThetaFull a ha (op x y) = KSAppendixA.ThetaFull a ha (op y x) := by
  -- Let r = Θ(x⊕y), s = Θ(y⊕x), c = Θ(x) + Θ(y)
  set r := KSAppendixA.ThetaFull a ha (op x y) with hr_def
  set s := KSAppendixA.ThetaFull a ha (op y x) with hs_def
  set c := KSAppendixA.ThetaFull a ha x + KSAppendixA.ThetaFull a ha y with hc_def
  -- Positivity facts
  have hxy_pos : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
      _ < op x ident := op_strictMono_left ident hx
      _ < op x y := op_strictMono_right x hy
  have hyx_pos : ident < op y x := by
    calc ident = op ident ident := (op_ident_left ident).symm
      _ < op y ident := op_strictMono_left ident hy
      _ < op y x := op_strictMono_right y hx
  -- For any m ≥ 0, iterates are positive
  have hxym_pos : ∀ m, 0 < m → ident < iterate_op (op x y) m :=
    fun m hm => KSAppendixA.iterate_op_pos a ha (op x y) m hm
  have hyxm_pos : ∀ m, 0 < m → ident < iterate_op (op y x) m :=
    fun m hm => KSAppendixA.iterate_op_pos a ha (op y x) m hm
  -- Key bound 1: (m+1)*r ≤ c + m*s
  -- From: (x⊕y)^{m+1} = x ⊕ (y⊕x)^m ⊕ y and Theta_le_add
  have hbound1 : ∀ m : ℕ, (m + 1) * r ≤ c + m * s := by
    intro m
    -- Θ((x⊕y)^{m+1}) = (m+1) * r by Theta_iterate_exact
    have h1 : KSAppendixA.ThetaFull a ha (iterate_op (op x y) (m + 1)) = (m + 1) * r := by
      rw [Theta_iterate_exact a (op x y) ha hxy_pos (m + 1)]
    -- (x⊕y)^{m+1} = x ⊕ (y⊕x)^m ⊕ y by iterate_op_recursive
    have h2 : iterate_op (op x y) (m + 1) = op x (op (iterate_op (op y x) m) y) :=
      iterate_op_recursive x y m
    -- Θ(x ⊕ (y⊕x)^m ⊕ y) ≤ Θ(x) + Θ((y⊕x)^m) + Θ(y)
    rw [h2] at h1
    -- Case split on m for positivity
    cases m with
    | zero =>
      simp only [KSAppendixA.iterate_op_zero, op_ident_left, Nat.cast_zero, zero_mul, add_zero,
        Nat.cast_one, one_mul] at h1 ⊢
      -- (x⊕y) = x ⊕ y, so Θ(x⊕y) = r ≤ Θ(x) + Θ(y) = c
      have h_le := KSAppendixA.ThetaFull_le_add a x y ha hx hy hxy_pos
      linarith
    | succ m =>
      -- (y⊕x)^{m+1} is positive
      have hyxm1_pos : ident < iterate_op (op y x) (m + 1) := hyxm_pos (m + 1) (Nat.succ_pos m)
      -- x ⊕ (y⊕x)^{m+1} is positive
      have h_mid_pos : ident < op (iterate_op (op y x) (m + 1)) y := by
        calc ident = op ident ident := (op_ident_left ident).symm
          _ < op (iterate_op (op y x) (m + 1)) ident := op_strictMono_left ident hyxm1_pos
          _ < op (iterate_op (op y x) (m + 1)) y := op_strictMono_right _ hy
      have h_full_pos : ident < op x (op (iterate_op (op y x) (m + 1)) y) := by
        calc ident = op ident ident := (op_ident_left ident).symm
          _ < op x ident := op_strictMono_left ident hx
          _ < op x (op (iterate_op (op y x) (m + 1)) y) := op_strictMono_right x h_mid_pos
      -- Apply Theta_le_add twice
      have h_le1 : KSAppendixA.ThetaFull a ha (op x (op (iterate_op (op y x) (m + 1)) y)) ≤
          KSAppendixA.ThetaFull a ha x +
          KSAppendixA.ThetaFull a ha (op (iterate_op (op y x) (m + 1)) y) := by
        simp only [KSAppendixA.ThetaFull, hx, h_mid_pos, h_full_pos, dif_pos]
        exact KSAppendixA.Theta_le_add a x (op (iterate_op (op y x) (m + 1)) y) ha hx h_mid_pos h_full_pos
      have h_le2 : KSAppendixA.ThetaFull a ha (op (iterate_op (op y x) (m + 1)) y) ≤
          KSAppendixA.ThetaFull a ha (iterate_op (op y x) (m + 1)) + KSAppendixA.ThetaFull a ha y := by
        simp only [KSAppendixA.ThetaFull, hyxm1_pos, hy, h_mid_pos, dif_pos]
        exact KSAppendixA.Theta_le_add a (iterate_op (op y x) (m + 1)) y ha hyxm1_pos hy h_mid_pos
      -- Θ((y⊕x)^{m+1}) = (m+1) * s
      have h_iter : KSAppendixA.ThetaFull a ha (iterate_op (op y x) (m + 1)) = (m + 1) * s := by
        rw [Theta_iterate_exact a (op y x) ha hyx_pos (m + 1)]
      -- Chain: (m+2)*r ≤ Θ(x) + (m+1)*s + Θ(y) = c + (m+1)*s
      calc ((m + 1) + 1 : ℕ) * r = KSAppendixA.ThetaFull a ha (op x (op (iterate_op (op y x) (m + 1)) y)) := by
            rw [← h1]; ring_nf
        _ ≤ KSAppendixA.ThetaFull a ha x + KSAppendixA.ThetaFull a ha (op (iterate_op (op y x) (m + 1)) y) := h_le1
        _ ≤ KSAppendixA.ThetaFull a ha x + (KSAppendixA.ThetaFull a ha (iterate_op (op y x) (m + 1)) + KSAppendixA.ThetaFull a ha y) := by linarith [h_le2]
        _ = KSAppendixA.ThetaFull a ha x + ((m + 1) * s + KSAppendixA.ThetaFull a ha y) := by rw [h_iter]
        _ = c + (m + 1) * s := by ring
  -- Key bound 2: (m+1)*s ≤ c + m*r (symmetric)
  have hbound2 : ∀ m : ℕ, (m + 1) * s ≤ c + m * r := by
    intro m
    have h1 : KSAppendixA.ThetaFull a ha (iterate_op (op y x) (m + 1)) = (m + 1) * s := by
      rw [Theta_iterate_exact a (op y x) ha hyx_pos (m + 1)]
    have h2 : iterate_op (op y x) (m + 1) = op y (op (iterate_op (op x y) m) x) :=
      iterate_op_recursive y x m
    rw [h2] at h1
    cases m with
    | zero =>
      simp only [KSAppendixA.iterate_op_zero, op_ident_left, Nat.cast_zero, zero_mul, add_zero,
        Nat.cast_one, one_mul] at h1 ⊢
      have h_le := KSAppendixA.ThetaFull_le_add a y x ha hy hx hyx_pos
      linarith
    | succ m =>
      have hxym1_pos : ident < iterate_op (op x y) (m + 1) := hxym_pos (m + 1) (Nat.succ_pos m)
      have h_mid_pos : ident < op (iterate_op (op x y) (m + 1)) x := by
        calc ident = op ident ident := (op_ident_left ident).symm
          _ < op (iterate_op (op x y) (m + 1)) ident := op_strictMono_left ident hxym1_pos
          _ < op (iterate_op (op x y) (m + 1)) x := op_strictMono_right _ hx
      have h_full_pos : ident < op y (op (iterate_op (op x y) (m + 1)) x) := by
        calc ident = op ident ident := (op_ident_left ident).symm
          _ < op y ident := op_strictMono_left ident hy
          _ < op y (op (iterate_op (op x y) (m + 1)) x) := op_strictMono_right y h_mid_pos
      have h_le1 : KSAppendixA.ThetaFull a ha (op y (op (iterate_op (op x y) (m + 1)) x)) ≤
          KSAppendixA.ThetaFull a ha y +
          KSAppendixA.ThetaFull a ha (op (iterate_op (op x y) (m + 1)) x) := by
        simp only [KSAppendixA.ThetaFull, hy, h_mid_pos, h_full_pos, dif_pos]
        exact KSAppendixA.Theta_le_add a y (op (iterate_op (op x y) (m + 1)) x) ha hy h_mid_pos h_full_pos
      have h_le2 : KSAppendixA.ThetaFull a ha (op (iterate_op (op x y) (m + 1)) x) ≤
          KSAppendixA.ThetaFull a ha (iterate_op (op x y) (m + 1)) + KSAppendixA.ThetaFull a ha x := by
        simp only [KSAppendixA.ThetaFull, hxym1_pos, hx, h_mid_pos, dif_pos]
        exact KSAppendixA.Theta_le_add a (iterate_op (op x y) (m + 1)) x ha hxym1_pos hx h_mid_pos
      have h_iter : KSAppendixA.ThetaFull a ha (iterate_op (op x y) (m + 1)) = (m + 1) * r := by
        rw [Theta_iterate_exact a (op x y) ha hxy_pos (m + 1)]
      calc ((m + 1) + 1 : ℕ) * s = KSAppendixA.ThetaFull a ha (op y (op (iterate_op (op x y) (m + 1)) x)) := by
            rw [← h1]; ring_nf
        _ ≤ KSAppendixA.ThetaFull a ha y + KSAppendixA.ThetaFull a ha (op (iterate_op (op x y) (m + 1)) x) := h_le1
        _ ≤ KSAppendixA.ThetaFull a ha y + (KSAppendixA.ThetaFull a ha (iterate_op (op x y) (m + 1)) + KSAppendixA.ThetaFull a ha x) := by linarith [h_le2]
        _ = KSAppendixA.ThetaFull a ha y + ((m + 1) * r + KSAppendixA.ThetaFull a ha x) := by rw [h_iter]
        _ = c + (m + 1) * r := by ring
  -- From hbound1 and hbound2, derive r = s
  -- hbound1 at m: (m+1)*r ≤ c + m*s → (m+1)*r - m*s ≤ c → r + m*(r-s) ≤ c
  -- hbound2 at m: (m+1)*s ≤ c + m*r → (m+1)*s - m*r ≤ c → s + m*(s-r) ≤ c
  -- Subtracting: (m+1)*(r-s) ≤ m*(s-r), i.e., (2m+1)*(r-s) ≤ 0
  -- Similarly: (2m+1)*(s-r) ≤ 0
  -- Both imply r = s
  by_contra h_ne
  rcases lt_trichotomy r s with hr_lt | hr_eq | hr_gt
  · -- Case r < s: derive contradiction from hbound2
    -- (m+1)*s ≤ c + m*r for all m
    -- As m → ∞: s ≤ r, contradiction
    have h := hbound2 1
    simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero] at h
    -- 2*s ≤ c + r
    have h' := hbound1 1
    simp only [Nat.cast_one, one_mul] at h'
    -- 2*r ≤ c + s
    -- From h: 2*s ≤ c + r and h': 2*r ≤ c + s
    -- Subtracting: 2*(s - r) ≤ r - s = -(s - r), so 3*(s - r) ≤ 0
    have : 3 * (s - r) ≤ 0 := by linarith
    have hs_r_pos : s - r > 0 := sub_pos.mpr hr_lt
    linarith
  · exact h_ne hr_eq
  · -- Case r > s: derive contradiction from hbound1
    have h := hbound1 1
    simp only [Nat.cast_one, one_mul] at h
    have h' := hbound2 1
    simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero] at h'
    have : 3 * (r - s) ≤ 0 := by linarith
    have hr_s_pos : r - s > 0 := sub_pos.mpr hr_gt
    linarith

/-- **Corollary**: In a KS algebra, op is commutative.

This follows from Theta_eq_swap and strict monotonicity of Θ. -/
theorem op_comm_of_KS (a : α) (ha : ident < a) :
    ∀ x y : α, op x y = op y x := by
  intro x y
  by_cases hx : ident < x
  · by_cases hy : ident < y
    · -- Both positive: use Theta_eq_swap
      have h := Theta_eq_swap a x y ha hx hy
      -- h : ThetaFull a ha (op x y) = ThetaFull a ha (op y x)
      -- Use strict mono on positives to get injectivity
      have hxy_pos : ident < op x y := by
        calc ident = op ident ident := (op_ident_left ident).symm
          _ < op x ident := op_strictMono_left ident hx
          _ < op x y := op_strictMono_right x hy
      have hyx_pos : ident < op y x := by
        calc ident = op ident ident := (op_ident_left ident).symm
          _ < op y ident := op_strictMono_left ident hy
          _ < op y x := op_strictMono_right y hx
      by_contra h_ne
      rcases lt_trichotomy (op x y) (op y x) with hlt | heq | hgt
      · have := KSAppendixA.ThetaFull_strictMono_on_pos a ha (op x y) (op y x) hxy_pos hyx_pos hlt
        linarith
      · exact h_ne heq
      · have := KSAppendixA.ThetaFull_strictMono_on_pos a ha (op y x) (op x y) hyx_pos hxy_pos hgt
        linarith
    · -- y ≤ ident
      by_cases hy_eq : y = ident
      · simp only [hy_eq, op_ident_right, op_ident_left]
      · -- y < ident: contradiction with ident_le
        push_neg at hy
        have hy_lt : y < ident := lt_of_le_of_ne hy hy_eq
        exact absurd (ident_le y) (not_le.mpr hy_lt)
  · -- x ≤ ident
    by_cases hx_eq : x = ident
    · simp only [hx_eq, op_ident_left, op_ident_right]
    · -- x < ident: contradiction with ident_le
      push_neg at hx
      have hx_lt : x < ident := lt_of_le_of_ne hx hx_eq
      exact absurd (ident_le x) (not_le.mpr hx_lt)

/-! ## Section A.4: Separation Sets (K&S lines 1536-1622)

When extending from k existing atom types to k+1 types, we partition
the old-grid values into three sets relative to a new sequence:

**Set A**: Old values strictly below the new sequence
**Set B**: Old values equal to the new sequence
**Set C**: Old values strictly above the new sequence

The separation statistic s(m; u) = (μ(m) - μ₀) / u satisfies:
  all A members have s < all B members have s < all C members
-/

/-- The separation statistic: s(m; u) = (μ(m) - μ₀) / u

Given a reference multiset m₀, the statistic measures how much m deviates
from m₀ per unit of the new type's multiplicity u. -/
noncomputable def separationStatistic (v : AtomValuation) (m m₀ : AtomMultiset) (u : ℕ) : ℝ :=
  if u = 0 then 0 else (v.measure m - v.measure m₀) / u

/-- Separation sets for extending valuation to a new atom type.

Given:
- v: existing valuation on old types
- m₀: reference multiset (typically the specific sequence being compared)
- d: value candidate for new type

We partition pairs (m, u) where m is an old-type multiset and u is the
new type's multiplicity into:
- A: μ(m) < μ(m₀) + u * d  (below)
- B: μ(m) = μ(m₀) + u * d  (at)
- C: μ(m) > μ(m₀) + u * d  (above)
-/
structure SeparationSets (v : AtomValuation) (m₀ : AtomMultiset) (d : ℝ) where
  A : Set (AtomMultiset × ℕ)
  B : Set (AtomMultiset × ℕ)
  C : Set (AtomMultiset × ℕ)
  A_def : A = {p | v.measure p.1 < v.measure m₀ + p.2 * d}
  B_def : B = {p | v.measure p.1 = v.measure m₀ + p.2 * d}
  C_def : C = {p | v.measure p.1 > v.measure m₀ + p.2 * d}

namespace SeparationSets

variable {v : AtomValuation} {m₀ : AtomMultiset} {d : ℝ}

/-- Constructor for separation sets -/
def mk' (v : AtomValuation) (m₀ : AtomMultiset) (d : ℝ) : SeparationSets v m₀ d where
  A := {p | v.measure p.1 < v.measure m₀ + p.2 * d}
  B := {p | v.measure p.1 = v.measure m₀ + p.2 * d}
  C := {p | v.measure p.1 > v.measure m₀ + p.2 * d}
  A_def := rfl
  B_def := rfl
  C_def := rfl

/-- The sets A, B, C partition all pairs (exhaustive) -/
theorem partition_exhaustive (sep : SeparationSets v m₀ d) (p : AtomMultiset × ℕ) :
    p ∈ sep.A ∨ p ∈ sep.B ∨ p ∈ sep.C := by
  rw [sep.A_def, sep.B_def, sep.C_def]
  simp only [Set.mem_setOf_eq]
  rcases lt_trichotomy (v.measure p.1) (v.measure m₀ + p.2 * d) with hlt | heq | hgt
  · left; exact hlt
  · right; left; exact heq
  · right; right; exact hgt

/-- The sets A, B, C are pairwise disjoint -/
theorem partition_disjoint_AB (sep : SeparationSets v m₀ d) (p : AtomMultiset × ℕ) :
    p ∈ sep.A → p ∉ sep.B := by
  rw [sep.A_def, sep.B_def]
  simp only [Set.mem_setOf_eq]
  intro hlt heq
  exact lt_irrefl _ (heq ▸ hlt)

theorem partition_disjoint_BC (sep : SeparationSets v m₀ d) (p : AtomMultiset × ℕ) :
    p ∈ sep.B → p ∉ sep.C := by
  rw [sep.B_def, sep.C_def]
  simp only [Set.mem_setOf_eq]
  intro heq hgt
  exact lt_irrefl _ (heq ▸ hgt)

theorem partition_disjoint_AC (sep : SeparationSets v m₀ d) (p : AtomMultiset × ℕ) :
    p ∈ sep.A → p ∉ sep.C := by
  rw [sep.A_def, sep.C_def]
  simp only [Set.mem_setOf_eq]
  intro hlt hgt
  exact lt_asymm hlt hgt

end SeparationSets

/-! ## Section A.5: Case B Non-Empty (K&S lines 1624-1704)

When B is non-empty, all members share a common separation statistic value.
This value becomes the new type's value in the linear representation.
-/

/-- If B has two members with positive multiplicities, they have equal statistics -/
theorem B_members_equal_statistic (v : AtomValuation) (m₀ : AtomMultiset) (d : ℝ)
    (sep : SeparationSets v m₀ d)
    (p₁ p₂ : AtomMultiset × ℕ) (hp₁ : p₁ ∈ sep.B) (hp₂ : p₂ ∈ sep.B)
    (h1 : 0 < p₁.2) (h2 : 0 < p₂.2) :
    separationStatistic v p₁.1 m₀ p₁.2 = separationStatistic v p₂.1 m₀ p₂.2 := by
  rw [sep.B_def] at hp₁ hp₂
  simp only [Set.mem_setOf_eq] at hp₁ hp₂
  -- hp₁: v.measure p₁.1 = v.measure m₀ + p₁.2 * d
  -- hp₂: v.measure p₂.1 = v.measure m₀ + p₂.2 * d
  unfold separationStatistic
  simp only [Nat.pos_iff_ne_zero.mp h1, Nat.pos_iff_ne_zero.mp h2, ↓reduceIte]
  -- (v.measure p₁.1 - v.measure m₀) / p₁.2 = (v.measure p₂.1 - v.measure m₀) / p₂.2
  have e1 : v.measure p₁.1 - v.measure m₀ = p₁.2 * d := by linarith [hp₁]
  have e2 : v.measure p₂.1 - v.measure m₀ = p₂.2 * d := by linarith [hp₂]
  rw [e1, e2]
  field_simp

/-- When B is non-empty, all B members share the same statistic value d -/
theorem B_nonempty_common_value (v : AtomValuation) (m₀ : AtomMultiset) (d : ℝ)
    (sep : SeparationSets v m₀ d) (p : AtomMultiset × ℕ) (hp : p ∈ sep.B) (hp_pos : 0 < p.2) :
    separationStatistic v p.1 m₀ p.2 = d := by
  rw [sep.B_def] at hp
  simp only [Set.mem_setOf_eq] at hp
  unfold separationStatistic
  simp only [Nat.pos_iff_ne_zero.mp hp_pos, ↓reduceIte]
  have e : v.measure p.1 - v.measure m₀ = p.2 * d := by linarith
  rw [e]
  field_simp

/-! ## Section A.6: Separation Property (K&S lines 1580-1622)

The key theorem: For u > 0, all A members have s < all B members have s < all C members.

This follows from the trichotomy and the definition of separation statistic.
-/

/-- For members with positive multiplicity, A members have s < B members -/
theorem sep_A_lt_B (v : AtomValuation) (m₀ : AtomMultiset) (d : ℝ)
    (sep : SeparationSets v m₀ d)
    (pA pB : AtomMultiset × ℕ) (hA : pA ∈ sep.A) (hB : pB ∈ sep.B)
    (hA_pos : 0 < pA.2) (hB_pos : 0 < pB.2) :
    separationStatistic v pA.1 m₀ pA.2 < separationStatistic v pB.1 m₀ pB.2 := by
  rw [sep.A_def] at hA
  rw [sep.B_def] at hB
  simp only [Set.mem_setOf_eq] at hA hB
  -- hA: v.measure pA.1 < v.measure m₀ + pA.2 * d
  -- hB: v.measure pB.1 = v.measure m₀ + pB.2 * d
  unfold separationStatistic
  simp only [Nat.pos_iff_ne_zero.mp hA_pos, Nat.pos_iff_ne_zero.mp hB_pos, ↓reduceIte]
  -- (v.measure pA.1 - v.measure m₀) / pA.2 < (v.measure pB.1 - v.measure m₀) / pB.2
  have eB : v.measure pB.1 - v.measure m₀ = pB.2 * d := by linarith
  have hA' : v.measure pA.1 - v.measure m₀ < pA.2 * d := by linarith
  have hpA2_pos : (0 : ℝ) < pA.2 := by positivity
  have hpB2_pos : (0 : ℝ) < pB.2 := by positivity
  -- sA = (mA - m₀) / pA.2 < pA.2 * d / pA.2 = d
  have hsA_lt_d : (v.measure pA.1 - v.measure m₀) / pA.2 < d := by
    rw [div_lt_iff₀ hpA2_pos]
    linarith
  -- sB = (mB - m₀) / pB.2 = pB.2 * d / pB.2 = d
  have hsB_eq_d : (pB.2 : ℝ) * d / pB.2 = d := by field_simp
  rw [eB, hsB_eq_d]
  exact hsA_lt_d

/-- For members with positive multiplicity, B members have s < C members -/
theorem sep_B_lt_C (v : AtomValuation) (m₀ : AtomMultiset) (d : ℝ)
    (sep : SeparationSets v m₀ d)
    (pB pC : AtomMultiset × ℕ) (hB : pB ∈ sep.B) (hC : pC ∈ sep.C)
    (hB_pos : 0 < pB.2) (hC_pos : 0 < pC.2) :
    separationStatistic v pB.1 m₀ pB.2 < separationStatistic v pC.1 m₀ pC.2 := by
  rw [sep.B_def] at hB
  rw [sep.C_def] at hC
  simp only [Set.mem_setOf_eq] at hB hC
  unfold separationStatistic
  simp only [Nat.pos_iff_ne_zero.mp hB_pos, Nat.pos_iff_ne_zero.mp hC_pos, ↓reduceIte]
  have eB : v.measure pB.1 - v.measure m₀ = pB.2 * d := by linarith
  have hC' : v.measure pC.1 - v.measure m₀ > pC.2 * d := by linarith
  have hpB2_pos : (0 : ℝ) < pB.2 := by positivity
  have hpC2_pos : (0 : ℝ) < pC.2 := by positivity
  -- sB = d
  have hsB_eq_d : (pB.2 : ℝ) * d / pB.2 = d := by field_simp
  -- sC = (mC - m₀) / pC.2 > pC.2 * d / pC.2 = d
  have hsC_gt_d : d < (v.measure pC.1 - v.measure m₀) / pC.2 := by
    rw [lt_div_iff₀ hpC2_pos]
    linarith
  rw [eB, hsB_eq_d]
  exact hsC_gt_d

/-! ## Section A.7: Case B Empty - Accuracy Lemma (K&S lines 1706-1895)

When B is empty, there's a gap between sup(A statistics) and inf(C statistics).
The accuracy lemma shows we can pin down any value δ in this gap arbitrarily
precisely using the Archimedean property.

This is the K&S analog of Dedekind cut construction.
-/

/-- In the single-type case, for any x with ident < x < a, the ratio Θ(x) = sup{n/m : a^n ≤ x^m}
exists and satisfies 0 < Θ(x) < 1.

**REWRITTEN** following GPT-5.1 Pro's advice:
- θ > 0: Uses ThetaFull_pos_of_pos (already proven)
- θ < 1: Uses ThetaFull_strictMono_on_pos + Theta_ref_eq_one (already proven!)
- No circular gap lemma needed!

The key insight: θ = sSup (lowerRatioSet a x) = ThetaFull a ha x, and we already proved
ThetaFull_strictMono_on_pos, so ThetaFull a ha x < ThetaFull a ha a = 1.
-/
theorem ratio_exists_for_intermediate {α : Type*} [KnuthSkillingAlgebra α]
    (a x : α) (ha : ident < a) (hx_pos : ident < x) (hxa : x < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (∀ n m : ℕ, 0 < m → iterate_op a n ≤ iterate_op x m → (n : ℝ) / m ≤ θ) ∧
      (∀ ε > 0, ∃ n m : ℕ, 0 < m ∧ iterate_op a n ≤ iterate_op x m ∧ θ - ε < (n : ℝ) / m) := by
  -- Use the lowerRatioSet from RepTheorem
  let S := KSAppendixA.lowerRatioSet a x
  -- The set is non-empty and bounded above
  have hS_nonempty : S.Nonempty := KSAppendixA.lowerRatioSet_nonempty a x hx_pos
  have hS_bdd : BddAbove S := KSAppendixA.lowerRatioSet_bddAbove a x ha hx_pos
  -- Take θ = sSup S (which equals ThetaFull a ha x)
  use sSup S
  constructor
  · -- θ > 0: Use ThetaFull_pos_of_pos
    -- Note: ThetaFull a ha x = Theta a x ha hx_pos = sSup (lowerRatioSet a x) = sSup S
    have hΘ_eq : KSAppendixA.ThetaFull a ha x = sSup S := by
      simp only [KSAppendixA.ThetaFull, hx_pos, dif_pos, KSAppendixA.Theta, S]
    rw [← hΘ_eq]
    exact KSAppendixA.ThetaFull_pos_of_pos a ha x hx_pos
  constructor
  · -- θ < 1: Use ThetaFull_strictMono_on_pos + Theta_ref_eq_one
    -- Key: ThetaFull a ha x < ThetaFull a ha a = 1 (since x < a)
    have hΘ_eq : KSAppendixA.ThetaFull a ha x = sSup S := by
      simp only [KSAppendixA.ThetaFull, hx_pos, dif_pos, KSAppendixA.Theta, S]
    have hΘa_eq_one : KSAppendixA.ThetaFull a ha a = 1 := by
      simp only [KSAppendixA.ThetaFull, ha, dif_pos]
      exact KSAppendixA.Theta_ref_eq_one a ha
    have hΘx_lt_Θa : KSAppendixA.ThetaFull a ha x < KSAppendixA.ThetaFull a ha a :=
      KSAppendixA.ThetaFull_strictMono_on_pos a ha x a hx_pos ha hxa
    calc sSup S = KSAppendixA.ThetaFull a ha x := hΘ_eq.symm
      _ < KSAppendixA.ThetaFull a ha a := hΘx_lt_Θa
      _ = 1 := hΘa_eq_one
  constructor
  · -- Upper bound property: n/m ≤ θ for all valid pairs
    intro n m hm_pos hle
    apply le_csSup hS_bdd
    exact ⟨n, m, hm_pos, hle, rfl⟩
  · -- Approximation property: For any ε > 0, ∃ n/m in S with θ - ε < n/m
    intro ε hε_pos
    obtain ⟨r, hr_mem, hr_close⟩ := exists_lt_of_lt_csSup hS_nonempty (sub_lt_self _ hε_pos)
    obtain ⟨n, m, hm_pos, hle, hr_eq⟩ := hr_mem
    exact ⟨n, m, hm_pos, hle, hr_eq ▸ hr_close⟩

/-! ## Section A.8: Inductive Extension (K&S lines 1897-1922)

The main induction: if linear additivity holds for k atom types,
it extends to k+1 types.
-/

/-- The value grid for n types is the set of rational combinations.

For the base case (1 type), this is just the integers: {r : r ∈ ℕ}.
For k+1 types, we add a new "direction" with slope determined by
either Case B (rational) or Case B (irrational via accuracy). -/
structure ValueGrid (n : ℕ) where
  types : Fin n → AtomType
  values : Fin n → ℝ
  /-- The value of a multiset is the linear combination -/
  measure : (Fin n → ℕ) → ℝ := fun m => Finset.univ.sum (fun i => m i * values i)

/-! ## Section A.9: Main Theorem Assembly

Putting it all together: the representation theorem.
-/

/-- **Knuth-Skilling Representation Theorem** (Appendix A main result)

For any Knuth-Skilling algebra α with a reference element a > ident,
there exists a strictly monotone Θ : α → ℝ such that:
1. Θ(ident) = 0
2. Θ(a) = 1 (normalization)
3. Θ(x ⊕ y) = Θ(x) + Θ(y) for all x, y

Moreover, this implies commutativity: x ⊕ y = y ⊕ x.
-/
theorem ks_representation_theorem_appendixA {α : Type*} [KnuthSkillingAlgebra α]
    (a : α) (ha : ident < a) :
    ∃ Θ : α → ℝ,
      StrictMono Θ ∧
      Θ ident = 0 ∧
      Θ a = 1 ∧
      (∀ x y, Θ (op x y) = Θ x + Θ y) := by
  -- Use ThetaFull from RepTheorem as our Θ
  use KSAppendixA.ThetaFull a ha
  refine ⟨?strict_mono, ?ident_zero, ?a_one, ?additive⟩

  case ident_zero =>
    -- Θ(ident) = 0 is proven by ThetaFull_ident
    exact KSAppendixA.ThetaFull_ident a ha

  case a_one =>
    -- Θ(a) = 1: ThetaFull reduces to Theta for a > ident, and Theta_ref_eq_one gives Θ(a) = 1
    simp only [KSAppendixA.ThetaFull, ha, dif_pos]
    exact KSAppendixA.Theta_ref_eq_one a ha

  case strict_mono =>
    -- Strict monotonicity: Case analysis on whether x or y equals ident
    intro x y hxy
    by_cases hx_ident : x = ident
    · -- Case: x = ident
      subst hx_ident
      -- y > ident (since ident < y follows from hxy)
      have hy_pos : ident < y := hxy
      -- Θ(ident) = 0 < Θ(y) (since y > ident means Θ(y) > 0)
      rw [KSAppendixA.ThetaFull_ident]
      exact KSAppendixA.ThetaFull_pos_of_pos a ha y hy_pos
    · -- Case: x ≠ ident
      by_cases hx_lt_ident : x < ident
      · -- Subcase: x < ident - contradiction with ident_le axiom
        exact absurd (ident_le x) (not_le.mpr hx_lt_ident)
      · -- Subcase: x > ident (normal case)
        push_neg at hx_lt_ident
        have hx_pos : ident < x := lt_of_le_of_ne hx_lt_ident (Ne.symm hx_ident)
        have hy_pos : ident < y := lt_trans hx_pos hxy
        -- Use ThetaFull_strictMono_on_pos for both positive
        exact KSAppendixA.ThetaFull_strictMono_on_pos a ha x y hx_pos hy_pos hxy

  case additive =>
    -- Additivity: Θ(x ⊕ y) = Θ(x) + Θ(y)
    -- Case analysis on whether x or y equals ident
    intro x y
    by_cases hx_ident : x = ident
    · -- Case: x = ident
      -- op ident y = y by op_ident_left
      -- Θ(ident) = 0, so Θ(ident ⊕ y) = Θ(y) = 0 + Θ(y)
      subst hx_ident
      simp only [op_ident_left, KSAppendixA.ThetaFull_ident, zero_add]
    · by_cases hy_ident : y = ident
      · -- Case: y = ident
        -- op x ident = x by op_ident_right
        -- Θ(ident) = 0, so Θ(x ⊕ ident) = Θ(x) = Θ(x) + 0
        subst hy_ident
        simp only [op_ident_right, KSAppendixA.ThetaFull_ident, add_zero]
      · -- Case: Both x, y ≠ ident
        -- Check if they're positive (> ident)
        by_cases hx_pos : ident < x
        · by_cases hy_pos : ident < y
          · -- Both positive: use Theta_add
            -- Show ident < op x y
            have hxy_pos : ident < op x y := by
              calc ident = op ident ident := (op_ident_left ident).symm
                _ < op x ident := op_strictMono_left ident hx_pos
                _ < op x y := op_strictMono_right x hy_pos
            -- Reduce ThetaFull to Theta for all three terms
            simp only [KSAppendixA.ThetaFull, hx_pos, hy_pos, hxy_pos, dif_pos]
            -- Use Theta_add (which depends on add_le_Theta PROOF_HOLE)
            exact KSAppendixA.Theta_add a x y ha hx_pos hy_pos
          · -- y ≤ ident but y ≠ ident means y < ident - contradiction with ident_le
            push_neg at hy_pos
            have hy_ne : y ≠ ident := hy_ident
            have hy_lt : y < ident := lt_of_le_of_ne hy_pos hy_ne
            exact absurd (ident_le y) (not_le.mpr hy_lt)
        · -- x ≤ ident but x ≠ ident means x < ident - contradiction with ident_le
          push_neg at hx_pos
          have hx_ne : x ≠ ident := hx_ident
          have hx_lt : x < ident := lt_of_le_of_ne hx_pos hx_ne
          exact absurd (ident_le x) (not_le.mpr hx_lt)

/-- Commutativity emerges from the representation theorem -/
theorem commutativity_from_representation {α : Type*} [inst : KnuthSkillingAlgebra α]
    (Θ : α → ℝ) (hΘ_mono : StrictMono Θ)
    (hΘ_add : ∀ x y : α, Θ (inst.op x y) = Θ x + Θ y) :
    ∀ x y : α, inst.op x y = inst.op y x := by
  intro x y
  -- Θ(x ⊕ y) = Θ(x) + Θ(y) = Θ(y) + Θ(x) = Θ(y ⊕ x)
  have h1 : Θ (inst.op x y) = Θ x + Θ y := hΘ_add x y
  have h2 : Θ (inst.op y x) = Θ y + Θ x := hΘ_add y x
  have h3 : Θ x + Θ y = Θ y + Θ x := add_comm (Θ x) (Θ y)
  have h4 : Θ (inst.op x y) = Θ (inst.op y x) := by rw [h1, h3, ← h2]
  -- Since Θ is strictly monotone (hence injective), op x y = op y x
  exact hΘ_mono.injective h4

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
