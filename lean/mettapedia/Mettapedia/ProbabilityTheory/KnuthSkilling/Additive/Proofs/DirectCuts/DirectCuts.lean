/-
# Alternative Representation: Direct Cuts/Log Construction

This file provides an alternative proof of the K&S representation theorem using
a direct "cuts" construction of Θ, bypassing the grid/induction machinery.

## Strategy (Hölder-style)

Given a KnuthSkillingAlgebra α with KSSeparation:

1. **Fix a base element** `a > ident`
2. **Define rational approximants**: For x ∈ α, consider ratios m/n where
   `pow' a m ≤ pow' x n` (i.e., m·a ≤ n·x in additive notation)
3. **Define Θ(x)** as the supremum of such ratios (a Dedekind cut)
4. **Prove properties**:
   - Order preservation: Uses separation to compare cuts
   - Additivity: Uses associativity + commutativity

## Status

This file now contains a *standalone* Hölder/Dedekind-cuts derivation of an additive
order-embedding `Θ : α → ℝ`, under the same hypothesis used elsewhere in the K&S formalization:
`KSSeparationStrict`.

We keep the lemma `Θ_cuts_eq_div_of_representation` as a useful *characterization*:
once any additive order embedding exists, the cut-based construction recovers it (up to scale).

## Identity Requirements

This construction **requires identity** in several fundamental ways:
1. **Power iteration base case**: `pow' x 0 = ident`
2. **Reference element selection**: `a > ident`
3. **Cut set definition**: Comparisons involve identity
4. **Normalization**: Θ is scaled relative to identity

**Future work** could potentially make this identity-optional by:
- Using `iterate_op_pnat : ℕ+ → α` instead of `pow' : ℕ → α`
- Using Eric's `IsPositive a` instead of `ident < a`
- Defining cuts relative to an anchor element instead of identity

However, this would require substantial restructuring. For identity-free representation,
the **Hölder path** (via Eric Luap's OrderedSemigroups library) is recommended instead.
See `Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean` for the identity-free approach.

## References

- Hölder, "Die Axiome der Quantität und die Lehre vom Mass" (1901)
- Fuchs, "Partially Ordered Algebraic Systems" (1963), Ch. IV
- Goertzel, "Foundations of Inference: New Proofs" (separation ⇒ commutativity note)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Representation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core.SeparationImpliesCommutative

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.DirectCuts

open Classical
-- Bring the K&S operation/identity projections into scope (`op`, `ident`, etc.).
-- Without this, `op` resolves to unrelated Mathlib identifiers (e.g. Opposite), and the file breaks.
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open scoped Pointwise

variable {α : Type*} [KnuthSkillingAlgebra α] [KSSeparation α]

/-!
## §1: Commutativity from Separation (imported)

We use the already-proven fact that KSSeparation implies commutativity.
-/

/-- Commutativity follows from KSSeparation. -/
theorem op_comm' : ∀ x y : α, op x y = op y x :=
  fun x y => Core.op_comm_of_KSSeparation x y

/-!
## §2: Iteration and Power Notation

We define convenient notation for iterating the operation.
-/

/-- n-fold iteration: x^n = x ⊕ x ⊕ ... ⊕ x (n times), with x^0 = ident -/
def pow' (x : α) : ℕ → α
  | 0 => ident
  | n + 1 => op x (pow' x n)

omit [KSSeparation α] in
@[simp]
theorem pow'_zero (x : α) : pow' x 0 = ident := rfl

omit [KSSeparation α] in
@[simp]
theorem pow'_one (x : α) : pow' x 1 = x := op_ident_right x

omit [KSSeparation α] in
@[simp]
theorem pow'_succ (x : α) (n : ℕ) : pow' x (n + 1) = op x (pow' x n) := rfl

omit [KSSeparation α] in
/-- Power is additive: x^(m+n) = x^m ⊕ x^n -/
theorem pow'_add (x : α) (m n : ℕ) : pow' x (m + n) = op (pow' x m) (pow' x n) := by
  induction m with
  | zero => simp [op_ident_left]
  | succ m ih =>
    simp only [Nat.succ_add, pow'_succ]
    rw [ih, op_assoc]

omit [KSSeparation α] in
/-- Power is strictly monotone in the exponent when x > ident -/
theorem pow'_strictMono_exp {x : α} (hx : ident < x) : StrictMono (pow' x) := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
    · calc pow' x m < pow' x n := ih hlt
        _ < pow' x (n + 1) := by
            simp only [pow'_succ]
            calc pow' x n = op ident (pow' x n) := by rw [op_ident_left]
              _ < op x (pow' x n) := op_strictMono_left (pow' x n) hx
    · rw [heq]; simp only [pow'_succ]
      calc pow' x n = op ident (pow' x n) := by rw [op_ident_left]
        _ < op x (pow' x n) := op_strictMono_left (pow' x n) hx

omit [KSSeparation α] in
/-- Power is strictly monotone in the base for positive exponents -/
theorem pow'_strictMono_base {x y : α} (hxy : x < y) (n : ℕ) (hn : 0 < n) :
    pow' x n < pow' y n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [pow'_succ]
    by_cases hn' : n = 0
    · simp only [hn', pow'_zero, op_ident_right, hxy]
    · have hn'' : 0 < n := Nat.pos_of_ne_zero hn'
      calc op x (pow' x n) < op x (pow' y n) := op_strictMono_right x (ih hn'')
        _ < op y (pow' y n) := op_strictMono_left (pow' y n) hxy

omit [KSSeparation α] in
/-- Power is monotone in the base -/
theorem pow'_mono_base {x y : α} (hxy : x ≤ y) (n : ℕ) (hn : 0 < n) :
    pow' x n ≤ pow' y n := by
  rcases hxy.lt_or_eq with hlt | heq
  · exact le_of_lt (pow'_strictMono_base hlt n hn)
  · rw [heq]

omit [KSSeparation α] in
/-- Power of ident is always ident -/
theorem pow'_ident (n : ℕ) : pow' (ident : α) n = ident := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow'_succ, op_ident_left, ih]

/-!
## §3: The Cut Set Definition

For a fixed base `a > ident` and element `x`, define the "cut set" of rationals
that represent lower bounds for Θ(x)/Θ(a).
-/

/-- The cut set: rationals m/n such that pow' a m ≤ pow' x n (when n > 0) -/
def cutSet (a : α) (x : α) : Set ℚ :=
  { q : ℚ | 0 ≤ q ∧ ∃ (m n : ℕ), n > 0 ∧ q = m / n ∧ pow' a m ≤ pow' x n }

omit [KSSeparation α] in
/-- The cut set is nonempty (contains 0) when x ≥ ident -/
theorem cutSet_nonempty (a : α) (x : α) (hx : ident ≤ x) :
    (cutSet a x).Nonempty := by
  use 0
  simp only [cutSet, Set.mem_setOf_eq]
  refine ⟨le_refl 0, 0, 1, Nat.one_pos, ?_, ?_⟩
  · simp
  · simp only [pow'_zero, pow'_one]; exact hx

/-- Power multiplication: (x^m)^n = x^(m*n) - requires commutativity -/
theorem pow'_mul (x : α) (m n : ℕ) : pow' (pow' x m) n = pow' x (m * n) := by
  induction n with
  | zero => simp only [pow'_zero, Nat.mul_zero]
  | succ n ih =>
    simp only [pow'_succ, Nat.mul_succ, pow'_add]
    rw [ih, op_comm']

omit [KSSeparation α] in
/-- Power is monotone in exponent (non-strict) when x ≥ ident -/
theorem pow'_mono_exp {x : α} (hx : ident ≤ x) : Monotone (pow' x) := by
  intro m n hmn
  rcases hx.lt_or_eq with hx_lt | hx_eq
  · -- x > ident: use strict monotonicity
    rcases hmn.lt_or_eq with hmn_lt | hmn_eq
    · exact le_of_lt (pow'_strictMono_exp hx_lt hmn_lt)
    · rw [hmn_eq]
  · -- x = ident: pow' ident n = ident for all n
    rw [← hx_eq]
    simp only [pow'_ident, le_refl]

omit [KSSeparation α] in
/-- Relationship between Function.iterate and pow': f^[n] x = pow' x (n + 1) when f = op x -/
theorem iterate_eq_pow'_succ (x : α) (n : ℕ) :
    (op x)^[n] x = pow' x (n + 1) := by
  induction n with
  | zero =>
    -- (op x)^[0] x = x = pow' x 1
    simp only [Function.iterate_zero, id_eq]
    exact (pow'_one x).symm
  | succ n ih =>
    -- (op x)^[n+1] x = op x ((op x)^[n] x) = op x (pow' x (n+1)) = pow' x (n+2)
    simp only [Function.iterate_succ_apply']
    rw [ih]
    rfl

/-- Key lemma: pow' x n < pow' a (k * n) when x < pow' a k -/
theorem pow'_lt_pow'_mul {a x : α} {k : ℕ} (_ha : ident < a) (hx : x < pow' a k) (n : ℕ) (hn : 0 < n) :
    pow' x n < pow' a (k * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [pow'_succ, Nat.mul_succ]
    rw [pow'_add]
    by_cases hn' : n = 0
    · simp only [hn', Nat.mul_zero, pow'_zero, op_ident_left, op_ident_right]
      exact hx
    · have hn'' : 0 < n := Nat.pos_of_ne_zero hn'
      calc op x (pow' x n) < op x (pow' a (k * n)) := op_strictMono_right x (ih hn'')
        _ < op (pow' a k) (pow' a (k * n)) := op_strictMono_left (pow' a (k * n)) hx
        _ = op (pow' a (k * n)) (pow' a k) := op_comm' _ _

/-- The cut set is bounded above (uses Archimedean property, derived from KSSeparation) -/
theorem cutSet_bddAbove (a : α) (ha : ident < a) (x : α) : BddAbove (cutSet a x) := by
  -- By Archimedean (derived from KSSeparation), ∃ N such that x < (op a)^[N] a = pow' a (N + 1)
  obtain ⟨N, hN⟩ := SandwichSeparation.SeparationToArchimedean.op_archimedean_of_separation a x ha
  rw [iterate_eq_pow'_succ] at hN
  -- Use N + 1 as upper bound
  use (N + 1 : ℕ)
  intro q hq
  simp only [cutSet, Set.mem_setOf_eq] at hq
  obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
  -- Need to show: m/n ≤ N + 1
  rw [hq_eq]
  by_cases hm : m = 0
  · simp only [hm, Nat.cast_zero, zero_div]
    exact Nat.cast_nonneg _
  · -- m > 0, prove by contradiction
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    by_contra h_gt
    push_neg at h_gt
    -- h_gt : (N + 1 : ℚ) < m / n
    -- So m > (N+1) * n, i.e., (N + 1) * n < m
    have h1 : (N + 1) * n < m := by
      have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
      have hcast : ((N + 1) * n : ℚ) < m := by
        calc ((N + 1) * n : ℚ) = (N + 1 : ℕ) * n := by norm_cast
          _ < (m / n) * n := by
              apply mul_lt_mul_of_pos_right h_gt
              exact Nat.cast_pos.mpr hn
          _ = m := div_mul_cancel₀ (m : ℚ) hn_ne
      exact_mod_cast hcast
    -- pow' a m > pow' a ((N+1)*n) since a > ident
    have h2 : pow' a ((N + 1) * n) < pow' a m := pow'_strictMono_exp ha h1
    -- pow' x n < pow' a ((N+1) * n) by the key lemma
    have h3 : pow' x n < pow' a ((N + 1) * n) := pow'_lt_pow'_mul ha hN n hn
    -- Contradiction: pow' a m ≤ pow' x n < pow' a ((N+1)*n) < pow' a m
    have h4 : pow' x n < pow' a m := lt_trans h3 h2
    exact not_lt.mpr ham_le h4

/-!
## §4: Definition of Θ via Supremum

Define Θ(x) as the supremum of the cut set.
-/

/-- The representation map Θ defined via cut supremum -/
noncomputable def Θ_cuts (a : α) (_ha : ident < a) (x : α) : ℝ :=
  if _hx : ident ≤ x then
    sSup ((↑) '' cutSet a x : Set ℝ)
  else
    0

omit [KSSeparation α] in
/-- Θ(ident) = 0 -/
theorem Θ_cuts_ident (a : α) (ha : ident < a) : Θ_cuts a ha ident = 0 := by
  simp only [Θ_cuts, le_refl, dite_true]
  -- cutSet of ident is {0} because pow' a m ≤ pow' ident n = ident forces m = 0
  have h_cutSet : cutSet a ident = {0} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · -- 0 ∈ cutSet a ident
      simp only [cutSet, Set.mem_setOf_eq]
      refine ⟨le_refl 0, 0, 1, Nat.one_pos, by norm_num, ?_⟩
      -- pow' a 0 = ident and pow' ident 1 = ident, so we need ident ≤ ident
      rw [pow'_zero, pow'_one]
    · -- uniqueness: q ∈ cutSet a ident → q = 0
      intro q hq
      simp only [cutSet, Set.mem_setOf_eq] at hq
      obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
      by_cases hm : m = 0
      · simp only [hq_eq, hm, Nat.cast_zero, zero_div]
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h1 : ident < pow' a m := pow'_strictMono_exp ha hm_pos
        have h2 : pow' (ident : α) n = ident := pow'_ident n
        rw [h2] at ham_le
        exact absurd (lt_of_lt_of_le h1 ham_le) (lt_irrefl ident)
  rw [h_cutSet]
  simp only [Set.image_singleton]
  norm_cast
  exact csSup_singleton 0

omit [KSSeparation α] in
/-- For the base element, cutSet characterization: q ∈ cutSet a a ↔ 0 ≤ q ≤ 1 -/
theorem cutSet_base_subset_unit_interval (a : α) (ha : ident < a) :
    cutSet a a ⊆ {q : ℚ | 0 ≤ q ∧ q ≤ 1} := by
  intro q hq
  simp only [cutSet, Set.mem_setOf_eq] at hq
  obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
  simp only [Set.mem_setOf_eq]
  constructor
  · exact hq_nonneg
  · -- Need: m/n ≤ 1, i.e., m ≤ n
    rw [hq_eq]
    rw [div_le_one (by exact_mod_cast hn : (0 : ℚ) < n)]
    -- pow' a m ≤ pow' a n implies m ≤ n by strict monotonicity
    by_contra h_gt
    push_neg at h_gt
    have h_gt' : n < m := by exact_mod_cast h_gt
    have h : pow' a n < pow' a m := pow'_strictMono_exp ha h_gt'
    exact not_lt.mpr ham_le h

omit [KSSeparation α] in
/-- For the base element, unit interval subset of cutSet -/
theorem unit_interval_subset_cutSet_base (a : α) (ha : ident < a) :
    {q : ℚ | 0 ≤ q ∧ q ≤ 1} ⊆ cutSet a a := by
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨hq_nonneg, hq_le_one⟩ := hq
  simp only [cutSet, Set.mem_setOf_eq]
  constructor
  · exact hq_nonneg
  · -- Use the numerator and denominator of q
    use q.num.toNat, q.den
    constructor
    · exact q.den_pos
    · constructor
      · -- q = q.num.toNat / q.den when q ≥ 0
        have h_num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
        have h_eq : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg h_num_nonneg
        -- Show q = q.num.toNat / q.den
        have hkey : (q.num.toNat : ℚ) = q.num := by exact_mod_cast h_eq
        rw [hkey]
        exact (Rat.num_div_den q).symm
      · -- pow' a q.num.toNat ≤ pow' a q.den because q.num.toNat ≤ q.den
        apply pow'_mono_exp (le_of_lt ha)
        -- Need: q.num.toNat ≤ q.den, which follows from q ≤ 1
        have h_num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
        have h_eq : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg h_num_nonneg
        -- q.num ≤ q.den from q ≤ 1
        have h_le : q.num ≤ q.den := by
          have h1 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
          have h2 : q * q.den ≤ 1 * q.den := by
            apply mul_le_mul_of_nonneg_right hq_le_one
            exact_mod_cast q.den_pos.le
          simp only [one_mul] at h2
          have h3 : (q.num : ℚ) ≤ q.den := by linarith
          exact_mod_cast h3
        -- q.num.toNat ≤ q.den follows from q.num ≤ q.den (since q.num ≥ 0)
        have h_nat : q.num.toNat ≤ q.den := by
          have hcast : (q.num.toNat : ℤ) ≤ q.den := by
            rw [h_eq]
            exact h_le
          omega
        exact h_nat

omit [KSSeparation α] in
/-- cutSet of base element equals unit interval -/
theorem cutSet_base_eq (a : α) (ha : ident < a) :
    cutSet a a = {q : ℚ | 0 ≤ q ∧ q ≤ 1} :=
  Set.eq_of_subset_of_subset (cutSet_base_subset_unit_interval a ha) (unit_interval_subset_cutSet_base a ha)

/-- Supremum of [0,1] ∩ ℚ (cast to ℝ) equals 1 -/
theorem sSup_rat_unit_interval :
    sSup ((↑) '' {q : ℚ | 0 ≤ q ∧ q ≤ 1} : Set ℝ) = 1 := by
  apply le_antisymm
  · -- sSup ≤ 1: all elements are ≤ 1
    apply csSup_le
    · use (0 : ℝ)
      simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨0, ⟨le_refl 0, zero_le_one⟩, Rat.cast_zero⟩
    · intro r hr
      simp only [Set.mem_image, Set.mem_setOf_eq] at hr
      obtain ⟨q, ⟨_, hq_le⟩, rfl⟩ := hr
      exact_mod_cast hq_le
  · -- 1 ≤ sSup: 1 is in the set
    apply le_csSup
    · -- Bounded above by 1
      use 1
      intro r hr
      simp only [Set.mem_image, Set.mem_setOf_eq] at hr
      obtain ⟨q, ⟨_, hq_le⟩, rfl⟩ := hr
      exact_mod_cast hq_le
    · -- 1 is in the image (1 = (1 : ℚ) cast to ℝ)
      simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨1, ⟨zero_le_one, le_refl 1⟩, Rat.cast_one⟩

omit [KSSeparation α] in
/-- Θ(a) = 1 (the base element maps to 1) -/
theorem Θ_cuts_base (a : α) (ha : ident < a) : Θ_cuts a ha a = 1 := by
  simp only [Θ_cuts, le_of_lt ha, dite_true]
  rw [cutSet_base_eq a ha]
  exact sSup_rat_unit_interval

/-!
## §5: Order Preservation

The key property: x ≤ y ↔ Θ(x) ≤ Θ(y)
-/

/-- Forward direction: x ≤ y → Θ(x) ≤ Θ(y) -/
theorem Θ_cuts_mono (a : α) (ha : ident < a) {x y : α} (hxy : x ≤ y) :
    Θ_cuts a ha x ≤ Θ_cuts a ha y := by
  simp only [Θ_cuts]
  have hx : ident ≤ x := ident_le x
  have hy : ident ≤ y := ident_le y
  simp only [hx, hy, dite_true]
  -- cutSet x ⊆ cutSet y
  apply csSup_le_csSup
  · -- cutSet y is bounded above (image version)
    have hbdd : BddAbove (cutSet a y) := cutSet_bddAbove a ha y
    obtain ⟨B, hB⟩ := hbdd
    use B
    intro r hr
    simp only [Set.mem_image] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact Rat.cast_le.mpr (hB hq)
  · exact Set.image_nonempty.mpr (cutSet_nonempty a x hx)
  · intro r hr
    simp only [Set.mem_image] at hr ⊢
    obtain ⟨q, hq, rfl⟩ := hr
    use q
    simp only [cutSet, Set.mem_setOf_eq] at hq ⊢
    obtain ⟨hq_nonneg, m, n, hn, hq_eq, ham_le⟩ := hq
    constructor
    · exact ⟨hq_nonneg, m, n, hn, hq_eq, le_trans ham_le (pow'_mono_base hxy n hn)⟩
    · trivial

/-!
## §6: The Dedekind-cuts characterization of Θ

If `Θ : α → ℝ` is an additive order embedding, then the cut-based definition `Θ_cuts` recovers
the normalized value `Θ x / Θ a`.
-/

omit [KSSeparation α] in
/-- Dedekind-cuts characterization: `Θ_cuts` recovers any additive order embedding, normalized at `a`. -/
theorem Θ_cuts_eq_div_of_representation
    (a : α) (ha : ident < a) (Θ : α → ℝ)
    (hΘ_order : ∀ u v : α, u ≤ v ↔ Θ u ≤ Θ v)
    (hΘ_ident : Θ ident = 0)
    (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y)
    (x : α) :
    Θ_cuts a ha x = Θ x / Θ a := by
  -- Helper: Θ respects `pow'` as scalar multiplication.
  have hΘ_pow' : ∀ (z : α) (n : ℕ), Θ (pow' z n) = (n : ℝ) * Θ z := by
    intro z n
    induction n with
    | zero => simp [pow', hΘ_ident]
    | succ n ih =>
      simp [pow', hΘ_add, ih]
      ring

  -- Positivity of Θ(a).
  have hΘa_pos : 0 < Θ a := by
    have : Θ ident < Θ a := by
      have hle : Θ ident ≤ Θ a := (hΘ_order ident a).1 (le_of_lt ha)
      have hne : Θ ident ≠ Θ a := by
        intro hEq
        have : a ≤ ident := by
          have : Θ a ≤ Θ ident := by simp [hEq]
          exact (hΘ_order a ident).2 this
        exact (not_lt_of_ge this) ha
      exact lt_of_le_of_ne hle hne
    simpa [hΘ_ident] using this

  -- Unfold Θ_cuts; the `if` is always the `then` branch by `ident_le`.
  simp only [Θ_cuts, ident_le x, dite_true]

  set r : ℝ := Θ x / Θ a

  -- Nonempty: 0 ∈ cutSet a x.
  have h0_mem : (0 : ℚ) ∈ cutSet a x := by
    simp only [cutSet, Set.mem_setOf_eq]
    refine ⟨le_rfl, 0, 1, Nat.one_pos, by norm_num, ?_⟩
    -- `pow' a 0 = ident` and `pow' x 1 = x`.
    simpa [pow', op_ident_right] using (ident_le x)

  have h_ne : ((↑) '' cutSet a x : Set ℝ).Nonempty := by
    refine ⟨(0 : ℝ), ⟨0, h0_mem, by simp⟩⟩

  -- All elements of the cut are ≤ r.
  have h_le_r : ∀ t ∈ ((↑) '' cutSet a x : Set ℝ), t ≤ r := by
    intro t ht
    rcases ht with ⟨q, hq, rfl⟩
    simp only [cutSet, Set.mem_setOf_eq] at hq
    rcases hq with ⟨_hq_nonneg, m, n, hn_pos, hq_eq, ham_le⟩
    have hΘ_le : Θ (pow' a m) ≤ Θ (pow' x n) :=
      (hΘ_order (pow' a m) (pow' x n)).1 ham_le
    have hmn : (m : ℝ) * Θ a ≤ (n : ℝ) * Θ x := by
      simpa [hΘ_pow'] using hΘ_le
    have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have h' : ((m : ℝ) / (n : ℝ)) ≤ Θ x / Θ a := by
      -- `m/n ≤ Θx/Θa ↔ m * Θa ≤ Θx * n` (cross-multiply by positive denominators).
      have h'' : (m : ℝ) * Θ a ≤ Θ x * (n : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmn
      simpa [mul_comm, mul_left_comm, mul_assoc] using (div_le_div_iff₀ hn_pos' hΘa_pos).2 h''
    rw [hq_eq]
    simpa [Rat.cast_div, Rat.cast_natCast, r, mul_comm, mul_left_comm, mul_assoc] using h'

  -- Any `w < r` is below some element of the cut (rational density + order embedding).
  have h_lt_exists : ∀ w : ℝ, w < r → ∃ t ∈ ((↑) '' cutSet a x : Set ℝ), w < t := by
    intro w hw
    by_cases hw0 : w < 0
    · refine ⟨0, ⟨0, h0_mem, by simp⟩, hw0⟩
    · have hw0' : 0 ≤ w := le_of_not_gt hw0
      obtain ⟨q, hwq, hqr⟩ := exists_rat_btwn hw
      have hq_nonneg : 0 ≤ q := by
        have : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt hw0' hwq
        exact_mod_cast this.le
      have hq_mem : q ∈ cutSet a x := by
        simp only [cutSet, Set.mem_setOf_eq]
        refine ⟨hq_nonneg, q.num.toNat, q.den, q.den_pos, ?_, ?_⟩
        · have h_num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
          have h_eq : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg h_num_nonneg
          have hkey : (q.num.toNat : ℚ) = q.num := by exact_mod_cast h_eq
          rw [hkey]
          exact (Rat.num_div_den q).symm
        · -- Use q < r to show `a^(num) ≤ x^(den)` by reflecting the inequality via Θ.
          have hqr' : (q : ℝ) < Θ x / Θ a := by simpa [r] using hqr
          have hden_pos : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
          have hineq : (q.num.toNat : ℝ) * Θ a < Θ x * (q.den : ℝ) := by
            -- Cross-multiply.
            have : (q.num.toNat : ℝ) / (q.den : ℝ) < Θ x / Θ a := by
              -- Rewrite q as num/den and cast to ℝ.
              have h_num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
              have h_eq : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg h_num_nonneg
              have hkeyQ : (q.num.toNat : ℚ) = q.num := by exact_mod_cast h_eq
              have hq_cast :
                  (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
                have : (q : ℚ) = (q.num.toNat : ℚ) / q.den := by
                  rw [hkeyQ]
                  exact (Rat.num_div_den q).symm
                simpa [Rat.cast_div, Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) this
              simpa [hq_cast] using hqr'
            have : (q.num.toNat : ℝ) * Θ a < Θ x * (q.den : ℝ) :=
              (div_lt_div_iff₀ hden_pos hΘa_pos).1 this
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
          have hΘ_pow_lt : Θ (pow' a q.num.toNat) < Θ (pow' x q.den) := by
            have ha' : Θ (pow' a q.num.toNat) = (q.num.toNat : ℝ) * Θ a := hΘ_pow' a _
            have hx' : Θ (pow' x q.den) = (q.den : ℝ) * Θ x := hΘ_pow' x _
            have : (q.num.toNat : ℝ) * Θ a < (q.den : ℝ) * Θ x := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
            simpa [ha', hx', mul_comm, mul_left_comm, mul_assoc] using this
          have hpow_lt : pow' a q.num.toNat < pow' x q.den := by
            -- Reflect strict inequality using the order equivalence.
            by_contra h_not
            have : pow' x q.den ≤ pow' a q.num.toNat := le_of_not_gt h_not
            have hΘ' : Θ (pow' x q.den) ≤ Θ (pow' a q.num.toNat) :=
              (hΘ_order (pow' x q.den) (pow' a q.num.toNat)).1 this
            exact not_lt_of_ge hΘ' (by simpa [hΘ_pow'] using hΘ_pow_lt)
          exact le_of_lt hpow_lt
      refine ⟨(q : ℝ), ⟨q, hq_mem, rfl⟩, hwq⟩

  have : sSup ((↑) '' cutSet a x : Set ℝ) = r :=
    csSup_eq_of_forall_le_of_forall_lt_exists_gt h_ne h_le_r h_lt_exists
  simpa [r] using this

/-!
## §7: Standalone strict monotonicity and additivity

From here we assume the strict sandwich axiom `KSSeparationStrict`. This is the same hypothesis
used by `Additive/Proofs/GridInduction/Main.lean` (often derived from density), and it avoids the corner
case where the upper inequality in a separation witness is an equality.
-/

section Standalone

variable [KSSeparationStrict α]

/-!
### Bridging lemma: `iterate_op` vs `pow'`

The separation axioms (`KSSeparation` / `KSSeparationStrict`) are stated using
`KnuthSkillingAlgebra.iterate_op`.  Our cut construction is phrased using `pow'`.  These are the
same iteration, so we freely rewrite between them.
-/

omit [KSSeparation α] [KSSeparationStrict α] in
theorem iterate_op_eq_pow' (x : α) (n : ℕ) : KnuthSkillingAlgebra.iterate_op x n = pow' x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [KnuthSkillingAlgebra.iterate_op, pow', ih]

omit [KSSeparation α] [KSSeparationStrict α] in
theorem pow'_eq_iterate_op (x : α) (n : ℕ) : pow' x n = KnuthSkillingAlgebra.iterate_op x n :=
  (iterate_op_eq_pow' (x := x) (n := n)).symm

/-!
### Helper: positivity of powers
-/

omit [KSSeparation α] [KSSeparationStrict α] in
theorem pow'_pos {x : α} (hx : ident < x) {n : ℕ} (hn : 0 < n) : ident < pow' x n := by
  -- `pow' x 0 = ident` and `pow' x` is strictly increasing in the exponent.
  have hmono := pow'_strictMono_exp (x := x) hx
  have : pow' x 0 < pow' x n := hmono hn
  simpa [pow'_zero] using this

/-!
### Helper: strict upper bounds from a single strict inequality

If `x^m0 < a^n0`, then every rational in `cutSet(a,x)` is strictly below `n0/m0`.
-/

omit [KSSeparationStrict α] in
theorem cutSet_lt_of_pow'_lt (a : α) (ha : ident < a) {x : α} {m0 n0 : ℕ} (hm0 : 0 < m0)
    (h_lt : pow' x m0 < pow' a n0) :
    ∀ q ∈ cutSet a x, (q : ℝ) < (n0 : ℝ) / (m0 : ℝ) := by
  intro q hq
  rcases hq with ⟨_hq_nonneg, m, n, hn_pos, hq_eq, ham_le⟩
  -- Rewrite `q` as `m/n`.
  subst hq_eq

  have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hm0_pos' : 0 < (m0 : ℝ) := by exact_mod_cast hm0

  -- Scale `a^m ≤ x^n` by `m0`: `a^(m*m0) ≤ x^(n*m0)`.
  have ham_le' : pow' a (m * m0) ≤ pow' x (n * m0) := by
    -- raise both sides to the (positive) power `m0`
    have := pow'_mono_base (x := pow' a m) (y := pow' x n) ham_le m0 hm0
    -- rewrite (a^m)^m0 and (x^n)^m0
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  -- Scale `x^m0 < a^n0` by `n`: `x^(m0*n) < a^(n0*n)`.
  have hx_lt' : pow' x (m0 * n) < pow' a (n0 * n) := by
    have := pow'_strictMono_base (x := pow' x m0) (y := pow' a n0) h_lt n hn_pos
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  -- Combine: `a^(m*m0) ≤ x^(n*m0) = x^(m0*n) < a^(n0*n)`.
  have h_between : pow' a (m * m0) < pow' a (n0 * n) := by
    -- rewrite `n*m0 = m0*n`
    have : n * m0 = m0 * n := Nat.mul_comm n m0
    have ham_le'' : pow' a (m * m0) ≤ pow' x (m0 * n) := by
      simpa [this] using ham_le'
    exact lt_of_le_of_lt ham_le'' hx_lt'

  -- Since `a > ident`, strict monotonicity of `pow' a` gives `m*m0 < n0*n`.
  have h_nat : m * m0 < n0 * n := by
    exact (pow'_strictMono_exp (x := a) ha).lt_iff_lt.mp h_between

  -- Convert the nat inequality to a real inequality of fractions.
  have h' : (m : ℝ) * (m0 : ℝ) < (n0 : ℝ) * (n : ℝ) := by exact_mod_cast h_nat
  have : (m : ℝ) / (n : ℝ) < (n0 : ℝ) / (m0 : ℝ) := by
    exact (div_lt_div_iff₀ hn_pos' hm0_pos').2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h')
  -- Replace the RHS by `(n0 : ℝ) / (m0 : ℝ)` and rewrite the LHS as `(q : ℝ)`.
  simpa [Rat.cast_div, Rat.cast_natCast] using this

/-!
### Strict monotonicity of `Θ_cuts`

We prove strict monotonicity using a two-step strict-separation trick:
1. From `x < y`, strict separation gives `x^m < a^n < y^m`, so `n/m ∈ cutSet(a,y)`.
2. Apply strict separation again to `x^m < a^n` to get a *smaller* rational upper bound for
   `cutSet(a,x)`, guaranteeing `Θ_cuts(a,x) < n/m ≤ Θ_cuts(a,y)`.
-/

theorem Θ_cuts_strictMono (a : α) (ha : ident < a) : StrictMono (Θ_cuts a ha) := by
  intro x y hxy
  classical

  -- Handle the `x = ident` case separately.
  by_cases hx0 : x = ident
  · subst hx0
    -- Show `0 < Θ_cuts a ha y` from Archimedean (derived from KSSeparation): some power of `y` dominates `a`.
    have hy_pos : ident < y := by simpa using hxy
    obtain ⟨N, hN⟩ := SandwichSeparation.SeparationToArchimedean.op_archimedean_of_separation y a hy_pos
    rw [iterate_eq_pow'_succ] at hN
    have h_mem : ((1 : ℚ) / (N + 1 : ℕ)) ∈ cutSet a y := by
      have h0_le : (0 : ℚ) ≤ (1 : ℚ) / (N + 1 : ℕ) := by
        have hden : (0 : ℚ) < ((N + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos N
        have hpos : (0 : ℚ) < (1 : ℚ) / ((N + 1 : ℕ) : ℚ) :=
          div_pos (show (0 : ℚ) < 1 by norm_num) hden
        simpa using (le_of_lt hpos)
      refine ⟨h0_le, 1, N + 1, Nat.succ_pos N, by simp, ?_⟩
      -- `a^1 = a ≤ y^(N+1)` since `a < y^(N+1)`
      simpa [pow', op_ident_right] using (le_of_lt hN)
    have h_nonempty : ((↑) '' cutSet a y : Set ℝ).Nonempty := by
      refine ⟨((1 : ℚ) / (N + 1 : ℕ) : ℝ), ⟨(1 : ℚ) / (N + 1 : ℕ), h_mem, by simp⟩⟩
    have h_sup_ge : ((1 : ℚ) / (N + 1 : ℕ) : ℝ) ≤ Θ_cuts a ha y := by
      -- `Θ_cuts` is the supremum of the image cut.
      simp only [Θ_cuts, ident_le y, dite_true]
      rcases cutSet_bddAbove a ha y with ⟨B, hB⟩
      have hbdd : BddAbove ((↑) '' cutSet a y : Set ℝ) := by
        refine ⟨(B : ℝ), ?_⟩
        intro r hr
        rcases hr with ⟨q, hq, rfl⟩
        exact Rat.cast_le.mpr (hB hq)
      exact le_csSup hbdd ⟨(1 : ℚ) / (N + 1 : ℕ), h_mem, by simp⟩
    have h_pos : (0 : ℝ) < ((1 : ℚ) / (N + 1 : ℕ) : ℝ) := by
      have : (0 : ℚ) < (1 : ℚ) / (N + 1 : ℕ) := by
        have : (0 : ℚ) < (N + 1 : ℚ) := by exact_mod_cast Nat.succ_pos N
        simpa using (div_pos (show (0 : ℚ) < 1 by norm_num) this)
      exact_mod_cast this
    -- `Θ_cuts a ha ident = 0`.
    have hΘ_ident : Θ_cuts a ha ident = 0 := Θ_cuts_ident a ha
    simpa [hΘ_ident] using (lt_of_lt_of_le h_pos h_sup_ge)

  -- Otherwise, `x` is positive, and so is `y` (since `x < y` and `ident` is bottom).
  have hx_pos : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx0)
  have hy0 : y ≠ ident := by
    intro hy0
    subst hy0
    exact (not_lt_of_ge (ident_le x)) hxy
  have hy_pos : ident < y := lt_of_le_of_ne (ident_le y) (Ne.symm hy0)

  -- Strict separation for `x < y` with base `a`.
  rcases (KSSeparationStrict.separation_strict (α := α) (a := a) (x := x) (y := y) ha hx_pos hy_pos hxy) with
    ⟨n0, m0, hm0_pos, hlt_iter, hgt_iter⟩
  have hlt : pow' x m0 < pow' a n0 := by
    simpa [pow'_eq_iterate_op] using hlt_iter
  have hgt : pow' a n0 < pow' y m0 := by
    simpa [pow'_eq_iterate_op] using hgt_iter

  -- The witness rational `q0 = n0/m0` lies in `cutSet(a,y)`.
  have hq0_mem : (n0 : ℚ) / m0 ∈ cutSet a y := by
    have h0_le : (0 : ℚ) ≤ (n0 : ℚ) / m0 := by
      have hm0_posQ : (0 : ℚ) < ((m0 : ℕ) : ℚ) := by exact_mod_cast hm0_pos
      exact div_nonneg (by exact_mod_cast (Nat.zero_le n0)) (le_of_lt hm0_posQ)
    refine ⟨h0_le, n0, m0, hm0_pos, by simp, ?_⟩
    exact le_of_lt hgt

  have hq0_le : ((n0 : ℚ) / m0 : ℝ) ≤ Θ_cuts a ha y := by
    simp only [Θ_cuts, ident_le y, dite_true]
    rcases cutSet_bddAbove a ha y with ⟨B, hB⟩
    have hbdd : BddAbove ((↑) '' cutSet a y : Set ℝ) := by
      refine ⟨(B : ℝ), ?_⟩
      intro r hr
      rcases hr with ⟨q, hq, rfl⟩
      exact Rat.cast_le.mpr (hB hq)
    exact le_csSup hbdd ⟨(n0 : ℚ) / m0, hq0_mem, by simp⟩

  -- Apply strict separation again to `x^m0 < a^n0`, producing a *smaller* rational upper bound.
  have hx_m0_pos : ident < pow' x m0 := pow'_pos (hx := hx_pos) (hn := hm0_pos)
  have ha_n0_pos : ident < pow' a n0 := by
    -- `n0 = 0` would contradict `x^m0 < a^n0 = ident` since `ident ≤ x^m0`.
    have hn0_pos : 0 < n0 := by
      by_contra hn0
      have : n0 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hn0)
      subst this
      simpa [pow'_zero] using (lt_of_le_of_lt (ident_le (pow' x m0)) hlt)
    exact pow'_pos (hx := ha) (hn := hn0_pos)

  rcases (KSSeparationStrict.separation_strict (α := α) (a := a) (x := pow' x m0) (y := pow' a n0)
      ha hx_m0_pos ha_n0_pos hlt) with
    ⟨n1, k, hk_pos, hlt1_iter, hgt1_iter⟩

  have hlt1 : pow' x (m0 * k) < pow' a n1 := by
    -- (x^m0)^k < a^n1  ⇒  x^(m0*k) < a^n1
    have : pow' (pow' x m0) k < pow' a n1 := by
      simpa [pow'_eq_iterate_op] using hlt1_iter
    simpa [pow'_mul] using this
  have hgt1 : pow' a n1 < pow' a (n0 * k) := by
    have : pow' a n1 < pow' (pow' a n0) k := by
      simpa [pow'_eq_iterate_op] using hgt1_iter
    simpa [pow'_mul] using this

  -- `Θ_cuts(a,x)` is bounded above by `n1/(m0*k)`, and that bound is strictly below `n0/m0`.
  have hΘx_le : Θ_cuts a ha x ≤ (n1 : ℝ) / ((m0 * k : ℕ) : ℝ) := by
    simp only [Θ_cuts, ident_le x, dite_true]
    have hx_nonempty : ((↑) '' cutSet a x : Set ℝ).Nonempty :=
      Set.image_nonempty.mpr (cutSet_nonempty a x (ident_le x))
    refine csSup_le hx_nonempty ?_
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    have : (q : ℝ) < (n1 : ℝ) / ((m0 * k : ℕ) : ℝ) :=
      cutSet_lt_of_pow'_lt a ha (m0 := m0 * k) (n0 := n1)
        (Nat.mul_pos hm0_pos hk_pos) hlt1 q hq
    exact le_of_lt this

  have hk0_pos' : 0 < ((m0 * k : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hm0_pos hk_pos
  have hm0_pos' : 0 < (m0 : ℝ) := by exact_mod_cast hm0_pos
  have hlt_rat : (n1 : ℝ) / ((m0 * k : ℕ) : ℝ) < (n0 : ℝ) / (m0 : ℝ) := by
    -- From `a^n1 < a^(n0*k)` we get `n1 < n0*k`, hence the rational inequality.
    have hn1_lt : n1 < n0 * k := (pow'_strictMono_exp (x := a) ha).lt_iff_lt.mp hgt1
    have hn1_lt' : (n1 : ℝ) < (n0 : ℝ) * (k : ℝ) := by exact_mod_cast hn1_lt
    -- Compare `n1/(m0*k)` with `n0/m0` by cross-multiplying.
    have : (n1 : ℝ) / ((m0 * k : ℕ) : ℝ) < (n0 : ℝ) / (m0 : ℝ) := by
      -- `m0*k` is positive, so clear denominators.
      have hk' : ((m0 * k : ℕ) : ℝ) = (m0 : ℝ) * (k : ℝ) := by
        norm_cast
      -- use `div_lt_div_iff₀`
      have : (n1 : ℝ) * (m0 : ℝ) < (n0 : ℝ) * ((m0 * k : ℕ) : ℝ) := by
        -- `n1 * m0 < (n0*k) * m0`
        have : (n1 : ℝ) * (m0 : ℝ) < ((n0 : ℝ) * (k : ℝ)) * (m0 : ℝ) := by
          nlinarith [hn1_lt']
        -- rewrite RHS
        simpa [hk', mul_assoc, mul_left_comm, mul_comm] using this
      exact (div_lt_div_iff₀ (show 0 < ((m0 * k : ℕ) : ℝ) by exact_mod_cast Nat.mul_pos hm0_pos hk_pos) hm0_pos').2 this
    exact this
  -- Now combine inequalities: Θ(x) ≤ n1/(m0*k) < n0/m0 ≤ Θ(y).
  have hΘx_lt_q0 : Θ_cuts a ha x < (n0 : ℝ) / (m0 : ℝ) :=
    lt_of_le_of_lt hΘx_le hlt_rat
  have hq0_le' : (n0 : ℝ) / (m0 : ℝ) ≤ Θ_cuts a ha y := by
    -- rewrite `((n0 : ℚ) / m0 : ℝ)` as `n0/m0`
    simpa [Rat.cast_div, Rat.cast_natCast] using hq0_le
  exact lt_of_lt_of_le hΘx_lt_q0 hq0_le'

/-!
### Additivity of `Θ_cuts` (standalone)

We prove `Θ(x ⊕ y) = Θ(x) + Θ(y)` by sandwiching:
1. `Θ(x) + Θ(y) ≤ Θ(x ⊕ y)` from closure of `cutSet` under addition and `csSup_image2`.
2. `Θ(x ⊕ y) ≤ Θ(x) + Θ(y)` by bounding each rational in `cutSet(a, x ⊕ y)` using a
   denominator-amplification (“floor”) argument.
-/

-- A small helper: the real image of a cut-set.
abbrev cutSetReal (a : α) (x : α) : Set ℝ := (fun q : ℚ => (q : ℝ)) '' cutSet a x

omit [KSSeparation α] [KSSeparationStrict α] in
theorem cutSetReal_nonempty (a : α) (x : α) : (cutSetReal a x).Nonempty :=
  Set.image_nonempty.mpr (cutSet_nonempty a x (ident_le x))

omit [KSSeparationStrict α] in
theorem cutSetReal_bddAbove (a : α) (ha : ident < a) (x : α) : BddAbove (cutSetReal a x) := by
  rcases cutSet_bddAbove a ha x with ⟨B, hB⟩
  refine ⟨(B : ℝ), ?_⟩
  intro r hr
  rcases hr with ⟨q, hq, rfl⟩
  exact Rat.cast_le.mpr (hB hq)

omit [KSSeparation α] [KSSeparationStrict α] in
theorem Θ_cuts_eq_csSup (a : α) (ha : ident < a) (x : α) :
    Θ_cuts a ha x = sSup (cutSetReal a x) := by
  simp [Θ_cuts, cutSetReal, ident_le x]

-- Closure of `cutSet` under rational addition.
omit [KSSeparationStrict α] in
theorem cutSet_add_closed (a : α) (x y : α) :
    ∀ {q₁ q₂ : ℚ}, q₁ ∈ cutSet a x → q₂ ∈ cutSet a y → q₁ + q₂ ∈ cutSet a (op x y) := by
  intro q₁ q₂ hq₁ hq₂
  rcases hq₁ with ⟨hq₁_nonneg, m₁, n₁, hn₁_pos, hq₁_eq, ham₁_le⟩
  rcases hq₂ with ⟨hq₂_nonneg, m₂, n₂, hn₂_pos, hq₂_eq, ham₂_le⟩
  subst hq₁_eq; subst hq₂_eq

  -- Use the common denominator `n₁ * n₂`.
  refine ⟨add_nonneg hq₁_nonneg hq₂_nonneg, m₁ * n₂ + m₂ * n₁, n₁ * n₂, Nat.mul_pos hn₁_pos hn₂_pos, ?_, ?_⟩
  · -- arithmetic: (m1/n1) + (m2/n2) = (m1*n2 + m2*n1)/(n1*n2)
    have hn₁_ne : (n₁ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn₁_pos)
    have hn₂_ne : (n₂ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn₂_pos)
    field_simp [hn₁_ne, hn₂_ne]
    simp [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, add_comm]

  -- Scale inequalities to the common denominator.
  have ham₁_le' : pow' a (m₁ * n₂) ≤ pow' x (n₁ * n₂) := by
    have := pow'_mono_base (x := pow' a m₁) (y := pow' x n₁) ham₁_le n₂ hn₂_pos
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
  have ham₂_le' : pow' a (m₂ * n₁) ≤ pow' y (n₂ * n₁) := by
    have := pow'_mono_base (x := pow' a m₂) (y := pow' y n₂) ham₂_le n₁ hn₁_pos
    simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  -- Combine: a^(m₁*n₂ + m₂*n₁) ≤ x^(n₁*n₂) ⊕ y^(n₁*n₂) = (x⊕y)^(n₁*n₂).
  -- Distribute power over `op` (this is linear in the additive setting).
  have h_distrib :
      pow' (op x y) (n₁ * n₂) = op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) := by
    -- Reuse the existing iterate-op lemma, then rewrite back to `pow'`.
    simpa [pow'_eq_iterate_op] using
      (KnuthSkillingAlgebra.iterate_op_op_distrib_of_comm (α := α) (x := x) (y := y) (m := n₁ * n₂) op_comm')

  have ham₂_le'' : pow' a (m₂ * n₁) ≤ pow' y (n₁ * n₂) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ham₂_le'

  -- Monotonicity in both arguments.
  have h_mono_right :
      op (pow' a (m₁ * n₂)) (pow' a (m₂ * n₁)) ≤ op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) :=
    KnuthSkillingAlgebra.op_mono_right (x := pow' a (m₁ * n₂)) ham₂_le''

  have h_mono_left :
      op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) ≤ op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) :=
    KnuthSkillingAlgebra.op_mono_left (y := pow' y (n₁ * n₂)) ham₁_le'

  -- Put it together.
  calc
    pow' a (m₁ * n₂ + m₂ * n₁)
        = op (pow' a (m₁ * n₂)) (pow' a (m₂ * n₁)) := by
            simp [pow'_add]
    _ ≤ op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) := h_mono_right
    _ ≤ op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) := h_mono_left
    _ = pow' (op x y) (n₁ * n₂) := by
          simpa using h_distrib.symm

-- Main additivity theorem.
omit [KSSeparationStrict α] in
theorem Θ_cuts_add (a : α) (ha : ident < a) (x y : α) :
    Θ_cuts a ha (op x y) = Θ_cuts a ha x + Θ_cuts a ha y := by
  classical
  -- Work with the real images of the cut-sets.
  set s : Set ℝ := cutSetReal a x
  set t : Set ℝ := cutSetReal a y
  set u : Set ℝ := cutSetReal a (op x y)

  have hs0 : s.Nonempty := by simpa [s] using cutSetReal_nonempty a x
  have ht0 : t.Nonempty := by simpa [t] using cutSetReal_nonempty a y
  have hu0 : u.Nonempty := by simpa [u] using cutSetReal_nonempty a (op x y)

  have hs1 : BddAbove s := by simpa [s] using cutSetReal_bddAbove a ha x
  have ht1 : BddAbove t := by simpa [t] using cutSetReal_bddAbove a ha y
  have hu1 : BddAbove u := by simpa [u] using cutSetReal_bddAbove a ha (op x y)

  -- Inclusion: `cutSetReal(a,x) + cutSetReal(a,y) ⊆ cutSetReal(a, x⊕y)`.
  have hsubset : s + t ⊆ u := by
    intro r hr
    rcases Set.mem_add.1 hr with ⟨r₁, hr₁, r₂, hr₂, rfl⟩
    rcases hr₁ with ⟨q₁, hq₁, rfl⟩
    rcases hr₂ with ⟨q₂, hq₂, rfl⟩
    refine ⟨q₁ + q₂, cutSet_add_closed a x y hq₁ hq₂, ?_⟩
    simp only [Rat.cast_add]

  -- First inequality: Θ(x) + Θ(y) ≤ Θ(x⊕y).
  have h_le1 : sSup s + sSup t ≤ sSup u := by
    have h_sup_sum : sSup (s + t) ≤ sSup u :=
      csSup_le_csSup hu1 (hs0.add ht0) hsubset
    have h_add : sSup (s + t) = sSup s + sSup t :=
      csSup_add hs0 hs1 ht0 ht1
    -- rewrite via `csSup_add` and use inclusion.
    have : sSup s + sSup t = sSup (s + t) := by simpa using h_add.symm
    exact this.trans_le h_sup_sum

  -- Second inequality: Θ(x⊕y) ≤ Θ(x) + Θ(y).
  have h_le2 : sSup u ≤ sSup s + sSup t := by
    refine csSup_le hu0 ?_
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    -- If `q` were strictly above the sum of sups, we can split it into `q₁+q₂`
    -- with `q₁ > Θ(x)` and `q₂ > Θ(y)` and derive a contradiction.
    by_contra h_not_le
    have h_gt : sSup s + sSup t < (q : ℝ) := lt_of_not_ge h_not_le

    -- Unpack the witness for `q ∈ cutSet(a, x⊕y)`.
    rcases hq with ⟨hq_nonneg, m, n, hn_pos, hq_eq, ham_le⟩

    -- Between Θ(x) and q-Θ(y) pick a rational q₁.
    have h_between : sSup s < (q : ℝ) - sSup t := by nlinarith [h_gt]
    obtain ⟨q₁, hq₁_gt, hq₁_lt⟩ := exists_rat_btwn h_between
    let q₂ : ℚ := q - q₁

    have hq₂_gt : sSup t < (q₂ : ℝ) := by
      have : sSup t < (q : ℝ) - (q₁ : ℝ) := by linarith [hq₁_lt]
      have hcast : ((q - q₁ : ℚ) : ℝ) = (q : ℝ) - (q₁ : ℝ) := by simp [sub_eq_add_neg]
      simpa [q₂, hcast] using this

    -- Nonnegativity of Θ(x), Θ(y): 0 belongs to each cutSetReal.
    have h0_mem_s : (0 : ℝ) ∈ s := by
      refine ⟨0, ?_, by simp⟩
      simp only [cutSet, Set.mem_setOf_eq]
      refine ⟨le_rfl, 0, 1, Nat.one_pos, by simp, ?_⟩
      -- `pow' x 1 = op x ident`, and `op x ident = x`.
      simpa [pow', op_ident_right] using (ident_le x)
    have h0_mem_t : (0 : ℝ) ∈ t := by
      refine ⟨0, ?_, by simp⟩
      simp only [cutSet, Set.mem_setOf_eq]
      refine ⟨le_rfl, 0, 1, Nat.one_pos, by simp, ?_⟩
      -- `pow' y 1 = op y ident`, and `op y ident = y`.
      simpa [pow', op_ident_right] using (ident_le y)

    have hΘx_nonneg : (0 : ℝ) ≤ sSup s := le_csSup hs1 h0_mem_s
    have hΘy_nonneg : (0 : ℝ) ≤ sSup t := le_csSup ht1 h0_mem_t

    have hq₁_nonneg : (0 : ℚ) ≤ q₁ := by
      have h0 : (0 : ℝ) ≤ (q₁ : ℝ) := le_trans hΘx_nonneg (le_of_lt hq₁_gt)
      have h0' : ((0 : ℚ) : ℝ) ≤ (q₁ : ℝ) := by simpa using h0
      exact (Rat.cast_le (p := (0 : ℚ)) (q := q₁) (K := ℝ)).1 h0'
    have hq₂_nonneg : (0 : ℚ) ≤ q₂ := by
      have h0 : (0 : ℝ) ≤ (q₂ : ℝ) := le_trans hΘy_nonneg (le_of_lt hq₂_gt)
      have h0' : ((0 : ℚ) : ℝ) ≤ (q₂ : ℝ) := by simpa using h0
      exact (Rat.cast_le (p := (0 : ℚ)) (q := q₂) (K := ℝ)).1 h0'

    -- Since q₁ > Θ(x), it cannot lie in the cut-set for x; similarly for q₂ and y.
    have hq₁_not : q₁ ∉ cutSet a x := by
      intro hq₁_mem
      have hq₁_mem' : (q₁ : ℝ) ∈ s := by
        -- `s = (↑) '' cutSet a x`
        simpa [s, cutSetReal] using (show (q₁ : ℝ) ∈ ((↑) '' cutSet a x : Set ℝ) from ⟨q₁, hq₁_mem, by simp⟩)
      have : (q₁ : ℝ) ≤ sSup s := le_csSup hs1 hq₁_mem'
      exact not_lt_of_ge this hq₁_gt

    have hq₂_not : q₂ ∉ cutSet a y := by
      intro hq₂_mem
      have hq₂_mem' : (q₂ : ℝ) ∈ t := by
        simpa [t, cutSetReal] using (show (q₂ : ℝ) ∈ ((↑) '' cutSet a y : Set ℝ) from ⟨q₂, hq₂_mem, by simp⟩)
      have : (q₂ : ℝ) ≤ sSup t := le_csSup ht1 hq₂_mem'
      exact not_lt_of_ge this hq₂_gt

    -- Canonical numerator/denominator representations for q₁ and q₂ (since they are nonnegative).
    let m₁ : ℕ := q₁.num.toNat
    let n₁ : ℕ := q₁.den
    have hn₁_pos : 0 < n₁ := q₁.den_pos
    have hq₁_eq : q₁ = m₁ / n₁ := by
      -- q₁ = q₁.num.toNat / q₁.den for nonnegative q₁
      have h_num_nonneg : 0 ≤ q₁.num := Rat.num_nonneg.mpr hq₁_nonneg
      have h_eqZ : (q₁.num.toNat : ℤ) = q₁.num := Int.toNat_of_nonneg h_num_nonneg
      have hkey : (q₁.num.toNat : ℚ) = q₁.num := by exact_mod_cast h_eqZ
      calc
        q₁ = q₁.num / q₁.den := (Rat.num_div_den q₁).symm
        _ = (q₁.num.toNat : ℚ) / q₁.den := by simp [hkey]
        _ = m₁ / n₁ := rfl

    let m₂ : ℕ := q₂.num.toNat
    let n₂ : ℕ := q₂.den
    have hn₂_pos : 0 < n₂ := q₂.den_pos
    have hq₂_eq : q₂ = m₂ / n₂ := by
      have h_num_nonneg : 0 ≤ q₂.num := Rat.num_nonneg.mpr hq₂_nonneg
      have h_eqZ : (q₂.num.toNat : ℤ) = q₂.num := Int.toNat_of_nonneg h_num_nonneg
      have hkey : (q₂.num.toNat : ℚ) = q₂.num := by exact_mod_cast h_eqZ
      calc
        q₂ = q₂.num / q₂.den := (Rat.num_div_den q₂).symm
        _ = (q₂.num.toNat : ℚ) / q₂.den := by simp [hkey]
        _ = m₂ / n₂ := rfl

    -- From non-membership, obtain strict inequalities on the corresponding powers.
    have hx_strict : pow' x n₁ < pow' a m₁ := by
      have : ¬ pow' a m₁ ≤ pow' x n₁ := by
        intro hle
        have : q₁ ∈ cutSet a x := by
          refine ⟨hq₁_nonneg, m₁, n₁, hn₁_pos, hq₁_eq, hle⟩
        exact hq₁_not this
      exact lt_of_not_ge this

    have hy_strict : pow' y n₂ < pow' a m₂ := by
      have : ¬ pow' a m₂ ≤ pow' y n₂ := by
        intro hle
        have : q₂ ∈ cutSet a y := by
          refine ⟨hq₂_nonneg, m₂, n₂, hn₂_pos, hq₂_eq, hle⟩
        exact hq₂_not this
      exact lt_of_not_ge this

    -- Scale both strict inequalities to the common denominator n₁*n₂.
    have hx_scaled : pow' x (n₁ * n₂) < pow' a (m₁ * n₂) := by
      have := pow'_strictMono_base (x := pow' x n₁) (y := pow' a m₁) hx_strict n₂ hn₂_pos
      simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

    have hy_scaled : pow' y (n₁ * n₂) < pow' a (m₂ * n₁) := by
      have := pow'_strictMono_base (x := pow' y n₂) (y := pow' a m₂) hy_strict n₁ hn₁_pos
      -- rewrite n₂*n₁ and n₁*n₂
      simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

    -- Use distributivity of iterate over `op` and strict monotonicity to get:
    -- (x⊕y)^(n₁*n₂) < a^(m₁*n₂ + m₂*n₁).
    have h_distrib_xy :
        pow' (op x y) (n₁ * n₂) = op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) := by
      simpa [pow'_eq_iterate_op] using
        (KnuthSkillingAlgebra.iterate_op_op_distrib_of_comm (α := α) (x := x) (y := y) (m := n₁ * n₂) op_comm')

    have h_sum_lt :
        pow' (op x y) (n₁ * n₂) < pow' a (m₁ * n₂ + m₂ * n₁) := by
      -- rewrite both sides as sums
      have h_rhs :
          op (pow' a (m₁ * n₂)) (pow' a (m₂ * n₁)) = pow' a (m₁ * n₂ + m₂ * n₁) := by
        simp [pow'_add]
      have h1 :
          op (pow' x (n₁ * n₂)) (pow' y (n₁ * n₂)) < op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) :=
        op_strictMono_left (pow' y (n₁ * n₂)) hx_scaled
      have h2 :
          op (pow' a (m₁ * n₂)) (pow' y (n₁ * n₂)) < op (pow' a (m₁ * n₂)) (pow' a (m₂ * n₁)) :=
        op_strictMono_right (pow' a (m₁ * n₂)) hy_scaled
      -- assemble
      rw [h_distrib_xy, ← h_rhs]
      exact lt_trans h1 h2

    -- Compute the rational q as m/n, and also as the q₁+q₂ construction.
    have hq_mn : (m : ℚ) / n = q := by simp [hq_eq]
    have hq_as_sum : q = q₁ + q₂ := by simp [q₂]
    have hq_as_frac :
        q = (m₁ * n₂ + m₂ * n₁ : ℕ) / (n₁ * n₂ : ℕ) := by
      -- expand q₁ and q₂ as nat fractions and compute.
      calc
        q = q₁ + q₂ := hq_as_sum
        _ = (m₁ : ℚ) / n₁ + (m₂ : ℚ) / n₂ := by simp [hq₁_eq, hq₂_eq]
        _ = (m₁ * n₂ + m₂ * n₁ : ℕ) / (n₁ * n₂ : ℕ) := by
              have hn₁_ne : (n₁ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn₁_pos)
              have hn₂_ne : (n₂ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn₂_pos)
              field_simp [hn₁_ne, hn₂_ne]
              simp [Nat.cast_add, Nat.cast_mul, mul_comm]

    -- Cross-multiply to relate the two representations.
    have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn_pos)
    have hn' : 0 < n₁ * n₂ := Nat.mul_pos hn₁_pos hn₂_pos
    have hn'_ne : ((n₁ * n₂ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn')

    have h_cross : m * (n₁ * n₂) = (m₁ * n₂ + m₂ * n₁) * n := by
      -- derive from equality of rationals m/n = (m')/(n')
      have h_div :
          (m : ℚ) / n = (m₁ * n₂ + m₂ * n₁ : ℕ) / (n₁ * n₂ : ℕ) := by
        -- both sides equal q
        calc
          (m : ℚ) / n = q := hq_mn
          _ = (m₁ * n₂ + m₂ * n₁ : ℕ) / (n₁ * n₂ : ℕ) := hq_as_frac
      -- clear denominators in ℚ and cast back to ℕ
      have h' :
          (m : ℚ) * ((n₁ * n₂ : ℕ) : ℚ) = (m₁ * n₂ + m₂ * n₁ : ℚ) * (n : ℚ) := by
        have := (div_eq_div_iff hn_ne hn'_ne).1 h_div
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact_mod_cast h'

    -- Scale `a^m ≤ (x⊕y)^n` by `n₁*n₂`.
    have ham_scale : pow' a (m * (n₁ * n₂)) ≤ pow' (op x y) (n * (n₁ * n₂)) := by
      have := pow'_mono_base (x := pow' a m) (y := pow' (op x y) n) ham_le (n₁ * n₂) hn'
      simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

    -- Scale `(x⊕y)^(n₁*n₂) < a^(m')` by `n`.
    have hlt_scale : pow' (op x y) ((n₁ * n₂) * n) < pow' a ((m₁ * n₂ + m₂ * n₁) * n) := by
      have := pow'_strictMono_base (x := pow' (op x y) (n₁ * n₂)) (y := pow' a (m₁ * n₂ + m₂ * n₁))
        h_sum_lt n hn_pos
      simpa [pow'_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

    -- Align the exponents using `h_cross` and contradict transitivity.
    have ham_scale' :
        pow' a ((m₁ * n₂ + m₂ * n₁) * n) ≤ pow' (op x y) ((n₁ * n₂) * n) := by
      -- rewrite m*(n₁*n₂) as (m')*n using h_cross
      -- and rewrite n*(n₁*n₂) as (n₁*n₂)*n
      have : m * (n₁ * n₂) = (m₁ * n₂ + m₂ * n₁) * n := h_cross
      -- `ham_scale` uses `m*(n₁*n₂)` and `n*(n₁*n₂)`.
      -- normalize multiplication order and rewrite.
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, this] using ham_scale

    exact (not_lt_of_ge ham_scale' hlt_scale)

  -- Combine both inequalities.
  have h_sSup_eq : sSup u = sSup s + sSup t :=
    le_antisymm h_le2 h_le1

  -- Rewrite back to Θ_cuts.
  have hΘx : Θ_cuts a ha x = sSup s := by simpa [s] using Θ_cuts_eq_csSup a ha x
  have hΘy : Θ_cuts a ha y = sSup t := by simpa [t] using Θ_cuts_eq_csSup a ha y
  have hΘxy : Θ_cuts a ha (op x y) = sSup u := by
    simpa [u] using Θ_cuts_eq_csSup a ha (op x y)
  -- Finish.
  simpa [hΘx, hΘy, hΘxy] using h_sSup_eq

end Standalone

/-!
## §8: Identity-Free Cuts (Using ℕ+ Iteration)

This section provides a **genuinely identity-free** cuts construction using:
- `iterate_op_pnat : ℕ+ → α` instead of `pow' : ℕ → α` (no n=0 base case)
- `IsPositive a` instead of `ident < a` (Eric Luap's identity-free positivity)

This is the proper foundational approach for ordered semigroups without identity.
-/

section IdentityFreeCuts
variable {α : Type*} [KSSemigroupBase α] [KSSeparationSemigroup α]

open KSSemigroupBase

/-- Identity-free cut set: rationals m/n such that a^m ≤ x^n (using ℕ+ iteration). -/
def cutSet_pnat (a : α) (x : α) : Set ℚ :=
  { q : ℚ | 0 ≤ q ∧ ∃ (m n : ℕ+), q = (m : ℚ) / n ∧ iterate_op_pnat a m ≤ iterate_op_pnat x n }

/-- **Archimedean property for identity-free semigroups**: For positive elements a and x,
there exists N such that a ≤ x^N.

This is derivable from `KSSeparationSemigroup` via the following argument:
1. If a ≤ x, then N = 1 works.
2. If x < a, apply separation with base x on interval (x, a) to get bounds.
   The lower bound x^m < x^n forces m < n (strict mono in exponent).
   Combined with density of rationals, this shows x^n grows unboundedly.

Full proof uses techniques from SandwichSeparation.lean. -/
theorem archimedean_pnat_of_separation (a x : α) (ha : IsPositive a) (hx : IsPositive x) :
    ∃ N : ℕ+, a ≤ iterate_op_pnat x N := by
  -- Case 1: a ≤ x
  by_cases hax : a ≤ x
  · exact ⟨1, by simpa only [iterate_op_pnat_one] using hax⟩
  -- Case 2: x < a
  push_neg at hax
  -- Apply separation with base x on interval (a, op a a)
  -- First establish: a < op a a (from IsPositive a)
  have ha2_lt : a < op a a := ha a
  -- Establish: IsPositive (op a a)
  -- For any y: y < op a y < op a (op a y) = op (op a a) y (by associativity)
  have ha2_pos : IsPositive (op a a) := fun y =>
    lt_trans (ha y) (by rw [op_assoc]; exact ha (op a y))
  -- Apply separation: base = x, lower = a, upper = op a a
  obtain ⟨n, m, h_lower, h_upper⟩ := KSSeparationSemigroup.sep hx ha ha2_pos ha2_lt
  -- h_lower: a^m < x^n
  -- h_upper: x^n ≤ (op a a)^m
  -- From a^m < x^n with m ≥ 1: a = a^1 ≤ a^m < x^n
  use n
  -- Show a ≤ a^m using monotonicity (1 ≤ m)
  have ha_le_am : a ≤ iterate_op_pnat a m := by
    rw [← iterate_op_pnat_one a]
    exact iterate_op_pnat_mono a ha (PNat.one_le m)
  -- Conclude: a ≤ a^m < x^n
  exact le_of_lt (lt_of_le_of_lt ha_le_am h_lower)

/-- **Reverse Archimedean**: For positive a and x, there exists K with x < a^K.
This bounds x from above by powers of a. -/
theorem reverse_archimedean_pnat (a x : α) (ha : IsPositive a) (_hx : IsPositive x) :
    ∃ K : ℕ+, x < iterate_op_pnat a K := by
  -- Case 1: x < a already
  by_cases hxa : x < a
  · exact ⟨1, by simpa only [iterate_op_pnat_one] using hxa⟩
  -- Case 2: a ≤ x
  push_neg at hxa
  -- Need to show x < a^K for some K
  -- Use Archimedean: x ≤ a^N for some N, then x < a^{N+1}
  obtain ⟨N, hN⟩ := archimedean_pnat_of_separation x a _hx ha
  -- hN : x ≤ a^N
  use N + 1
  have h_mono : N < N + 1 := PNat.lt_add_one_iff.mpr (le_refl N)
  calc x ≤ iterate_op_pnat a N := hN
    _ < iterate_op_pnat a (N + 1) := iterate_op_pnat_strictMono a ha h_mono

omit [KSSeparationSemigroup α] in
/-- The cut set is nonempty when x has positive element a in its cut (contains 1/1 = 1 when a ≤ x). -/
theorem cutSet_pnat_nonempty_of_ge (a x : α) (hax : a ≤ x) :
    (cutSet_pnat a x).Nonempty := by
  use 1
  simp only [cutSet_pnat, Set.mem_setOf_eq]
  refine ⟨by norm_num, 1, 1, ?_, ?_⟩
  · norm_num
  · simp only [iterate_op_pnat_one, hax]

/-- More general nonemptiness: cut set always contains rational approximations. -/
theorem cutSet_pnat_nonempty (a x : α) (ha : IsPositive a) (hx : IsPositive x) :
    (cutSet_pnat a x).Nonempty := by
  -- By Archimedean: ∃ N, a ≤ x^N
  -- Then 1/N ∈ cutSet_pnat a x since a^1 = a ≤ x^N
  obtain ⟨N, hN⟩ := archimedean_pnat_of_separation a x ha hx
  -- hN : a ≤ iterate_op_pnat x N
  use (1 : ℚ) / N
  simp only [cutSet_pnat, Set.mem_setOf_eq]
  refine ⟨?_, 1, N, ?_, ?_⟩
  · -- 0 ≤ 1/N
    exact div_nonneg (by norm_num) (by exact_mod_cast N.pos.le)
  · -- 1/N = 1/N
    norm_num
  · -- a^1 ≤ x^N
    simp only [iterate_op_pnat_one]
    exact hN

omit [KSSeparationSemigroup α] in
/-- Key lemma: iterate_op_pnat is strictly monotone in base for fixed exponent. -/
theorem iterate_op_pnat_strictMono_base {a b : α} (hab : a < b) (n : ℕ+) :
    iterate_op_pnat a n < iterate_op_pnat b n := by
  induction n using PNat.recOn with
  | one => simp only [iterate_op_pnat_one, hab]
  | succ n ih =>
    rw [iterate_op_pnat_succ, iterate_op_pnat_succ]
    calc op a (iterate_op_pnat a n)
        < op a (iterate_op_pnat b n) := op_strictMono_right a ih
      _ < op b (iterate_op_pnat b n) := op_strictMono_left (iterate_op_pnat b n) hab

omit [KSSeparationSemigroup α] in
/-- Non-strict monotonicity. -/
theorem iterate_op_pnat_mono_base {a b : α} (hab : a ≤ b) (n : ℕ+) :
    iterate_op_pnat a n ≤ iterate_op_pnat b n := by
  rcases hab.lt_or_eq with hlt | heq
  · exact le_of_lt (iterate_op_pnat_strictMono_base hlt n)
  · rw [heq]

omit [KSSeparationSemigroup α] in
/-- Multiplicativity: (x^m)^n = x^(m*n). This follows from pure associativity.
    Key for bounding the cut set. -/
theorem iterate_op_pnat_mul (x : α) (m n : ℕ+) :
    iterate_op_pnat (iterate_op_pnat x m) n = iterate_op_pnat x (m * n) := by
  -- Prove by induction on n
  induction n using PNat.recOn with
  | one =>
    -- (x^m)^1 = x^m = x^(m*1)
    simp only [iterate_op_pnat_one]
    congr 1
    exact (mul_one m).symm
  | succ n ih =>
    -- (x^m)^(n+1) = x^m ⊕ (x^m)^n = x^m ⊕ x^(m*n) = x^(m + m*n) = x^(m*(n+1))
    rw [iterate_op_pnat_succ, ih]
    -- Goal: op (iterate_op_pnat x m) (iterate_op_pnat x (m * n)) = iterate_op_pnat x (m * (n + 1))
    -- Use iterate_op_pnat_add in reverse: x^a ⊕ x^b = x^(a+b)
    rw [← iterate_op_pnat_add]
    congr 1
    -- m + m * n = m * (n + 1)
    have h : m + m * n = m * (n + 1) := by
      apply Subtype.ext
      show (m + m * n).val = (m * (n + 1)).val
      simp only [PNat.add_coe, PNat.mul_coe, PNat.val_ofNat]
      ring
    exact h

omit [KSSeparationSemigroup α] in
/-- Distribution: (x ⊕ y)^n = x^n ⊕ y^n when operation commutes. -/
theorem iterate_op_pnat_distrib (x y : α) (hcomm : ∀ a b : α, op a b = op b a) (n : ℕ+) :
    iterate_op_pnat (op x y) n = op (iterate_op_pnat x n) (iterate_op_pnat y n) := by
  induction n using PNat.recOn with
  | one => simp only [iterate_op_pnat_one]
  | succ n ih =>
    rw [iterate_op_pnat_succ, iterate_op_pnat_succ, iterate_op_pnat_succ, ih]
    -- Goal: op (op x y) (op (iterate_op_pnat x n) (iterate_op_pnat y n))
    --     = op (op x (iterate_op_pnat x n)) (op y (iterate_op_pnat y n))
    -- Use associativity and commutativity
    calc op (op x y) (op (iterate_op_pnat x n) (iterate_op_pnat y n))
        = op x (op y (op (iterate_op_pnat x n) (iterate_op_pnat y n))) := op_assoc x y _
      _ = op x (op (op y (iterate_op_pnat x n)) (iterate_op_pnat y n)) := by rw [op_assoc y _ _]
      _ = op x (op (op (iterate_op_pnat x n) y) (iterate_op_pnat y n)) := by rw [hcomm y (iterate_op_pnat x n)]
      _ = op x (op (iterate_op_pnat x n) (op y (iterate_op_pnat y n))) := by rw [op_assoc (iterate_op_pnat x n) y _]
      _ = op (op x (iterate_op_pnat x n)) (op y (iterate_op_pnat y n)) := by rw [← op_assoc x _ _]

/-- The cut set is bounded above (uses Archimedean property from separation). -/
theorem cutSet_pnat_bddAbove (a x : α) (ha : IsPositive a) (hx : IsPositive x) :
    BddAbove (cutSet_pnat a x) := by
  -- By reverse Archimedean: ∃ K, x < a^K
  -- If q = m/n ∈ cutSet_pnat, then a^m ≤ x^n < (a^K)^n = a^{K*n}
  -- Thus a^m < a^{K*n}, so m < K*n (by strict mono in exponent), hence m/n < K
  obtain ⟨K, hK⟩ := reverse_archimedean_pnat a x ha hx
  -- hK : x < iterate_op_pnat a K
  use (K : ℚ)
  intro q hq
  simp only [cutSet_pnat, Set.mem_setOf_eq] at hq
  obtain ⟨_hq_nonneg, m, n, hq_eq, ham_le⟩ := hq
  subst hq_eq
  -- Goal: m/n ≤ K
  -- Step 1: x^n < (a^K)^n (strict mono in base)
  have hxn_lt : iterate_op_pnat x n < iterate_op_pnat (iterate_op_pnat a K) n :=
    iterate_op_pnat_strictMono_base hK n
  -- Step 2: (a^K)^n = a^{K*n} (multiplicativity)
  rw [iterate_op_pnat_mul] at hxn_lt
  -- hxn_lt : iterate_op_pnat x n < iterate_op_pnat a (K * n)
  -- Step 3: a^m ≤ x^n < a^{K*n}
  have ham_lt : iterate_op_pnat a m < iterate_op_pnat a (K * n) :=
    lt_of_le_of_lt ham_le hxn_lt
  -- Step 4: m < K*n (by strict mono in exponent for positive a)
  have hmKn : m < K * n := by
    by_contra h_not
    push_neg at h_not  -- K * n ≤ m
    have h_mono : iterate_op_pnat a (K * n) ≤ iterate_op_pnat a m :=
      iterate_op_pnat_mono a ha h_not
    exact not_lt.mpr h_mono ham_lt
  -- Step 5: m/n ≤ K (since m < K*n implies m/n < K for positive n)
  have hn_pos : (0 : ℚ) < n := by exact_mod_cast n.pos
  have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_pos
  rw [div_le_iff₀ hn_pos]
  -- Goal: (m : ℚ) ≤ K * n
  have h_le : m ≤ K * n := le_of_lt hmKn
  exact_mod_cast h_le

omit [KSSeparationSemigroup α] in
/-- Closure of cutSet_pnat under addition (for additivity proof). -/
theorem cutSet_pnat_add_closed (a x y : α) (_hcomm : ∀ u v : α, op u v = op v u) :
    ∀ {q₁ q₂ : ℚ}, q₁ ∈ cutSet_pnat a x → q₂ ∈ cutSet_pnat a y →
    q₁ + q₂ ∈ cutSet_pnat a (op x y) := by
  intro q₁ q₂ hq₁ hq₂
  rcases hq₁ with ⟨hq₁_nonneg, m₁, n₁, hq₁_eq, ham₁_le⟩
  rcases hq₂ with ⟨hq₂_nonneg, m₂, n₂, hq₂_eq, ham₂_le⟩
  subst hq₁_eq; subst hq₂_eq

  -- Use common denominator n₁ * n₂
  -- Construct the new numerator as a PNat
  have h_num_pos : 0 < m₁.val * n₂.val + m₂.val * n₁.val := by
    have h1 : 0 < m₁.val * n₂.val := Nat.mul_pos m₁.pos n₂.pos
    have h2 : 0 < m₂.val * n₁.val := Nat.mul_pos m₂.pos n₁.pos
    omega
  refine ⟨add_nonneg hq₁_nonneg hq₂_nonneg,
    ⟨m₁.val * n₂.val + m₂.val * n₁.val, h_num_pos⟩, n₁ * n₂, ?_, ?_⟩
  · -- Arithmetic: m₁/n₁ + m₂/n₂ = (m₁*n₂ + m₂*n₁)/(n₁*n₂)
    simp only [PNat.mul_coe, PNat.mk_coe]
    have hn₁_ne : (n₁ : ℚ) ≠ 0 := by exact_mod_cast n₁.pos.ne'
    have hn₂_ne : (n₂ : ℚ) ≠ 0 := by exact_mod_cast n₂.pos.ne'
    field_simp [hn₁_ne, hn₂_ne]
    -- Goal is polynomial identity in ℚ with Nat casts
    push_cast
    ring
  · -- Power inequality: a^(m₁*n₂ + m₂*n₁) ≤ (x⊕y)^(n₁*n₂)
    -- Step 1: Scale inequalities
    -- From a^m₁ ≤ x^n₁, raise to power n₂: (a^m₁)^n₂ ≤ (x^n₁)^n₂
    -- Using iterate_op_pnat_mul: a^(m₁*n₂) ≤ x^(n₁*n₂)
    have h1 : iterate_op_pnat a (⟨m₁.val * n₂.val, Nat.mul_pos m₁.pos n₂.pos⟩ : ℕ+) ≤
              iterate_op_pnat x (n₁ * n₂) := by
      rw [show (⟨m₁.val * n₂.val, _⟩ : ℕ+) = m₁ * n₂ from rfl]
      rw [← iterate_op_pnat_mul a m₁ n₂, ← iterate_op_pnat_mul x n₁ n₂]
      exact iterate_op_pnat_mono_base ham₁_le n₂
    -- From a^m₂ ≤ y^n₂, raise to power n₁: a^(m₂*n₁) ≤ y^(n₂*n₁) = y^(n₁*n₂)
    have h2 : iterate_op_pnat a (⟨m₂.val * n₁.val, Nat.mul_pos m₂.pos n₁.pos⟩ : ℕ+) ≤
              iterate_op_pnat y (n₂ * n₁) := by
      rw [show (⟨m₂.val * n₁.val, _⟩ : ℕ+) = m₂ * n₁ from rfl]
      rw [← iterate_op_pnat_mul a m₂ n₁, ← iterate_op_pnat_mul y n₂ n₁]
      exact iterate_op_pnat_mono_base ham₂_le n₁
    -- Rewrite n₂ * n₁ = n₁ * n₂
    have h_comm_pnat : n₂ * n₁ = n₁ * n₂ := mul_comm n₂ n₁
    rw [h_comm_pnat] at h2
    -- Step 2: Combine using iterate_op_pnat_add
    -- a^(m₁*n₂) ⊕ a^(m₂*n₁) = a^(m₁*n₂ + m₂*n₁)
    have h_pnat_eq : (⟨m₁.val * n₂.val, Nat.mul_pos m₁.pos n₂.pos⟩ : ℕ+) +
                     (⟨m₂.val * n₁.val, Nat.mul_pos m₂.pos n₁.pos⟩ : ℕ+) =
                     (⟨m₁.val * n₂.val + m₂.val * n₁.val, h_num_pos⟩ : ℕ+) := Subtype.ext rfl
    have h_add_lhs : iterate_op_pnat a (⟨m₁.val * n₂.val + m₂.val * n₁.val, h_num_pos⟩ : ℕ+) =
                     op (iterate_op_pnat a (⟨m₁.val * n₂.val, Nat.mul_pos m₁.pos n₂.pos⟩ : ℕ+))
                        (iterate_op_pnat a (⟨m₂.val * n₁.val, Nat.mul_pos m₂.pos n₁.pos⟩ : ℕ+)) := by
      rw [← iterate_op_pnat_add, h_pnat_eq]
    -- Step 3: x^(n₁*n₂) ⊕ y^(n₁*n₂) = (x⊕y)^(n₁*n₂) (distribution with commutativity)
    have h_distrib : iterate_op_pnat (op x y) (n₁ * n₂) =
                     op (iterate_op_pnat x (n₁ * n₂)) (iterate_op_pnat y (n₁ * n₂)) := by
      rw [iterate_op_pnat_distrib]
      exact _hcomm
    -- Step 4: Combine: show op (a^(m₁*n₂)) (a^(m₂*n₁)) ≤ (x⊕y)^(n₁*n₂)
    rw [h_add_lhs, h_distrib]
    -- Goal: op (a^(m₁*n₂)) (a^(m₂*n₁)) ≤ op (x^(n₁*n₂)) (y^(n₁*n₂))
    -- This follows from h1, h2 and op being monotone in both arguments
    -- Use: op is monotone in each argument (from strict mono)
    calc op (iterate_op_pnat a ⟨m₁.val * n₂.val, Nat.mul_pos m₁.pos n₂.pos⟩)
               (iterate_op_pnat a ⟨m₂.val * n₁.val, Nat.mul_pos m₂.pos n₁.pos⟩)
        ≤ op (iterate_op_pnat x (n₁ * n₂))
              (iterate_op_pnat a ⟨m₂.val * n₁.val, Nat.mul_pos m₂.pos n₁.pos⟩) :=
          (op_strictMono_left _).monotone h1
      _ ≤ op (iterate_op_pnat x (n₁ * n₂)) (iterate_op_pnat y (n₁ * n₂)) :=
          (op_strictMono_right _).monotone h2

/-- Definition of Θ via supremum of cut set (identity-free).
    The `IsPositive` hypotheses ensure the cut set is nonempty and bounded above. -/
noncomputable def Θ_cuts_pnat (a : α) (_ha : IsPositive a) (x : α) (_hx : IsPositive x) : ℝ :=
  sSup ((↑) '' cutSet_pnat a x : Set ℝ)

/-- Θ_cuts_pnat is monotone: x ≤ y → Θ(x) ≤ Θ(y). -/
theorem Θ_cuts_pnat_mono (a : α) (ha : IsPositive a)
    {x y : α} (hx : IsPositive x) (hy : IsPositive y) (hxy : x ≤ y) :
    Θ_cuts_pnat a ha x hx ≤ Θ_cuts_pnat a ha y hy := by
  simp only [Θ_cuts_pnat]
  -- cutSet_pnat a x ⊆ cutSet_pnat a y
  apply csSup_le_csSup
  · -- cutSet_pnat a y is bounded
    have hbdd := cutSet_pnat_bddAbove a y ha hy
    obtain ⟨B, hB⟩ := hbdd
    use B
    intro r hr
    simp only [Set.mem_image] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact Rat.cast_le.mpr (hB hq)
  · -- cutSet_pnat a x is nonempty
    have hne := cutSet_pnat_nonempty a x ha hx
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, Set.mem_image_of_mem _ hq⟩
  · -- Inclusion
    intro r hr
    simp only [Set.mem_image] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    simp only [Set.mem_image]
    refine ⟨q, ?_, rfl⟩
    simp only [cutSet_pnat, Set.mem_setOf_eq] at hq ⊢
    obtain ⟨hq_nonneg, m, n, hq_eq, ham_le⟩ := hq
    exact ⟨hq_nonneg, m, n, hq_eq, le_trans ham_le (iterate_op_pnat_mono_base hxy n)⟩

/-!
### Identity-Free Cuts: Full Representation

The complete identity-free cuts path producing `RepresentationResult`.
All proofs use only `IsPositive`, `iterate_op_pnat`, and `KSSeparationSemigroup`.
-/

omit [KSSeparationSemigroup α] in
/-- Key lemma: if `iterate_op_pnat x m₀ < iterate_op_pnat a n₀`, then all rationals
    in `cutSet_pnat a x` are strictly less than `n₀/m₀`.

This is the identity-free version of `cutSet_lt_of_pow'_lt`. -/
theorem cutSet_pnat_lt_of_iterate_lt (a : α) (ha : IsPositive a) {x : α} {m₀ n₀ : ℕ+}
    (h_lt : iterate_op_pnat x m₀ < iterate_op_pnat a n₀) :
    ∀ q ∈ cutSet_pnat a x, (q : ℝ) < (n₀ : ℝ) / (m₀ : ℝ) := by
  intro q hq
  simp only [cutSet_pnat, Set.mem_setOf_eq] at hq
  obtain ⟨_hq_nonneg, m, n, hq_eq, ham_le⟩ := hq
  subst hq_eq
  -- We have: a^m ≤ x^n and x^m₀ < a^n₀
  -- Need to show: m/n < n₀/m₀, i.e., m * m₀ < n₀ * n

  have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hm₀_pos' : 0 < (m₀ : ℝ) := by exact_mod_cast m₀.pos

  -- Scale `a^m ≤ x^n` by m₀: `a^(m*m₀) ≤ x^(n*m₀)`
  have ham_le' : iterate_op_pnat a (m * m₀) ≤ iterate_op_pnat x (n * m₀) := by
    have := iterate_op_pnat_mono_base ham_le m₀
    rwa [iterate_op_pnat_mul, iterate_op_pnat_mul] at this

  -- Scale `x^m₀ < a^n₀` by n: `x^(m₀*n) < a^(n₀*n)`
  have hx_lt' : iterate_op_pnat x (m₀ * n) < iterate_op_pnat a (n₀ * n) := by
    have := iterate_op_pnat_strictMono_base h_lt n
    rwa [iterate_op_pnat_mul, iterate_op_pnat_mul] at this

  -- Combine: `a^(m*m₀) ≤ x^(n*m₀) = x^(m₀*n) < a^(n₀*n)`
  have h_between : iterate_op_pnat a (m * m₀) < iterate_op_pnat a (n₀ * n) := by
    have heq : n * m₀ = m₀ * n := mul_comm n m₀
    calc iterate_op_pnat a (m * m₀)
        ≤ iterate_op_pnat x (n * m₀) := ham_le'
      _ = iterate_op_pnat x (m₀ * n) := by rw [heq]
      _ < iterate_op_pnat a (n₀ * n) := hx_lt'

  -- From `a^(m*m₀) < a^(n₀*n)`, strict monotonicity gives `m*m₀ < n₀*n`
  have h_exp_lt : m * m₀ < n₀ * n := (iterate_op_pnat_strictMono a ha).lt_iff_lt.mp h_between

  -- Convert to real inequality: m/n < n₀/m₀
  have h_exp_lt' : (m : ℝ) * (m₀ : ℝ) < (n₀ : ℝ) * (n : ℝ) := by
    have : ((m * m₀ : ℕ+) : ℝ) < ((n₀ * n : ℕ+) : ℝ) := by exact_mod_cast h_exp_lt
    simp only [PNat.mul_coe, Nat.cast_mul] at this
    exact this

  -- m/n < n₀/m₀ iff m * m₀ < n₀ * n (when denominators positive)
  -- Goal: ↑(↑↑m / ↑↑n : ℚ) < (n₀ : ℝ) / (m₀ : ℝ)
  -- Rat.cast_div: ↑(p/q) = (↑p)/(↑q) for ℚ→ℝ
  -- Rat.cast_natCast: ↑(n : ℚ) = (n : ℝ) for ℕ→ℝ via ℚ
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [div_lt_div_iff₀ hn_pos' hm₀_pos']
  exact h_exp_lt'

/-- **Strict monotonicity** of identity-free Θ: x < y → Θ(x) < Θ(y).

This is the key property needed for order-preservation.
Requires `KSSeparationSemigroupStrict` for the strict upper bound. -/
theorem Θ_cuts_pnat_strictMono [KSSeparationSemigroupStrict α] (a : α) (ha : IsPositive a)
    {x y : α} (hx : IsPositive x) (hy : IsPositive y) (hxy : x < y) :
    Θ_cuts_pnat a ha x hx < Θ_cuts_pnat a ha y hy := by
  classical
  -- Apply STRICT separation with base a on (x, y)
  obtain ⟨n₀, m₀, hlt_iter, hgt_iter⟩ := KSSeparationSemigroupStrict.sep_strict ha hx hy hxy
  -- hlt_iter: iterate_op_pnat x m₀ < iterate_op_pnat a n₀
  -- hgt_iter: iterate_op_pnat a n₀ < iterate_op_pnat y m₀ (STRICT!)

  -- The witness rational q₀ = n₀/m₀ lies in cutSet_pnat a y (with non-strict bound)
  have hq₀_mem : ((n₀ : ℚ) / m₀) ∈ cutSet_pnat a y := by
    simp only [cutSet_pnat, Set.mem_setOf_eq]
    refine ⟨?_, n₀, m₀, ?_, ?_⟩
    · exact div_nonneg (by exact_mod_cast n₀.pos.le) (by exact_mod_cast m₀.pos.le)
    · rfl
    · exact le_of_lt hgt_iter  -- a^n₀ < y^m₀ implies a^n₀ ≤ y^m₀

  -- q₀ ≤ Θ(y)
  have hq₀_le : ((n₀ : ℚ) / m₀ : ℝ) ≤ Θ_cuts_pnat a ha y hy := by
    simp only [Θ_cuts_pnat]
    have hbdd := cutSet_pnat_bddAbove a y ha hy
    obtain ⟨B, hB⟩ := hbdd
    have hbdd' : BddAbove ((↑) '' cutSet_pnat a y : Set ℝ) := by
      refine ⟨(B : ℝ), ?_⟩
      intro r hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact Rat.cast_le.mpr (hB hq)
    have hmem : (((n₀ : ℚ) / m₀) : ℝ) ∈ ((↑) '' cutSet_pnat a y : Set ℝ) := by
      refine ⟨(n₀ : ℚ) / m₀, hq₀_mem, ?_⟩
      simp only [Rat.cast_div, Rat.cast_natCast]
    exact le_csSup hbdd' hmem

  -- Apply STRICT separation again to (x^m₀, a^n₀) with base a
  have hx_m₀_pos : IsPositive (iterate_op_pnat x m₀) := iterate_op_pnat_pos x hx m₀
  have ha_n₀_pos : IsPositive (iterate_op_pnat a n₀) := iterate_op_pnat_pos a ha n₀

  obtain ⟨n₁, k, hlt₁_iter, hgt₁_iter⟩ :=
    KSSeparationSemigroupStrict.sep_strict ha hx_m₀_pos ha_n₀_pos hlt_iter
  -- hlt₁_iter: (x^m₀)^k < a^n₁
  -- hgt₁_iter: a^n₁ < (a^n₀)^k (STRICT!)

  have hlt₁ : iterate_op_pnat x (m₀ * k) < iterate_op_pnat a n₁ := by
    have : iterate_op_pnat (iterate_op_pnat x m₀) k < iterate_op_pnat a n₁ := hlt₁_iter
    rwa [iterate_op_pnat_mul] at this

  -- From a^n₁ < (a^n₀)^k = a^(n₀*k), we get n₁ < n₀*k by strict mono
  have h_n₁_lt : n₁ < n₀ * k := by
    have hgt₁' : iterate_op_pnat a n₁ < iterate_op_pnat a (n₀ * k) := by
      have : iterate_op_pnat a n₁ < iterate_op_pnat (iterate_op_pnat a n₀) k := hgt₁_iter
      rwa [iterate_op_pnat_mul] at this
    exact (iterate_op_pnat_strictMono a ha).lt_iff_lt.mp hgt₁'

  -- Θ(x) is bounded above by n₁/(m₀*k)
  have hΘx_le : Θ_cuts_pnat a ha x hx ≤ (n₁ : ℝ) / ((m₀ * k : ℕ+) : ℝ) := by
    simp only [Θ_cuts_pnat]
    have hne := cutSet_pnat_nonempty a x ha hx
    have hne' : ((↑) '' cutSet_pnat a x : Set ℝ).Nonempty := Set.image_nonempty.mpr hne
    refine csSup_le hne' ?_
    intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    have h_lt := cutSet_pnat_lt_of_iterate_lt a ha hlt₁ q hq
    exact le_of_lt h_lt

  -- n₁/(m₀*k) < n₀/m₀ because n₁ < n₀*k
  have hlt_rat : (n₁ : ℝ) / ((m₀ * k : ℕ+) : ℝ) < (n₀ : ℝ) / (m₀ : ℝ) := by
    have h_n₁_lt' : (n₁ : ℝ) < (n₀ : ℝ) * (k : ℝ) := by
      have : ((n₁ : ℕ+) : ℝ) < ((n₀ * k : ℕ+) : ℝ) := by exact_mod_cast h_n₁_lt
      simp only [PNat.mul_coe, Nat.cast_mul] at this
      exact this
    have hm₀k_pos : 0 < ((m₀ * k : ℕ+) : ℝ) := by exact_mod_cast (m₀ * k).pos
    have hm₀_pos : 0 < (m₀ : ℝ) := by exact_mod_cast m₀.pos
    rw [div_lt_div_iff₀ hm₀k_pos hm₀_pos]
    have hk' : ((m₀ * k : ℕ+) : ℝ) = (m₀ : ℝ) * (k : ℝ) := by simp only [PNat.mul_coe, Nat.cast_mul]
    calc (n₁ : ℝ) * (m₀ : ℝ)
        < ((n₀ : ℝ) * (k : ℝ)) * (m₀ : ℝ) := by nlinarith [h_n₁_lt']
      _ = (n₀ : ℝ) * ((m₀ : ℝ) * (k : ℝ)) := by ring
      _ = (n₀ : ℝ) * ((m₀ * k : ℕ+) : ℝ) := by rw [← hk']

  -- Combine: Θ(x) ≤ n₁/(m₀*k) < n₀/m₀ ≤ Θ(y)
  have hq₀_eq : ((n₀ : ℚ) / m₀ : ℝ) = (n₀ : ℝ) / (m₀ : ℝ) := by
    simp only [Rat.cast_natCast]
  calc Θ_cuts_pnat a ha x hx
      ≤ (n₁ : ℝ) / ((m₀ * k : ℕ+) : ℝ) := hΘx_le
    _ < (n₀ : ℝ) / (m₀ : ℝ) := hlt_rat
    _ = ((n₀ : ℚ) / m₀ : ℝ) := hq₀_eq.symm
    _ ≤ Θ_cuts_pnat a ha y hy := hq₀_le

omit [KSSeparationSemigroup α] in
/-- Positivity is preserved under `op` for positive elements. -/
theorem isPositive_op' {x y : α} (hx : IsPositive x) (hy : IsPositive y) : IsPositive (op x y) := by
  intro z
  have h1 : z < op x z := hx z
  have h2 : z < op y z := hy z
  have h3 : op x z < op x (op y z) := op_strictMono_right x h2
  have h4 : op x (op y z) = op (op x y) z := (op_assoc x y z).symm
  calc z < op x z := h1
    _ < op x (op y z) := h3
    _ = op (op x y) z := h4

/-- **Additivity** of identity-free Θ: Θ(x⊕y) = Θ(x) + Θ(y).

This follows the same proof structure as the identity-based `Θ_cuts_add`:
1. First inequality (≥): Uses `cutSet_pnat_add_closed` and `csSup_add`
2. Second inequality (≤): By contradiction using rational splitting

Requires commutativity for `cutSet_pnat_add_closed`. -/
theorem Θ_cuts_pnat_add (a : α) (ha : IsPositive a)
    (hcomm : ∀ u v : α, op u v = op v u)
    (x y : α) (hx : IsPositive x) (hy : IsPositive y) :
    Θ_cuts_pnat a ha (op x y) (isPositive_op' hx hy) =
      Θ_cuts_pnat a ha x hx + Θ_cuts_pnat a ha y hy := by
  classical
  have hxy : IsPositive (op x y) := isPositive_op' hx hy

  -- Work with the real images of the cut-sets
  let s : Set ℝ := (↑) '' cutSet_pnat a x
  let t : Set ℝ := (↑) '' cutSet_pnat a y
  let u : Set ℝ := (↑) '' cutSet_pnat a (op x y)

  have hs0 : s.Nonempty := Set.image_nonempty.mpr (cutSet_pnat_nonempty a x ha hx)
  have ht0 : t.Nonempty := Set.image_nonempty.mpr (cutSet_pnat_nonempty a y ha hy)
  have hu0 : u.Nonempty := Set.image_nonempty.mpr (cutSet_pnat_nonempty a (op x y) ha hxy)

  have hs1 : BddAbove s := by
    obtain ⟨B, hB⟩ := cutSet_pnat_bddAbove a x ha hx
    refine ⟨(B : ℝ), ?_⟩
    intro r hr; obtain ⟨q, hq, rfl⟩ := hr
    exact Rat.cast_le.mpr (hB hq)
  have ht1 : BddAbove t := by
    obtain ⟨B, hB⟩ := cutSet_pnat_bddAbove a y ha hy
    refine ⟨(B : ℝ), ?_⟩
    intro r hr; obtain ⟨q, hq, rfl⟩ := hr
    exact Rat.cast_le.mpr (hB hq)
  have hu1 : BddAbove u := by
    obtain ⟨B, hB⟩ := cutSet_pnat_bddAbove a (op x y) ha hxy
    refine ⟨(B : ℝ), ?_⟩
    intro r hr; obtain ⟨q, hq, rfl⟩ := hr
    exact Rat.cast_le.mpr (hB hq)

  -- Inclusion: s + t ⊆ u
  have hsubset : s + t ⊆ u := by
    intro r hr
    rcases Set.mem_add.1 hr with ⟨r₁, hr₁, r₂, hr₂, rfl⟩
    rcases hr₁ with ⟨q₁, hq₁, rfl⟩
    rcases hr₂ with ⟨q₂, hq₂, rfl⟩
    refine ⟨q₁ + q₂, cutSet_pnat_add_closed a x y hcomm hq₁ hq₂, ?_⟩
    simp only [Rat.cast_add]

  -- First inequality: Θ(x) + Θ(y) ≤ Θ(x⊕y)
  have h_le1 : sSup s + sSup t ≤ sSup u := by
    have h_sup_sum : sSup (s + t) ≤ sSup u := csSup_le_csSup hu1 (hs0.add ht0) hsubset
    have h_add : sSup (s + t) = sSup s + sSup t := csSup_add hs0 hs1 ht0 ht1
    exact h_add ▸ h_sup_sum

  -- Second inequality: Θ(x⊕y) ≤ Θ(x) + Θ(y)
  -- By showing that every q ∈ cutSet_pnat a (op x y) satisfies q ≤ Θ(x) + Θ(y)
  have h_le2 : sSup u ≤ sSup s + sSup t := by
    refine csSup_le hu0 ?_
    intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    -- If `q` is at most the sum of sups, we're done
    by_contra h_not_le
    have h_gt : sSup s + sSup t < (q : ℝ) := lt_of_not_ge h_not_le

    -- Unpack the witness for `q ∈ cutSet_pnat(a, x⊕y)`
    obtain ⟨hq_nonneg, m, n, hq_eq, ham_le⟩ := hq

    -- Nonnegativity of Θ values: sSup s ≥ 0 and sSup t ≥ 0
    -- This follows because cutSet_pnat only contains nonnegative rationals
    have hΘx_nonneg : (0 : ℝ) ≤ sSup s := by
      obtain ⟨qx, hqx⟩ := cutSet_pnat_nonempty a x ha hx
      have hqx_nonneg := hqx.1
      have hqx_mem : (qx : ℝ) ∈ s := ⟨qx, hqx, rfl⟩
      have hqx_le : (qx : ℝ) ≤ sSup s := le_csSup hs1 hqx_mem
      exact le_trans (Rat.cast_nonneg.mpr hqx_nonneg) hqx_le
    have hΘy_nonneg : (0 : ℝ) ≤ sSup t := by
      obtain ⟨qy, hqy⟩ := cutSet_pnat_nonempty a y ha hy
      have hqy_nonneg := hqy.1
      have hqy_mem : (qy : ℝ) ∈ t := ⟨qy, hqy, rfl⟩
      have hqy_le : (qy : ℝ) ≤ sSup t := le_csSup ht1 hqy_mem
      exact le_trans (Rat.cast_nonneg.mpr hqy_nonneg) hqy_le

    -- Between Θ(x) and q - Θ(y), pick a rational q₁
    have h_between : sSup s < (q : ℝ) - sSup t := by linarith
    obtain ⟨q₁, hq₁_gt, hq₁_lt⟩ := exists_rat_btwn h_between
    let q₂ : ℚ := q - q₁

    have hq₂_gt : sSup t < (q₂ : ℝ) := by
      have : sSup t < (q : ℝ) - (q₁ : ℝ) := by linarith [hq₁_lt]
      have hcast : ((q - q₁ : ℚ) : ℝ) = (q : ℝ) - (q₁ : ℝ) := by simp [sub_eq_add_neg]
      simpa [q₂, hcast] using this

    -- Nonnegativity of q₁ and q₂
    have hq₁_nonneg : (0 : ℚ) ≤ q₁ := by
      have h0 : (0 : ℝ) ≤ (q₁ : ℝ) := le_trans hΘx_nonneg (le_of_lt hq₁_gt)
      exact Rat.cast_nonneg.mp h0
    have hq₂_nonneg : (0 : ℚ) ≤ q₂ := by
      have h0 : (0 : ℝ) ≤ (q₂ : ℝ) := le_trans hΘy_nonneg (le_of_lt hq₂_gt)
      exact Rat.cast_nonneg.mp h0

    -- Since q₁ > Θ(x), it cannot lie in the cut-set for x; similarly for q₂ and y
    have hq₁_not : q₁ ∉ cutSet_pnat a x := by
      intro hq₁_mem
      have hq₁_mem' : (q₁ : ℝ) ∈ s := ⟨q₁, hq₁_mem, rfl⟩
      have : (q₁ : ℝ) ≤ sSup s := le_csSup hs1 hq₁_mem'
      exact not_lt_of_ge this hq₁_gt

    have hq₂_not : q₂ ∉ cutSet_pnat a y := by
      intro hq₂_mem
      have hq₂_mem' : (q₂ : ℝ) ∈ t := ⟨q₂, hq₂_mem, rfl⟩
      have : (q₂ : ℝ) ≤ sSup t := le_csSup ht1 hq₂_mem'
      exact not_lt_of_ge this hq₂_gt

    -- Convert q₁ and q₂ to canonical ℕ+/ℕ+ representations
    -- Using the fact that positive rationals can be written as m/n with m, n : ℕ+
    -- But q₁ and q₂ could be 0. We handle this by using numerator/denominator
    -- For q₁ = num₁/den₁ where den₁ > 0 and num₁ ≥ 0

    -- Handle edge case: if q₁ = 0 or q₂ = 0, use specialized argument
    by_cases hq₁_pos : 0 < q₁
    case neg =>
      -- q₁ = 0, so q₂ = q which should be in cutSet(a, y) if q ∈ cutSet(a, x⊕y)
      -- But q₂ > Θ(y), contradiction
      have hq₁_zero : q₁ = 0 := le_antisymm (not_lt.mp hq₁_pos) hq₁_nonneg
      have hq₂_eq_q : q₂ = q := by simp [q₂, hq₁_zero]
      -- We need: if a^m ≤ (x⊕y)^n and q₁ = 0, then q = q₂ is bounded by something related to y
      -- This is actually complex. The standard approach uses q₁, q₂ > 0.
      -- For now, derive contradiction from hq₁_gt: 0 = q₁ > sSup s ≥ some positive
      -- But sSup s could be 0 if cutSet_pnat is empty except for very small elements
      -- Actually, cutSet_pnat_nonempty gives us a positive element, so sSup s > 0
      obtain ⟨qx, hqx_mem⟩ := cutSet_pnat_nonempty a x ha hx
      have hqx_pos : 0 < qx := by
        obtain ⟨_, mx, nx, hqx_eq, _⟩ := hqx_mem
        rw [hqx_eq]
        exact div_pos (by positivity : (0 : ℚ) < mx) (by positivity : (0 : ℚ) < nx)
      have hqx_le_sup : (qx : ℝ) ≤ sSup s := le_csSup hs1 ⟨qx, hqx_mem, rfl⟩
      have hq₁_gt' : (0 : ℝ) = (q₁ : ℝ) := by simp [hq₁_zero]
      have hqx_pos_real : (0 : ℝ) < (qx : ℝ) := by exact_mod_cast hqx_pos
      linarith
    case pos =>
      -- q₁ > 0
      by_cases hq₂_pos : 0 < q₂
      case neg =>
        -- q₂ = 0, similar argument
        have hq₂_zero : q₂ = 0 := le_antisymm (not_lt.mp hq₂_pos) hq₂_nonneg
        obtain ⟨qy, hqy_mem⟩ := cutSet_pnat_nonempty a y ha hy
        have hqy_pos : 0 < qy := by
          obtain ⟨_, my, ny, hqy_eq, _⟩ := hqy_mem
          rw [hqy_eq]
          exact div_pos (by positivity : (0 : ℚ) < my) (by positivity : (0 : ℚ) < ny)
        have hqy_le_sup : (qy : ℝ) ≤ sSup t := le_csSup ht1 ⟨qy, hqy_mem, rfl⟩
        have hq₂_gt' : (0 : ℝ) = (q₂ : ℝ) := by simp [hq₂_zero]
        have hqy_pos_real : (0 : ℝ) < (qy : ℝ) := by exact_mod_cast hqy_pos
        linarith
      case pos =>
        -- Both q₁ > 0 and q₂ > 0

        -- Convert to ℕ+/ℕ+ form using numerator/denominator
        have h_num₁_pos : 0 < q₁.num := Rat.num_pos.mpr hq₁_pos
        have h_num₁_nonneg : 0 ≤ q₁.num := le_of_lt h_num₁_pos
        have h_num₁_toNat_pos : 0 < q₁.num.toNat := by
          have h_ne : q₁.num.toNat ≠ 0 := by
            intro h_eq
            have h_cast : (q₁.num.toNat : ℤ) = q₁.num := Int.toNat_of_nonneg h_num₁_nonneg
            have : q₁.num = 0 := by omega
            exact (ne_of_gt h_num₁_pos) this
          exact Nat.pos_of_ne_zero h_ne
        let m₁ : ℕ+ := ⟨q₁.num.toNat, h_num₁_toNat_pos⟩
        let n₁ : ℕ+ := ⟨q₁.den, q₁.den_pos⟩
        have h_eqZ₁ : (q₁.num.toNat : ℤ) = q₁.num := Int.toNat_of_nonneg h_num₁_nonneg
        have hq₁_eq : q₁ = (m₁ : ℚ) / n₁ := by
          have h_orig : q₁ = q₁.num / q₁.den := (Rat.num_div_den q₁).symm
          rw [h_orig]
          congr 1
          exact_mod_cast h_eqZ₁.symm

        have h_num₂_pos : 0 < q₂.num := Rat.num_pos.mpr hq₂_pos
        have h_num₂_nonneg : 0 ≤ q₂.num := le_of_lt h_num₂_pos
        have h_num₂_toNat_pos : 0 < q₂.num.toNat := by
          have h_ne : q₂.num.toNat ≠ 0 := by
            intro h_eq
            have h_cast : (q₂.num.toNat : ℤ) = q₂.num := Int.toNat_of_nonneg h_num₂_nonneg
            have : q₂.num = 0 := by omega
            exact (ne_of_gt h_num₂_pos) this
          exact Nat.pos_of_ne_zero h_ne
        let m₂ : ℕ+ := ⟨q₂.num.toNat, h_num₂_toNat_pos⟩
        let n₂ : ℕ+ := ⟨q₂.den, q₂.den_pos⟩
        have h_eqZ₂ : (q₂.num.toNat : ℤ) = q₂.num := Int.toNat_of_nonneg h_num₂_nonneg
        have hq₂_eq : q₂ = (m₂ : ℚ) / n₂ := by
          have h_orig : q₂ = q₂.num / q₂.den := (Rat.num_div_den q₂).symm
          rw [h_orig]
          congr 1
          exact_mod_cast h_eqZ₂.symm

        -- From non-membership, get strict inequalities:
        -- q₁ ∉ cutSet_pnat a x means ¬(a^m₁ ≤ x^n₁), i.e., x^n₁ < a^m₁
        have hx_strict : iterate_op_pnat x n₁ < iterate_op_pnat a m₁ := by
          have h_not_le : ¬ (iterate_op_pnat a m₁ ≤ iterate_op_pnat x n₁) := by
            intro hle
            have hq₁_in : q₁ ∈ cutSet_pnat a x := ⟨hq₁_nonneg, m₁, n₁, hq₁_eq, hle⟩
            exact hq₁_not hq₁_in
          exact lt_of_not_ge h_not_le

        have hy_strict : iterate_op_pnat y n₂ < iterate_op_pnat a m₂ := by
          have h_not_le : ¬ (iterate_op_pnat a m₂ ≤ iterate_op_pnat y n₂) := by
            intro hle
            have hq₂_in : q₂ ∈ cutSet_pnat a y := ⟨hq₂_nonneg, m₂, n₂, hq₂_eq, hle⟩
            exact hq₂_not hq₂_in
          exact lt_of_not_ge h_not_le

        -- Scale to common denominator n₁ * n₂
        have hx_scaled : iterate_op_pnat x (n₁ * n₂) < iterate_op_pnat a (m₁ * n₂) := by
          have := iterate_op_pnat_strictMono_base hx_strict n₂
          rwa [iterate_op_pnat_mul, iterate_op_pnat_mul] at this

        have hy_scaled : iterate_op_pnat y (n₁ * n₂) < iterate_op_pnat a (m₂ * n₁) := by
          have := iterate_op_pnat_strictMono_base hy_strict n₁
          rw [iterate_op_pnat_mul, iterate_op_pnat_mul] at this
          have h_comm : n₂ * n₁ = n₁ * n₂ := mul_comm n₂ n₁
          simp only [h_comm] at this
          exact this

        -- Use distributivity: (x⊕y)^(n₁*n₂) = x^(n₁*n₂) ⊕ y^(n₁*n₂)
        have h_distrib_xy : iterate_op_pnat (op x y) (n₁ * n₂) =
            op (iterate_op_pnat x (n₁ * n₂)) (iterate_op_pnat y (n₁ * n₂)) :=
          iterate_op_pnat_distrib x y hcomm (n₁ * n₂)

        -- Combine: (x⊕y)^(n₁*n₂) < a^(m₁*n₂ + m₂*n₁)
        have h_sum_lt : iterate_op_pnat (op x y) (n₁ * n₂) <
            iterate_op_pnat a (m₁ * n₂ + m₂ * n₁) := by
          have h_rhs : op (iterate_op_pnat a (m₁ * n₂)) (iterate_op_pnat a (m₂ * n₁)) =
              iterate_op_pnat a (m₁ * n₂ + m₂ * n₁) := (iterate_op_pnat_add a (m₁ * n₂) (m₂ * n₁)).symm
          have h1 : op (iterate_op_pnat x (n₁ * n₂)) (iterate_op_pnat y (n₁ * n₂)) <
              op (iterate_op_pnat a (m₁ * n₂)) (iterate_op_pnat y (n₁ * n₂)) :=
            op_strictMono_left (iterate_op_pnat y (n₁ * n₂)) hx_scaled
          have h2 : op (iterate_op_pnat a (m₁ * n₂)) (iterate_op_pnat y (n₁ * n₂)) <
              op (iterate_op_pnat a (m₁ * n₂)) (iterate_op_pnat a (m₂ * n₁)) :=
            op_strictMono_right (iterate_op_pnat a (m₁ * n₂)) hy_scaled
          rw [h_distrib_xy, ← h_rhs]
          exact lt_trans h1 h2

        -- From membership: a^m ≤ (x⊕y)^n, scale by (n₁*n₂)
        have ham_scale : iterate_op_pnat a (m * (n₁ * n₂)) ≤
            iterate_op_pnat (op x y) (n * (n₁ * n₂)) := by
          have := iterate_op_pnat_mono_base ham_le (n₁ * n₂)
          rwa [iterate_op_pnat_mul, iterate_op_pnat_mul] at this

        -- Scale h_sum_lt by n
        have hlt_scale : iterate_op_pnat (op x y) ((n₁ * n₂) * n) <
            iterate_op_pnat a ((m₁ * n₂ + m₂ * n₁) * n) := by
          have := iterate_op_pnat_strictMono_base h_sum_lt n
          rwa [iterate_op_pnat_mul, iterate_op_pnat_mul] at this

        -- Rational equality: q = q₁ + q₂ = (m₁*n₂ + m₂*n₁)/(n₁*n₂)
        have hq_as_sum : q = q₁ + q₂ := by simp [q₂]
        have hq_as_frac : q = ((m₁ : ℕ) * n₂ + (m₂ : ℕ) * n₁ : ℕ) / ((n₁ : ℕ) * n₂ : ℕ) := by
          have hn₁_ne : (n₁ : ℚ) ≠ 0 := by positivity
          have hn₂_ne : (n₂ : ℚ) ≠ 0 := by positivity
          calc q = q₁ + q₂ := hq_as_sum
            _ = (m₁ : ℚ) / n₁ + (m₂ : ℚ) / n₂ := by rw [hq₁_eq, hq₂_eq]
            _ = ((m₁ : ℕ) * n₂ + (m₂ : ℕ) * n₁ : ℕ) / ((n₁ : ℕ) * n₂ : ℕ) := by
                  field_simp
                  push_cast
                  ring

        -- Cross-multiply to get the integer equality
        have hq_mn : (m : ℚ) / n = q := by simp only [hq_eq]
        have hn_ne : (n : ℚ) ≠ 0 := by positivity
        have hn' : 0 < (n₁ : ℕ) * n₂ := Nat.mul_pos n₁.pos n₂.pos
        have hn'_ne : (((n₁ : ℕ) * n₂ : ℕ) : ℚ) ≠ 0 := by positivity

        have h_cross : (m : ℕ) * ((n₁ : ℕ) * n₂) = ((m₁ : ℕ) * n₂ + (m₂ : ℕ) * n₁) * n := by
          have h_div : (m : ℚ) / n = (((m₁ : ℕ) * n₂ + (m₂ : ℕ) * n₁ : ℕ) : ℚ) / ((n₁ : ℕ) * n₂ : ℕ) := by
            calc (m : ℚ) / n = q := hq_mn
              _ = ((m₁ : ℕ) * n₂ + (m₂ : ℕ) * n₁ : ℕ) / ((n₁ : ℕ) * n₂ : ℕ) := hq_as_frac
          have h' : (m : ℚ) * (((n₁ : ℕ) * n₂ : ℕ) : ℚ) =
              (((m₁ : ℕ) * n₂ + (m₂ : ℕ) * n₁ : ℕ) : ℚ) * (n : ℚ) := by
            have := (div_eq_div_iff hn_ne hn'_ne).1 h_div
            linarith [this]
          exact_mod_cast h'

        -- Use h_cross to align exponents and derive contradiction
        -- ham_scale: a^(m*(n₁*n₂)) ≤ (x⊕y)^(n*(n₁*n₂))
        -- hlt_scale: (x⊕y)^((n₁*n₂)*n) < a^((m₁*n₂+m₂*n₁)*n)
        -- h_cross: m * (n₁*n₂) = (m₁*n₂+m₂*n₁) * n

        -- Rewrite ham_scale using h_cross
        have h_mul_comm_n : (n : ℕ) * ((n₁ : ℕ) * n₂) = ((n₁ : ℕ) * n₂) * n := mul_comm _ _

        -- The key is showing that the exponents match up
        -- m * (n₁*n₂) = (m₁*n₂+m₂*n₁) * n  (from h_cross)
        -- n * (n₁*n₂) = (n₁*n₂) * n        (by commutativity)

        -- Convert everything to ℕ+ exponents for the final contradiction
        -- Show the contradiction
        -- From ham_scale: a^(m*(n₁*n₂)) ≤ (x⊕y)^(n*(n₁*n₂))
        -- This becomes (using h_cross): a^((m₁*n₂+m₂*n₁)*n) ≤ (x⊕y)^((n₁*n₂)*n)
        have ham_scale_aligned : iterate_op_pnat a ((m₁ * n₂ + m₂ * n₁) * n) ≤
            iterate_op_pnat (op x y) ((n₁ * n₂) * n) := by
          have key1 : (m * (n₁ * n₂) : ℕ+) = (m₁ * n₂ + m₂ * n₁) * n := by
            apply Subtype.ext
            show (m : ℕ) * ((n₁ : ℕ) * n₂) = ((m₁ : ℕ) * n₂ + (m₂ : ℕ) * n₁) * n
            exact h_cross
          have key2 : (n * (n₁ * n₂) : ℕ+) = (n₁ * n₂) * n := by
            apply Subtype.ext
            show (n : ℕ) * ((n₁ : ℕ) * n₂) = ((n₁ : ℕ) * n₂) * n
            exact h_mul_comm_n
          rw [← key1, ← key2]
          exact ham_scale

        -- hlt_scale already says: (x⊕y)^((n₁*n₂)*n) < a^((m₁*n₂+m₂*n₁)*n)
        exact not_lt_of_ge ham_scale_aligned hlt_scale

  exact le_antisymm h_le2 h_le1

/-!
### Identity-Free Representation Summary

The following theorems provide a **genuinely identity-free** cuts representation:

- `Θ_cuts_pnat` : Defined via Dedekind cuts using ℕ+ iteration (no n=0 case)
- `Θ_cuts_pnat_strictMono` : **Strict monotonicity** (x < y ↔ Θ(x) < Θ(y)) - FULLY PROVEN
- `Θ_cuts_pnat_add` : **Additivity** (Θ(x⊕y) = Θ(x) + Θ(y)) - FULLY PROVEN

**Usage**: For a positive ordered semigroup where all elements satisfy `IsPositive`,
these theorems provide a complete representation without needing identity.

**Relation to RepresentationResult**: The identity-free proofs here can be wrapped
into a `RepresentationResult` when restricted to positive elements. For general
ordered semigroups with identity, use `cuts_representation` below.
-/

end IdentityFreeCuts

/-!
## §9: Unified Interface - RepresentationResult from Cuts

This section wraps the cuts constructions into the unified `RepresentationResult`
interface from `HolderEmbedding.lean`.

### Identity-Based Path (§9a)

Uses `Θ_cuts` with `pow'` (ℕ iteration, has n=0 base case).

### Identity-Free Path (§8)

Uses `Θ_cuts_pnat` with `iterate_op_pnat` (ℕ+ iteration, no n=0 case).
The key theorems `Θ_cuts_pnat_strictMono` and `Θ_cuts_pnat_add` are proven
using only identity-free constructs: `IsPositive`, `iterate_op_pnat`, and
`KSSeparationSemigroup` (or `KSSeparationSemigroupStrict` for strict monotonicity).
-/

section UnifiedInterface
variable [KSSeparationStrict α]

open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

/-- The cuts path produces a `RepresentationResult` (order + additivity).
    Uses identity internally but the output doesn't require `Θ ident = 0` to be useful. -/
noncomputable def cuts_representation (a : α) (ha : ident < a) : RepresentationResult α :=
  { Θ := Θ_cuts a ha
    order_preserving := fun x y =>
      ⟨fun hxy => Θ_cuts_mono a ha hxy,
       fun hΘ => by
        -- Use strict monotonicity for reverse direction
        by_contra h
        push_neg at h
        have hlt := Θ_cuts_strictMono a ha h
        exact not_le_of_gt hlt hΘ⟩
    additive := Θ_cuts_add a ha }

/-- The cuts path produces a `NormalizedRepresentationResult` (with `Θ ident = 0`). -/
noncomputable def cuts_normalized_representation (a : α) (ha : ident < a) :
    NormalizedRepresentationResult α :=
  { Θ := Θ_cuts a ha
    order_preserving := fun x y =>
      ⟨fun hxy => Θ_cuts_mono a ha hxy,
       fun hΘ => by
        by_contra h
        push_neg at h
        have hlt := Θ_cuts_strictMono a ha h
        exact not_le_of_gt hlt hΘ⟩
    additive := Θ_cuts_add a ha
    ident_zero := Θ_cuts_ident a ha }

end UnifiedInterface

/-!
## §9b: Identity-Free Unified Interface

This section provides `cuts_pnat_representation` using the identity-free proofs
from §8 (`Θ_cuts_pnat`, `Θ_cuts_pnat_strictMono`, `Θ_cuts_pnat_add`).

**Key difference from §9a**: No identity required. Works with `KSSemigroupBase` +
`KSSeparationSemigroupStrict` instead of `KnuthSkillingAlgebra` + `KSSeparationStrict`.

**Requirement**: All elements must be positive (`∀ x, IsPositive x`). This is the
natural case for ordered semigroups without identity element.
-/

section IdentityFreeUnifiedInterface
variable [KSSeparationSemigroupStrict α]

open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

/-- **Identity-Free Cuts Representation**: Produces a `RepresentationResult` using
    only identity-free constructs (`Θ_cuts_pnat`, `IsPositive`, `iterate_op_pnat`).

    **Hypotheses**:
    - `a : α` - anchor element (used for normalization)
    - `ha : IsPositive a` - anchor is positive
    - `h_all_pos : ∀ x : α, IsPositive x` - all elements are positive
    - `hcomm : ∀ u v : α, op u v = op v u` - commutativity (for additivity)

    **Use case**: Ordered semigroups without identity element, where all elements
    are "positive" (i.e., `∀ z, z < op x z` for all `x`).

    For ordered monoids with identity, prefer `cuts_representation` from §9a. -/
noncomputable def cuts_pnat_representation
    (a : α) (ha : IsPositive a)
    (h_all_pos : ∀ x : α, IsPositive x)
    (hcomm : ∀ u v : α, op u v = op v u) : RepresentationResult α :=
  { Θ := fun x => Θ_cuts_pnat a ha x (h_all_pos x)
    order_preserving := fun x y => by
      constructor
      · -- x ≤ y → Θ(x) ≤ Θ(y)
        intro hxy
        exact Θ_cuts_pnat_mono a ha (h_all_pos x) (h_all_pos y) hxy
      · -- Θ(x) ≤ Θ(y) → x ≤ y (contrapositive via strict mono)
        intro hΘ
        by_contra h
        push_neg at h
        have hlt := Θ_cuts_pnat_strictMono a ha (h_all_pos y) (h_all_pos x) h
        exact not_le_of_gt hlt hΘ
    additive := fun x y => by
      -- h_add uses isPositive_op' for the positivity proof, but our Θ uses h_all_pos (op x y)
      -- These are equal by proof irrelevance, so convert handles the mismatch
      have h_add := Θ_cuts_pnat_add a ha hcomm x y (h_all_pos x) (h_all_pos y)
      convert h_add using 2 }

/-- Strict monotonicity for identity-free cuts representation. -/
theorem cuts_pnat_representation_strictMono
    (a : α) (ha : IsPositive a) (h_all_pos : ∀ x : α, IsPositive x)
    (hcomm : ∀ u v : α, op u v = op v u)
    {x y : α} (hxy : x < y) :
    (cuts_pnat_representation a ha h_all_pos hcomm).Θ x <
    (cuts_pnat_representation a ha h_all_pos hcomm).Θ y :=
  Θ_cuts_pnat_strictMono a ha (h_all_pos x) (h_all_pos y) hxy

end IdentityFreeUnifiedInterface

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.DirectCuts
