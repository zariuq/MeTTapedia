/-
# Knuth-Skilling Separation Property - Proof from Axioms

This file is a work-in-progress attempt to prove the separation property (`KSSeparation`)
from the primitive `KnuthSkillingAlgebra` axioms (Archimedean + strict monotonicity).

**Current status**: The development succeeds in reducing `KSSeparation` to a single remaining
large-regime lemma, which is packaged as `LargeRegimeSeparationSpec`. Assuming that spec, we
provide an instance `KSSeparation α`.

Important: `KSSeparation` is **not** derivable from the base axioms alone in general; see the
compiled counterexample `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/KSSeparationNotDerivable.lean`.

**Layer Structure** (avoiding circularity):
- **RepTheorem.lean** assumes `[KSSeparation α]` and proves the representation theorem
- **This file** isolates the remaining large-regime argument as a separate explicit spec

**Mathematical Content**:
The key insight is gap growth: if x < y, then y^m - x^m grows unboundedly with m.
Eventually this gap exceeds any step size a^{k+1} - a^k, allowing us to fit a power
of a strictly between x^m and y^m, giving witnesses (n, m).

**Proof Strategy**:
1. Small regime (x < a): Use explicit witnesses based on L, M
2. Large regime (a ≤ x < y): Use gap growth to find eventual separation
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-! ## Helper Lemmas for Separation -/

/-- Convenience wrapper around `Nat.findGreatest_eq_iff`: it packages the
maximality facts for a decidable predicate together with the guarantee that
the predicate holds at the chosen index. We include `hP0 : P 0` to cover the
corner case where the greatest witness is `0`. -/
lemma findGreatest_crossing (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (hP0 : P 0) :
    P (Nat.findGreatest P n) ∧ Nat.findGreatest P n ≤ n ∧
      ∀ k, Nat.findGreatest P n < k → k ≤ n → ¬ P k := by
  -- Unpack the characterisation of `findGreatest`
  have h := (Nat.findGreatest_eq_iff (P := P) (k := n) (m := Nat.findGreatest P n)).1 rfl
  -- Extract the three pieces: bound, predicate (if nonzero), maximality
  have h_le : Nat.findGreatest P n ≤ n := h.1
  have h_pred_if_pos : Nat.findGreatest P n ≠ 0 → P (Nat.findGreatest P n) := h.2.1
  have h_max : ∀ k, Nat.findGreatest P n < k → k ≤ n → ¬ P k := by
    intro k hk hk_le
    exact h.2.2 hk hk_le
  -- Show the predicate holds at `findGreatest P n`, covering the zero case
  have h_pred : P (Nat.findGreatest P n) := by
    by_cases h0 : Nat.findGreatest P n = 0
    · simpa [h0] using hP0
    · exact h_pred_if_pos h0
  exact ⟨h_pred, h_le, h_max⟩

/-- Helper: Find minimal N ≥ 1 with x < a^N.
This ensures N has the minimality property needed for the separation proof. -/
private lemma exists_minimal_N_for_x_lt_iterate
    (a x : α) (ha : ident < a) (_hx : ident < x) :
    ∃ N : ℕ, 1 ≤ N ∧
      x < iterate_op a N ∧
      ∀ k : ℕ, 1 ≤ k → k < N → ¬ x < iterate_op a k := by
  classical
  -- Use bounded_by_iterate for existence
  obtain ⟨N₀, hN₀⟩ := bounded_by_iterate a ha x
  -- Define N via Nat.find over P n := x < iterate_op a n
  let P : ℕ → Prop := fun n => x < iterate_op a n
  have hex : ∃ n, P n := ⟨N₀, hN₀⟩
  let N := Nat.find hex
  have hN : P N := Nat.find_spec hex
  have hN_pos : 0 < N := by
    -- Forbid N = 0: that would say x < a⁰ = ident, contradicting ident ≤ x
    by_contra hN0
    push_neg at hN0
    have hN_eq0 : N = 0 := by omega
    rw [hN_eq0] at hN
    have hx_lt_ident : x < ident := by simpa [P, iterate_op_zero] using hN
    have hident_le_x : ident ≤ x := ident_le x
    exact absurd hident_le_x (not_le_of_gt hx_lt_ident)
  have hN_ge1 : 1 ≤ N := Nat.succ_le_of_lt hN_pos
  have hN_min : ∀ k : ℕ, 1 ≤ k → k < N → ¬ P k := by
    intro k _hk1 hkN
    -- Nat.find_min has shape: n < find hex → ¬ P n
    exact Nat.find_min hex hkN
  exact ⟨N, hN_ge1, hN, hN_min⟩

/-- If x < a¹ and N is minimal with x < a^N, then N ≤ 1. -/
private lemma N_le_one_of_x_lt_a {a x : α} {N : ℕ}
    (_hN_ge1 : 1 ≤ N)
    (hN_min : ∀ k : ℕ, 1 ≤ k → k < N → ¬ x < iterate_op a k)
    (hx_lt_a1 : x < iterate_op a 1) :
    N ≤ 1 := by
  -- If N > 1, then 1 < N and minimality says ¬ (x < a¹), contradicting hx_lt_a1
  by_contra hN_gt
  push_neg at hN_gt
  have h1_lt_N : (1 : ℕ) < N := by omega
  have h_not : ¬ x < iterate_op a 1 := hN_min 1 (by decide) h1_lt_N
  exact h_not hx_lt_a1

/-- Find minimal L ≥ 1 with a < y^L (for separation lemma) -/
private lemma exists_minimal_L_for_a_lt_iterate
    (y a : α) (hy : ident < y) (_ha : ident < a) :
    ∃ L : ℕ, 1 ≤ L ∧
      a < iterate_op y L ∧
      ∀ k : ℕ, 1 ≤ k → k < L → ¬ a < iterate_op y k := by
  classical
  obtain ⟨L₀, hL₀⟩ := bounded_by_iterate y hy a
  let P : ℕ → Prop := fun n => a < iterate_op y n
  have hex : ∃ n, P n := ⟨L₀, hL₀⟩
  let L := Nat.find hex
  have hL : P L := Nat.find_spec hex
  have hL_pos : 0 < L := by
    by_contra hL0
    push_neg at hL0
    have hL_eq0 : L = 0 := by omega
    rw [hL_eq0] at hL
    have ha_lt_ident : a < ident := by simpa [P, iterate_op_zero] using hL
    have hident_le_a : ident ≤ a := ident_le a
    exact absurd hident_le_a (not_le_of_gt ha_lt_ident)
  have hL_ge1 : 1 ≤ L := Nat.succ_le_of_lt hL_pos
  have hL_min : ∀ k : ℕ, 1 ≤ k → k < L → ¬ P k := by
    intro k _hk1 hkL
    exact Nat.find_min hex hkL
  exact ⟨L, hL_ge1, hL, hL_min⟩

/-! ## Large-Regime Separation (a ≤ x < y)

When a ≤ x < y, the gap y^m - x^m grows unboundedly. Eventually this exceeds
any interval [a^k, a^{k+1}), allowing separation. -/

/-- **Explicit blocker**: large-regime separation (`a ≤ x < y`).

This is the remaining hard step in the current `SeparationProof.lean` development. To avoid
leaving an unfinished proof term in the library, we package the statement as a `Prop`-class and
treat it as an explicit assumption for now. -/
class LargeRegimeSeparationSpec (α : Type*) [KnuthSkillingAlgebra α] : Prop where
  /-- When `a ≤ x < y`, there exist witnesses `(n,m)` with `x^m < a^n ≤ y^m`. -/
  exists_power_separation_of_ge :
      ∀ a x y : α, ident < a → x < y → a ≤ x →
        ∃ n m : ℕ, 0 < m ∧
          iterate_op x m < iterate_op a n ∧
          iterate_op a n ≤ iterate_op y m

/-- **Large-regime separation lemma**: When a ≤ x < y, there exist witnesses (n, m)
	that separate powers of x and y by a power of a.

This is the key lemma for the "large" regime where a ≤ x, which includes:
- The L = M subcase in N = 1 (where a ≤ x^M < y^M)
- The N ≥ 2 case (where a ≤ x < y directly)

**Proof strategy** (TODO): Use Archimedean gap growth. Since x < y, the gap
y^m - x^m grows with m. Eventually this gap exceeds the step size from a^k to a^{k+1},
allowing us to fit a power of a between x^m and y^m. -/
theorem exists_power_separation_of_ge
    (a x y : α) (ha : ident < a) (hxy : x < y) (hax : a ≤ x)
    [LargeRegimeSeparationSpec α] :
    ∃ n m : ℕ, 0 < m ∧
      iterate_op x m < iterate_op a n ∧
      iterate_op a n ≤ iterate_op y m := by
  simpa using
    (LargeRegimeSeparationSpec.exists_power_separation_of_ge (α := α) a x y ha hxy hax)
/- 
  -- Prerequisites
  have hx : ident < x := lt_of_lt_of_le ha hax
  have hy : ident < y := lt_trans hx hxy

  -- Step 1: By Archimedean, ∃ K such that x < a^K
  obtain ⟨K, hK⟩ := bounded_by_iterate a ha x
  have hK_pos : K ≥ 1 := by
    by_contra h0
    push_neg at h0
    have hK0 : K = 0 := by omega
    simp [hK0, iterate_op_zero] at hK
    exact absurd (le_of_lt hK) (not_le_of_gt hx)

  -- Define P_x predicate for findGreatest
  let P_x : ℕ → Prop := fun k => iterate_op a k ≤ x

  -- f₁ = max{k : a^k ≤ x}, using K as upper bound
  let f₁ := Nat.findGreatest P_x K

  -- Base property: P_x 0 holds (ident ≤ x)
  have hP_x0 : P_x 0 := by simp [P_x, iterate_op_zero]; exact le_of_lt hx

  -- Key fact: a ≤ x means P_x 1 holds
  have hP_x1 : P_x 1 := by simp [P_x, iterate_op_one]; exact hax

  have hf₁_ge1 : f₁ ≥ 1 := Nat.le_findGreatest hK_pos hP_x1

  -- Get crossing properties for f₁
  have h_cross_x := findGreatest_crossing (P := P_x) K hP_x0
  have hP_xf₁ : iterate_op a f₁ ≤ x := h_cross_x.1
  have hf₁_le_K : f₁ ≤ K := h_cross_x.2.1

  -- x < a^K means f₁ < K, so x < a^{f₁+1}
  have hf₁_lt_K : f₁ < K := by
    by_contra h_ge
    push_neg at h_ge
    have hf₁_eq_K : f₁ = K := le_antisymm hf₁_le_K h_ge
    have : iterate_op a K ≤ x := by rw [← hf₁_eq_K]; exact hP_xf₁
    exact not_lt_of_ge this hK

  have h_not_Px_f₁succ : ¬ P_x (f₁ + 1) :=
    h_cross_x.2.2 (f₁ + 1) (Nat.lt_succ_self f₁) (Nat.succ_le_of_lt hf₁_lt_K)
  have hx_lt_af₁succ : x < iterate_op a (f₁ + 1) := lt_of_not_ge h_not_Px_f₁succ

  -- Now: We have a^{f₁} ≤ x < a^{f₁+1}
  -- Since x < y, also a^{f₁} ≤ x < y.
  -- The key question: is a^{f₁+1} ≤ y?

  rcases le_or_gt (iterate_op a (f₁ + 1)) y with h_sep | h_same

  · -- **CASE 1**: a^{f₁+1} ≤ y
    -- Witnesses: n = f₁ + 1, m = 1
    have hx1 : iterate_op x 1 < iterate_op a (f₁ + 1) := by
      simp only [iterate_op_one]; exact hx_lt_af₁succ
    have hy1 : iterate_op a (f₁ + 1) ≤ iterate_op y 1 := by
      simp only [iterate_op_one]; exact h_sep
    exact ⟨f₁ + 1, 1, Nat.one_pos, hx1, hy1⟩

  · -- **CASE 2**: y < a^{f₁+1}
    -- Both x and y are in [a^{f₁}, a^{f₁+1}), need to use gap growth

    -- By Archimedean, ∃ L with a < y^L
    obtain ⟨L, hL⟩ := bounded_by_iterate y hy a
    have hL_pos : L ≥ 1 := by
      by_contra hL0
      push_neg at hL0
      have : L = 0 := by omega
      simp [this, iterate_op_zero] at hL
      exact absurd (le_of_lt hL) (not_le_of_gt ha)

    -- Gap growth lemma: y^{L+m} > x^m ⊕ a for all m ≥ 1
    have gap_growth : ∀ m : ℕ, m ≥ 1 → iterate_op y (L + m) > op (iterate_op x m) a := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
        cases m with
        | zero =>
          calc iterate_op y (L + 1)
              = op y (iterate_op y L) := rfl
            _ > op y a := op_strictMono_right y hL
            _ > op x a := op_strictMono_left a hxy
            _ = op (iterate_op x 1) a := by rw [iterate_op_one]
        | succ n =>
          have ih' : iterate_op y (L + (n + 1)) > op (iterate_op x (n + 1)) a := ih (by omega)
          have h_idx : L + (n + 2) = (L + (n + 1)) + 1 := by omega
          calc iterate_op y (L + (n + 2))
              = iterate_op y ((L + (n + 1)) + 1) := by rw [h_idx]
            _ = op y (iterate_op y (L + (n + 1))) := rfl
            _ > op y (op (iterate_op x (n + 1)) a) := op_strictMono_right y ih'
            _ = op (op y (iterate_op x (n + 1))) a := (op_assoc y (iterate_op x (n + 1)) a).symm
            _ > op (op x (iterate_op x (n + 1))) a :=
                op_strictMono_left a (op_strictMono_left (iterate_op x (n + 1)) hxy)
            _ = op (iterate_op x (n + 2)) a := rfl

    -- Use gap at m = L
    have h_gap_L : iterate_op y (2 * L) > op (iterate_op x L) a := by
      have : 2 * L = L + L := by ring
      rw [this]
      exact gap_growth L hL_pos

    -- Find crossing point for x^{2L}
    obtain ⟨K''', hK'''⟩ := bounded_by_iterate a ha (iterate_op x (2 * L))
    let P2 : ℕ → Prop := fun k => iterate_op a k ≤ iterate_op x (2 * L)
    let n2 := Nat.findGreatest P2 K'''

    have hP2_0 : P2 0 := by simp [P2, iterate_op_zero]; exact ident_le _

    have h_cross2 := findGreatest_crossing (P := P2) K''' hP2_0
    have hP2_n2 : iterate_op a n2 ≤ iterate_op x (2 * L) := h_cross2.1

    have hn2_lt_K''' : n2 < K''' := by
      by_contra h_ge
      push_neg at h_ge
      have hn2_eq : n2 = K''' := le_antisymm h_cross2.2.1 h_ge
      have : iterate_op a K''' ≤ iterate_op x (2 * L) := by rw [← hn2_eq]; exact hP2_n2
      exact not_lt_of_ge this hK'''

    have h_not_P2_succ : ¬ P2 (n2 + 1) :=
      h_cross2.2.2 (n2 + 1) (Nat.lt_succ_self n2) (Nat.succ_le_of_lt hn2_lt_K''')
    have hx2L_lt : iterate_op x (2 * L) < iterate_op a (n2 + 1) := lt_of_not_ge h_not_P2_succ

    -- Check if a^{n2+1} ≤ y^{2L}
    rcases le_or_gt (iterate_op a (n2 + 1)) (iterate_op y (2 * L)) with h_upper | h_nosep

    · -- SUCCESS: a^{n2+1} ≤ y^{2L}
      have h2L_pos : 2 * L > 0 := by omega
      exact ⟨n2 + 1, 2 * L, h2L_pos, hx2L_lt, h_upper⟩

    · -- Both x^{2L} and y^{2L} in [a^{n2}, a^{n2+1})
      -- Key insight: gap_growth at m=2L gives y^{3L} > x^{2L} ⊕ a ≥ a^{n2+1}
      -- This directly shows y^{3L} exceeds the interval containing x^{2L}

      -- From h_nosep: y^{2L} < a^{n2+1}
      have hy2L_lt : iterate_op y (2 * L) < iterate_op a (n2 + 1) := h_nosep

      -- From hP2_n2: a^{n2} ≤ x^{2L}
      -- So x^{2L} ⊕ a ≥ a^{n2} ⊕ a = a^{n2+1}
      have hxL_plus_a_ge : op (iterate_op x (2 * L)) a ≥ iterate_op a (n2 + 1) := by
        have h1 : iterate_op a n2 ≤ iterate_op x (2 * L) := hP2_n2
        have h2 : op (iterate_op a n2) a ≤ op (iterate_op x (2 * L)) a := op_mono_left a h1
        -- a^{n2} ⊕ a^1 = a^{n2+1}
        have h4 : op (iterate_op a n2) (iterate_op a 1) = iterate_op a (n2 + 1) := by
          rw [iterate_op_add]
        simp only [iterate_op_one] at h4
        rw [← h4]
        exact h2

      -- From gap_growth at m = 2L: y^{L + 2L} = y^{3L} > x^{2L} ⊕ a
      have h_gap_3L : iterate_op y (3 * L) > op (iterate_op x (2 * L)) a := by
        have h3L : 3 * L = L + 2 * L := by ring
        rw [h3L]
        exact gap_growth (2 * L) (by omega : 2 * L ≥ 1)

      -- Combining: y^{3L} > x^{2L} ⊕ a ≥ a^{n2+1}
      have hy3L_gt : iterate_op y (3 * L) > iterate_op a (n2 + 1) :=
        lt_of_le_of_lt hxL_plus_a_ge h_gap_3L

      -- Now find the crossing for x^{3L}
      obtain ⟨K4, hK4⟩ := bounded_by_iterate a ha (iterate_op x (3 * L))
      let P3 : ℕ → Prop := fun k => iterate_op a k ≤ iterate_op x (3 * L)
      let n3 := Nat.findGreatest P3 K4

      have hP3_0 : P3 0 := by simp [P3, iterate_op_zero]; exact ident_le _

      have h_cross3 := findGreatest_crossing (P := P3) K4 hP3_0
      have hP3_n3 : iterate_op a n3 ≤ iterate_op x (3 * L) := h_cross3.1

      have hn3_lt_K4 : n3 < K4 := by
        by_contra h_ge
        push_neg at h_ge
        have hn3_eq : n3 = K4 := le_antisymm h_cross3.2.1 h_ge
        have : iterate_op a K4 ≤ iterate_op x (3 * L) := by rw [← hn3_eq]; exact hP3_n3
        exact not_lt_of_ge this hK4

      have h_not_P3_succ : ¬ P3 (n3 + 1) :=
        h_cross3.2.2 (n3 + 1) (Nat.lt_succ_self n3) (Nat.succ_le_of_lt hn3_lt_K4)
      have hx3L_lt : iterate_op x (3 * L) < iterate_op a (n3 + 1) := lt_of_not_ge h_not_P3_succ

      -- Now check: is a^{n3+1} ≤ y^{3L}?
      rcases le_or_gt (iterate_op a (n3 + 1)) (iterate_op y (3 * L)) with h_upper3 | h_nosep3

      · -- SUCCESS at m = 3L: a^{n3+1} ≤ y^{3L}
        have h3L_pos : 3 * L > 0 := by omega
        exact ⟨n3 + 1, 3 * L, h3L_pos, hx3L_lt, h_upper3⟩

      · -- **Case 2b.2**: Both x^{3L} and y^{3L} in [a^{n3}, a^{n3+1})
        -- Instead of unrolling more cases, use Nat.find to find the first m where separation occurs

        -- Define predicate: y^m has jumped ahead of x^m by at least one interval
        -- Specifically: ∃ n, x^m < a^n ∧ a^n ≤ y^m
        let P : ℕ → Prop := fun m => ∃ n : ℕ, iterate_op x m < iterate_op a n ∧
                                              iterate_op a n ≤ iterate_op y m

        -- Prove existence: for large enough m, the gap y^{L+m} - x^m exceeds any interval
        have hex : ∃ m : ℕ, P m := by
          -- Key observation: We already know y^{3L} > a^{n2+1} (from hy3L_gt)
          -- We'll use repeated application of gap_growth to show eventual separation

          -- Strategy: iterate by multiples of L
          -- At each step, the "floor" of y increases by at least as much as the floor of x
          -- But gap_growth ensures y gets extra boost, so eventually y jumps ahead

          -- Concrete witness: use m = L * (n2 + 3)
          -- By induction, we can show y^{L*(n2+3)} jumps many intervals ahead of x^{L*(n2+3)}

          -- For now, use a simpler direct argument:
          -- Since we're in Case 2b.2, we have both x^{3L} and y^{3L} in [a^{n3}, a^{n3+1})
          -- But by iterating further, gap_growth ensures eventual separation

          -- Strategy: We'll use the key fact that y accumulates advantage over x.
          -- From gap_growth: y^{L+m} > x^m ⊕ a for all m ≥ 1
          --
          -- We use m = (n3+1) * L as witness. The key insight is:
          -- 1. Since a < y^L, by repetition_lemma_lt: a^{n3+1} < y^{L*(n3+1)}
          -- 2. This gives us the UPPER bound: a^{n3+1} ≤ y^{(n3+1)*L}
          -- 3. For the lower bound on x, we use strict monotonicity
          --
          -- But first, let's establish that n3 ≥ n2 (the floors are non-decreasing)
          -- since x^{3L} ≥ x^{2L} implies floor(x^{3L}) ≥ floor(x^{2L})

          -- Key insight: From a < y^L, by repetition_lemma_lt: a^k < y^{L*k} for k ≥ 1
          -- So floor(y^{L*k}) ≥ k. For x, a ≤ x means a^m ≤ x^m, so floor(x^m) ≥ m.
          -- But x^m is bounded above by some a^K (Archimedean), so floor(x^m) < K.
          --
          -- The key: for k > K, floor(y^{L*k}) ≥ k > K > floor(x^{L*k})
          -- This gives separation!

          -- Get the Archimedean bound K for x^{L*K4}
          -- We need K such that x^{L*K} < a^K for the argument to work
          -- Use K4 from context: x^{3L} < a^{K4}

          -- From a ≤ x, we have a^m ≤ x^m for all m
          have ha_le_x_pow : ∀ m : ℕ, iterate_op a m ≤ iterate_op x m := by
            intro m
            induction m with
            | zero => simp [iterate_op_zero]
            | succ m ih =>
              calc iterate_op a (m + 1)
                  = op a (iterate_op a m) := rfl
                _ ≤ op a (iterate_op x m) := op_mono_right a ih
                _ ≤ op x (iterate_op x m) := op_mono_left (iterate_op x m) hax
                _ = iterate_op x (m + 1) := rfl

          -- Key: x^{3L} < a^{K4} and a^{K4} ≤ x^{K4} imply 3L < K4
          have hK4_pos : K4 > 0 := by
            by_contra h0
            push_neg at h0
            have hK4_eq0 : K4 = 0 := by omega
            simp [hK4_eq0, iterate_op_zero] at hK4
            exact absurd (ident_le _) (not_le_of_gt hK4)

          have h3L_lt_K4 : 3 * L < K4 := by
            have h1 : iterate_op x (3 * L) < iterate_op a K4 := hK4
            have h2 : iterate_op a K4 ≤ iterate_op x K4 := ha_le_x_pow K4
            have h3 : iterate_op x (3 * L) < iterate_op x K4 := lt_of_lt_of_le h1 h2
            have hx_pos : ident < x := lt_of_lt_of_le ha hax
            exact iterate_op_strictMono x hx_pos |>.lt_iff_lt.mp h3

          -- Use witness m = L * (K4 + 1)
          -- This is large enough that floor(y^m) ≥ K4 + 1 > floor(x^m)
          use L * (K4 + 1)

          -- Need: ∃ n, x^{L*(K4+1)} < a^n ∧ a^n ≤ y^{L*(K4+1)}

          -- Step 1: Upper bound for y
          -- From a < y^L, by repetition: a^{K4+1} < y^{L*(K4+1)}
          have hK4succ_pos : K4 + 1 > 0 := Nat.succ_pos K4

          have hy_ge : iterate_op a (K4 + 1) < iterate_op y (L * (K4 + 1)) := by
            have h_rep := repetition_lemma_lt a y 1 L (K4 + 1) hK4succ_pos
            simp only [Nat.one_mul] at h_rep
            rw [iterate_op_one] at h_rep
            exact h_rep hL

          -- So a^{K4+1} ≤ y^{L*(K4+1)}
          have hy_upper : iterate_op a (K4 + 1) ≤ iterate_op y (L * (K4 + 1)) := le_of_lt hy_ge

          -- Step 2: Lower bound for x
          -- We need x^{L*(K4+1)} < a^{K4+1}
          -- From x^{3L} < a^{K4} and the structure of the algebra

          -- Since L*(K4+1) = L*K4 + L and 3L < K4, we have:
          -- L*K4 ≥ L*4 = 4L > 3L (since K4 > 3L implies K4 ≥ 4 for L ≥ 1)

          -- The key: we need to show x^{L*(K4+1)} < a^{K4+1}
          -- This follows from: floor(x^{L*(K4+1)}) < K4 + 1

          -- Get the floor of x^{L*(K4+1)}
          obtain ⟨K6, hK6⟩ := bounded_by_iterate a ha (iterate_op x (L * (K4 + 1)))
          let P_x6 : ℕ → Prop := fun k => iterate_op a k ≤ iterate_op x (L * (K4 + 1))
          let n6 := Nat.findGreatest P_x6 K6

          have hP_x6_0 : P_x6 0 := by simp [P_x6, iterate_op_zero]; exact ident_le _
          have h_cross6 := findGreatest_crossing (P := P_x6) K6 hP_x6_0

          have hn6_lt_K6 : n6 < K6 := by
            by_contra h_ge
            push_neg at h_ge
            have hn6_eq : n6 = K6 := le_antisymm h_cross6.2.1 h_ge
            have : iterate_op a K6 ≤ iterate_op x (L * (K4 + 1)) := by
              rw [← hn6_eq]; exact h_cross6.1
            exact not_lt_of_ge this hK6

          have hx_lt : iterate_op x (L * (K4 + 1)) < iterate_op a (n6 + 1) := by
            have h_not : ¬ P_x6 (n6 + 1) :=
              h_cross6.2.2 (n6 + 1) (Nat.lt_succ_self n6) (Nat.succ_le_of_lt hn6_lt_K6)
            exact lt_of_not_ge h_not

          -- Now check: is a^{n6+1} ≤ y^{L*(K4+1)}?
          -- From hy_ge: a^{K4+1} < y^{L*(K4+1)}
          -- If n6 + 1 ≤ K4 + 1 (i.e., n6 ≤ K4), then a^{n6+1} ≤ a^{K4+1} ≤ y^{L*(K4+1)} ✓

          rcases le_or_gt (n6 + 1) (K4 + 1) with hn6_le | hn6_gt

          · -- Case: n6 + 1 ≤ K4 + 1, so a^{n6+1} ≤ a^{K4+1} ≤ y^{L*(K4+1)}
            have h_upper : iterate_op a (n6 + 1) ≤ iterate_op y (L * (K4 + 1)) := by
              calc iterate_op a (n6 + 1)
                  ≤ iterate_op a (K4 + 1) := iterate_op_strictMono a ha |>.monotone hn6_le
                _ ≤ iterate_op y (L * (K4 + 1)) := hy_upper
            exact ⟨n6 + 1, hx_lt, h_upper⟩

          · -- Case: n6 + 1 > K4 + 1, i.e., n6 ≥ K4 + 1
            -- This means floor(x^{L*(K4+1)}) ≥ K4 + 1
            -- So a^{K4+1} ≤ x^{L*(K4+1)}

            have hn6_ge : n6 ≥ K4 + 1 := by omega

            -- From a^{n6} ≤ x^{L*(K4+1)} and n6 ≥ K4+1:
            -- a^{K4+1} ≤ a^{n6} ≤ x^{L*(K4+1)}

            have hx_ge_K4succ : iterate_op a (K4 + 1) ≤ iterate_op x (L * (K4 + 1)) := by
              calc iterate_op a (K4 + 1)
                  ≤ iterate_op a n6 := iterate_op_strictMono a ha |>.monotone hn6_ge
                _ ≤ iterate_op x (L * (K4 + 1)) := h_cross6.1

            -- Also y^{L*(K4+1)} > x^{L*(K4+1)} since y > x
            have hy_gt_x : iterate_op y (L * (K4 + 1)) > iterate_op x (L * (K4 + 1)) := by
              have hLK4succ_pos : L * (K4 + 1) > 0 := Nat.mul_pos hL_pos hK4succ_pos
              exact iterate_op_strictMono_base (L * (K4 + 1)) hLK4succ_pos x y hxy

            -- So: a^{K4+1} ≤ x^{L*(K4+1)} < y^{L*(K4+1)}
            -- And: a^{K4+1} < y^{L*(K4+1)} (from hy_ge)

            -- Both x and y have floor ≥ K4+1. Are they in the same interval?
            -- We have x^{L*(K4+1)} < a^{n6+1} (from hx_lt)
            -- Is y^{L*(K4+1)} < a^{n6+1} or ≥ a^{n6+1}?

            rcases le_or_gt (iterate_op a (n6 + 1)) (iterate_op y (L * (K4 + 1))) with h_sep | h_nosep

            · -- a^{n6+1} ≤ y^{L*(K4+1)}: Separation!
              exact ⟨n6 + 1, hx_lt, h_sep⟩

            · -- y^{L*(K4+1)} < a^{n6+1}: Both in [a^{n6}, a^{n6+1})
              -- This is the deepest case where explicit witnesses fail
              --
              -- PROOF BY CONTRADICTION using gap_growth:
              -- If ∀ m, ¬P m (no separation), then floor(y^m) ≤ floor(x^m) for all m.
              -- But gap_growth says y^{L+m} > x^m ⊕ a ≥ a^{floor(x^m)+1}.
              -- So floor(y^{L+m}) ≥ floor(x^m) + 1.
              -- Combined: floor(x^{L+m}) ≥ floor(y^{L+m}) ≥ floor(x^m) + 1.
              -- This means floor(x^m) grows unboundedly, contradicting Archimedean.

              by_contra h_none
              -- Full completion of this contradiction branch remains open; we mark it
              -- as BLOCKED in this archived proof attempt.
              BLOCKED

              -- Hmm, we need the bound to be tighter. Let me think again...

              -- Actually, the key is that in this SPECIFIC case (line 500),
              -- we have both x^{L*(K4+1)} and y^{L*(K4+1)} in [a^{n6}, a^{n6+1}).
              -- The h_nosep says y^{L*(K4+1)} < a^{n6+1}.
              -- But gap_growth at m = L*K4 says y^{L + L*K4} = y^{L*(K4+1)} > x^{L*K4} ⊕ a.
              -- And from hax (a ≤ x), we have x^{L*K4} ≥ a^{L*K4}, so
              -- x^{L*K4} ⊕ a ≥ a^{L*K4} ⊕ a = a^{L*K4+1}.
              -- So y^{L*(K4+1)} > a^{L*K4+1}.
              -- But we need y^{L*(K4+1)} < a^{n6+1} (from h_nosep).
              -- This requires n6+1 > L*K4+1, i.e., n6 > L*K4.

              -- From h_cross6: n6 is the floor of x^{L*(K4+1)}, i.e., a^{n6} ≤ x^{L*(K4+1)} < a^{n6+1}.
              -- From hax: a^{L*(K4+1)} ≤ x^{L*(K4+1)}, so n6 ≥ L*(K4+1).
              -- So n6 ≥ L*K4 + L ≥ L*K4 + 1 > L*K4. Good, n6 > L*K4.

              -- So a^{n6+1} > a^{L*K4+1}, consistent with h_nosep (y < a^{n6+1}) and gap (y > a^{L*K4+1}).
              -- This means L*K4+1 ≤ n6 < n6+1, so n6 ≥ L*K4+1, i.e., n6 > L*K4.

              -- The contradiction: we've shown y^{L*(K4+1)} > a^{L*K4+1} but also y^{L*(K4+1)} < a^{n6+1}.
              -- Since n6+1 > L*K4+1, there's room for both. No immediate contradiction.

              -- Let me try the original approach more carefully with SPECIFIC bounds.
              -- From h_floor_growth and h_unbounded, floor_x (k*L) ≥ k.
              -- We have hK4: x^{3L} < a^{K4}, so floor_x (3L) < K4.
              -- Taking k = 3: floor_x (3L) ≥ 3.
              -- So 3 ≤ floor_x (3L) < K4, meaning K4 > 3. OK.

              -- Taking k = K4: floor_x (K4 * L) ≥ K4.
              -- But what's the bound on floor_x (K4 * L)?
              -- From hax (a ≤ x): x^{K4*L} ≥ a^{K4*L}, so floor_x (K4*L) ≥ K4*L.
              -- Wait, this is STRONGER than h_unbounded's k bound!

              -- So floor_x (K4*L) ≥ K4*L (from a ≤ x) and we need floor_x (K4*L) ≥ K4.
              -- Since L ≥ 1, K4*L ≥ K4, so floor_x (K4*L) ≥ K4*L ≥ K4. Consistent.

              -- The gap_growth gives ADDITIONAL growth beyond the a ≤ x baseline.
              -- floor_x (L + m) ≥ floor_x (m) + 1.
              -- Starting from floor_x (L) ≥ L (from a ≤ x), we get:
              -- floor_x (2L) ≥ floor_x (L) + 1 ≥ L + 1
              -- floor_x (3L) ≥ floor_x (2L) + 1 ≥ L + 2
              -- floor_x (k*L) ≥ L + (k-1) = L + k - 1 for k ≥ 1

              -- Compare with floor_x (k*L) < K6 (Archimedean bound from line 436).
              -- Actually, K6 is the Archimedean bound for x^{L*(K4+1)}, not k*L general.

              -- Let's get a general bound. x^{k*L} < a^{N_x}^{k*L} is wrong.
              -- The correct bound: x < a^{N_x}, so by iteration x^m < a^{m*N_x}? NO.
              -- iterate_op is NOT multiplication!

              -- From x < a^{N_x} and strict mono: x^m < (a^{N_x})^m would require
              -- (x ⊕ x ⊕ ...) < ((a^{N_x}) ⊕ (a^{N_x}) ⊕ ...), which IS true by monotonicity.
              -- So x^m < (a^{N_x})^m = a^{N_x * m}.
              -- Therefore floor_x (m) < N_x * m.

              -- Now: floor_x (k*L) ≥ L + k - 1 (from gap_growth argument)
              -- floor_x (k*L) < N_x * k * L (from Archimedean)
              -- Need: L + k - 1 < N_x * k * L for all k? Or contradiction for large k?

              -- L + k - 1 < N_x * k * L
              -- L + k - 1 < N_x * k * L
              -- For large k: k < N_x * k * L, i.e., 1 < N_x * L. True if N_x ≥ 1, L ≥ 1.

              -- So there's no contradiction for large k with this bound!

              -- THE REAL INSIGHT: The gap_growth argument shows floor increases by 1 per L steps
              -- BEYOND the baseline. But we need floor_x (k*L) ≥ k (not L + k - 1).
              -- Let me re-examine h_floor_growth.

              -- ACTUALLY, the proof I outlined is wrong. Let me reconsider.

              -- In the case we're handling (both in same interval), ¬P m means
              -- x^m and y^m have THE SAME floor (both in [a^n, a^{n+1})).
              -- gap_growth: y^{L+m} > x^m ⊕ a.
              -- If floor(x^m) = n, then x^m ⊕ a ≥ a^n ⊕ a = a^{n+1}.
              -- So y^{L+m} > a^{n+1}.
              -- By ¬P (L+m): floor(y^{L+m}) ≤ floor(x^{L+m}).
              -- From y^{L+m} > a^{n+1}: floor(y^{L+m}) ≥ n+1.
              -- So floor(x^{L+m}) ≥ n+1 = floor(x^m) + 1.

              -- This IS the floor growth I claimed! floor_x (L+m) ≥ floor_x (m) + 1.

              -- Now the issue is that floor_x (m) ≥ m (from a ≤ x), so
              -- floor_x (k*L) ≥ floor_x ((k-1)*L) + 1 ≥ ... ≥ floor_x (L) + (k-1) ≥ L + k - 1.

              -- But the Archimedean bound floor_x (k*L) < N_x * k * L is too weak.

              -- HOWEVER: In the SPECIFIC context of line 500:
              -- We have hK4: x^{3L} < a^{K4}, which gives floor_x (3L) < K4.
              -- From floor_x (3L) ≥ L + 2 (taking k = 3), we get L + 2 ≤ floor_x (3L) < K4.
              -- So L + 2 < K4.

              -- Now take k such that L + k - 1 ≥ K4, i.e., k ≥ K4 - L + 1.
              -- Let k = K4 - L + 1 (assuming this is ≥ 1, which needs K4 > L).
              -- Then floor_x (k*L) ≥ L + k - 1 = L + (K4 - L + 1) - 1 = K4.
              -- But floor_x (k*L) < ??? We need a bound.

              -- From x^{3L} < a^{K4} and x^m is increasing:
              -- x^m < a^{K4} for m ≤ 3L? NO, x^m increases, so x^{3L} < a^{K4} doesn't bound larger m.

              -- We need a GLOBAL bound on floor_x. From x < a^{N_x}:
              -- x^m < a^{N_x * m}, so floor_x (m) < N_x * m.

              -- With k = K4 - L + 1:
              -- floor_x ((K4 - L + 1) * L) ≥ K4
              -- floor_x ((K4 - L + 1) * L) < N_x * (K4 - L + 1) * L

              -- Need K4 ≤ N_x * (K4 - L + 1) * L? This is:
              -- K4 ≤ N_x * L * K4 - N_x * L^2 + N_x * L
              -- K4 * (1 - N_x * L) ≤ N_x * L * (1 - L)
              -- If N_x * L > 1, then LHS is negative (K4 > 0), RHS is ≤ 0 (L ≥ 1). Consistent.
              -- If N_x * L = 1 (impossible since N_x, L ≥ 1).
              -- If N_x * L < 1 (impossible).

              -- So no contradiction this way either!

              -- I think the approach needs to be different. Let me re-read the context.
              -- We're inside the proof of hex : ∃ m, P m, in a specific subcase.
              -- The outer structure handles this by Nat.find AFTER we prove hex.
              -- The BLOCKED marker above is for proving `hex` in this specific deepest case.

              -- Maybe the answer is simpler: in this case, we've established certain bounds
              -- (n6 ≥ K4 + 1 from hn6_gt, etc.) that should give a direct contradiction.

              -- From hn6_gt: n6 + 1 > K4 + 1, i.e., n6 ≥ K4 + 1.
              -- From h_cross6.1: a^{n6} ≤ x^{L*(K4+1)}.
              -- From hx_lt: x^{L*(K4+1)} < a^{n6+1}.
              -- From h_nosep: y^{L*(K4+1)} < a^{n6+1}.
              -- From hy_ge: a^{K4+1} < y^{L*(K4+1)}.

              -- So: a^{K4+1} < y^{L*(K4+1)} < a^{n6+1}.
              -- Since n6 ≥ K4+1, we have n6+1 ≥ K4+2 > K4+1. Consistent.

              -- And: a^{n6} ≤ x^{L*(K4+1)} < a^{n6+1}.

              -- From gap_growth at m = L*K4 (if K4 ≥ 1):
              -- y^{L + L*K4} = y^{L*(K4+1)} > x^{L*K4} ⊕ a.

              -- From ha_le_x_pow: a^{L*K4} ≤ x^{L*K4}.
              -- So x^{L*K4} ⊕ a ≥ a^{L*K4} ⊕ a = a^{L*K4+1}.
              -- Thus y^{L*(K4+1)} > a^{L*K4+1}.

              -- Combined with y^{L*(K4+1)} < a^{n6+1}:
              -- a^{L*K4+1} < a^{n6+1}, i.e., L*K4+1 < n6+1, i.e., L*K4 < n6.
              -- We already have n6 ≥ K4+1.
              -- If L ≥ 1 and K4 ≥ 1, then L*K4 ≥ K4, so this gives n6 > L*K4 ≥ K4 ≥ K4.
              -- This is consistent with n6 ≥ K4+1 when L*K4 ≤ K4, i.e., L ≤ 1. Since L ≥ 1, L = 1.

              -- If L = 1: n6 > K4 and n6 ≥ K4+1. These are the same.

              -- If L > 1: L*K4 > K4, so n6 > L*K4 > K4.
              -- But we also have n6 ≥ K4+1. These can both be true (n6 ≥ max(K4+1, L*K4+1) = L*K4+1 if L ≥ 1).

              -- I don't see an immediate contradiction. The proof needs more work.

              -- For now, the BLOCKED marker above handles this case.
              -- The key insight is correct: use gap_growth + contradiction.
              -- The implementation is delicate and may require explicit induction.

        -- Find the minimal m where P holds
        let m_sep := Nat.find hex

        -- P(m_sep) holds by construction
        have hP_m_sep : P m_sep := Nat.find_spec hex

        -- m_sep > 0 (since P(0) doesn't hold)
        have hm_sep_pos : m_sep > 0 := by
          by_contra h0
          push_neg at h0
          have hm0 : m_sep = 0 := by omega
          -- At m = 0, we'd have x^0 = ident < a^n ≤ y^0 = ident for some n
          -- This contradicts ident ≤ a^n
          rw [hm0] at hP_m_sep
          obtain ⟨n, hx0, hy0⟩ := hP_m_sep
          simp [iterate_op_zero] at hx0 hy0
          -- x^0 = ident < a^n ≤ y^0 = ident gives ident < ident
          have : ident < ident := calc ident = iterate_op x 0 := (iterate_op_zero x).symm
            _ < iterate_op a n := hx0
            _ ≤ iterate_op y 0 := hy0
            _ = ident := iterate_op_zero y
          exact lt_irrefl ident this

        -- Extract witnesses from P(m_sep)
        obtain ⟨n_sep, hx_sep, hy_sep⟩ := hP_m_sep

        -- Witnesses: (n_sep, m_sep)
        exact ⟨n_sep, m_sep, hm_sep_pos, hx_sep, hy_sep⟩

-/

/-! ## Main Separation Lemma

The full separation lemma handles both small regime (x < a) and large regime (a ≤ x). -/

/-- **Main Separation Lemma** (from K-S axioms): For any x < y and base a,
there exist exponents (n, m) such that x^m < a^n ≤ y^m.

This is the key algebraic property that enables the representation theorem.

**Proof Structure**:
- Case 1: a^N ≤ y for minimal N with x < a^N → witnesses (N, 1)
- Case 2: y < a^N (both in same interval [a^{N-1}, a^N))
  - Subcase N = 1 (small regime): x < a
    - If L ≤ M-1: use explicit witnesses from small-regime formula
    - If L = M: reduce to large-regime via (x^M, y^M)
  - Subcase N ≥ 2 (large regime): a ≤ x, use large-regime lemma directly

where:
- N = minimal with x < a^N
- L = minimal with a < y^L
- M = minimal with a ≤ x^M (if it exists)
-/
theorem ks_separation_lemma (a x y : α) (ha : ident < a) (hx : ident < x)
    (hy : ident < y) (hxy : x < y) [LargeRegimeSeparationSpec α] :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  -- Get minimal N ≥ 1 such that x < iterate_op a N
  classical
  obtain ⟨N, hN_ge1, hN, hN_min⟩ := exists_minimal_N_for_x_lt_iterate a x ha hx
  -- Case split: either iterate_op a N ≤ y (separation at m=1) or y < iterate_op a N
  rcases le_or_gt (iterate_op a N) y with h_sep | h_same
  · -- Case 1: iterate_op a N ≤ y. Then n = N, m = 1 works.
    exact ⟨N, 1, Nat.one_pos, by rwa [iterate_op_one], by rwa [iterate_op_one]⟩
  · -- Case 2: y < iterate_op a N. Both x, y are in the same "interval" between
    -- consecutive iterates of a.
    --
    -- **Proof strategy** (K&S paper lines 1536-1622):
    -- Key insight: The gap between iterate_op y m and iterate_op x m grows unboundedly.
    -- For large enough m, this gap "contains" a full step of a.
    --
    -- Step 1: By Archimedean on y, ∃ L such that iterate_op y L > a.
    -- Use minimal L for easier reasoning about y^{L-1} ≤ a
    obtain ⟨L, hL_ge1, hL, hL_min⟩ := exists_minimal_L_for_a_lt_iterate y a hy ha
    -- Step 2: We prove by induction that iterate_op y (L + m) > op (iterate_op x m) a
    -- Then with M = L + L, we have iterate_op y M > op (iterate_op x (M - L)) a.
    have gap_dominates : ∀ m : ℕ, m ≥ 1 → iterate_op y (L + m) > op (iterate_op x m) a := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
        cases m with
        | zero =>
          -- Base case: m = 1
          -- iterate_op y (L + 1) = op y (iterate_op y L) > op y a > op x a = op (iterate_op x 1) a
          calc iterate_op y (L + 1)
              = op y (iterate_op y L) := by rfl
            _ > op y a := op_strictMono_right y hL
            _ > op x a := op_strictMono_left a hxy
            _ = op (iterate_op x 1) a := by rw [iterate_op_one]
        | succ n =>
          -- Inductive step: assume holds for m = n + 1 ≥ 1, prove for m = n + 2
          have ih' : iterate_op y (L + (n + 1)) > op (iterate_op x (n + 1)) a := ih (by omega)
          have h_idx : L + (n + 2) = (L + (n + 1)) + 1 := by omega
          calc iterate_op y (L + (n + 2))
              = iterate_op y ((L + (n + 1)) + 1) := by rw [h_idx]
            _ = op y (iterate_op y (L + (n + 1))) := rfl
            _ > op y (op (iterate_op x (n + 1)) a) := op_strictMono_right y ih'
            _ = op (op y (iterate_op x (n + 1))) a := (op_assoc y (iterate_op x (n + 1)) a).symm
            _ > op (op x (iterate_op x (n + 1))) a := op_strictMono_left a (op_strictMono_left (iterate_op x (n + 1)) hxy)
            _ = op (iterate_op x (n + 2)) a := rfl
    -- Step 3: Use gap_dominates to find separation
    -- From gap_dominates, the gap between y^m and x^m grows unboundedly.
    -- For large enough m, we can fit an iterate of a in this gap.
    --
    -- Technical approach using Nat.findGreatest:
    --   1. Take m = 2L (where L is from step 1)
    --   2. Define n_x = Nat.findGreatest (λ k => iterate_op a k ≤ iterate_op x m) (upper_bound)
    --   3. Then iterate_op x m < iterate_op a (n_x + 1) by definition of findGreatest
    --   4. Show iterate_op a (n_x + 1) ≤ iterate_op y m using gap_dominates
    --
    -- This requires:
    --   - Showing findGreatest gives a usable crossing point
    --   - Connecting the gap from gap_dominates to the iterate bounds
    -- By Archimedean, there is an iterate of `a` strictly above `x^L ⊕ a`
    obtain ⟨K, hK⟩ := bounded_by_iterate a ha (op (iterate_op x L) a)
    -- Let P k := iterate_op a k ≤ op (iterate_op x L) a. We know:
    --   • P 0 holds (ident ≤ x^L ⊕ a)
    --   • P K is false (since x^L ⊕ a < a^K from hK)
    -- so `Nat.findGreatest` gives the last k ≤ K with P k.
    let P : ℕ → Prop := fun k => iterate_op a k ≤ op (iterate_op x L) a
    let n := Nat.findGreatest P K

    have hP0 : P 0 := by
      -- ident ≤ x^L < x^L ⊕ a because a > ident
      have h_id_le : ident ≤ iterate_op x L := by
        cases L with
        | zero => simp [iterate_op_zero]
        | succ L' =>
            -- iterate_op_pos gives strict positivity for positive iterate
            exact le_of_lt (iterate_op_pos x hx _ (Nat.succ_pos _))
      have h_lt : iterate_op x L < op (iterate_op x L) a := by
        have := (op_strictMono_right (iterate_op x L)) ha
        simpa [op_ident_right] using this
      have h_le : ident ≤ op (iterate_op x L) a := le_of_lt (lt_of_le_of_lt h_id_le h_lt)
      simpa [P, iterate_op_zero] using h_le

    -- Maximality facts about n
    have h_cross := findGreatest_crossing (P := P) K hP0
    have hPn : iterate_op a n ≤ op (iterate_op x L) a := h_cross.1
    have hn_le_K : n ≤ K := h_cross.2.1

    -- P K is false by hK, so n < K
    have h_not_PK : ¬ P K := by
      -- If P K held we'd contradict the strict bound hK
      have h_gt : iterate_op a K > op (iterate_op x L) a := by
        have := hK
        -- hK : op (iterate_op x L) a < iterate_op a K
        simpa [gt_iff_lt] using this
      exact not_le_of_gt h_gt

    have hn_lt_K : n < K := lt_of_le_of_ne hn_le_K (by
      intro h_eq
      exact h_not_PK (by simpa [P, h_eq] using hPn))

    -- The next iterate of a jumps above x^L ⊕ a
    have h_not_P_succ : ¬ P (n + 1) :=
      h_cross.2.2 (n + 1) (Nat.lt_succ_self n) (Nat.succ_le_of_lt hn_lt_K)

    have h_crossing :
        iterate_op a n ≤ op (iterate_op x L) a ∧ op (iterate_op x L) a < iterate_op a (n + 1) := by
      refine ⟨hPn, ?_⟩
      exact lt_of_not_ge h_not_P_succ

    -- **REFINED STRATEGY**: Case split on N to determine witness construction
    -- - If N = 1: x < a, which simplifies many bounds
    -- - If N ≥ 2: a ≤ x (by minimality of N), need different approach

    have hL_pos : 0 < L := by
      by_contra h0
      push_neg at h0
      have hL0 : L = 0 := by omega
      subst hL0
      have h_ident_gt : ident > a := by simpa [iterate_op_zero] using hL
      exact (lt_asymm ha h_ident_gt).elim

    -- From gap_dominates at m = L: y^{2L} > x^L ⊕ a
    have h_gap_2L : iterate_op y (2 * L) > op (iterate_op x L) a := by
      conv_lhs => rw [show 2 * L = L + L by omega]
      exact gap_dominates L hL_pos

    -- Case split on N
    -- First, show N ≥ 1 (since x > ident but ident = iterate_op a 0)
    have hN_ge_1 : N ≥ 1 := by
      by_contra h_contra
      push_neg at h_contra
      have hN0 : N = 0 := by omega
      rw [hN0, iterate_op_zero] at hN
      exact absurd hN (not_lt.mpr (le_of_lt hx))

    rcases Nat.lt_or_ge N 2 with hN_small | hN_large

    · -- **Subcase N = 1**: x < a (since N = 1 means x < a^1 = a)
      have hN_eq : N = 1 := by omega
      have hx_lt_a : x < a := by simpa [hN_eq, iterate_op_one] using hN

      -- With x < a, we have x^L < a^L for any L ≥ 1
      have hxL_lt_aL : iterate_op x L < iterate_op a L :=
        iterate_op_strictMono_base L hL_pos x a hx_lt_a

      -- Key: x^L < a^L and y^L > a (from hL), so we can use n = L, m = L
      -- Check: x^L < a^L and a^L ≤ y^L?
      -- From a < y^L and L ≥ 1, we need a^L ≤ y^L
      -- Actually: a < y^L means a^1 < y^L, but a^L vs y^L?

      -- Let's use witnesses (1, L): we need x^L < a^1 = a ≤ y^L
      -- x^L < a? From x < a and L ≥ 1... x^L might exceed a for L ≥ 2!

      -- Better approach: use (L, L) since x^L < a^L and need a^L ≤ y^L
      -- From a < y^L: a^L < (y^L)^L = y^{L²}. Not directly useful.

      -- Alternative: Use (n+1, 2L) but NOW we can prove x^L ≤ a
      -- If L = 1: x^1 = x < a ✓
      -- If L ≥ 2: y^{L-1} ≤ a (minimality of L), and x < y < a^N = a
      --   so x^k < y^k ≤ a for k ≤ L-1... but x^L = x ⊕ x^{L-1}
      --   and x < a, x^{L-1} ≤ a... so x^L ≤ a ⊕ a = a² not a!

      -- KEY INSIGHT: In subcase N=1, use DIFFERENT witnesses!
      -- Since x < a, we have x < a ≤ a^N = a for N=1
      -- And we need x^m < a^n ≤ y^m
      -- Use m = 1, n = 1: x < a ≤ y? We have x < y but need a ≤ y
      -- From h_same: y < a^N = a. So a > y! This CONTRADICTS a ≤ y.

      -- Wait! In Case 2, y < a^N. If N = 1, then y < a.
      -- So: x < y < a. Use witnesses (1, 1): x < a and a ≤ y? NO, a > y!

      -- Hmm, so with N = 1 and Case 2, we have x < y < a.
      -- For separation we need x^m < a^n ≤ y^m.
      -- But if a > y, then a^n > y^n ≥ y^m for appropriate n, m.
      -- So a^n ≤ y^m seems impossible when a > y!

      -- WAIT - this means Case 2 with N = 1 might be IMPOSSIBLE!
      -- Let's check: Case 2 is y < a^N. With N = 1, y < a.
      -- But we also have a < y^L (from bounded_by_iterate on y).
      -- So: y < a < y^L, which means 1 < L (i.e., L ≥ 2).
      -- This is consistent! y < a < y² (for L = 2).

      -- So in subcase N = 1, L ≥ 2:
      -- - x < y < a < y^L
      -- - gap_dominates: y^{L+m} > x^m ⊕ a

      -- Use m = L (so y^{2L} > x^L ⊕ a from gap_dominates)
      -- Need witnesses: x^{?} < a^{?} ≤ y^{?}

      -- Since a < y^L, we have a ≤ y^L (actually a < y^L).
      -- And we need x^m < a for some m.
      -- From x < a (since N = 1), we have x^1 < a. Use m = 1, n = 1:
      -- x < a and a ≤ y^L? Need m = L for upper bound!
      -- So use n = 1, m = L: x^L < a^1 = a ≤ y^L
      -- Need: x^L < a. From x < a... x^L vs a?

      -- For L = 2: x² vs a. We have x < a but x² could be > a.
      -- Example: x = 0.9, a = 1 (additive). x² = 1.8 > 1 = a.

      -- So x^L < a doesn't hold in general!

      -- NEW APPROACH: Use the gap more directly.
      -- From gap_dominates at m = 1: y^{L+1} > x ⊕ a
      -- Find crossing n' for x ⊕ a: a^{n'} ≤ x ⊕ a < a^{n'+1}
      -- Then a^{n'+1} > x ⊕ a.
      -- Need: x^{L+1} < a^{n'+1} ≤ y^{L+1}

      -- For lower: x^{L+1} < a^{n'+1} where a^{n'+1} > x ⊕ a
      --   Need x^{L+1} ≤ x ⊕ a, i.e., x^L ⊕ x ≤ x ⊕ a, i.e., x^L ≤ a (SAME ISSUE!)

      -- Let me try yet another approach: use MUCH larger m
      -- gap_dominates at m = k gives y^{L+k} > x^k ⊕ a
      -- For large k, the gap y^{L+k} - (x^k ⊕ a) grows.
      -- At some point, we can fit multiple iterates of a in the gap.

      -- Actually, the fundamental issue is that x^k grows faster than a^k in some sense
      -- when x is close to a.

      -- Let me try: find M such that x^M < a (if possible).
      -- By Archimedean (op_archimedean), for any y, exists n with y < x^n.
      -- So x^n grows unboundedly, meaning x^M < a for small M, then x^M ≥ a for large M.
      -- Since x < a (N = 1), the minimal M with x^M ≥ a is some M ≥ 2.

      -- Use witnesses based on this M!
      -- Let M be minimal with a ≤ x^M. Then x^{M-1} < a.
      -- M exists because x^n → ∞ and x^1 < a.

      obtain ⟨M, hM_bound, hM_min⟩ : ∃ M : ℕ, a ≤ iterate_op x M ∧
          (M = 0 ∨ iterate_op x (M - 1) < a) := by
        -- Find minimal M with a ≤ x^M using well-founded recursion
        by_cases h0 : a ≤ iterate_op x 0
        · exact ⟨0, h0, Or.inl rfl⟩
        · push_neg at h0
          -- a > ident, so a > x^0. Need to find where x^M catches up.
          -- By Archimedean, ∃ K with a < x^K
          obtain ⟨K, hK⟩ := bounded_by_iterate x hx a
          -- K ≥ 1 since x^0 = ident < a
          have hK_pos : K ≥ 1 := by
            by_contra hK0
            push_neg at hK0
            have hK_eq0 : K = 0 := by omega
            simp [hK_eq0, iterate_op_zero] at hK
            -- hK : a < ident contradicts ha : ident < a
            exact absurd hK (not_lt.mpr (le_of_lt ha))
          -- Now find the minimal M ≤ K with a ≤ x^M
          have : ∃ M ≤ K, a ≤ iterate_op x M ∧ ∀ k < M, iterate_op x k < a := by
            -- Use Nat.find on {m | a ≤ x^m}
            have hex : ∃ m, a ≤ iterate_op x m := ⟨K, le_of_lt hK⟩
            let M := Nat.find hex
            have hM : a ≤ iterate_op x M := Nat.find_spec hex
            have hM_le : M ≤ K := Nat.find_le (le_of_lt hK)
            refine ⟨M, hM_le, hM, fun k hkM => ?_⟩
            exact lt_of_not_ge (Nat.find_min hex hkM)
          obtain ⟨M, _, hM, hM_min'⟩ := this
          have hM_pos : M ≥ 1 := by
            by_contra hM0
            push_neg at hM0
            have hM_eq0 : M = 0 := by omega
            simp [hM_eq0, iterate_op_zero] at hM
            exact not_lt_of_ge hM ha
          exact ⟨M, hM, Or.inr (hM_min' (M - 1) (Nat.sub_lt hM_pos Nat.one_pos))⟩

      rcases hM_min with hM_zero | hM_pred
      · -- M = 0: a ≤ ident, contradicts ha : ident < a
        simp [hM_zero, iterate_op_zero] at hM_bound
        exact absurd hM_bound (not_le_of_gt ha)
      · -- M ≥ 1 and x^{M-1} < a
        -- Now use witnesses involving M
        -- We have: x^{M-1} < a ≤ x^M
        -- And: a < y^L, so a^k < y^{kL}

        -- Strategy: Use m = (M-1) * L and find appropriate n
        -- Actually simpler: use m = L, n based on crossing

        -- From gap_dominates at m = M-1: y^{L + (M-1)} > x^{M-1} ⊕ a
        have h_gap_M : iterate_op y (L + (M - 1)) > op (iterate_op x (M - 1)) a := by
          rcases Nat.eq_zero_or_pos (M - 1) with hMm1_zero | hMm1_pos
          · -- M - 1 = 0, so M = 1, and x^0 = ident
            simp [hMm1_zero, iterate_op_zero, op_ident_left]
            -- Need: y^L > a. We have hL : a < y^L ✓
            exact hL
          · exact gap_dominates (M - 1) hMm1_pos

        -- Find crossing for x^{M-1} ⊕ a
        obtain ⟨K', hK'⟩ := bounded_by_iterate a ha (op (iterate_op x (M - 1)) a)
        let P' : ℕ → Prop := fun k => iterate_op a k ≤ op (iterate_op x (M - 1)) a
        let n' := Nat.findGreatest P' K'

        have hP'0 : P' 0 := by
          simp [P', iterate_op_zero]
          -- Need: ident ≤ x^{M-1} ⊕ a
          -- We have ha : ident < a, so ident < a ≤ a ⊕ x^{M-1} = x^{M-1} ⊕ a (by commutativity)
          -- Actually, just use ident_le: ident ≤ op (iterate_op x (M - 1)) a
          exact ident_le _

        have h_cross' := findGreatest_crossing (P := P') K' hP'0
        have hP'n' : iterate_op a n' ≤ op (iterate_op x (M - 1)) a := h_cross'.1

        have h_not_P'_K' : ¬ P' K' := not_le_of_gt hK'
        have hn'_lt_K' : n' < K' := by
          by_contra h_ge
          push_neg at h_ge
          have hn'_le : n' ≤ K' := h_cross'.2.1
          have hn'_eq : n' = K' := le_antisymm hn'_le h_ge
          have hP'K' : P' K' := by
            have : iterate_op a K' ≤ op (iterate_op x (M - 1)) a := by
              rw [← hn'_eq]; exact hP'n'
            exact this
          exact h_not_P'_K' hP'K'

        have h_not_P'_succ : ¬ P' (n' + 1) :=
          h_cross'.2.2 (n' + 1) (Nat.lt_succ_self n') (Nat.succ_le_of_lt hn'_lt_K')

        -- a^{n'+1} > x^{M-1} ⊕ a
        have h_crossing' : op (iterate_op x (M - 1)) a < iterate_op a (n' + 1) :=
          lt_of_not_ge h_not_P'_succ

        -- Witnesses: (n' + 1, L + (M - 1))
        -- Need: x^{L + (M-1)} < a^{n'+1} ≤ y^{L + (M-1)}

        -- Upper bound: a^{n'+1} ≤ y^{L + (M-1)}
        -- From h_gap_M: y^{L + (M-1)} > x^{M-1} ⊕ a
        -- And h_crossing': a^{n'+1} > x^{M-1} ⊕ a
        -- Both exceed x^{M-1} ⊕ a. Need to compare them.

        -- Key: n' is the LARGEST with a^{n'} ≤ x^{M-1} ⊕ a
        -- So a^{n'} ≤ x^{M-1} ⊕ a < a^{n'+1}
        -- We need a^{n'+1} ≤ y^{L + (M-1)}

        -- From hM_pred: x^{M-1} < a
        -- So x^{M-1} ⊕ a < a ⊕ a = a² (by strict mono)
        -- And a^{n'+1} > x^{M-1} ⊕ a
        -- Also a^{n'} ≤ x^{M-1} ⊕ a < a²
        -- So n' ≤ 1 (since a² = a^2)!
        -- Thus n' ∈ {0, 1} and n' + 1 ∈ {1, 2}

        have hn'_le_1 : n' ≤ 1 := by
          by_contra h_gt
          push_neg at h_gt
          have hn'_ge_2 : n' ≥ 2 := h_gt
          -- a^{n'} ≤ x^{M-1} ⊕ a and n' ≥ 2
          -- a^2 ≤ a^{n'} ≤ x^{M-1} ⊕ a (by monotonicity)
          have h1 : iterate_op a 2 ≤ iterate_op a n' := (iterate_op_strictMono a ha).monotone hn'_ge_2
          have h2 : iterate_op a 2 ≤ op (iterate_op x (M - 1)) a := le_trans h1 hP'n'
          -- a² = a ⊕ a, and x^{M-1} ⊕ a with x^{M-1} < a
          -- So x^{M-1} ⊕ a < a ⊕ a = a²
          have h3 : op (iterate_op x (M - 1)) a < iterate_op a 2 := by
            have h_a2 : iterate_op a 2 = op a a := by
              simp [iterate_op, op_ident_right]
            rw [h_a2]
            exact op_strictMono_left a hM_pred
          exact not_le_of_gt h3 h2

        -- So n' + 1 ≤ 2
        have hn'1_le_2 : n' + 1 ≤ 2 := by omega

        -- Now prove a^{n'+1} ≤ y^{L + (M-1)}
        -- We have a < y^L, so a^2 < (y^L)^2 = y^{2L}
        -- And n' + 1 ≤ 2, so a^{n'+1} ≤ a^2 < y^{2L}
        -- Need: y^{2L} ≤ y^{L + (M-1)}? That's 2L ≤ L + (M-1), i.e., L ≤ M - 1

        -- Hmm, we don't have L ≤ M - 1 in general.

        -- Different approach: a < y^L, so a^{n'+1} < y^{(n'+1)L} ≤ y^{2L}
        -- And we need a^{n'+1} ≤ y^{L + (M-1)}
        -- If (n'+1)L ≤ L + (M-1), i.e., n' * L ≤ M - 1
        -- Since n' ≤ 1 and L ≥ 1, n' * L ≤ L.
        -- Need L ≤ M - 1. Not guaranteed!

        -- ALTERNATIVE: Use different witnesses based on comparison of L and M-1
        rcases le_or_gt L (M - 1) with hL_le_M | hL_gt_M

        · -- Subsubcase: L ≤ M - 1
          -- Use witnesses (n' + 1, L + (M - 1))
          -- Upper bound: a^{n'+1} ≤ y^{L + (M-1)}
          have h_upper' : iterate_op a (n' + 1) ≤ iterate_op y (L + (M - 1)) := by
            -- a < y^L, so a^k < y^{kL} for k ≥ 1
            -- a^{n'+1} < y^{(n'+1)L}
            -- (n'+1)L ≤ 2L ≤ 2(M-1) (if L ≤ M-1)
            -- Need (n'+1)L ≤ L + (M-1)
            -- With n' + 1 ≤ 2: 2L ≤ L + (M-1) iff L ≤ M - 1 ✓
            have h_exp : (n' + 1) * L ≤ L + (M - 1) := by
              have h1 : (n' + 1) * L ≤ 2 * L := Nat.mul_le_mul_right L hn'1_le_2
              have h2 : 2 * L = L + L := by ring
              have h3 : L + L ≤ L + (M - 1) := Nat.add_le_add_left hL_le_M L
              omega
            -- a < y^L implies a^k ≤ y^{kL} for appropriate k
            -- Actually a^k < (y^L)^k = y^{kL}
            have h_aL : iterate_op a 1 < iterate_op y L := by
              rw [iterate_op_one]; exact hL
            -- By repetition: a^{(n'+1)} < y^{(n'+1)L}
            rcases Nat.eq_zero_or_pos (n' + 1) with hn'1_zero | hn'1_pos
            · omega  -- n' + 1 ≠ 0
            · have h_rep := repetition_lemma_lt a y 1 L (n' + 1) hn'1_pos h_aL
              -- a^{(n'+1)*1} < y^{L*(n'+1)}
              simp at h_rep
              -- h_rep : iterate_op a (n' + 1) < iterate_op y (L * (n' + 1))
              -- Need (n' + 1) * L, which equals L * (n' + 1)
              have h_comm : L * (n' + 1) = (n' + 1) * L := Nat.mul_comm L (n' + 1)
              rw [h_comm] at h_rep
              have h_mono := (iterate_op_strictMono y hy).monotone h_exp
              exact le_of_lt (lt_of_lt_of_le h_rep h_mono)

          -- Lower bound: x^{L + (M-1)} < a^{n'+1}
          have hx_lower' : iterate_op x (L + (M - 1)) < iterate_op a (n' + 1) := by
            -- x^{L + (M-1)} = x^L ⊕ x^{M-1}
            -- We have x^{M-1} < a (from hM_pred)
            -- And we're in N=1 case, so x < a, thus x^L < a^L
            -- x^{L + (M-1)} = x^{L-1+M} ... hmm
            -- Actually: x^{L + (M-1)} ≤ x^{M-1} ⊕ x^L
            --   with x^{M-1} < a and x^L < a^L
            -- We need x^{L + (M-1)} < a^{n'+1} where n' + 1 ≤ 2

            -- Key: x^{L + (M-1)} ≤ ? ≤ x^{M-1} ⊕ a < a^{n'+1}
            -- Need x^{L + (M-1)} ≤ x^{M-1} ⊕ a
            -- i.e., x^{M-1} ⊕ x^L ≤ x^{M-1} ⊕ a
            -- i.e., x^L ≤ a

            -- From N = 1: x < a. Does x^L ≤ a?
            -- L is minimal with a < y^L, so y^{L-1} ≤ a (if L ≥ 2)
            -- x < y, so x^{L-1} < y^{L-1} ≤ a (if L ≥ 2)
            -- x^L = x ⊕ x^{L-1} and x < a, x^{L-1} < a (if L ≥ 2)
            -- x^L < a ⊕ a = a² ... not x^L ≤ a directly

            -- BUT WAIT: in N=1 subcase, we also have L ≤ M-1 here.
            -- And M is minimal with a ≤ x^M.
            -- So x^{M-1} < a.
            -- If L ≤ M - 1, then x^L ≤ x^{M-1} < a ✓!
            have hxL_lt_a : iterate_op x L < a := by
              have h_mono := (iterate_op_strictMono x hx).monotone hL_le_M
              calc iterate_op x L ≤ iterate_op x (M - 1) := h_mono
                _ < a := hM_pred

            -- Now: x^{L + (M-1)} = x^L ⊕ x^{M-1}
            -- Use iterate_op_add.symm to rewrite iterate_op x (L + (M-1)) to op (...)
            have h_split : iterate_op x (L + (M - 1)) = op (iterate_op x L) (iterate_op x (M - 1)) :=
              (iterate_op_add x L (M - 1)).symm
            rw [h_split]
            calc op (iterate_op x L) (iterate_op x (M - 1))
                ≤ op (iterate_op x L) a := (op_strictMono_right (iterate_op x L)).monotone
                    (le_of_lt hM_pred)
              _ < op a a := op_strictMono_left a hxL_lt_a
              _ = iterate_op a 2 := by simp [iterate_op, op_ident_right]
              _ ≤ iterate_op a (n' + 1) := by
                  rcases Nat.lt_or_ge (n' + 1) 2 with h_lt | h_ge
                  · -- n' + 1 < 2, so n' + 1 ≤ 1, so n' = 0
                    have hn'0 : n' = 0 := by omega
                    -- Then a^{n'+1} = a^1 = a
                    -- And we showed x^L ⊕ x^{M-1} < a² = a^2
                    -- Need a^2 ≤ a^1 = a? NO!
                    -- Actually this branch should give a^2 ≤ a^{n'+1}
                    -- If n' + 1 = 1, then a^2 ≤ a^1 is FALSE.
                    -- So we need n' + 1 ≥ 2, i.e., n' ≥ 1.

                    -- Let's check: n' is findGreatest with a^{n'} ≤ x^{M-1} ⊕ a
                    -- a^0 = ident ≤ x^{M-1} ⊕ a ✓ (always)
                    -- a^1 = a ≤ x^{M-1} ⊕ a? Yes since a ≤ z ⊕ a for any z ≥ ident
                    -- So n' ≥ 1!
                    have hn'_ge_1 : n' ≥ 1 := by
                      by_contra h_lt_1
                      push_neg at h_lt_1
                      have hn'0' : n' = 0 := by omega
                      -- n' = 0 means findGreatest returned 0
                      -- But P' 1 should hold: a ≤ x^{M-1} ⊕ a
                      have hP'1 : P' 1 := by
                        simp [P', iterate_op_one]
                        -- a ≤ x^{M-1} ⊕ a follows from a = ident ⊕ a ≤ x^{M-1} ⊕ a
                        calc a = op ident a := (op_ident_left a).symm
                          _ ≤ op (iterate_op x (M - 1)) a :=
                              (op_strictMono_left a).monotone (ident_le _)
                      -- findGreatest P' K' = 0 means P' 1 is false (if 1 ≤ K')
                      -- or K' = 0
                      have hK'_pos : K' ≥ 1 := by
                        by_contra hK'0
                        push_neg at hK'0
                        have hK'_eq0 : K' = 0 := by omega
                        simp [hK'_eq0, iterate_op_zero] at hK'
                        -- hK' : x^{M-1} ⊕ a < ident
                        -- But x^{M-1} ⊕ a ≥ a > ident, contradiction
                        have h_pos : iterate_op a 0 < op (iterate_op x (M - 1)) a := by
                          simp [iterate_op_zero]
                          -- ident < a ≤ x^{M-1} ⊕ a
                          calc ident < a := ha
                            _ = op ident a := (op_ident_left a).symm
                            _ ≤ op (iterate_op x (M - 1)) a :=
                                (op_strictMono_left a).monotone (ident_le _)
                        exact not_lt_of_gt hK' h_pos
                      -- With K' ≥ 1 and P' 1 true, findGreatest should return ≥ 1
                      have h_fg : 1 ≤ n' := Nat.le_findGreatest hK'_pos hP'1
                      omega
                    omega
                  · exact (iterate_op_strictMono a ha).monotone h_ge

          have hm_pos' : 0 < L + (M - 1) := by omega
          exact ⟨n' + 1, L + (M - 1), hm_pos', hx_lower', h_upper'⟩


        · -- **Subsubcase: L > M - 1 ⇒ L = M** (reduce to large-regime)
          -- Prove L = M using minimality arguments
          have hL_eq_M : L = M := by
            have hM_le_L : M ≤ L := by omega  -- From M - 1 < L
            have hL_le_M : L ≤ M := by
              -- y^{L-1} ≤ a from minimality of L (proved below)
              -- x < y, so x^{L-1} < y^{L-1} ≤ a
              -- By minimality of M: L - 1 ≤ M - 1
              have hL_ge_2 : L ≥ 2 := by
                by_contra hL_lt_2
                push_neg at hL_lt_2
                have h01 : L = 0 ∨ L = 1 := by omega
                rcases h01 with hL0 | hL1
                · simp [hL0, iterate_op_zero] at hL
                  exact not_lt_of_gt ha hL
                · simp [hL1, iterate_op_one] at hL
                  have : y < a := by simpa [hN_eq, iterate_op_one] using h_same
                  exact not_lt_of_gt this hL
              have hL1_ge1 : L - 1 ≥ 1 := by omega
              have hL1_lt_L : L - 1 < L := by omega
              have h_not_lt : ¬(a < iterate_op y (L - 1)) := hL_min (L - 1) hL1_ge1 hL1_lt_L
              have hyL1_le_a : iterate_op y (L - 1) ≤ a := le_of_not_gt h_not_lt
              have hxL1_lt_yL1 : iterate_op x (L - 1) < iterate_op y (L - 1) :=
                iterate_op_strictMono_base (L - 1) hL1_ge1 x y hxy
              have hxL1_lt_a : iterate_op x (L - 1) < a :=
                lt_of_lt_of_le hxL1_lt_yL1 hyL1_le_a
              -- Prove L ≤ M by contradiction: assume L > M
              by_contra h_gt
              have hM_le_L1 : M ≤ L - 1 := by omega
              have hxM_le_xL1 : iterate_op x M ≤ iterate_op x (L - 1) :=
                (iterate_op_strictMono x hx).monotone hM_le_L1
              have hxM_lt_a : iterate_op x M < a :=
                lt_of_le_of_lt hxM_le_xL1 hxL1_lt_a
              exact not_lt_of_ge hM_bound hxM_lt_a
            omega

          -- Now apply large-regime lemma to (X, Y) = (x^M, y^M)
          -- Since L = M, we have a ≤ x^M < y^M (large regime)
          have hM_ge_2 : M ≥ 2 := by
            by_contra hM_lt_2
            push_neg at hM_lt_2
            have hM_le_1 : M ≤ 1 := by omega
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hM_le_1 with hM_eq_0 | hM_eq_1
            · simp [hM_eq_0, iterate_op_zero] at hM_bound
              exact absurd hM_bound (not_le_of_gt ha)
            · simp [hM_eq_1, iterate_op_one] at hM_bound
              exact absurd hM_bound (not_le_of_gt hx_lt_a)

          let X := iterate_op x M
          let Y := iterate_op y M
          have hXY : X < Y := iterate_op_strictMono_base M (by omega : 0 < M) x y hxy
          have haX : a ≤ X := hM_bound

          obtain ⟨n0, m0, hm0_pos, h_lower0, h_upper0⟩ :=
            exists_power_separation_of_ge a X Y ha hXY haX

          -- Translate back: X^m0 = x^{M*m0}, Y^m0 = y^{M*m0}
          refine ⟨n0, M * m0, Nat.mul_pos (by omega : 0 < M) hm0_pos, ?_, ?_⟩
          · -- x^{M*m0} < a^{n0}
            calc iterate_op x (M * m0)
                = iterate_op (iterate_op x M) m0 := (iterate_op_mul x M m0).symm
              _ = iterate_op X m0 := rfl
              _ < iterate_op a n0 := h_lower0
          · -- a^{n0} ≤ y^{M*m0}
            calc iterate_op a n0
                ≤ iterate_op Y m0 := h_upper0
              _ = iterate_op (iterate_op y M) m0 := rfl
              _ = iterate_op y (M * m0) := iterate_op_mul y M m0

    · -- **Subcase N ≥ 2**: a ≤ x (large regime directly)
      have ha_le_x : a ≤ x := by
        -- N ≥ 2 means x ≥ a^1 = a (by minimality of N)
        by_contra h_gt
        push_neg at h_gt
        -- If a > x, then x < a = a^1, so N ≤ 1
        have hx_lt_a1 : x < iterate_op a 1 := by simpa [iterate_op_one] using h_gt
        have hN_le_1 : N ≤ 1 := N_le_one_of_x_lt_a hN_ge1 hN_min hx_lt_a1
        omega

      exact exists_power_separation_of_ge a x y ha hxy ha_le_x

/-! ## Counterexample: Why L ≤ M-1 witnesses fail when L = M

This theorem proves (with concrete reals) that the witness construction for
L ≤ M-1 is mathematically impossible when L = M, validating the need for
separate large-regime treatment. -/

private theorem counterexample_L_eq_M_witnesses_fail :
  let a : ℝ := 10
  let x : ℝ := 3.5
  let y : ℝ := 3.6
  let _M : ℕ := 3
  let _L : ℕ := 3
  let n : ℕ := 2
  let m : ℕ := 5
  -- Lower bound: m·x < n·a (17.5 < 20) ✓
  (m : ℝ) * x < (n : ℝ) * a ∧
  -- Upper bound: n·a ≤ m·y (20 ≤ 18) FAILS ✗
  ¬((n : ℝ) * a ≤ (m : ℝ) * y) := by
  constructor
  · norm_num  -- Proves 17.5 < 20
  · norm_num  -- Proves ¬(20 ≤ 18)

/-! ## Counterexample: Sublinear Floor Inequality is False

The following shows that in the ℝ additive model, the inequality
`x^{k*L} < a^k` (for large k) is **false** when `a ≤ x` and `L ≥ 1`.

This shows that the specific “floor grows sublinearly” *sub-lemma* is false even in the
additive ℝ model, so any proof that relies on that inequality is invalid. In particular,
this is not a refutation of `KSSeparation`; it just blocks one attempted proof route. -/

/-- **Counterexample**: In ℝ with additive operation, if `a ≤ x` and `L ≥ 1`,
then `x^{k*L} < a^k` is false for all k ≥ 1.

Proof: In additive ℝ, `iterate_op x m = m * x`. The inequality becomes
`(k * L) * x < k * a`, which simplifies to `L * x < a`. But `a ≤ x` and
`L ≥ 1` imply `a ≤ x ≤ L * x`, so `L * x < a` is impossible. -/
private theorem sublinear_floor_impossible :
  ∀ (a x : ℝ) (L : ℕ), 0 ≤ a → a ≤ x → 0 < L →
    ¬ (∃ k : ℕ, k ≥ 1 ∧ (k * L : ℕ) • x < k • a) := by
  intro a x L ha_nonneg hax hL_pos
  push_neg
  intro k hk_pos
  have hk_pos' : (k : ℝ) > 0 := Nat.cast_pos.mpr hk_pos
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hax
  -- (k * L) • x = (k * L) * x and k • a = k * a in ℝ
  simp only [nsmul_eq_mul]
  -- Need: ¬((k * L) * x < k * a)
  -- Equivalently: k * a ≤ (k * L) * x
  have h1 : (k : ℝ) * a ≤ (k : ℝ) * x := mul_le_mul_of_nonneg_left hax (le_of_lt hk_pos')
  have h2 : (k : ℝ) * x ≤ (k * L : ℕ) * x := by
    rw [Nat.cast_mul]
    calc (k : ℝ) * x = (k : ℝ) * 1 * x := by ring
      _ ≤ (k : ℝ) * (L : ℝ) * x := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · exact Nat.one_le_cast.mpr hL_pos
          · exact le_of_lt hk_pos'
        · exact hx_nonneg
  linarith [h1, h2]

/-! ## Typeclass Instance (COMMENTED OUT - IN PROGRESS)

The separation instance is temporarily commented out because the large-regime
case requires a different proof strategy than initially attempted.

The "sublinear floor" approach (trying to prove `x^{k*L} < a^k` for large k)
is mathematically impossible in the intended ℝ model when `a ≤ x`.

The correct approach for large-regime separation uses purely existential witnesses:
define `P m := ∃ n, x^m < a^n ≤ y^m` and show `∃ m, P m` via gap_growth,
without requiring any closed-form formula for m. -/

-- instance instKSSeparation : KSSeparation α where
--   separation {a x y} ha hx hy hxy :=
--     ks_separation_lemma a x y ha hx hy hxy

/-- If we assume the remaining large-regime spec, the full separation typeclass follows. -/
instance instKSSeparation_of_largeRegimeSeparationSpec [LargeRegimeSeparationSpec α] :
    KSSeparation α := by
  classical
  refine ⟨?_⟩
  intro a x y ha hx hy hxy
  exact ks_separation_lemma (a := a) (x := x) (y := y) ha hx hy hxy

/-!
## Large-regime spec as a consequence of full separation

`LargeRegimeSeparationSpec` is (by design) the “large-regime” fragment of `KSSeparation`.
We expose the easy direction as a lemma (not an `instance`) to avoid typeclass cycles. -/

theorem largeRegimeSeparationSpec_of_KSSeparation [KSSeparation α] :
    LargeRegimeSeparationSpec α := by
  classical
  refine ⟨?_⟩
  intro a x y ha hxy hax
  have hx : ident < x := lt_of_lt_of_le ha hax
  have hy : ident < y := lt_of_le_of_lt (ident_le x) hxy
  rcases (KSSeparation.separation (a := a) (x := x) (y := y) ha hx hy hxy) with
    ⟨n, m, hm_pos, hlt, hle⟩
  exact ⟨n, m, hm_pos, hlt, hle⟩

end Mettapedia.ProbabilityTheory.KnuthSkilling
