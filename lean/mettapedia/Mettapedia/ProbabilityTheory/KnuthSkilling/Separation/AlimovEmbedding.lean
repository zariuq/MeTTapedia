/-
# Alimov Embedding Theorem

This file formalizes the Alimov/Fuchs embedding theorem from ordered semigroup theory:

> **Main Theorem (Alimov 1950, Fuchs 1963, Binder 2016)**:
> A totally ordered cancellative semigroup embeds (order-preservingly) into (ℝ, +)
> if and only if it has no anomalous pairs.

## Key Results

1. **Proposition 2.7 (Binder)**: Non-anomalous → Archimedean
2. **Theorem 2.10 (Alimov)**: Non-anomalous → Commutative
3. **Main Embedding**: Non-anomalous + cancellative → embeds in ℝ

## References

- Alimov, N. G. (1950). "On ordered semigroups." Izv. Akad. Nauk SSSR Ser. Mat. 14, 569–576.
- Binder, D. (2016). "Non-Anomalous Semigroups and Real Numbers." arXiv:1607.05997
- Fuchs, L. (1963). "Partially Ordered Algebraic Systems." Pergamon Press.

## Relation to K&S

We have already shown (in `AnomalousPairs.lean`) that `KSSeparation ⇒ NoAnomalousPairs`.
This file provides the converse direction via the embedding: once embedded in ℝ,
separation follows from density of rationals.

-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AlimovEmbedding

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open Separation.AnomalousPairs

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-! ## Preliminary Lemmas -/

/-- The identity element raised to any power is itself the identity. -/
lemma iterate_op_ident (n : ℕ) : iterate_op (ident : α) n = ident := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [iterate_op, ih, op_ident_left]

/-- For a positive element a, iterate_op a m > ident for m > 0. -/
lemma iterate_op_pos_of_pos {a : α} (ha : ident < a) {m : ℕ} (hm : 0 < m) :
    ident < iterate_op a m := by
  cases m with
  | zero => omega
  | succ k =>
    induction k with
    | zero =>
      have h1 : iterate_op a 1 = a := iterate_op_one a
      rw [h1]
      exact ha
    | succ j ih =>
      have ih' := ih (Nat.succ_pos j)
      calc ident < a := ha
        _ = op a ident := (op_ident_right a).symm
        _ < op a (iterate_op a (j + 1)) := op_strictMono_right a ih'
        _ = iterate_op a (j + 2) := rfl

/-! ## Section 1: Archimedean Property from No Anomalous Pairs

Binder's Proposition 2.7: Any non-anomalous semigroup is Archimedean.

**Proof idea**: If S is not Archimedean, there exist positive x, y with y^n < x for all n.
Then x and xy form an anomalous pair. -/

/-- A K&S algebra is Archimedean if for all positive a, b, there exists n with b^n ≥ a.
This is the semigroup-theoretic version (positive elements only). -/
def IsArchimedean (α : Type*) [KnuthSkillingAlgebraBase α] : Prop :=
  ∀ {a b : α}, ident < a → ident < b →
    ∃ n : ℕ, 0 < n ∧ a ≤ iterate_op b n

/-- **Helper for Lemma 2.4**: If yx < xy, then y·x^n < x^n·y for all n ≥ 1.

This captures the key insight that the non-commutativity gap propagates through powers.
When yx < xy, we can "push y past powers of x", each time gaining from the gap. -/
lemma helper_push_y_past_powers {x y : α} (h_order : op y x < op x y) (n : ℕ) (hn : 0 < n) :
    op y (iterate_op x n) < op (iterate_op x n) y := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- Base case: n+1 = 1, so y · x^1 = yx < xy = x^1 · y
      -- iterate_op x 1 = op x (iterate_op x 0) = op x ident = x
      have h1 : iterate_op x 1 = x := iterate_op_one x
      rw [h1]
      exact h_order
    | succ m =>
      -- Inductive case: n+1 = m+2 ≥ 2
      -- y · x^{m+2} = y · (x · x^{m+1})
      --             = (yx) · x^{m+1}        [by assoc]
      --             < (xy) · x^{m+1}        [by h_order]
      --             = x · (y · x^{m+1})     [by assoc]
      --             < x · (x^{m+1} · y)     [by IH]
      --             = x^{m+2} · y           [by assoc]
      have ih_prev : op y (iterate_op x (m + 1)) < op (iterate_op x (m + 1)) y :=
        ih (by omega)
      calc op y (iterate_op x (m + 2))
          = op y (op x (iterate_op x (m + 1))) := rfl
        _ = op (op y x) (iterate_op x (m + 1)) := by rw [← op_assoc]
        _ < op (op x y) (iterate_op x (m + 1)) := op_strictMono_left _ h_order
        _ = op x (op y (iterate_op x (m + 1))) := by rw [op_assoc]
        _ < op x (op (iterate_op x (m + 1)) y) := op_strictMono_right x ih_prev
        _ = op (op x (iterate_op x (m + 1))) y := by rw [← op_assoc]
        _ = op (iterate_op x (m + 2)) y := rfl

/-- **Lemma 2.4 (Binder)**: If xy > yx, then x^n·y^n > (xy)^n for all n ≥ 2.

Intuitively: when x and y don't commute (xy > yx), the "separated" product x^n·y^n
is strictly larger than the "interleaved" product (xy)^n. The non-commutativity
creates a gap that persists at all scales.

Note: For n = 1, both sides equal xy (equality). The strict inequality requires n ≥ 2.

This is the key technical lemma for proving both Archimedean and commutativity.
-/
lemma binder_lemma_2_4 {x y : α} (_hx : ident < x) (_hy : ident < y)
    (h_order : op y x < op x y) (n : ℕ) (hn : 1 < n) :
    iterate_op (op x y) n < op (iterate_op x n) (iterate_op y n) := by
  -- The proof uses strong induction.
  -- For n=2: (xy)^2 = (xy)(xy) = x(yx)y < x(xy)y = x^2y^2 using h_order.
  -- For n=k+1 (k≥2): Use IH and the gap from non-commutativity.

  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega  -- n+1 = 1, but we need n+1 ≥ 2
    | succ m =>
      -- n+1 = m+2, so n = m+1
      -- We need to prove: (xy)^{m+2} < x^{m+2} · y^{m+2}
      cases m with
      | zero =>
        -- Base case: n+1 = 2
        -- (xy)^2 = (xy) · (xy) = x · (yx) · y
        -- x^2 · y^2 = x · (xy) · y
        -- Since yx < xy, we have x(yx)y < x(xy)y
        have h_iter2_x : iterate_op x 2 = op x x := by
          show op x (op x ident) = op x x
          rw [op_ident_right]
        have h_iter2_y : iterate_op y 2 = op y y := by
          show op y (op y ident) = op y y
          rw [op_ident_right]
        have h_iter2_xy : iterate_op (op x y) 2 = op (op x y) (op x y) := by
          show op (op x y) (op (op x y) ident) = op (op x y) (op x y)
          rw [op_ident_right]
        rw [h_iter2_x, h_iter2_y, h_iter2_xy]
        calc op (op x y) (op x y)
            = op x (op (op y x) y) := by rw [op_assoc, ← op_assoc y x y]
          _ < op x (op (op x y) y) := by
              exact op_strictMono_right x (op_strictMono_left y h_order)
          _ = op x (op x (op y y)) := by rw [op_assoc]
          _ = op (op x x) (op y y) := by rw [← op_assoc]
      | succ k =>
        -- Inductive case: m+2 = k+3, so we're proving for n+1 = k+3 ≥ 3
        -- IH gives us: (xy)^{k+2} < x^{k+2} · y^{k+2}
        have ih_prev : iterate_op (op x y) (k + 2) <
            op (iterate_op x (k + 2)) (iterate_op y (k + 2)) := ih (by omega)

        -- Use the helper: y · x^{k+2} < x^{k+2} · y
        have h_helper : op y (iterate_op x (k + 2)) < op (iterate_op x (k + 2)) y :=
          helper_push_y_past_powers h_order (k + 2) (by omega)

        -- (xy)^{k+3} = (xy) · (xy)^{k+2}
        --           < (xy) · (x^{k+2} · y^{k+2})  [by IH]
        --           = x · (y · x^{k+2}) · y^{k+2}  [assoc]
        --           < x · (x^{k+2} · y) · y^{k+2}  [by helper]
        --           = x^{k+3} · y^{k+3}            [assoc]
        calc iterate_op (op x y) (k + 3)
            = op (op x y) (iterate_op (op x y) (k + 2)) := rfl
          _ < op (op x y) (op (iterate_op x (k + 2)) (iterate_op y (k + 2))) := by
              exact op_strictMono_right (op x y) ih_prev
          _ = op x (op y (op (iterate_op x (k + 2)) (iterate_op y (k + 2)))) := by
              rw [op_assoc]
          _ = op x (op (op y (iterate_op x (k + 2))) (iterate_op y (k + 2))) := by
              rw [← op_assoc y]
          _ < op x (op (op (iterate_op x (k + 2)) y) (iterate_op y (k + 2))) := by
              exact op_strictMono_right x (op_strictMono_left (iterate_op y (k + 2)) h_helper)
          _ = op x (op (iterate_op x (k + 2)) (op y (iterate_op y (k + 2)))) := by
              rw [op_assoc]
          _ = op (op x (iterate_op x (k + 2))) (op y (iterate_op y (k + 2))) := by
              rw [← op_assoc]
          _ = op (iterate_op x (k + 3)) (iterate_op y (k + 3)) := rfl

/-- If x and y commute, then y commutes with all powers of x. -/
lemma comm_with_iterate {x y : α} (h_comm : op x y = op y x) (n : ℕ) :
    op y (iterate_op x n) = op (iterate_op x n) y := by
  induction n with
  | zero =>
    simp only [iterate_op_zero, op_ident_right, op_ident_left]
  | succ n ih =>
    -- y ⊕ x^{n+1} = y ⊕ (x ⊕ x^n)
    --             = (y ⊕ x) ⊕ x^n       [assoc]
    --             = (x ⊕ y) ⊕ x^n       [h_comm]
    --             = x ⊕ (y ⊕ x^n)       [assoc]
    --             = x ⊕ (x^n ⊕ y)       [IH]
    --             = (x ⊕ x^n) ⊕ y       [assoc]
    --             = x^{n+1} ⊕ y
    calc op y (iterate_op x (n + 1))
        = op y (op x (iterate_op x n)) := rfl
      _ = op (op y x) (iterate_op x n) := by rw [← op_assoc]
      _ = op (op x y) (iterate_op x n) := by rw [h_comm]
      _ = op x (op y (iterate_op x n)) := by rw [op_assoc]
      _ = op x (op (iterate_op x n) y) := by rw [ih]
      _ = op (op x (iterate_op x n)) y := by rw [← op_assoc]
      _ = op (iterate_op x (n + 1)) y := rfl

/-- When op x y = op y x (local commutativity), we have (xy)^n = x^n·y^n. -/
lemma iterate_op_comm_expand {x y : α} (h_comm : op x y = op y x)
    (n : ℕ) :
    iterate_op (op x y) n = op (iterate_op x n) (iterate_op y n) := by
  induction n with
  | zero =>
    simp only [iterate_op_zero, op_ident_left]
  | succ n ih =>
    -- (xy)^{n+1} = (xy) ⊕ (xy)^n
    --            = (xy) ⊕ (x^n ⊕ y^n)  [by IH]
    --            = x ⊕ (y ⊕ (x^n ⊕ y^n))  [assoc]
    --            = x ⊕ ((y ⊕ x^n) ⊕ y^n)  [assoc]
    --            = x ⊕ ((x^n ⊕ y) ⊕ y^n)  [comm_with_iterate]
    --            = x ⊕ (x^n ⊕ (y ⊕ y^n))  [assoc]
    --            = (x ⊕ x^n) ⊕ (y ⊕ y^n)  [assoc]
    --            = x^{n+1} ⊕ y^{n+1}
    calc iterate_op (op x y) (n + 1)
        = op (op x y) (iterate_op (op x y) n) := rfl
      _ = op (op x y) (op (iterate_op x n) (iterate_op y n)) := by rw [ih]
      _ = op x (op y (op (iterate_op x n) (iterate_op y n))) := by rw [op_assoc]
      _ = op x (op (op y (iterate_op x n)) (iterate_op y n)) := by rw [← op_assoc y]
      _ = op x (op (op (iterate_op x n) y) (iterate_op y n)) := by rw [comm_with_iterate h_comm]
      _ = op x (op (iterate_op x n) (op y (iterate_op y n))) := by rw [op_assoc]
      _ = op (op x (iterate_op x n)) (op y (iterate_op y n)) := by rw [← op_assoc]
      _ = op (iterate_op x (n + 1)) (iterate_op y (n + 1)) := rfl

/-- **Proposition 2.7 (Binder)**: Non-anomalous semigroups are Archimedean.

The proof proceeds by contradiction: if not Archimedean, then there exist positive
elements x, y with y^n < x for all n. Then x and xy form an anomalous pair.
-/
theorem archimedean_of_noAnomalousPairs [NoAnomalousPairs α] : IsArchimedean α := by
  intro a b ha hb
  -- By contradiction: suppose for all n, a > b^n
  by_contra h_not_arch
  push_neg at h_not_arch
  -- h_not_arch : ∀ n, 0 < n → iterate_op b n < a
  -- We'll construct an anomalous pair from this.

  -- Key fact: b < a (take n=1 in h_not_arch)
  have hb_lt_a : b < a := by
    have := h_not_arch 1 Nat.one_pos
    simp only [iterate_op_one] at this
    exact this

  -- Consider c = op a b. We have a < c (since b > ident)
  have hc_gt_a : a < op a b := by
    conv_lhs => rw [← op_ident_right a]
    exact op_strictMono_right a hb

  -- The key inequality: (ab)^n < a^n·b^n < a^{n+1}
  -- Second part: a^n·b^n < a^{n+1} because b^n < a
  have h_key : ∀ n : ℕ, 0 < n →
      op (iterate_op a n) (iterate_op b n) < iterate_op a (n + 1) := by
    intro n hn
    -- a^{n+1} = a^n ⊕ a  (by iterate_op_add with m=n, n=1)
    rw [← iterate_op_add a n 1, iterate_op_one]
    -- Need: a^n ⊕ b^n < a^n ⊕ a
    exact op_strictMono_right (iterate_op a n) (h_not_arch n hn)

  -- Now show that (a, op a b) form an anomalous pair
  have h_anom : AnomalousPair a (op a b) := by
    constructor
    · exact ha  -- ident < a
    constructor
    · exact hc_gt_a  -- a < op a b
    · intro n hn
      constructor
      · -- a^n < (ab)^n: follows from a < ab and strictMono on base
        exact iterate_op_strictMono_base n hn a (op a b) hc_gt_a
      · -- (ab)^n < a^{n+1}: Split on n = 1 vs n ≥ 2
        by_cases hn_eq_1 : n = 1
        · -- Case n = 1: (ab)^1 = ab < a·a = a^2 since b < a
          subst hn_eq_1
          simp only [iterate_op_one]
          have h_iter2_a : iterate_op a 2 = op a a := by
            show op a (op a ident) = op a a; rw [op_ident_right]
          rw [h_iter2_a]
          exact op_strictMono_right a hb_lt_a
        · -- Case n ≥ 2: Split on order of ab vs ba
          have hn_ge_2 : 1 < n := by omega
          rcases lt_trichotomy (op a b) (op b a) with hab_lt | hab_eq | hab_gt
          · -- Subcase: ab < ba
            -- Use: (ab)^n < (ba)^n < b^n·a^n < a^{n+1}
            -- Step 1: (ab)^n < (ba)^n (since ab < ba)
            have h_step1 : iterate_op (op a b) n < iterate_op (op b a) n :=
              iterate_op_strictMono_base n hn (op a b) (op b a) hab_lt
            -- Step 2: (ba)^n < b^n·a^n (by Lemma 2.4 with x=b, y=a, since ba > ab)
            have h_step2 : iterate_op (op b a) n < op (iterate_op b n) (iterate_op a n) :=
              binder_lemma_2_4 hb ha hab_lt n hn_ge_2
            -- Step 3: b^n·a^n < a^{n+1} (since b^n < a)
            have h_bn_lt_a : iterate_op b n < a := h_not_arch n hn
            have h_step3 : op (iterate_op b n) (iterate_op a n) < iterate_op a (n + 1) := by
              -- a^{n+1} = op a (iterate_op a n) by definition
              -- b^n < a → b^n · a^n < a · a^n (by op_strictMono_left)
              exact op_strictMono_left (iterate_op a n) h_bn_lt_a
            exact lt_trans (lt_trans h_step1 h_step2) h_step3
          · -- Subcase: ab = ba (commutative case)
            -- Then (ab)^n = a^n·b^n by iterate_op_comm_expand
            rw [iterate_op_comm_expand hab_eq]
            exact h_key n hn
          · -- Subcase: ab > ba
            -- By Lemma 2.4: (ab)^n < a^n·b^n < a^{n+1}
            have h_lem := binder_lemma_2_4 ha hb hab_gt n hn_ge_2
            exact lt_trans h_lem (h_key n hn)

  -- But NoAnomalousPairs says there are no anomalous pairs!
  exact NoAnomalousPairs.not_anomalous ha hc_gt_a h_anom

/-! ## Section 2: Commutativity from No Anomalous Pairs

Binder's Theorem 2.10 (Alimov's Theorem): Any non-anomalous semigroup is commutative.

This is a beautiful theorem showing that the absence of infinitesimals forces commutativity.
The proof uses the Archimedean property (which we just proved follows from non-anomalous)
and a clever contradiction argument.
-/

/-- **Lemma 2.8 (Binder)**: In an Archimedean semigroup, for positive x > y,
there exists n such that y^{n+1} > x ≥ y^n. -/
lemma exists_iterate_bracket [NoAnomalousPairs α] {x y : α}
    (hy : ident < y) (hxy : y < x) :
    ∃ n : ℕ, 0 < n ∧ iterate_op y n ≤ x ∧ x < iterate_op y (n + 1) := by
  -- Use Archimedean property to bound x above by some y^m
  have h_arch := @archimedean_of_noAnomalousPairs α _ _ x y (lt_trans hy hxy) hy
  rcases h_arch with ⟨m, hm_pos, hm_le⟩
  -- There exists m with x ≤ y^m
  -- Now find the smallest m with x < y^m

  -- First, we know y^1 = y < x (from hxy)
  have hy1_lt : iterate_op y 1 < x := by simp only [iterate_op_one]; exact hxy

  -- Define the predicate for being "above" x
  let P : ℕ → Prop := fun k => x < iterate_op y k

  -- P is decidable (uses Classical)
  have hP_dec : DecidablePred P := fun _ => Classical.dec _

  -- Show there exists some k with P k
  have hP_exists : ∃ k, P k := by
    by_cases h : x < iterate_op y m
    · exact ⟨m, h⟩
    · -- x = y^m (since x ≤ y^m and ¬(x < y^m))
      push_neg at h
      have heq : x = iterate_op y m := le_antisymm hm_le h
      -- Then x < y^{m+1}
      use m + 1
      show x < iterate_op y (m + 1)
      rw [heq]
      exact KnuthSkillingAlgebra.iterate_op_strictMono y hy (Nat.lt_succ_self m)

  -- Find minimum k with P k
  let min_k := Nat.find hP_exists
  have h_min_k_mem : P min_k := Nat.find_spec hP_exists
  have h_min_k_min : ∀ k, P k → min_k ≤ k := fun k hk => Nat.find_min' hP_exists hk

  -- min_k ≥ 2 because P 1 is false (y^1 = y < x, so ¬(x < y^1))
  have h_not_P_0 : ¬P 0 := by
    show ¬(x < iterate_op y 0)
    simp only [iterate_op_zero]
    exact not_lt.mpr (le_of_lt (lt_trans hy hxy))

  have h_not_P_1 : ¬P 1 := by
    show ¬(x < iterate_op y 1)
    simp only [iterate_op_one]
    exact not_lt.mpr (le_of_lt hxy)

  have h_min_k_ge_2 : 2 ≤ min_k := by
    by_contra h
    push_neg at h
    interval_cases min_k
    · exact h_not_P_0 h_min_k_mem
    · exact h_not_P_1 h_min_k_mem

  -- Let n = min_k - 1. Then n ≥ 1 and y^n ≤ x < y^{n+1}
  use min_k - 1
  constructor
  · -- n = min_k - 1 ≥ 1
    omega
  constructor
  · -- y^n ≤ x: Since n = min_k - 1 < min_k, we have ¬P n, i.e., ¬(x < y^n)
    have h_n_lt : min_k - 1 < min_k := by omega
    have h_not_P_n : ¬P (min_k - 1) := Nat.find_min hP_exists h_n_lt
    show iterate_op y (min_k - 1) ≤ x
    exact not_lt.mp h_not_P_n
  · -- x < y^{n+1}: Since n + 1 = min_k, and P min_k
    have h_eq : min_k - 1 + 1 = min_k := by omega
    show x < iterate_op y (min_k - 1 + 1)
    rw [h_eq]
    exact h_min_k_mem

/-- **Lemma 2.9 (Binder)**: If x is positive and y is negative in a non-anomalous semigroup,
then there exists n such that op x (iterate_op y n) is positive.

Actually, this is trivially true with n = 0: x · y^0 = x · ident = x > ident. -/
lemma exists_positive_power {x y : α}
    (hx : ident < x) (_hy : y < ident) :
    ∃ n : ℕ, ident < op x (iterate_op y n) := by
  use 0
  rw [iterate_op_zero, op_ident_right]
  exact hx

/-- **Alimov's Key Identity**: (xy)^{n+1} = x · (yx)^n · y

This is proven by induction using associativity. It's the key to proving commutativity. -/
lemma alimov_identity {x y : α} (n : ℕ) :
    iterate_op (op x y) (n + 1) = op x (op (iterate_op (op y x) n) y) := by
  induction n with
  | zero =>
    -- (xy)^1 = x · (yx)^0 · y = x · ident · y = x · y = xy ✓
    have h1 : iterate_op (op x y) 1 = op x y := iterate_op_one (op x y)
    have h0 : iterate_op (op y x) 0 = ident := iterate_op_zero (op y x)
    rw [h1, h0, op_ident_left]
  | succ k ih =>
    -- (xy)^{k+2} = (xy) · (xy)^{k+1}
    --            = (xy) · [x · (yx)^k · y]  [by IH]
    --            = x · (y · x · (yx)^k · y)  [by assoc]
    --            = x · ((yx) · (yx)^k · y)  [by assoc]
    --            = x · (((yx) · (yx)^k) · y)  [by assoc]
    --            = x · (yx)^{k+1} · y
    calc iterate_op (op x y) (k + 2)
        = op (op x y) (iterate_op (op x y) (k + 1)) := rfl
      _ = op (op x y) (op x (op (iterate_op (op y x) k) y)) := by rw [ih]
      _ = op x (op y (op x (op (iterate_op (op y x) k) y))) := by rw [op_assoc]
      _ = op x (op (op y x) (op (iterate_op (op y x) k) y)) := by rw [← op_assoc y x _]
      _ = op x (op (op (op y x) (iterate_op (op y x) k)) y) := by
          rw [← op_assoc (op y x) (iterate_op (op y x) k) y]
      _ = op x (op (iterate_op (op y x) (k + 1)) y) := rfl

/-- **Negative Anomalous Pair Construction** (adapted from Eric Luap's OrderedSemigroups).

For negative x, y with xy < yx, we show (yx, xy) forms a negative anomalous pair.
The key chain is:
  (xy)^n > (xy)^n · x    -- multiplying by negative x on right decreases
        > y · (xy)^n · x  -- multiplying by negative y on left decreases more
        = (yx)^{n+1}      -- by Alimov's identity (reversed)

Combined with (yx)^n < (xy)^n (from yx > xy and iteration), this gives the negative
anomalous pair structure. -/
lemma neg_not_comm_neg_anomalous_pair {x y : α}
    (hx : x < ident) (hy : y < ident) (h_order : op x y < op y x) :
    NegAnomalousPair (op y x) (op x y) := by
  -- First establish that yx > xy (given) and both products are negative
  have h_xy_neg : op x y < ident := by
    calc op x y < op x ident := op_strictMono_right x hy
      _ = x := op_ident_right x
      _ < ident := hx
  have h_yx_neg : op y x < ident := by
    calc op y x < op y ident := op_strictMono_right y hx
      _ = y := op_ident_right y
      _ < ident := hy
  -- Structure: yx > xy and yx < ident
  refine ⟨h_order, h_yx_neg, ?_⟩
  intro n hn
  constructor
  · -- (xy)^n < (yx)^n : follows from xy < yx and strict mono of iteration
    exact iterate_op_strictMono_base n h_order hn
  · -- (yx)^{n+1} < (xy)^n : the key chain argument
    -- Using Alimov identity: (yx)^{n+1} = y · (xy)^n · x
    have h_identity : iterate_op (op y x) (n + 1) = op y (op (iterate_op (op x y) n) x) :=
      alimov_identity n
    rw [h_identity]
    -- Now: y · (xy)^n · x < (xy)^n via two applications of neg decreasing
    calc op y (op (iterate_op (op x y) n) x)
        < op (iterate_op (op x y) n) x := op_left_neg_lt hy
      _ < iterate_op (op x y) n := op_right_neg_lt hx

/-- **Alimov's Theorem 3 (Commutativity)**: In a non-anomalous semigroup,
if xy < yx with both x, y positive, then (xy, yx) form an anomalous pair.

The proof uses the identity: (xy)^{n+1} = x · (yx)^n · y > (yx)^n
since x, y > ident. This gives (yx)^n < (xy)^{n+1}, the anomalous pair condition. -/
lemma comm_of_positive [NoAnomalousPairs α] {x y : α}
    (hx : ident < x) (hy : ident < y) :
    op x y = op y x := by
  -- By contradiction: assume xy ≠ yx
  by_contra h_not_comm
  -- WLOG: assume xy < yx (otherwise swap x and y)
  rcases lt_trichotomy (op x y) (op y x) with h_lt | h_eq | h_gt
  · -- Case: xy < yx
    -- xy is positive (since x, y > ident)
    have h_xy_pos : ident < op x y := by
      calc ident < x := hx
        _ = op x ident := (op_ident_right x).symm
        _ < op x y := op_strictMono_right x hy

    -- We'll show (xy, yx) form an anomalous pair, contradicting NoAnomalousPairs
    have h_anom : AnomalousPair (op x y) (op y x) := by
      constructor
      · exact h_xy_pos  -- ident < xy
      constructor
      · exact h_lt  -- xy < yx
      · -- For all n > 0: (xy)^n < (yx)^n < (xy)^{n+1}
        intro n hn
        constructor
        · -- (xy)^n < (yx)^n: follows from xy < yx
          exact iterate_op_strictMono_base n hn _ _ h_lt
        · -- (yx)^n < (xy)^{n+1}: use Alimov's identity
          -- (xy)^{n+1} = x · (yx)^n · y > (yx)^n since x, y > ident
          rw [alimov_identity]
          -- Need: (yx)^n < x · (yx)^n · y
          calc iterate_op (op y x) n
              = op ident (iterate_op (op y x) n) := (op_ident_left _).symm
            _ < op x (iterate_op (op y x) n) := op_strictMono_left _ hx
            _ = op x (op (iterate_op (op y x) n) ident) := by rw [op_ident_right]
            _ < op x (op (iterate_op (op y x) n) y) := op_strictMono_right x (op_strictMono_right _ hy)

    -- But NoAnomalousPairs says no anomalous pairs exist!
    exact NoAnomalousPairs.not_anomalous h_xy_pos h_lt h_anom

  · exact absurd h_eq h_not_comm

  · -- Case: xy > yx (i.e., yx < xy)
    -- By symmetry, swap x and y
    have h_yx_pos : ident < op y x := by
      calc ident < y := hy
        _ = op y ident := (op_ident_right y).symm
        _ < op y x := op_strictMono_right y hx

    have h_anom : AnomalousPair (op y x) (op x y) := by
      constructor
      · exact h_yx_pos
      constructor
      · exact h_gt  -- yx < xy
      · intro n hn
        constructor
        · exact iterate_op_strictMono_base n hn _ _ h_gt
        · -- (xy)^n < (yx)^{n+1} = y · (xy)^n · x > (xy)^n
          rw [alimov_identity]
          calc iterate_op (op x y) n
              = op ident (iterate_op (op x y) n) := (op_ident_left _).symm
            _ < op y (iterate_op (op x y) n) := op_strictMono_left _ hy
            _ = op y (op (iterate_op (op x y) n) ident) := by rw [op_ident_right]
            _ < op y (op (iterate_op (op x y) n) x) := op_strictMono_right y (op_strictMono_right _ hx)

    exact NoAnomalousPairs.not_anomalous h_yx_pos h_gt h_anom

/-- **Theorem 2.10 (Alimov)**: Non-anomalous semigroups are commutative.

**Positive case** (proven above as `comm_of_positive`):
For positive x, y > ident, if xy ≠ yx we construct an anomalous pair using Alimov's identity.

**Negative and mixed cases**:
In the standard literature (Alimov 1950, Binder 2016), commutativity of negative elements
follows FROM the embedding theorem, not before it. The approach is:
1. Prove commutativity of positive elements (done via `comm_of_positive`)
2. Build the embedding θ: S → ℝ using only positive element properties
3. Since ℝ is commutative and θ is injective, S must be commutative

**Current proof status**:
- Positive case: DONE (`comm_of_positive`)
- Mixed sign (x<0<y) with xy>0: DONE (reduces to positive case via Alimov's argument)
- Mixed sign (x<0<y) with xy=0: DONE (implies yx=0 by cancellation)
- Mixed sign (x<0<y) with xy<0: TODO (blocked on embedding)
- Both negative: TODO (blocked on Archimedean lifting infrastructure)

The remaining cases can be resolved once the embedding theorem is established,
since ℝ is commutative and the embedding is injective.
-/
theorem comm_of_noAnomalousPairs [NoAnomalousPairs α] :
    ∀ x y : α, op x y = op y x := by
  intro x y
  -- Handle cases based on whether x, y are positive, negative, or ident
  rcases lt_trichotomy x ident with hx_neg | hx_eq | hx_pos
  · -- x < ident (negative)
    rcases lt_trichotomy y ident with hy_neg | hy_eq | hy_pos
    · -- Both negative: use negative anomalous pair construction (Eric Luap's approach)
      -- If x, y < ident and xy ≠ yx, we construct a NegAnomalousPair.
      -- This requires NoNegAnomalousPairs to derive contradiction.
      by_cases h_exists_pos : ∃ base : α, ident < base
      · rcases h_exists_pos with ⟨base, h_base⟩
        -- Derive NoNegAnomalousPairs from NoAnomalousPairs + existence of positive element
        haveI h_no_neg_anom := NoAnomalousPairs.noNegAnomalousPairs_of_noAnomalousPairs ⟨base, h_base⟩

        -- Now use trichotomy on xy vs yx
        rcases lt_trichotomy (op x y) (op y x) with h_lt | h_eq | h_gt
        · -- Case xy < yx: construct NegAnomalousPair (yx, xy)
          have h_anom : NegAnomalousPair (op y x) (op x y) :=
            neg_not_comm_neg_anomalous_pair hx_neg hy_neg h_lt
          -- This contradicts NoNegAnomalousPairs
          have h_yx_neg : op y x < ident := by
            calc op y x < op y ident := op_strictMono_right y hx_neg
              _ = y := op_ident_right y
              _ < ident := hy_neg
          exact absurd h_anom (NoNegAnomalousPairs.not_neg_anomalous h_lt h_yx_neg)
        · exact h_eq
        · -- Case yx < xy: construct NegAnomalousPair (xy, yx)
          have h_anom : NegAnomalousPair (op x y) (op y x) :=
            neg_not_comm_neg_anomalous_pair hy_neg hx_neg h_gt
          -- This contradicts NoNegAnomalousPairs
          have h_xy_neg : op x y < ident := by
            calc op x y < op x ident := op_strictMono_right x hy_neg
              _ = x := op_ident_right x
              _ < ident := hx_neg
          exact absurd h_anom (NoNegAnomalousPairs.not_neg_anomalous h_gt h_xy_neg)
      · -- No positive elements: algebra is trivial (all elements = ident)
        push_neg at h_exists_pos
        have hx_eq : x = ident := le_antisymm (h_exists_pos x) (ident_le x)
        have hy_eq : y = ident := le_antisymm (h_exists_pos y) (ident_le y)
        simp only [hx_eq, hy_eq, op_ident_left]
    · -- y = ident
      subst hy_eq
      rw [op_ident_right, op_ident_left]
    · -- x negative, y positive (Alimov page 573, case 3)
      -- Key insight: if xy > ident, then yx > ident as well, reducing to positive case
      by_cases h_xy : op x y = ident
      · -- Case: xy = ident
        -- Then x + (yx) = x, so yx = ident, hence xy = yx
        have h1 : op x (op y x) = x := by
          calc op x (op y x) = op (op x y) x := by rw [op_assoc]
            _ = op ident x := by rw [h_xy]
            _ = x := op_ident_left x
        -- From x + (yx) = x and strict mono, yx = ident
        have h_yx : op y x = ident := by
          by_contra h_ne
          rcases lt_trichotomy (op y x) ident with h_lt | h_eq | h_gt
          · have : op x (op y x) < op x ident := op_strictMono_right x h_lt
            rw [op_ident_right, h1] at this
            exact lt_irrefl x this
          · exact h_ne h_eq
          · have : op x ident < op x (op y x) := op_strictMono_right x h_gt
            rw [op_ident_right, h1] at this
            exact lt_irrefl x this
        rw [h_xy, h_yx]
      · -- Case: xy ≠ ident
        rcases lt_trichotomy (op x y) ident with h_xy_neg | h_xy_eq | h_xy_pos
        · -- xy < ident: First show yx < ident, then use negative case
          -- Key lemma: if xy < ident < yx, we get contradiction via associativity
          -- y(xy) = (yx)y by assoc, but y(xy) < y (since xy < ident) and (yx)y > y (if yx > ident)
          have h_yx_neg : op y x < ident := by
            by_contra h_not
            push_neg at h_not
            rcases lt_or_eq_of_le h_not with h_gt | h_eq
            · -- yx > ident: derive contradiction via associativity
              -- y(xy) = (yx)y
              have h_assoc : op y (op x y) = op (op y x) y := by
                rw [← op_assoc]
              -- y(xy) < y since xy < ident
              have h1 : op y (op x y) < y := by
                calc op y (op x y) < op y ident := op_strictMono_right y h_xy_neg
                  _ = y := op_ident_right y
              -- (yx)y > y since yx > ident
              have h2 : op (op y x) y > y := by
                calc op (op y x) y > op ident y := op_strictMono_left y h_gt
                  _ = y := op_ident_left y
              -- But y(xy) = (yx)y, so y > y, contradiction
              rw [h_assoc] at h1
              exact lt_asymm h1 h2
            · -- yx = ident: similar argument
              -- y(xy) < y but (yx)y = y
              have h_assoc : op y (op x y) = op (op y x) y := by rw [← op_assoc]
              have h1 : op y (op x y) < y := by
                calc op y (op x y) < op y ident := op_strictMono_right y h_xy_neg
                  _ = y := op_ident_right y
              rw [h_assoc, h_eq, op_ident_left] at h1
              exact lt_irrefl y h1
          -- Now both xy and yx are negative, use the negative commutativity case
          -- We need NoNegAnomalousPairs
          by_cases h_exists_pos' : ∃ base : α, ident < base
          · rcases h_exists_pos' with ⟨base, h_base⟩
            haveI h_no_neg_anom := NoAnomalousPairs.noNegAnomalousPairs_of_noAnomalousPairs ⟨base, h_base⟩
            -- xy and yx are both negative
            rcases lt_trichotomy (op x y) (op y x) with h_lt | h_eq' | h_gt
            · -- xy < yx: construct NegAnomalousPair (yx, xy)
              have h_anom : NegAnomalousPair (op y x) (op x y) :=
                neg_not_comm_neg_anomalous_pair h_xy_neg h_yx_neg h_lt
              exact absurd h_anom (NoNegAnomalousPairs.not_neg_anomalous h_lt h_yx_neg)
            · exact h_eq'
            · -- yx < xy: construct NegAnomalousPair (xy, yx)
              have h_anom : NegAnomalousPair (op x y) (op y x) :=
                neg_not_comm_neg_anomalous_pair h_yx_neg h_xy_neg h_gt
              exact absurd h_anom (NoNegAnomalousPairs.not_neg_anomalous h_gt h_xy_neg)
          · -- No positive elements: trivial
            push_neg at h_exists_pos'
            have hy_eq : y = ident := le_antisymm (h_exists_pos' y) (ident_le y)
            exact absurd hy_eq (ne_of_gt hy_pos)
        · exact absurd h_xy_eq h_xy
        · -- xy > ident: Alimov's main argument (page 573)
          -- Step 1: Show yx > ident as well
          -- From (xy)(xy) > xy, we get x(yx)y > xy
          -- This implies (yx)y > y, hence yx > ident
          have h_yx_pos : ident < op y x := by
            -- (xy)(xy) > xy since xy > 0
            have h_2xy_gt : op x y < op (op x y) (op x y) := by
              calc op x y = op (op x y) ident := (op_ident_right _).symm
                _ < op (op x y) (op x y) := op_strictMono_right _ h_xy_pos
            -- Rewrite (xy)(xy) = x(yx)y
            have h_rewrite : op (op x y) (op x y) = op x (op (op y x) y) := by
              calc op (op x y) (op x y)
                  = op (op (op x y) x) y := by rw [← op_assoc]
                _ = op (op x (op y x)) y := by rw [op_assoc x y x]
                _ = op x (op (op y x) y) := by rw [op_assoc]
            -- So xy < x((yx)y)
            rw [h_rewrite] at h_2xy_gt
            -- By cancellation: y < (yx)y
            have h_y_lt : y < op (op y x) y := by
              by_contra h_not
              push_neg at h_not
              rcases lt_or_eq_of_le h_not with h_lt | h_eq
              · -- (yx)y < y implies x((yx)y) < xy (by mono), contradiction
                have : op x (op (op y x) y) < op x y := op_strictMono_right x h_lt
                exact lt_asymm h_2xy_gt this
              · -- (yx)y = y implies x((yx)y) = xy, but xy < x((yx)y)
                rw [h_eq] at h_2xy_gt
                exact lt_irrefl _ h_2xy_gt
            -- From y < (yx)y and y > ident, we get yx > ident
            by_contra h_not
            push_neg at h_not
            rcases lt_or_eq_of_le h_not with h_lt | h_eq
            · -- yx < ident implies (yx)y < y (by mono), contradiction
              have : op (op y x) y < op ident y := op_strictMono_left y h_lt
              rw [op_ident_left] at this
              exact lt_asymm h_y_lt this
            · -- yx = ident implies (yx)y = y, but y < (yx)y
              rw [h_eq, op_ident_left] at h_y_lt
              exact lt_irrefl y h_y_lt
          -- Step 2: Both (yx) and y positive, so (yx)y = y(yx)
          have h_comm : op (op y x) y = op y (op y x) :=
            comm_of_positive h_yx_pos hy_pos
          -- Step 3: Show xy = yx by contradiction
          by_contra h_ne
          rcases lt_trichotomy (op x y) (op y x) with h_lt | h_eq | h_gt
          · -- Case xy < yx: derive 2(xy) < 2(xy)
            -- 2(xy) < (xy)(yx) = x(y(yx)) = x((yx)y) = x(yx)y = (xy)(xy) = 2(xy)
            have h_chain : op (op x y) (op y x) = op (op x y) (op x y) := by
              calc op (op x y) (op y x)
                  = op x (op y (op y x)) := by rw [op_assoc]
                _ = op x (op (op y x) y) := by rw [← h_comm]
                _ = op (op x (op y x)) y := by rw [← op_assoc]
                _ = op (op (op x y) x) y := by rw [op_assoc x y x]
                _ = op (op x y) (op x y) := by rw [← op_assoc]
            have : op (op x y) (op x y) < op (op x y) (op y x) :=
              op_strictMono_right _ h_lt
            rw [h_chain] at this
            exact lt_irrefl _ this
          · exact h_ne h_eq
          · -- Case xy > yx (i.e., h_gt : yx < xy): derive contradiction
            -- Since xy and yx are both positive, they commute: (xy)(yx) = (yx)(xy)
            have h_comm2 : op (op x y) (op y x) = op (op y x) (op x y) :=
              comm_of_positive h_xy_pos h_yx_pos
            -- The key chain: (xy)(yx) = 2(xy)
            have h_chain : op (op x y) (op y x) = op (op x y) (op x y) := by
              calc op (op x y) (op y x)
                  = op x (op y (op y x)) := by rw [op_assoc]
                _ = op x (op (op y x) y) := by rw [← h_comm]
                _ = op (op x (op y x)) y := by rw [← op_assoc]
                _ = op (op (op x y) x) y := by rw [op_assoc x y x]
                _ = op (op x y) (op x y) := by rw [← op_assoc]
            -- From h_gt (yx < xy) and h_comm2: (xy)(yx) = (yx)(xy) < (xy)(xy)
            -- But h_chain says (xy)(yx) = (xy)(xy), contradiction!
            have h_contra : op (op x y) (op y x) < op (op x y) (op x y) := by
              calc op (op x y) (op y x)
                  = op (op y x) (op x y) := h_comm2
                _ < op (op x y) (op x y) := op_strictMono_left (op x y) h_gt
            rw [h_chain] at h_contra
            exact lt_irrefl _ h_contra
  · -- x = ident
    subst hx_eq
    rw [op_ident_left, op_ident_right]
  · -- x > ident (positive)
    rcases lt_trichotomy y ident with hy_neg | hy_eq | hy_pos
    · -- x positive, y negative (symmetric to x negative, y positive)
      -- By symmetry, swap roles of x and y in the proof
      by_cases h_yx : op y x = ident
      · -- Case: yx = ident, show xy = ident
        have h1 : op y (op x y) = y := by
          calc op y (op x y) = op (op y x) y := by rw [op_assoc]
            _ = op ident y := by rw [h_yx]
            _ = y := op_ident_left y
        have h_xy : op x y = ident := by
          by_contra h_ne
          rcases lt_trichotomy (op x y) ident with h_lt | h_eq | h_gt
          · have : op y (op x y) < op y ident := op_strictMono_right y h_lt
            rw [op_ident_right, h1] at this
            exact lt_irrefl y this
          · exact h_ne h_eq
          · have : op y ident < op y (op x y) := op_strictMono_right y h_gt
            rw [op_ident_right, h1] at this
            exact lt_irrefl y this
        rw [h_xy, h_yx]
      · -- Case: yx ≠ ident
        rcases lt_trichotomy (op y x) ident with h_yx_neg | h_yx_eq | h_yx_pos
        · -- yx < ident: First show xy < ident, then use negative case (symmetric to above)
          -- Key: if yx < ident < xy, we get contradiction via associativity
          have h_xy_neg : op x y < ident := by
            by_contra h_not
            push_neg at h_not
            rcases lt_or_eq_of_le h_not with h_gt | h_eq
            · -- xy > ident: derive contradiction
              -- x(yx) = (xy)x by assoc
              have h_assoc : op x (op y x) = op (op x y) x := by rw [← op_assoc]
              -- x(yx) < x since yx < ident
              have h1 : op x (op y x) < x := by
                calc op x (op y x) < op x ident := op_strictMono_right x h_yx_neg
                  _ = x := op_ident_right x
              -- (xy)x > x since xy > ident
              have h2 : op (op x y) x > x := by
                calc op (op x y) x > op ident x := op_strictMono_left x h_gt
                  _ = x := op_ident_left x
              rw [h_assoc] at h1
              exact lt_asymm h1 h2
            · -- xy = ident: similar
              have h_assoc : op x (op y x) = op (op x y) x := by rw [← op_assoc]
              have h1 : op x (op y x) < x := by
                calc op x (op y x) < op x ident := op_strictMono_right x h_yx_neg
                  _ = x := op_ident_right x
              rw [h_assoc, h_eq, op_ident_left] at h1
              exact lt_irrefl x h1
          -- Both xy and yx are negative
          by_cases h_exists_pos' : ∃ base : α, ident < base
          · rcases h_exists_pos' with ⟨base, h_base⟩
            haveI h_no_neg_anom := NoAnomalousPairs.noNegAnomalousPairs_of_noAnomalousPairs ⟨base, h_base⟩
            rcases lt_trichotomy (op x y) (op y x) with h_lt | h_eq' | h_gt
            · -- xy < yx: construct NegAnomalousPair (yx, xy)
              have h_anom : NegAnomalousPair (op y x) (op x y) :=
                neg_not_comm_neg_anomalous_pair h_xy_neg h_yx_neg h_lt
              exact absurd h_anom (NoNegAnomalousPairs.not_neg_anomalous h_lt h_yx_neg)
            · exact h_eq'
            · -- yx < xy: construct NegAnomalousPair (xy, yx)
              have h_anom : NegAnomalousPair (op x y) (op y x) :=
                neg_not_comm_neg_anomalous_pair h_yx_neg h_xy_neg h_gt
              exact absurd h_anom (NoNegAnomalousPairs.not_neg_anomalous h_gt h_xy_neg)
          · -- No positive elements but x > ident: contradiction
            push_neg at h_exists_pos'
            have hx_eq : x = ident := le_antisymm (h_exists_pos' x) (ident_le x)
            exact absurd hx_eq (ne_of_gt hx_pos)
        · exact absurd h_yx_eq h_yx
        · -- yx > ident: Alimov's main argument (symmetric)
          -- Step 1: Show xy > ident as well
          have h_xy_pos : ident < op x y := by
            -- (yx)(yx) > yx since yx > 0
            have h_2yx_gt : op y x < op (op y x) (op y x) := by
              calc op y x = op (op y x) ident := (op_ident_right _).symm
                _ < op (op y x) (op y x) := op_strictMono_right _ h_yx_pos
            -- Rewrite (yx)(yx) = y(xy)x
            have h_rewrite : op (op y x) (op y x) = op y (op (op x y) x) := by
              calc op (op y x) (op y x)
                  = op (op (op y x) y) x := by rw [← op_assoc]
                _ = op (op y (op x y)) x := by rw [op_assoc y x y]
                _ = op y (op (op x y) x) := by rw [op_assoc]
            rw [h_rewrite] at h_2yx_gt
            -- By cancellation: x < (xy)x
            have h_x_lt : x < op (op x y) x := by
              by_contra h_not
              push_neg at h_not
              rcases lt_or_eq_of_le h_not with h_lt | h_eq
              · have : op y (op (op x y) x) < op y x := op_strictMono_right y h_lt
                exact lt_asymm h_2yx_gt this
              · rw [h_eq] at h_2yx_gt
                exact lt_irrefl _ h_2yx_gt
            -- From x < (xy)x and x > ident, we get xy > ident
            by_contra h_not
            push_neg at h_not
            rcases lt_or_eq_of_le h_not with h_lt | h_eq
            · have : op (op x y) x < op ident x := op_strictMono_left x h_lt
              rw [op_ident_left] at this
              exact lt_asymm h_x_lt this
            · rw [h_eq, op_ident_left] at h_x_lt
              exact lt_irrefl x h_x_lt
          -- Step 2: Both xy and x positive, so (xy)x = x(xy)
          have h_comm : op (op x y) x = op x (op x y) :=
            comm_of_positive h_xy_pos hx_pos
          -- Step 3: Show xy = yx by contradiction
          by_contra h_ne
          rcases lt_trichotomy (op x y) (op y x) with h_lt | h_eq | h_gt
          · -- Case xy < yx: derive contradiction via chain
            -- Chain: (yx)(xy) = 2(yx) (symmetric to other case)
            have h_chain : op (op y x) (op x y) = op (op y x) (op y x) := by
              calc op (op y x) (op x y)
                  = op y (op x (op x y)) := by rw [op_assoc]
                _ = op y (op (op x y) x) := by rw [← h_comm]
                _ = op (op y (op x y)) x := by rw [← op_assoc]
                _ = op (op (op y x) y) x := by rw [op_assoc y x y]
                _ = op (op y x) (op y x) := by rw [← op_assoc]
            -- From xy < yx: (yx)(xy) < (yx)(yx) = 2(yx)
            -- But h_chain says (yx)(xy) = 2(yx), contradiction!
            have h_strict : op (op y x) (op x y) < op (op y x) (op y x) :=
              op_strictMono_right (op y x) h_lt
            rw [h_chain] at h_strict
            exact lt_irrefl _ h_strict
          · exact h_ne h_eq
          · -- Case xy > yx (i.e., h_gt : yx < xy): derive contradiction
            have h_comm2 : op (op x y) (op y x) = op (op y x) (op x y) :=
              comm_of_positive h_xy_pos h_yx_pos
            have h_chain : op (op y x) (op x y) = op (op y x) (op y x) := by
              calc op (op y x) (op x y)
                  = op y (op x (op x y)) := by rw [op_assoc]
                _ = op y (op (op x y) x) := by rw [← h_comm]
                _ = op (op y (op x y)) x := by rw [← op_assoc]
                _ = op (op (op y x) y) x := by rw [op_assoc y x y]
                _ = op (op y x) (op y x) := by rw [← op_assoc]
            -- From yx < xy: 2(yx) < (xy)(yx) = (yx)(xy) = 2(yx), contradiction
            have h_contra : op (op y x) (op y x) < op (op y x) (op y x) := by
              calc op (op y x) (op y x)
                  < op (op x y) (op y x) := op_strictMono_left (op y x) h_gt
                _ = op (op y x) (op x y) := h_comm2
                _ = op (op y x) (op y x) := h_chain
            exact lt_irrefl _ h_contra
    · -- y = ident
      subst hy_eq
      rw [op_ident_right, op_ident_left]
    · -- Both positive: the main case
      exact comm_of_positive hx_pos hy_pos

/-! ## Section 3: The Embedding Theorem

With Archimedean and commutativity established, we can now state the main embedding theorem.

The construction uses Dedekind cuts: for each element a, we define its "cut" in ℚ
as the set of rationals m/n where a^m ≤ (base)^n. This defines a real number.
-/

/-- The embedding function from a non-anomalous semigroup to ℝ.

Given a base element e > ident, we map each element a to the real number
representing the "ratio" of a to e in the Archimedean sense.

**Definition**: θ(a) = sup { m/n : base^m ≤ a^n, n > 0 }

This measures "how many copies of base fit into a^n, divided by n".
- θ(ident) = 0 (since base^m ≤ ident only when m = 0)
- θ(base) = 1 (since base^m ≤ base^n iff m ≤ n)
- θ(a) < θ(b) when a < b (order preserving)
- θ(a·b) = θ(a) + θ(b) (homomorphism)
-/
noncomputable def embeddingToReal [NoAnomalousPairs α] (base : α) (_h_base : ident < base) :
    α → ℝ := fun a =>
  -- Use the Archimedean property to define the supremum
  -- The set { m/n : base^m ≤ a^n } is bounded (by Archimedean) and nonempty (0/1 ∈ it)
  sSup { (m : ℝ) / n | (m : ℕ) (n : ℕ) (_hn : 0 < n)
    (_h : iterate_op base m ≤ iterate_op a n) }

/-- The embedding preserves order.

**Proof strategy** (Binder Theorem 3.1):
1. θ(x) = sup { m/n : base^m ≤ x^n }
2. θ(y) = sup { m/n : base^m ≤ y^n }
3. Since x < y, if base^m ≤ x^n then base^m ≤ x^n < y^n, so θ(x)'s set ⊆ θ(y)'s set
4. For strict inequality: by Archimedean property, ∃ m,n with x^n < base^m ≤ y^n
5. Then m/n ∈ θ(y)'s set but m/n ∉ θ(x)'s set, so θ(x) < θ(y)

The key insight is that NoAnomalousPairs → Archimedean (Prop 2.7), which provides
the "separating rational" between any two distinct elements.
-/
theorem embeddingToReal_strictMono [NoAnomalousPairs α] (base : α) (h_base : ident < base) :
    StrictMono (embeddingToReal base h_base) := by
  intro x y hxy
  -- Proof requires showing:
  -- 1. θ(x) ≤ θ(y) (containment of sets)
  -- 2. θ(x) < θ(y) (strict, via Archimedean separation)
  sorry

/-- The embedding preserves the operation (maps op to +).

**Proof strategy** (Binder Theorem 3.1):
1. θ(xy) = sup { m/n : base^m ≤ (xy)^n }
2. θ(x) + θ(y) = sup { (m₁+m₂)/(n₁n₂) : base^m₁ ≤ x^n₁, base^m₂ ≤ y^n₂ } (by properties of sup)
3. Key: (xy)^n = x^n · y^n (requires commutativity!)
4. If base^m₁ ≤ x^n and base^m₂ ≤ y^n, then base^(m₁+m₂) ≤ x^n · y^n = (xy)^n
5. Conversely, use Archimedean to decompose any bound on (xy)^n

**Note**: This proof requires `comm_of_noAnomalousPairs` for step 3.
For positive elements, we have `comm_of_positive`. The negative element
cases can be handled by the structure of the embedding (negative elements
map to negative reals).
-/
theorem embeddingToReal_op [NoAnomalousPairs α] (base : α) (h_base : ident < base)
    (x y : α) :
    embeddingToReal base h_base (op x y) =
    embeddingToReal base h_base x + embeddingToReal base h_base y := by
  -- Proof requires:
  -- 1. Commutativity (to get (xy)^n = x^n · y^n)
  -- 2. Careful manipulation of suprema over sets of rationals
  -- 3. Archimedean property for decomposition
  sorry

/-- **Main Theorem (Alimov/Fuchs)**: Non-anomalous semigroups embed in ℝ.

This combines all the pieces:
1. NoAnomalousPairs → Archimedean (Prop 2.7)
2. NoAnomalousPairs → Commutative (Thm 2.10)
3. The embedding construction preserves order and operation
-/
theorem noAnomalousPairs_embeds_in_reals [NoAnomalousPairs α] :
    ∃ (f : α → ℝ), StrictMono f ∧ ∀ x y : α, f (op x y) = f x + f y := by
  -- Need a base element
  by_cases h : ∃ a : α, ident < a
  · rcases h with ⟨base, h_base⟩
    use embeddingToReal base h_base
    constructor
    · exact embeddingToReal_strictMono base h_base
    · exact embeddingToReal_op base h_base
  · -- Degenerate case: all elements equal ident
    push_neg at h
    -- In this case, the semigroup is trivial {ident} and embeds trivially
    use fun _ => 0
    constructor
    · intro x y hxy
      have hx : x ≤ ident := h x
      have hy : ident ≤ y := ident_le y
      have hxy' : x < y := hxy
      -- x ≤ ident and ident ≤ y with x < y means x = ident and y = ident, contradiction
      have heq_x : x = ident := le_antisymm hx (ident_le x)
      have heq_y : y = ident := le_antisymm (h y) (ident_le y)
      simp only [heq_x, heq_y] at hxy'
      exact absurd hxy' (lt_irrefl _)
    · intro x y
      simp

/-! ## Section 4: The Converse Direction

If a semigroup embeds order-preservingly in ℝ, then it has no anomalous pairs.
This is much easier to prove using the density of rationals in ℝ.
-/

/-- An order-preserving additive embedding into ℝ. -/
structure OrderEmbeddingIntoReals (α : Type*) [KnuthSkillingAlgebraBase α] where
  f : α → ℝ
  strictMono : StrictMono f
  preserves_op : ∀ x y : α, f (op x y) = f x + f y
  preserves_ident : f ident = 0

/-- **Converse**: If a semigroup embeds in ℝ, it has no anomalous pairs.

The proof uses density of rationals: given a < b embedded as f(a) < f(b),
there exist rationals between f(a) and f(b), and the Archimedean property of ℝ
ensures the gap grows large enough to separate them at some iterate.
-/
theorem noAnomalousPairs_of_embedding (emb : OrderEmbeddingIntoReals α) :
    NoAnomalousPairs α := by
  constructor
  intro a b ha hab
  -- f(a) < f(b) since f is strictly monotone
  have h_fa_lt_fb : emb.f a < emb.f b := emb.strictMono hab
  -- The difference f(b) - f(a) > 0
  have h_diff_pos : 0 < emb.f b - emb.f a := by linarith

  -- f(ident) = 0 and f(a) > f(ident) since a > ident
  have h_fa_pos : 0 < emb.f a := by
    have := emb.strictMono ha
    simp only [emb.preserves_ident] at this
    exact this

  -- In ℝ, we can find n such that n * (f(b) - f(a)) > f(a)
  -- This is the Archimedean property of ℝ
  have h_arch : ∃ n : ℕ, emb.f a < n * (emb.f b - emb.f a) := by
    rcases exists_nat_gt (emb.f a / (emb.f b - emb.f a)) with ⟨n, hn⟩
    use n
    have h_div_pos : emb.f a / (emb.f b - emb.f a) ≥ 0 := by positivity
    calc emb.f a = (emb.f a / (emb.f b - emb.f a)) * (emb.f b - emb.f a) := by field_simp
      _ < n * (emb.f b - emb.f a) := by nlinarith

  rcases h_arch with ⟨n, hn⟩

  -- We need: iterate_op a (m+1) ≤ iterate_op b m for some m
  -- Using the embedding: f(a^{m+1}) ≤ f(b^m) means (m+1) * f(a) ≤ m * f(b)
  -- From hn: f(a) < n * (f(b) - f(a)) = n * f(b) - n * f(a)
  -- So (n+1) * f(a) < n * f(b), i.e., f(a^{n+1}) < f(b^n)

  use n
  constructor
  · -- n > 0: follows from hn (otherwise f(a) < 0 * ... = 0, contradicting f(a) > 0)
    by_contra h_n_zero
    push_neg at h_n_zero
    interval_cases n
    simp at hn
    linarith
  · -- iterate_op a (n+1) ≤ iterate_op b n
    -- We have (n+1) * f(a) < n * f(b)
    -- Need to translate back via the embedding

    -- First, show f(iterate_op x k) = k * f(x) for all k
    have f_iterate : ∀ (x : α) (k : ℕ), emb.f (iterate_op x k) = k * emb.f x := by
      intro x k
      induction k with
      | zero => simp [iterate_op_zero, emb.preserves_ident]
      | succ k ih =>
        simp only [iterate_op_succ, emb.preserves_op, ih]
        push_cast
        ring

    -- Now the conclusion follows
    -- From hn: f(a) < n * (f(b) - f(a))
    -- So f(a) < n * f(b) - n * f(a)
    -- Thus (n+1) * f(a) < n * f(b)
    have h_ineq : (n + 1 : ℕ) * emb.f a < n * emb.f b := by
      -- From hn: f(a) < n * (f(b) - f(a)) = n * f(b) - n * f(a)
      -- Adding n * f(a) to both sides: f(a) + n * f(a) < n * f(b)
      -- That is: (n + 1) * f(a) < n * f(b)
      have expand_diff : (n : ℕ) * (emb.f b - emb.f a) = n * emb.f b - n * emb.f a := by ring
      have h_expanded : emb.f a < n * emb.f b - n * emb.f a := by
        calc emb.f a < n * (emb.f b - emb.f a) := hn
          _ = n * emb.f b - n * emb.f a := expand_diff
      -- Now add n * f(a) to both sides
      have h_add : emb.f a + n * emb.f a < n * emb.f b := by linarith
      -- And simplify LHS
      have h_lhs : emb.f a + (n : ℕ) * emb.f a = (n + 1 : ℕ) * emb.f a := by push_cast; ring
      linarith

    -- Translate through the embedding
    have h_fa_iter : emb.f (iterate_op a (n + 1)) = (n + 1 : ℕ) * emb.f a := f_iterate a (n + 1)
    have h_fb_iter : emb.f (iterate_op b n) = n * emb.f b := f_iterate b n

    -- f(a^{n+1}) < f(b^n) and f is strictly mono (hence reflects order), so a^{n+1} < b^n
    have h_f_ineq : emb.f (iterate_op a (n + 1)) < emb.f (iterate_op b n) := by
      rw [h_fa_iter, h_fb_iter]
      exact h_ineq

    -- StrictMono.lt_iff_lt says f(x) < f(y) ↔ x < y
    have h_strict : iterate_op a (n + 1) < iterate_op b n := emb.strictMono.lt_iff_lt.mp h_f_ineq
    exact le_of_lt h_strict

/-! ## Section 5: Equivalence Theorem

Combining the above, we get the full characterization:
-/

/-- **Alimov/Fuchs Embedding Theorem (Full Characterization)**:

A totally ordered semigroup with the K&S axioms embeds order-preservingly in (ℝ, +)
if and only if it has no anomalous pairs.
-/
theorem embedding_iff_noAnomalousPairs :
    (∃ (emb : OrderEmbeddingIntoReals α), True) ↔ NoAnomalousPairs α := by
  constructor
  · -- Embedding → NoAnomalousPairs
    intro ⟨emb, _⟩
    exact noAnomalousPairs_of_embedding emb
  · -- NoAnomalousPairs → Embedding
    intro h_nap
    haveI : NoAnomalousPairs α := h_nap
    by_cases h : ∃ a : α, ident < a
    · rcases h with ⟨base, h_base⟩
      use {
        f := embeddingToReal base h_base
        strictMono := embeddingToReal_strictMono base h_base
        preserves_op := embeddingToReal_op base h_base
        preserves_ident := by
          -- embeddingToReal ident = 0
          -- The set is { m/n : base^m ≤ ident^n = ident, n > 0 }
          -- Since base > ident, base^m > ident for m > 0, so only m = 0 satisfies the condition
          -- Thus the set is {0} and sSup {0} = 0
          unfold embeddingToReal
          -- Show the set equals {0}
          have h_set_eq : { x : ℝ | ∃ m n : ℕ, ∃ (_ : 0 < n),
                ∃ (_ : iterate_op base m ≤ iterate_op ident n), (m : ℝ) / n = x } = {0} := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
            constructor
            · -- x ∈ set → x = 0
              intro ⟨m, n, hn, hle, hx⟩
              rw [iterate_op_ident] at hle
              -- Show m = 0
              cases m with
              | zero => simp at hx; exact hx.symm
              | succ k =>
                have hbase_m_pos : ident < iterate_op base (k + 1) :=
                  iterate_op_pos_of_pos h_base (Nat.succ_pos k)
                exact absurd hle (not_le.mpr hbase_m_pos)
            · -- x = 0 → x ∈ set
              intro hx
              subst hx
              refine ⟨0, 1, Nat.one_pos, ?_, ?_⟩
              · -- iterate_op base 0 ≤ iterate_op ident 1
                rw [iterate_op_zero, iterate_op_ident]
              · -- (0 : ℝ) / 1 = 0
                norm_num
          rw [h_set_eq]
          exact csSup_singleton 0
      }
    · -- Trivial case
      push_neg at h
      use {
        f := fun _ => 0
        strictMono := by
          intro x y hxy
          have heq_x : x = ident := le_antisymm (h x) (ident_le x)
          have heq_y : y = ident := le_antisymm (h y) (ident_le y)
          simp only [heq_x, heq_y] at hxy
          exact absurd hxy (lt_irrefl _)
        preserves_op := by simp
        preserves_ident := rfl
      }

end Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AlimovEmbedding
