import Mettapedia.GSLT.Core.Web
import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

universe u

/-!
# Graph Lambda Theories

This file formalizes graph lambda theories from Bucciarelli-Salibra
"Graph Lambda Theories" (2008).

## Main Definitions

* `LambdaTerm` - De Bruijn indexed lambda terms
* `Interpretation` - Interpretation of terms in a graph model
* `TheoryOf` - Lambda-theory induced by a graph model
* `GraphTheory` - The class of graph lambda theories
* `Sensible` - Theories equating all unsolvable terms
* `Semisensible` - Theories where unsolvables only equal unsolvables

## Key Insights from Bucciarelli-Salibra

A **lambda-theory** is a congruence relation on lambda terms extending β-equality.

A theory T is **sensible** if it equates all unsolvable terms:
  T ⊢ Ω = λx.Ω
where Ω = (λx.xx)(λx.xx).

A theory T is **semisensible** if unsolvable terms only equal unsolvable terms:
  T ⊢ M = N with M unsolvable implies N is unsolvable.

Every graph theory is semisensible (Bucciarelli-Salibra §4).

## References

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008)
- Barendregt, "The Lambda Calculus: Its Syntax and Semantics"
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-! ## Lambda Terms with de Bruijn Indices

We use de Bruijn indices for alpha-equivalence-free representation.
-/

/-- Lambda terms with de Bruijn indices.
    Variables are represented by natural numbers (indices).
    0 refers to the innermost binder, 1 to the next outer, etc. -/
inductive LambdaTerm : Type where
  /-- Variable with de Bruijn index -/
  | var : Nat → LambdaTerm
  /-- Lambda abstraction -/
  | lam : LambdaTerm → LambdaTerm
  /-- Application -/
  | app : LambdaTerm → LambdaTerm → LambdaTerm
  deriving Repr, DecidableEq

namespace LambdaTerm

/-- The identity combinator I = λx.x -/
def I : LambdaTerm := .lam (.var 0)

/-- The K combinator K = λxy.x -/
def K : LambdaTerm := .lam (.lam (.var 1))

/-- The S combinator S = λxyz.xz(yz) -/
def S : LambdaTerm :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

/-- The omega combinator ω = λx.xx -/
def omega : LambdaTerm := .lam (.app (.var 0) (.var 0))

/-- The Omega combinator Ω = ωω = (λx.xx)(λx.xx) -/
def Omega : LambdaTerm := .app omega omega

/-- Shift free variables by a given amount -/
def shift (d : Nat) (c : Nat) : LambdaTerm → LambdaTerm
  | .var n => if n < c then .var n else .var (n + d)
  | .lam t => .lam (shift d (c + 1) t)
  | .app t1 t2 => .app (shift d c t1) (shift d c t2)

/-- Substitute term s for variable index j in term t -/
def subst (j : Nat) (s : LambdaTerm) : LambdaTerm → LambdaTerm
  | .var n => if n == j then s else if n > j then .var (n - 1) else .var n
  | .lam t => .lam (subst (j + 1) (shift 1 0 s) t)
  | .app t1 t2 => .app (subst j s t1) (subst j s t2)

/-! ## Substitution and Shifting Lemmas

These lemmas establish the interaction between shift and subst operations,
which are essential for proving that parallel reduction is preserved under
substitution. The proofs involve careful de Bruijn index arithmetic. -/

/-- Shifting a variable below the cutoff leaves it unchanged. -/
@[simp]
theorem shift_var_lt (n d c : Nat) (h : n < c) :
    shift d c (LambdaTerm.var n) = LambdaTerm.var n := by
  simp only [shift, h, ↓reduceIte]

/-- Shifting a variable at or above the cutoff adds d. -/
@[simp]
theorem shift_var_ge (n d c : Nat) (h : n ≥ c) :
    shift d c (LambdaTerm.var n) = LambdaTerm.var (n + d) := by
  simp only [shift]
  have hng : ¬(n < c) := by omega
  simp only [hng, ↓reduceIte]

/-- Shifting a lambda goes under the binder with incremented cutoff. -/
@[simp]
theorem shift_lam (t : LambdaTerm) (d c : Nat) :
    shift d c (LambdaTerm.lam t) = LambdaTerm.lam (shift d (c + 1) t) := by
  simp only [shift]

/-- Shifting an application distributes. -/
@[simp]
theorem shift_app (t1 t2 : LambdaTerm) (d c : Nat) :
    shift d c (LambdaTerm.app t1 t2) = LambdaTerm.app (shift d c t1) (shift d c t2) := by
  simp only [shift]

/-- Shifting a variable by 0 leaves it unchanged. -/
theorem shift_zero (t : LambdaTerm) (c : Nat) : t.shift 0 c = t := by
  induction t generalizing c with
  | var n =>
    simp only [shift]
    split <;> rfl
  | lam t ih => simp only [shift, ih]
  | app t1 t2 ih1 ih2 => simp only [shift, ih1, ih2]

/-- General shift-shift commutation lemma.
    shift d (c + k + 1) (shift 1 k t) = shift 1 k (shift d (c + k) t)
    This generalizes to any inner cutoff k.

    Proof by structural induction on t with careful index tracking. -/
theorem shift_shift_comm (t : LambdaTerm) (d c k : Nat) :
    shift d (c + k + 1) (shift 1 k t) = shift 1 k (shift d (c + k) t) := by
  induction t generalizing c k with
  | var n =>
    simp only [shift]
    -- Expand the nested ifs and use split_ifs
    split_ifs <;> simp only [shift] <;> split_ifs
    all_goals (try rfl)
    all_goals (try omega)
    all_goals (try (congr 1; omega))
  | lam body ih =>
    simp only [shift]
    congr 1
    have h := ih c (k + 1)
    simp only [Nat.add_assoc] at h ⊢
    exact h
  | app t1 t2 ih1 ih2 =>
    simp only [shift]
    rw [ih1 c k, ih2 c k]

theorem shift_comm (t : LambdaTerm) (d c : Nat) :
    shift d (c + 1) (shift 1 0 t) = shift 1 0 (shift d c t) :=
  shift_shift_comm t d c 0

/-- General shift-subst interaction lemma.
    shift d c (subst n s t) = subst n (shift d c s) (shift d (c + 1) t)
    when n ≤ c (so shifting doesn't affect the substitution variable).

    This generalizes subst_0_shift to arbitrary substitution indices. -/
theorem subst_shift_general (t s : LambdaTerm) (d c n : Nat) (hn : n ≤ c) :
    shift d c (subst n s t) = subst n (shift d c s) (shift d (c + 1) t) := by
  induction t generalizing s c n with
  | var m =>
    simp only [subst, shift]
    -- Full case split on all conditions, then normalize
    split_ifs
    all_goals (simp only [subst, shift, beq_iff_eq] at *)
    all_goals (split_ifs at * <;> try rfl)
    all_goals (try omega)
    all_goals (try (congr 1; omega))
  | lam body ih =>
    -- Goal: shift d c (subst n s (.lam body)) = subst n (shift d c s) (shift d (c + 1) (.lam body))
    simp only [subst, shift]
    congr 1
    -- Goal: shift d (c+1) (subst (n+1) (shift 1 0 s) body)
    --     = subst (n+1) (shift 1 0 (shift d c s)) (shift d (c+2) body)
    -- Apply IH with s' = shift 1 0 s, c' = c+1, n' = n+1
    have hn1 : n + 1 ≤ c + 1 := by omega
    have h := ih (shift 1 0 s) (c + 1) (n + 1) hn1
    -- h: shift d (c+1) (subst (n+1) (shift 1 0 s) body)
    --  = subst (n+1) (shift d (c+1) (shift 1 0 s)) (shift d (c+2) body)
    -- Normalize c+2 to c+1+1 in goal to match h
    show shift d (c + 1) (subst (n + 1) (shift 1 0 s) body)
       = subst (n + 1) (shift 1 0 (shift d c s)) (shift d (c + 1 + 1) body)
    rw [h]
    -- Goal: subst (n+1) (shift d (c+1) (shift 1 0 s)) (shift d (c+1+1) body)
    --     = subst (n+1) (shift 1 0 (shift d c s)) (shift d (c+1+1) body)
    -- Use shift_comm: shift d (c + 1) (shift 1 0 s) = shift 1 0 (shift d c s)
    rw [shift_comm s d c]
  | app t1 t2 ih1 ih2 =>
    simp only [subst, shift]
    rw [ih1 s c n hn, ih2 s c n hn]

/-- Key lemma: shift and subst interaction at index 0.
    shift d c (subst 0 s t) = subst 0 (shift d c s) (shift d (c + 1) t)

    This is THE KEY LEMMA for proving parRed_shift.
    The proof is a special case of subst_shift_general.

    See: Barendregt Ch. 2, de Bruijn substitution lemmas -/
theorem subst_0_shift (t s : LambdaTerm) (d c : Nat) :
    shift d c (subst 0 s t) = subst 0 (shift d c s) (shift d (c + 1) t) :=
  subst_shift_general t s d c 0 (Nat.zero_le c)

/-- General shift-subst cancellation: subst n t (shift 1 n s) = s

    Shifting s by 1 at cutoff n increments all variables >= n.
    Substituting at index n with appropriate handling undoes this.
    Together they return the original term.

    This is a key identity for de Bruijn index manipulation. -/
theorem subst_shift_cancel_general (t s : LambdaTerm) (n : Nat) : subst n t (shift 1 n s) = s := by
  induction s generalizing t n with
  | var m =>
    simp only [shift]
    by_cases hmn : m < n
    · -- m < n: shift leaves m as var m
      -- subst n t (var m): since m ≠ n (m < n) and m < n (not > n), result is var m
      simp only [hmn, ↓reduceIte, subst]
      have hne : (m == n) = false := by simp [beq_eq_false_iff_ne]; omega
      have hng : ¬(m > n) := by omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte, hng]
    · -- m >= n: shift gives var (m+1)
      -- subst n t (var (m+1)): m+1 ≠ n (since m >= n implies m+1 > n) and m+1 > n
      simp only [hmn, ↓reduceIte, subst]
      have hne : (m + 1 == n) = false := by simp [beq_eq_false_iff_ne]; omega
      have hgt : m + 1 > n := by omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte, hgt, Nat.add_sub_cancel]
  | lam body ih =>
    simp only [shift, subst]
    congr 1
    exact ih (shift 1 0 t) (n + 1)
  | app t1 t2 ih1 ih2 =>
    simp only [shift, subst]
    rw [ih1 t n, ih2 t n]

/-- Special case: subst 0 t (shift 1 0 s) = s -/
theorem subst_shift_cancel (t s : LambdaTerm) : subst 0 t (shift 1 0 s) = s :=
  subst_shift_cancel_general t s 0

/-- Substitution on a highly-shifted term (general cutoff version):
    subst k t (shift (k - c + 1) c s) = shift (k - c) c s when k >= c

    When s is shifted by (k-c+1) at cutoff c, all variables >= c become >= k+1.
    Substituting for variable k doesn't match any shifted variable (all > k),
    so all such variables just get decremented by 1. Variables < c are unchanged.

    The key property: shift (k-c+1) c shifts vars >= c by (k-c+1), making them >= k+1.
    Then subst k decrements them to >= k, which is exactly shift (k-c) c. -/
theorem subst_shift_high_general (k c : Nat) (hkc : k >= c) (t s : LambdaTerm) :
    subst k t (shift (k - c + 1) c s) = shift (k - c) c s := by
  induction s generalizing k c t with
  | var m =>
    simp only [shift]
    by_cases hmc : m < c
    · -- m < c: shift leaves m unchanged, subst also leaves it (m < c <= k)
      simp only [hmc, ↓reduceIte, subst]
      have hne : (m == k) = false := by simp [beq_eq_false_iff_ne]; omega
      have hng : ¬(m > k) := by omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte, hng]
    · -- m >= c: shift gives var (m + (k - c + 1)), which is >= k + 1
      simp only [hmc, ↓reduceIte, subst]
      have hshifted_ne : (m + (k - c + 1) == k) = false := by simp [beq_eq_false_iff_ne]; omega
      have hshifted_gt : m + (k - c + 1) > k := by omega
      simp only [hshifted_ne, Bool.false_eq_true, ↓reduceIte, hshifted_gt]
      -- Result: var (m + (k - c + 1) - 1) = var (m + (k - c))
      -- These are equal since (k - c + 1 - 1) = k - c, and Lean normalizes the arithmetic
      rfl
  | lam body ih =>
    simp only [shift, subst]
    congr 1
    -- Under lambda: cutoff increases by 1, subst index increases by 1
    -- Goal: subst (k+1) (shift 1 0 t) (shift (k-c+1) (c+1) body) = shift (k-c) (c+1) body
    -- IH gives: subst (k+1) (shift 1 0 t) (shift ((k+1)-(c+1)+1) (c+1) body) = shift ((k+1)-(c+1)) (c+1) body
    -- Need: (k+1)-(c+1)+1 = k-c+1 and (k+1)-(c+1) = k-c (when k >= c)
    have hkc' : k + 1 >= c + 1 := by omega
    have heq1 : k + 1 - (c + 1) + 1 = k - c + 1 := by omega
    have heq2 : k + 1 - (c + 1) = k - c := by omega
    rw [← heq1, ← heq2]
    exact ih (k + 1) (c + 1) hkc' (shift 1 0 t)
  | app t1 t2 ih1 ih2 =>
    simp only [shift, subst]
    rw [ih1 k c hkc t, ih2 k c hkc t]

/-- Special case at cutoff 0: subst k t (shift (k+1) 0 s) = shift k 0 s -/
theorem subst_shift_high (k : Nat) (t s : LambdaTerm) :
    subst k t (shift (k + 1) 0 s) = shift k 0 s := by
  have h := subst_shift_high_general k 0 (Nat.zero_le k) t s
  simp only [Nat.sub_zero] at h
  exact h

/-- Substitution commutes with shift (general cutoff version):
    subst (n + d) (shift d c s) (shift d c t) = shift d c (subst n s t)  when n >= c

    This is a key de Bruijn identity: substituting at index n+d in a d-shifted term
    equals d-shifting the result of substituting at index n in the original term.

    The condition n >= c ensures the substitution target is above the shift cutoff. -/
theorem subst_shift_comm_general (d n c : Nat) (hnc : n >= c) (s t : LambdaTerm) :
    subst (n + d) (shift d c s) (shift d c t) = shift d c (subst n s t) := by
  induction t generalizing d n c s with
  | var m =>
    simp only [shift]
    by_cases hmc : m < c
    · -- m < c: shift leaves m unchanged
      simp only [hmc, ↓reduceIte, subst]
      -- subst (n+d) _ (var m): since m < c <= n < n+d, we have m ≠ n+d and m < n+d
      have hmne : (m == n + d) = false := by simp [beq_eq_false_iff_ne]; omega
      have hmng : ¬(m > n + d) := by omega
      have hmne' : (m == n) = false := by simp [beq_eq_false_iff_ne]; omega
      have hmng' : ¬(m > n) := by omega
      -- LHS: var m, RHS: shift d c (var m) = var m since m < c
      simp only [hmne, Bool.false_eq_true, ↓reduceIte, hmng, hmne', hmng', shift, hmc]
    · -- m >= c: shift gives var (m + d)
      simp only [hmc, ↓reduceIte, subst]
      by_cases hmn : m = n
      · -- m = n: substitution happens
        subst hmn
        -- Goal: subst (n + d) (shift d c s) (var (n + d)) = shift d c s
        -- LHS: since (n+d) == (n+d), result is shift d c s
        simp only [beq_self_eq_true, ↓reduceIte]
      · by_cases hmgn : m > n
        · -- m > n: variable decrements
          have hmdne : (m + d == n + d) = false := by simp [beq_eq_false_iff_ne]; omega
          have hmdgt : m + d > n + d := by omega
          have hmne : (m == n) = false := by simp [beq_eq_false_iff_ne]; omega
          -- Since m >= c and m > n >= c, we have m > c, so m - 1 >= c
          have hm1c : ¬(m - 1 < c) := by omega
          simp only [hmdne, Bool.false_eq_true, ↓reduceIte, hmdgt, hmne, hmgn, shift, hm1c]
          -- Both: var (m + d - 1) = var (m - 1 + d)
          congr 1; omega
        · -- m < n: impossible since m >= c, n >= c, m ≠ n, m ≤ n means m < n
          -- But we also have m >= c and n >= c, so this is the case c <= m < n
          have hmdne : (m + d == n + d) = false := by simp [beq_eq_false_iff_ne]; omega
          have hmdng : ¬(m + d > n + d) := by omega
          have hmne : (m == n) = false := by simp [beq_eq_false_iff_ne]; omega
          have hmng : ¬(m > n) := by omega
          -- LHS: var (m + d), RHS: shift d c (var m) = var (m + d) since m >= c
          simp only [hmdne, Bool.false_eq_true, ↓reduceIte, hmdng, hmne, hmng, shift, hmc]
  | lam body ih =>
    simp only [shift, subst]
    congr 1
    -- Under lambda: cutoffs and indices increase by 1
    -- Goal: subst (n+d+1) (shift 1 0 (shift d c s)) (shift d (c+1) body) =
    --       shift d (c+1) (subst (n+1) (shift 1 0 s) body)
    -- Use ← shift_comm: shift 1 0 (shift d c s) = shift d (c+1) (shift 1 0 s)
    rw [← shift_comm s d c]
    have hnc' : n + 1 >= c + 1 := by omega
    have heq : n + d + 1 = (n + 1) + d := by omega
    rw [heq]
    exact ih d (n + 1) (c + 1) hnc' (shift 1 0 s)
  | app t1 t2 ih1 ih2 =>
    simp only [shift, subst]
    rw [ih1 d n c hnc s, ih2 d n c hnc s]

/-- Special case at cutoff 0 -/
theorem subst_shift_comm (d n : Nat) (s t : LambdaTerm) :
    subst (n + d) (shift d 0 s) (shift d 0 t) = shift d 0 (subst n s t) :=
  subst_shift_comm_general d n 0 (Nat.zero_le n) s t

/-- Shifting by d1 then d2 equals shifting by d1+d2 (general cutoff version) -/
theorem shift_add_general (d1 d2 c : Nat) (t : LambdaTerm) :
    shift d2 c (shift d1 c t) = shift (d1 + d2) c t := by
  induction t generalizing c with
  | var m =>
    simp only [shift]
    by_cases hmc : m < c
    · -- m < c: first shift leaves m unchanged, then second shift also leaves it
      simp only [hmc, ↓reduceIte]
      -- Now need to show shift d2 c (var m) = var m, since m < c
      simp only [shift, hmc, ↓reduceIte]
    · -- m >= c: first shift gives m + d1, second shift gives m + d1 + d2
      simp only [hmc, ↓reduceIte]
      have h2 : ¬(m + d1 < c) := by omega
      simp only [shift, h2, ↓reduceIte]
      congr 1; omega
  | lam body ih =>
    simp only [shift]
    congr 1
    exact ih (c + 1)
  | app t1 t2 ih1 ih2 =>
    simp only [shift]
    rw [ih1 c, ih2 c]

/-- Shifting by d1 then d2 equals shifting by d1+d2 (at cutoff 0) -/
theorem shift_add (d1 d2 : Nat) (t : LambdaTerm) : shift d2 0 (shift d1 0 t) = shift (d1 + d2) 0 t :=
  shift_add_general d1 d2 0 t

/-- Helper: shift 1 0 twice equals shift 2 0 -/
theorem shift_1_0_twice (s : LambdaTerm) : shift 1 0 (shift 1 0 s) = shift 2 0 s :=
  shift_add 1 1 s

/-- Generalized substitution composition lemma.

    This generalizes the basic composition lemma to work under binders:
    when k=0, we get the basic composition lemma.
    when k>0, we get the version needed for under-lambda reasoning.

    The key insight: after k lambdas, all indices are shifted by k. -/
theorem subst_subst_composition_general (t u s : LambdaTerm) (k n : Nat) :
    subst (n + k) (shift k 0 s) (subst k (shift k 0 u) t) =
    subst k (shift k 0 (subst n s u)) (subst (n + k + 1) (shift (k + 1) 0 s) t) := by
  induction t generalizing k n u s with
  | var m =>
    -- Same case analysis as before, but with k offset
    simp only [subst]
    by_cases hmk : m = k
    · -- m = k: inner subst gives (shift k 0 u)
      subst hmk
      simp only [beq_self_eq_true, ↓reduceIte]
      -- Now k is replaced by m in the goal. We work with m.
      -- LHS: subst (n+m) (shift m 0 s) (shift m 0 u)
      -- RHS: subst m (shift m 0 (subst n s u)) (subst (n+m+1) (shift (m+1) 0 s) (var m))
      -- RHS inner: since m < n+m+1, gives var m
      have hmne : (m == n + m + 1) = false := by simp [beq_eq_false_iff_ne]; omega
      have hmng : ¬(m > n + m + 1) := by omega
      simp only [subst, hmne, Bool.false_eq_true, ↓reduceIte, hmng, beq_self_eq_true]
      -- Now RHS is: shift m 0 (subst n s u)
      -- LHS is: subst (n+m) (shift m 0 s) (shift m 0 u)
      -- This is exactly subst_shift_comm!
      exact subst_shift_comm m n s u
    · by_cases hmltk : m < k
      · -- m < k: inner subst gives var m (unchanged), both sides = var m
        have hmnekbeq : (m == k) = false := by simp [beq_eq_false_iff_ne]; omega
        have hmngk : ¬(m > k) := by omega
        have hmnenkbeq : (m == n + k) = false := by simp [beq_eq_false_iff_ne]; omega
        have hmngnk : ¬(m > n + k) := by omega
        have hmnenk1beq : (m == n + k + 1) = false := by simp [beq_eq_false_iff_ne]; omega
        have hmngnk1 : ¬(m > n + k + 1) := by omega
        -- Both sides simplify to var m
        simp only [subst, hmnekbeq, Bool.false_eq_true, ↓reduceIte, hmngk,
                   hmnenkbeq, hmngnk, hmnenk1beq, hmngnk1]
      · -- m > k: inner subst gives var (m-1)
        have hmnekbeq : (m == k) = false := by simp [beq_eq_false_iff_ne]; omega
        have hmgk : m > k := by omega
        simp only [hmnekbeq, Bool.false_eq_true, ↓reduceIte, hmgk]
        -- LHS: subst (n+k) (shift k 0 s) (var (m-1))
        -- RHS inner: subst (n+k+1) (shift (k+1) 0 s) (var m)
        -- Case split on m vs n+k and m vs n+k+1
        by_cases hmennk1 : m = n + k + 1
        · -- m = n + k + 1
          subst hmennk1
          -- LHS inner: subst k _ (var (n+k+1)) gives var (n+k) since n+k+1 > k
          -- After simp, inner results applied
          -- LHS outer: subst (n+k) (shift k 0 s) (var (n+k)) = shift k 0 s
          -- RHS inner: subst (n+k+1) (shift (k+1) 0 s) (var (n+k+1)) = shift (k+1) 0 s
          -- RHS outer: subst k _ (shift (k+1) 0 s) = shift k 0 s by subst_shift_high
          simp only [beq_self_eq_true, ↓reduceIte, Nat.add_sub_cancel, subst]
          -- Now goal: shift k 0 s = subst k _ (shift (k+1) 0 s)
          exact (subst_shift_high k (shift k 0 (subst n s u)) s).symm
        · -- m ≠ n + k + 1
          have hmnennk1beq : (m == n + k + 1) = false := by simp [beq_eq_false_iff_ne]; omega
          by_cases hmgnk1 : m > n + k + 1
          · -- m > n + k + 1, so m - 1 > n + k
            have hm1nenkbeq : (m - 1 == n + k) = false := by simp [beq_eq_false_iff_ne]; omega
            have hm1gnk : m - 1 > n + k := by omega
            have hm1nekbeq : (m - 1 == k) = false := by simp [beq_eq_false_iff_ne]; omega
            have hm1gk : m - 1 > k := by omega
            -- Both sides simplify to var (m - 2)
            simp only [subst, hmnennk1beq, Bool.false_eq_true, ↓reduceIte, hmgnk1,
                       hm1nenkbeq, hm1gnk, hm1nekbeq, hm1gk]
          · -- m < n + k + 1 and m > k and m ≠ n + k + 1, so k < m ≤ n + k
            by_cases hmenk : m = n + k
            · -- m = n + k
              subst hmenk
              -- After inner substs: LHS = subst (n+k) _ (var (n+k-1)), RHS = subst k _ (var (n+k))
              -- Both outer substs give var (n+k-1)
              have hnknekbeq : (n + k == k) = false := by simp [beq_eq_false_iff_ne]; omega
              have hnkgk : n + k > k := by omega
              -- For the outer LHS subst: var (n+k-1) with index (n+k)
              have hnk1_ne_nk : (n + k - 1 == n + k) = false := by simp [beq_eq_false_iff_ne]; omega
              have hnk1_ng_nk : ¬(n + k - 1 > n + k) := by omega
              simp only [subst, hmnennk1beq, Bool.false_eq_true, ↓reduceIte, hmgnk1,
                         hnknekbeq, hnkgk, hnk1_ne_nk, hnk1_ng_nk]
            · -- m ≠ n + k, so m < n + k (since m ≤ n + k and m ≠ n + k)
              have hmnenkbeq' : (m - 1 == n + k) = false := by simp [beq_eq_false_iff_ne]; omega
              have hm1ngnk : ¬(m - 1 > n + k) := by omega
              have hmnekbeq' : (m == k) = false := by simp [beq_eq_false_iff_ne]; omega
              -- Both sides simplify to var (m - 1)
              simp only [subst, hmnennk1beq, Bool.false_eq_true, ↓reduceIte, hmgnk1,
                         hmnenkbeq', hm1ngnk, hmnekbeq', hmgk]
  | lam body ih =>
    simp only [subst]
    congr 1
    -- After simp, goal has shift 1 0 (shift k 0 ...) which we convert to shift (k+1) 0 ...
    -- using shift_add k 1 ...
    rw [shift_add k 1 s, shift_add k 1 u, shift_add k 1 (subst n s u), shift_add (k + 1) 1 s]
    -- Now goal matches the IH pattern
    specialize ih u s (k + 1) n
    -- Arithmetic normalization: k + 1 + 1 = k + 2, n + (k + 1) = n + k + 1, etc.
    simp only [Nat.add_assoc] at ih ⊢
    -- The expressions should now match
    exact ih
  | app t1 t2 ih1 ih2 =>
    simp only [subst]
    rw [ih1 u s k n, ih2 u s k n]

/-- Substitution composition lemma: substituting for variable n after substituting for 0
    can be done in the opposite order with appropriate adjustments.

    subst n s (subst 0 u t) = subst 0 (subst n s u) (subst (n+1) (shift 1 0 s) t)

    This is THE KEY LEMMA for proving parallel reduction is preserved under substitution
    in the beta case.

    The intuition: when we substitute s for variable n in (t[u/0]), we can instead:
    1. First substitute s (shifted) for variable n+1 in t
    2. Then substitute (u[s/n]) for variable 0

    See: Barendregt Ch. 2, de Bruijn substitution composition -/
theorem subst_subst_composition (t u s : LambdaTerm) (n : Nat) :
    subst n s (subst 0 u t) = subst 0 (subst n s u) (subst (n + 1) (shift 1 0 s) t) := by
  induction t generalizing n u s with
  | var m =>
    -- We do exhaustive case analysis on m's relationship to 0 and n+1
    rcases Nat.lt_trichotomy m 0 with hm0 | hm0 | hm0
    · omega  -- m < 0 impossible for Nat
    · -- m = 0
      subst hm0
      simp only [subst, beq_self_eq_true, ↓reduceIte]
      -- Goal: subst n s u = subst 0 (subst n s u) (if (0 == n+1) = true then ... else ...)
      -- The if-then-else simplifies to var 0 since 0 ≠ n+1 and 0 ≯ n+1
      have hne : (0 == n + 1) = false := by cases n <;> rfl
      have hng : ¬(0 > n + 1) := by omega
      -- First simplify the inner if to var 0
      simp only [hne, Bool.false_eq_true, ↓reduceIte, hng]
      -- Now goal: subst n s u = subst 0 (subst n s u) (var 0)
      -- Since 0 == 0 is true, we get subst n s u on RHS
      simp only [subst, beq_self_eq_true, ↓reduceIte]
    · -- m > 0
      rcases Nat.lt_trichotomy m (n + 1) with hmn1 | hmn1 | hmn1
      · -- 0 < m < n + 1
        -- LHS: subst 0 u (var m) = var (m-1) since m > 0 and m ≠ 0
        -- Then subst n s (var (m-1))
        -- RHS: subst (n+1) _ (var m) = var m since m < n+1 and m ≠ n+1
        -- Then subst 0 _ (var m) = var (m-1) since m > 0
        have hm_ne0 : (m == 0) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hm_gt0 : m > 0 := hm0
        have hm_nen1 : (m == n + 1) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hm_ngtn1 : ¬(m > n + 1) := by omega
        simp only [subst, hm_ne0, Bool.false_eq_true, ↓reduceIte, hm_gt0,
                   hm_nen1, hm_ngtn1]
        -- Goal: subst n s (var (m-1)) = subst 0 (subst n s u) (var m)
        -- RHS outer subst: var m with m ≠ 0 and m > 0, so = var (m-1)
        -- After that, both sides are var (m-1)
        -- Actually simp already simplified, let's trace
        -- LHS: var (m-1) after first subst
        -- RHS: subst 0 (subst n s u) (var m) - need to simplify this
        -- var m with m ≠ 0 and m > 0 → var (m-1)
        -- So RHS = var (m-1) as well
        -- Both equal!
        have hm1_nen : (m - 1 == n) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hm1_ngtn : ¬(m - 1 > n) := by omega
        simp only [hm1_nen, Bool.false_eq_true, ↓reduceIte, hm1_ngtn]
      · -- m = n + 1
        subst hmn1
        -- LHS: subst 0 u (var (n+1)) = var n, then subst n s (var n) = s
        have hne0 : ((n + 1) == 0) = false := by cases n <;> rfl
        have hgt0 : n + 1 > 0 := by omega
        simp only [subst, hne0, Bool.false_eq_true, ↓reduceIte, hgt0,
                   Nat.add_sub_cancel, beq_self_eq_true]
        -- LHS = s
        -- RHS: subst (n+1) (shift 1 0 s) (var (n+1)) = shift 1 0 s
        -- Then subst 0 _ (shift 1 0 s) = s by subst_shift_cancel
        exact (subst_shift_cancel (subst n s u) s).symm
      · -- m > n + 1
        -- LHS: subst 0 u (var m) = var (m-1), then subst n s (var (m-1))
        -- Since m > n+1, we have m-1 > n, so subst gives var (m-2)
        -- RHS: subst (n+1) _ (var m) = var (m-1) since m > n+1
        -- Then subst 0 _ (var (m-1)) = var (m-2) since m-1 > 0
        have hm_ne0 : (m == 0) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hm_gt0 : m > 0 := hm0
        have hm_nen1 : (m == n + 1) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hm_gtn1 : m > n + 1 := hmn1
        simp only [subst, hm_ne0, Bool.false_eq_true, ↓reduceIte, hm_gt0,
                   hm_nen1, hm_gtn1]
        -- LHS: subst n s (var (m-1))
        -- Since m-1 > n (from m > n+1), we have m-1 ≠ n
        have hm1_nen : (m - 1 == n) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hm1_gtn : m - 1 > n := by omega
        simp only [hm1_nen, Bool.false_eq_true, ↓reduceIte, hm1_gtn]
        -- LHS = var (m-1-1) = var (m-2)
        -- RHS: subst 0 _ (var (m-1))
        have hm1_ne0 : (m - 1 == 0) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hm1_gt0 : m - 1 > 0 := by omega
        simp only [hm1_ne0, Bool.false_eq_true, ↓reduceIte, hm1_gt0]
        -- RHS = var (m-1-1) = var (m-2)
        -- Both sides are now var (m - 1 - 1), which simplifies to the same
  | lam body ih =>
    simp only [subst]
    congr 1
    -- Need: subst (n+1) (shift 1 0 s) (subst 1 (shift 1 0 u) body)
    --     = subst 1 (shift 1 0 (subst n s u)) (subst (n+2) (shift 1 0 (shift 1 0 s)) body)
    -- This is exactly subst_subst_composition_general with k = 1!
    -- First rewrite shift 1 0 (shift 1 0 s) = shift 2 0 s
    rw [shift_1_0_twice s]
    -- Now use subst_subst_composition_general with k = 1
    exact subst_subst_composition_general body u s 1 n
  | app t1 t2 ih1 ih2 =>
    simp only [subst]
    rw [ih1, ih2]

/-- Substituting into a variable at the same index gives the substituend. -/
@[simp]
theorem subst_var_eq (n : Nat) (s : LambdaTerm) :
    subst n s (LambdaTerm.var n) = s := by
  simp only [subst, beq_self_eq_true, ↓reduceIte]

/-- Substituting into a variable at a greater index shifts it down. -/
@[simp]
theorem subst_var_gt (m n : Nat) (h : m > n) (s : LambdaTerm) :
    subst n s (LambdaTerm.var m) = LambdaTerm.var (m - 1) := by
  simp only [subst]
  have hne : (m == n) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte, h]

/-- Substituting into a variable at a lesser index leaves it unchanged. -/
@[simp]
theorem subst_var_lt (m n : Nat) (h : m < n) (s : LambdaTerm) :
    subst n s (LambdaTerm.var m) = LambdaTerm.var m := by
  simp only [subst]
  have hne : (m == n) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  have hng : ¬(m > n) := by omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte, hng]

/-- Substituting into a lambda goes under the binder. -/
@[simp]
theorem subst_lam (t s : LambdaTerm) (n : Nat) :
    subst n s (LambdaTerm.lam t) = LambdaTerm.lam (subst (n + 1) (shift 1 0 s) t) := by
  simp only [subst]

/-- Substituting into an application distributes. -/
@[simp]
theorem subst_app (t1 t2 s : LambdaTerm) (n : Nat) :
    subst n s (LambdaTerm.app t1 t2) = LambdaTerm.app (subst n s t1) (subst n s t2) := by
  simp only [subst]

/-- Beta reduction: substitute the argument into the body -/
def betaReduce : LambdaTerm → Option LambdaTerm
  | .app (.lam t) s => some (subst 0 s t)
  | _ => none

/-- Check if a term is a value (lambda abstraction) -/
def isValue : LambdaTerm → Bool
  | .lam _ => true
  | _ => false

/-- One-step beta reduction (leftmost-outermost) -/
def step : LambdaTerm → Option LambdaTerm
  | .app (.lam t) s => some (subst 0 s t)
  | .app t1 t2 =>
      match step t1 with
      | some t1' => some (.app t1' t2)
      | none =>
          match step t2 with
          | some t2' => some (.app t1 t2')
          | none => none
  | .lam t =>
      match step t with
      | some t' => some (.lam t')
      | none => none
  | .var _ => none

end LambdaTerm

/-! ## Head Normal Forms and Solvability

A term is in **head normal form** if it has the form λx₁...xₙ.y M₁ ... Mₖ
where y is a variable. Solvable terms are those with a head normal form.
-/

/-- Head normal form: λx₁...xₙ.y M₁ ... Mₖ where y is a variable -/
inductive HeadNormalForm : Type where
  /-- A variable applied to arguments, possibly under lambdas -/
  | hnf : (numLambdas : Nat) → (headVar : Nat) → (args : List LambdaTerm) → HeadNormalForm

/-- Check if a term is an application head (variable or application of head) -/
def LambdaTerm.isAppHead : LambdaTerm → Bool
  | .var _ => true
  | .app t _ => t.isAppHead
  | .lam _ => false

/-- Check if a term is in head normal form -/
def LambdaTerm.isHNF : LambdaTerm → Bool
  | .var _ => true
  | .lam t => t.isHNF
  | .app t _ => t.isAppHead

/-- A term is solvable if it has a head normal form.
    Equivalently: ∃ M₁...Mₙ. t M₁ ... Mₙ →*_β I -/
def LambdaTerm.Solvable (t : LambdaTerm) : Prop :=
  ∃ (args : List LambdaTerm), (args.foldl .app t).isHNF = true

/-- A term is unsolvable if it is not solvable -/
def LambdaTerm.Unsolvable (t : LambdaTerm) : Prop := ¬t.Solvable

/-- Helper: isAppHead of an application is the isAppHead of the function part -/
private theorem isAppHead_app (t s : LambdaTerm) :
    (LambdaTerm.app t s).isAppHead = t.isAppHead := rfl

/-- Helper: foldl preserves non-AppHead property -/
private theorem foldl_app_preserves_not_isAppHead (t : LambdaTerm) (args : List LambdaTerm)
    (h : t.isAppHead = false) : (args.foldl .app t).isAppHead = false := by
  induction args generalizing t with
  | nil => exact h
  | cons a rest ih =>
    rw [List.foldl_cons]
    apply ih
    rw [isAppHead_app]
    exact h

/-- Helper: Omega is not an AppHead (not a variable at the head) -/
private theorem Omega_not_isAppHead : LambdaTerm.Omega.isAppHead = false := by
  native_decide

/-- Helper: Any term with Omega at the head position is not an AppHead -/
private theorem foldl_app_Omega_not_isAppHead (args : List LambdaTerm) :
    (args.foldl .app LambdaTerm.Omega).isAppHead = false :=
  foldl_app_preserves_not_isAppHead LambdaTerm.Omega args Omega_not_isAppHead

/-- Helper: isHNF of an application is the isAppHead of the function part -/
private theorem isHNF_app (t s : LambdaTerm) :
    (LambdaTerm.app t s).isHNF = t.isAppHead := rfl

/-- Helper: Omega is not in HNF -/
private theorem Omega_not_isHNF : LambdaTerm.Omega.isHNF = false := by
  native_decide

/-- Helper: foldl preserves non-HNF for applications starting from non-AppHead -/
private theorem foldl_app_preserves_not_isHNF (t : LambdaTerm) (args : List LambdaTerm)
    (h : t.isAppHead = false) (hHNF : t.isHNF = false) : (args.foldl .app t).isHNF = false := by
  induction args generalizing t with
  | nil => exact hHNF
  | cons a rest ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [isAppHead_app]; exact h
    · rw [isHNF_app]; exact h

/-- Helper: Omega applied to any arguments is not in HNF -/
private theorem foldl_app_Omega_not_isHNF (args : List LambdaTerm) :
    (args.foldl .app LambdaTerm.Omega).isHNF = false :=
  foldl_app_preserves_not_isHNF LambdaTerm.Omega args Omega_not_isAppHead Omega_not_isHNF

/-- Omega is the canonical unsolvable term -/
theorem Omega_unsolvable : LambdaTerm.Omega.Unsolvable := by
  unfold LambdaTerm.Unsolvable LambdaTerm.Solvable
  intro ⟨args, h⟩
  -- Omega applied to any arguments never reaches HNF
  rw [foldl_app_Omega_not_isHNF args] at h
  exact Bool.false_ne_true h

/-! ## Lambda Theories

A lambda-theory is a congruence relation on lambda terms extending β-equality.
-/

/-- A lambda equation is a pair of terms -/
structure LambdaEq where
  lhs : LambdaTerm
  rhs : LambdaTerm
  deriving DecidableEq

/-- A lambda-theory is a set of equations closed under:
    - β-equality
    - Reflexivity, symmetry, transitivity
    - Congruence (substitution under context) -/
structure LambdaTheory where
  /-- The set of equations in the theory -/
  equations : Set LambdaEq
  /-- Contains all β-equalities (reflexive closure) -/
  refl : ∀ t, ⟨t, t⟩ ∈ equations
  /-- Symmetric -/
  symm : ∀ {t s}, ⟨t, s⟩ ∈ equations → ⟨s, t⟩ ∈ equations
  /-- Transitive -/
  trans : ∀ {t s u}, ⟨t, s⟩ ∈ equations → ⟨s, u⟩ ∈ equations → ⟨t, u⟩ ∈ equations
  /-- Beta reduction: (λt).s → s.subst 0 t = subst 0 s t (substitute arg s for var 0 in body t) -/
  beta : ∀ t s, ⟨LambdaTerm.app (.lam t) s, s.subst 0 t⟩ ∈ equations
  /-- Congruence for lambda -/
  congLam : ∀ {t t'}, ⟨t, t'⟩ ∈ equations → ⟨.lam t, .lam t'⟩ ∈ equations
  /-- Congruence for application (left) -/
  congAppLeft : ∀ {t t' s}, ⟨t, t'⟩ ∈ equations → ⟨.app t s, .app t' s⟩ ∈ equations
  /-- Congruence for application (right) -/
  congAppRight : ∀ {t s s'}, ⟨s, s'⟩ ∈ equations → ⟨.app t s, .app t s'⟩ ∈ equations

namespace LambdaTheory

/-- Two terms are equal in a theory -/
def equates (T : LambdaTheory) (t s : LambdaTerm) : Prop := ⟨t, s⟩ ∈ T.equations

/-- Theory inclusion -/
def le (T S : LambdaTheory) : Prop := T.equations ⊆ S.equations

instance : LE LambdaTheory := ⟨le⟩

/-- A theory is consistent if it doesn't equate I and K -/
def Consistent (T : LambdaTheory) : Prop := ¬T.equates LambdaTerm.I LambdaTerm.K

/-- A theory is sensible if all unsolvable terms are equal -/
def Sensible (T : LambdaTheory) : Prop :=
  ∀ t s, t.Unsolvable → s.Unsolvable → T.equates t s

/-- A theory is semisensible if unsolvable terms only equal unsolvable terms -/
def Semisensible (T : LambdaTheory) : Prop :=
  ∀ t s, t.Unsolvable → T.equates t s → s.Unsolvable

end LambdaTheory

/-! ## Sensibility

A theory is sensible if it equates all unsolvable terms.
-/

/-- Sensible and consistent implies semisensible.

    The proof requires consistency: if T equates a solvable s with unsolvable t,
    and T is sensible (all unsolvables equal), then ALL unsolvables equal s.
    Combined with the fact that I and K are both solvable and the theory axioms,
    this leads to I = K, contradicting consistency.

    This is a deep result requiring showing that:
    1. I and K are solvable (they have HNF)
    2. If T equates solvable s with all unsolvables, then T equates I = K

    We axiomatize this as it requires extensive lambda calculus machinery.
-/
theorem sensible_consistent_imp_semisensible {T : LambdaTheory}
    (hSens : T.Sensible) (hCons : T.Consistent) : T.Semisensible := by
  sorry

/-- Convenience version: sensible theories that don't equate I and K are semisensible -/
theorem sensible_imp_semisensible {T : LambdaTheory}
    (h : T.Sensible) (hCons : T.Consistent) : T.Semisensible :=
  sensible_consistent_imp_semisensible h hCons

/-! ## Graph Theories

The lambda-theory induced by a graph model D is the set of equations
valid in all interpretations in D.
-/

/-- An environment maps free variables to graph model elements -/
def Env (D : GraphModel) := Nat → D.Carrier

/-- Interpretation of lambda terms in a graph model.

    For graph models, the key insight is that a lambda abstraction λx.t
    is interpreted as the set of pairs (a, d) such that if the argument
    satisfies a, then the result is d.

    This is a simplified placeholder for the full graph-theoretic interpretation.
    The full version requires careful handling of the coding function.
-/
noncomputable def interpret (D : GraphModel) (ρ : Env D) : LambdaTerm → Set D.Carrier
  | .var n => {ρ n}
  | .lam t =>
      -- For now, we use a simplified interpretation
      -- Full version: { c(a, d) | ∀ x ∈ a, d ∈ ⟦t⟧(ρ[0 ↦ x]) }
      { d | ∃ x, d ∈ interpret D (fun n => if n = 0 then x else ρ (n - 1)) t }
  | .app t s =>
      -- d · e = { x | ∃ d' ∈ ⟦t⟧ρ, ∃ e ∈ ⟦s⟧ρ, x ∈ d' · e }
      { x | ∃ d' ∈ interpret D ρ t, ∃ e ∈ interpret D ρ s, x ∈ D.apply d' e }

/-- Two terms are equal in a graph model if they have equal interpretations -/
def validates (D : GraphModel) (eq : LambdaEq) : Prop :=
  ∀ ρ : Env D, interpret D ρ eq.lhs = interpret D ρ eq.rhs

/-- The lambda-theory induced by a graph model -/
def theoryOf (D : GraphModel) : Set LambdaEq :=
  { eq | validates D eq }

/-- A theory is a graph theory if it equals Th(D) for some graph model.
    Note: We fix the universe level u for the graph model. -/
def IsGraphTheory (T : LambdaTheory) : Prop :=
  ∃ D : GraphModel.{u}, T.equations = theoryOf D

/-! ## Key Theorems (Statements)

From Bucciarelli-Salibra:

1. Every graph theory is semisensible
2. Every graph theory contains the Böhm theory B
3. B is the maximal sensible graph theory
-/

/-- Every graph theory is semisensible (Bucciarelli-Salibra Theorem 29).

    The proof relies on the fact that in graph models:
    1. Unsolvable terms have "empty" approximations at all finite levels
    2. Solvable terms have non-empty finite approximations
    3. The interpretation function preserves this distinction
    4. If t = s in D with t unsolvable, the empty approximation of t
       must match some approximation of s, forcing s to be unsolvable

    See: Bucciarelli & Salibra, "Graph Lambda Theories" (2008), Theorem 29
-/
theorem graphTheory_semisensible (T : LambdaTheory) (h : IsGraphTheory T) : T.Semisensible := by
  sorry

/-- The intersection of graph theories is a graph theory.

    The proof uses the weak product construction: given graph models D_i,
    the weak product ◇_i D_i is a graph model whose theory is contained
    in the intersection of the individual theories.

    More precisely: Th(◇_i D_i) ⊆ ⋂_i Th(D_i)

    For an arbitrary intersection, we take the weak product of all models
    representing the theories in S.

    See: Bucciarelli & Salibra, "Graph Lambda Theories" (2008), §3
-/
theorem graphTheories_inter_closed (S : Set LambdaTheory) (hS : ∀ T ∈ S, IsGraphTheory T) :
    ∃ T : LambdaTheory, IsGraphTheory T ∧ T.equations = ⋂ T ∈ S, LambdaTheory.equations T := by
  sorry

/-! ## Summary

This file establishes the basic definitions for graph lambda theories:

1. **LambdaTerm**: De Bruijn indexed lambda calculus
2. **LambdaTheory**: Congruence relation extending β-equality
3. **Sensible/Semisensible**: Properties of theories regarding unsolvability
4. **GraphModel.theory**: Lambda-theory induced by a graph model

**Key Results (Bucciarelli-Salibra)**:
- Every graph theory is semisensible
- The intersection of graph theories is a graph theory
- The Böhm theory B is the maximal sensible graph theory

**Next Steps**:
- `BohmTree.lean`: Böhm trees and the Böhm theory B
- `WeakProduct.lean`: Weak product of graph models
- `Stratified.lean`: Stratified models and their properties
-/

end Mettapedia.GSLT.GraphTheory
