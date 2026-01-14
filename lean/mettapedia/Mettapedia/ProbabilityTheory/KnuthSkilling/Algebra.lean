/-
# Knuth-Skilling Algebra: Basic Operations

Basic lemmas for KnuthSkillingAlgebra including:
- iterate_op function
- Commutativity for commutative operations
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open KnuthSkillingAlgebraBase

namespace KnuthSkillingAlgebra

section Base

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-- Iterate the operation: x ⊕ x ⊕ ... ⊕ x (n times).
This builds the sequence: ident, x, x⊕x, x⊕(x⊕x), ... -/
def iterate_op (x : α) : ℕ → α
  | 0 => ident
  | n + 1 => op x (iterate_op x n)

/-- iterate_op 0 = ident -/
theorem iterate_op_zero (a : α) : iterate_op a 0 = ident := rfl

/-- iterate_op 1 = a -/
theorem iterate_op_one (a : α) : iterate_op a 1 = a := by
  simp [iterate_op, op_ident_right]

/-- For commutative K&S algebras, iterate_op respects addition.
Note: The minimal KnuthSkillingAlgebra doesn't assume commutativity.
For the probability case (combine_fn is commutative), this holds. -/
theorem iterate_op_add_comm (x : α) (h_comm : ∀ a b : α, op a b = op b a)
    (m n : ℕ) :
    iterate_op x (m + n) = op (iterate_op x m) (iterate_op x n) := by
  induction n with
  | zero => simp [iterate_op, op_ident_right]
  | succ n ih =>
    -- Use commutativity to swap arguments and apply associativity
    calc iterate_op x (m + (n + 1))
        = iterate_op x ((m + n) + 1) := by ring_nf
      _ = op x (iterate_op x (m + n)) := rfl
      _ = op x (op (iterate_op x m) (iterate_op x n)) := by rw [ih]
      _ = op (op x (iterate_op x m)) (iterate_op x n) := by rw [← op_assoc]
      _ = op (op (iterate_op x m) x) (iterate_op x n) := by rw [h_comm x]
      _ = op (iterate_op x m) (op x (iterate_op x n)) := by rw [op_assoc]
      _ = op (iterate_op x m) (iterate_op x (n + 1)) := rfl

/-- Relation between Nat.iterate (op a) and iterate_op.
Nat.iterate (op a) n a = iterate_op a (n+1) -/
theorem nat_iterate_eq_iterate_op_succ (a : α) (n : ℕ) :
    Nat.iterate (op a) n a = iterate_op a (n + 1) := by
  induction n with
  | zero => simp [iterate_op, op_ident_right]
  | succ k ih =>
    -- Goal: (op a)^[k+1] a = iterate_op a (k+2)
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [ih]
    -- Now: op a (iterate_op a (k+1)) = iterate_op a (k+2)
    -- By definition: iterate_op a (k+2) = op a (iterate_op a (k+1))
    rfl

/-- iterate_op is strict mono in its iteration count for a > ident -/
theorem iterate_op_strictMono (a : α) (ha : ident < a) : StrictMono (iterate_op a) := by
  intro m n hmn
  induction n with
  | zero => exact (Nat.not_lt_zero m hmn).elim
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
    · -- m < k case: use IH and then show iterate_op a k < iterate_op a (k+1)
      have h1 : iterate_op a m < iterate_op a k := ih hlt
      have h2 : iterate_op a k < iterate_op a (k + 1) := by
        conv_lhs => rw [← op_ident_left (iterate_op a k)]
        exact op_strictMono_left (iterate_op a k) ha
      exact lt_trans h1 h2
    · -- m = k case: show iterate_op a m < iterate_op a (k+1)
      rw [heq]
      conv_lhs => rw [← op_ident_left (iterate_op a k)]
      exact op_strictMono_left (iterate_op a k) ha

/-- op is monotone in the left argument (from strict monotonicity). -/
theorem op_mono_left (y : α) {x₁ x₂ : α} (h : x₁ ≤ x₂) : op x₁ y ≤ op x₂ y := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (op_strictMono_left y hlt)
  · rw [heq]

/-- op is monotone in the right argument (from strict monotonicity). -/
theorem op_mono_right (x : α) {y₁ y₂ : α} (h : y₁ ≤ y₂) : op x y₁ ≤ op x y₂ := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (op_strictMono_right x hlt)
  · rw [heq]

/-- iterate_op preserves the operation: a^{n+1} = a ⊕ a^n -/
theorem iterate_op_succ (a : α) (n : ℕ) : iterate_op a (n + 1) = op a (iterate_op a n) := rfl

/-- Addition law for iterate_op: a^m ⊕ a^n = a^{m+n} -/
theorem iterate_op_add (a : α) (m n : ℕ) :
    op (iterate_op a m) (iterate_op a n) = iterate_op a (m + n) := by
  induction m with
  | zero =>
    simp only [iterate_op_zero, op_ident_left, Nat.zero_add]
  | succ m ih =>
    calc op (iterate_op a (m + 1)) (iterate_op a n)
        = op (op a (iterate_op a m)) (iterate_op a n) := by rw [iterate_op_succ]
      _ = op a (op (iterate_op a m) (iterate_op a n)) := by rw [op_assoc]
      _ = op a (iterate_op a (m + n)) := by rw [ih]
      _ = iterate_op a (m + n + 1) := by rw [← iterate_op_succ]
      _ = iterate_op a (m + 1 + n) := by ring_nf

/-- Multiplication law: (a^n)^m = a^{nm} -/
theorem iterate_op_mul (x : α) (n m : ℕ) :
    iterate_op (iterate_op x n) m = iterate_op x (n * m) := by
  induction m with
  | zero => simp only [iterate_op_zero, Nat.mul_zero]
  | succ m ih =>
    calc iterate_op (iterate_op x n) (m + 1)
        = op (iterate_op x n) (iterate_op (iterate_op x n) m) := rfl
      _ = op (iterate_op x n) (iterate_op x (n * m)) := by rw [ih]
      _ = iterate_op x (n + n * m) := by rw [iterate_op_add]
      _ = iterate_op x (n * (m + 1)) := by ring_nf

/-- Repetition lemma (≤ version): If a^n ≤ x^m then a^{nk} ≤ x^{mk} -/
theorem repetition_lemma_le (a x : α) (n m k : ℕ) (h : iterate_op a n ≤ iterate_op x m) :
    iterate_op a (n * k) ≤ iterate_op x (m * k) := by
  induction k with
  | zero => simp only [Nat.mul_zero, iterate_op_zero]; exact le_refl _
  | succ k ih =>
    have eq_a : n * (k + 1) = n * k + n := by ring
    have eq_x : m * (k + 1) = m * k + m := by ring
    rw [eq_a, eq_x, ← iterate_op_add, ← iterate_op_add]
    calc op (iterate_op a (n * k)) (iterate_op a n)
        ≤ op (iterate_op a (n * k)) (iterate_op x m) := op_mono_right _ h
      _ ≤ op (iterate_op x (m * k)) (iterate_op x m) := op_mono_left _ ih

/-- Repetition lemma (< version): If a^n < x^m then a^{nk} < x^{mk} for k > 0 -/
theorem repetition_lemma_lt (a x : α) (n m k : ℕ) (hk : k > 0) (h : iterate_op a n < iterate_op x m) :
    iterate_op a (n * k) < iterate_op x (m * k) := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero =>
      rw [Nat.zero_add, Nat.mul_one, Nat.mul_one]
      exact h
    | succ k ih =>
      have eq_a : n * (k + 1 + 1) = n * (k + 1) + n := by ring
      have eq_x : m * (k + 1 + 1) = m * (k + 1) + m := by ring
      rw [eq_a, eq_x, ← iterate_op_add, ← iterate_op_add]
      calc op (iterate_op a (n * (k + 1))) (iterate_op a n)
          < op (iterate_op a (n * (k + 1))) (iterate_op x m) :=
            op_strictMono_right _ h
        _ < op (iterate_op x (m * (k + 1))) (iterate_op x m) :=
            op_strictMono_left _ (ih (Nat.succ_pos k))

/-- iterate_op is strictly monotone in base for positive iterations -/
theorem iterate_op_strictMono_base (m : ℕ) (hm : 0 < m) (x y : α) (hxy : x < y) :
    iterate_op x m < iterate_op y m := by
  cases m with
  | zero => omega
  | succ n =>
    induction n with
    | zero =>
      simp only [Nat.zero_add, iterate_op_one]
      exact hxy
    | succ n ih =>
      have hm_pos : 0 < n + 1 := Nat.succ_pos n
      calc iterate_op x (n + 1 + 1)
          = op x (iterate_op x (n + 1)) := rfl
        _ < op x (iterate_op y (n + 1)) := op_strictMono_right x (ih hm_pos)
        _ < op y (iterate_op y (n + 1)) := op_strictMono_left (iterate_op y (n + 1)) hxy
        _ = iterate_op y (n + 1 + 1) := rfl

/-- Positive iterations are strictly greater than identity -/
theorem iterate_op_pos (y : α) (hy : ident < y) (m : ℕ) (hm : m > 0) :
    ident < iterate_op y m := by
  calc ident = iterate_op y 0 := (iterate_op_zero y).symm
    _ < iterate_op y m := iterate_op_strictMono y hy hm

/-- **Distribution lemma**: `(x ⊕ y)^m = x^m ⊕ y^m` when op is commutative.

This is the key lemma for expanding iterates of sums. Note that this is FALSE without
commutativity (see counterexample in Counterexamples.lean). -/
theorem iterate_op_op_distrib_of_comm (x y : α) (h_comm : ∀ a b : α, op a b = op b a) (m : ℕ) :
    iterate_op (op x y) m = op (iterate_op x m) (iterate_op y m) := by
  induction m with
  | zero => simp only [iterate_op_zero, op_ident_left]
  | succ m ih =>
    -- Goal: (x⊕y)^{m+1} = x^{m+1} ⊕ y^{m+1}
    -- LHS = (x⊕y) ⊕ (x^m ⊕ y^m) by IH
    -- RHS = (x ⊕ x^m) ⊕ (y ⊕ y^m)
    -- We need to rearrange (x⊕y)⊕(x^m⊕y^m) to (x⊕x^m)⊕(y⊕y^m)
    have step1 : op (op x y) (op (iterate_op x m) (iterate_op y m)) =
        op x (op y (op (iterate_op x m) (iterate_op y m))) := by
      rw [op_assoc]
    have step2 : op y (op (iterate_op x m) (iterate_op y m)) =
        op (op y (iterate_op x m)) (iterate_op y m) := by
      rw [← op_assoc]
    have step3 : op y (iterate_op x m) = op (iterate_op x m) y := h_comm y (iterate_op x m)
    have step4 : op (op (iterate_op x m) y) (iterate_op y m) =
        op (iterate_op x m) (op y (iterate_op y m)) := op_assoc _ _ _
    have step5 : op x (op (iterate_op x m) (op y (iterate_op y m))) =
        op (op x (iterate_op x m)) (op y (iterate_op y m)) := by
      rw [← op_assoc]
    calc iterate_op (op x y) (m + 1)
        = op (op x y) (iterate_op (op x y) m) := rfl
      _ = op (op x y) (op (iterate_op x m) (iterate_op y m)) := by rw [ih]
      _ = op x (op y (op (iterate_op x m) (iterate_op y m))) := by rw [step1]
      _ = op x (op (op y (iterate_op x m)) (iterate_op y m)) := by rw [step2]
      _ = op x (op (op (iterate_op x m) y) (iterate_op y m)) := by rw [step3]
      _ = op x (op (iterate_op x m) (op y (iterate_op y m))) := by rw [step4]
      _ = op (op x (iterate_op x m)) (op y (iterate_op y m)) := by rw [step5]
      _ = op (iterate_op x (m + 1)) (iterate_op y (m + 1)) := rfl

/-- Variant: op distributes over iterate_op in opposite order -/
theorem iterate_op_op_distrib_of_comm' (x y : α) (h_comm : ∀ a b : α, op a b = op b a) (m : ℕ) :
    op (iterate_op x m) (iterate_op y m) = iterate_op (op x y) m :=
  (iterate_op_op_distrib_of_comm x y h_comm m).symm

end Base

/-! The Archimedean property (`bounded_by_iterate`, `op_archimedean_of_separation`) is
derived from `KSSeparation` in `Separation/SandwichSeparation.lean`. It is NOT an axiom. -/

end KnuthSkillingAlgebra

/-! ## Separation Typeclass

`KSSeparation` captures the “rational separation” property used throughout the representation
arguments: for `ident < x < y` and any base `a > ident`, some power of `a` sits strictly between a
power of `x` and a power of `y`.

In the original K&S Appendix A narrative this is treated as a derived lemma, but in our
formalization it is an *explicit* typeclass assumption: it is **not** derivable from the base
`KnuthSkillingAlgebra` axioms in general (see
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/KSSeparationNotDerivable.lean`).

`Separation/Derivation.lean` is the (still experimental) attempt to derive `KSSeparation` from additional
structured hypotheses, and it currently packages the remaining hard step as a `Prop`-class
(`LargeRegimeSeparationSpec`). -/

/-- **KSSeparation**: the iterate/power “sandwich” axiom.

Paper cross-reference:
- `paper/ks-formalization.tex`, Subsection “The Separation Property” and Subsection
  “The Separation Type Classes” (inside Section `sec:main`).

This is the statement that for any positive `a` and `ident < x < y`, there exist exponents `n,m`
with `0 < m` such that `x^m < a^n ≤ y^m`.

Important meta-fact (formalized):
`KSSeparation` is **not** derivable from the bare `KnuthSkillingAlgebra` axioms in general.
See the semidirect-product countermodel in
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/KSSeparationNotDerivable.lean`.

Related files:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Separation/Derivation.lean` explores additional structured
  hypotheses under which `KSSeparation` *can* be derived. -/
class KSSeparation (α : Type*) [KnuthSkillingAlgebraBase α] where
  /-- For any positive x < y and any base a > ident, we can find exponents (n, m)
  such that x^m < a^n ≤ y^m. This is the key property enabling representation. -/
  separation : ∀ {a x y : α}, KnuthSkillingAlgebraBase.ident < a →
      KnuthSkillingAlgebraBase.ident < x → KnuthSkillingAlgebraBase.ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
      KnuthSkillingAlgebra.iterate_op a n ≤ KnuthSkillingAlgebra.iterate_op y m

namespace KSSeparation

open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α]

/-- Strengthening of `KSSeparation.separation`: we can request an arbitrarily large exponent `m`.

This follows by applying `separation` to `x^(N+1) < y^(N+1)` and unfolding with `iterate_op_mul`. -/
theorem separation_large_m {a x y : α} (ha : ident < a) (hx : ident < x) (hy : ident < y) (hxy : x < y)
    (N : ℕ) :
    ∃ n m : ℕ, N < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  classical
  set p : ℕ := N + 1
  have hp_pos : 0 < p := Nat.succ_pos N
  have hx_p : ident < iterate_op x p := iterate_op_pos x hx p hp_pos
  have hy_p : ident < iterate_op y p := iterate_op_pos y hy p hp_pos
  have hxy_p : iterate_op x p < iterate_op y p := iterate_op_strictMono_base p hp_pos x y hxy
  rcases (KSSeparation.separation (a := a) (x := iterate_op x p) (y := iterate_op y p) ha hx_p hy_p hxy_p) with
    ⟨n, m₁, hm₁_pos, h_gap, h_in⟩
  refine ⟨n, p * m₁, ?_, ?_, ?_⟩
  · -- N < p * m₁
    have hp_lt : N < p := Nat.lt_succ_self N
    have hm₁_pos' : 0 < m₁ := hm₁_pos
    have : p ≤ p * m₁ := Nat.le_mul_of_pos_right p hm₁_pos'
    exact lt_of_lt_of_le hp_lt this
  · -- unfold the left inequality
    simpa [iterate_op_mul, Nat.mul_assoc] using h_gap
  · -- unfold the right inequality
    simpa [iterate_op_mul, Nat.mul_assoc] using h_in

/-- A convenient “one-sided commensurability” corollary of `KSSeparation`:
for any positive base `a` and positive element `x`, some power of `a` sits above a power of `x`
and below a *square-power* of `x`.

This is the schematic inequality `x^m < a^n ≤ (x⊕x)^m = x^(2m)` that mimics the fact that
`log_a(x)` lies in some rational interval of width `1`. -/
theorem separation_between_self_and_square {a x : α} (ha : ident < a) (hx : ident < x) :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op x (2 * m) := by
  -- Apply separation to `x < x⊕x`.
  have hx2 : ident < iterate_op x 2 := iterate_op_pos x hx 2 (by decide)
  have hx_lt_x2 : x < iterate_op x 2 := by
    -- `x = x^1 < x^2` since iterations of a positive element are strictly increasing.
    simpa [iterate_op_one] using (iterate_op_strictMono x hx (by decide : (1 : ℕ) < 2))
  rcases KSSeparation.separation (a := a) (x := x) (y := iterate_op x 2) ha hx hx2 hx_lt_x2 with
    ⟨n, m, hm_pos, hlt, hle⟩
  refine ⟨n, m, hm_pos, hlt, ?_⟩
  -- Rewrite the upper bound `(x^2)^m` as `x^(2m)`.
  simpa [iterate_op_mul, Nat.mul_assoc] using hle

end KSSeparation

/-! ## A Strict Variant of Separation

`KSSeparation` only guarantees `a^n ≤ y^m` on the upper side. For some Appendix A.3.4 steps
(notably, ruling out “minimal” C-statistics hitting the cut), it is convenient to assume the
strict strengthening where `a^n < y^m`.  This is packaged separately so we can precisely
track where strictness is used.
-/

/-- **KSSeparationStrict**: strengthen `KSSeparation` by making the upper bound strict.

Paper cross-reference:
- `paper/ks-formalization.tex`, Subsection “The Separation Type Classes” (Section `sec:main`).
- The informal “density implies strict separation” remark corresponds to
  `KSSeparation.toKSSeparationStrict_of_denselyOrdered` below. -/
class KSSeparationStrict (α : Type*) [KnuthSkillingAlgebraBase α] extends KSSeparation α where
  /-- For any positive `x < y` and any base `a > ident`, find exponents `(n,m)` with `0 < m` and
  `x^m < a^n < y^m`. -/
  separation_strict : ∀ {a x y : α}, KnuthSkillingAlgebraBase.ident < a →
      KnuthSkillingAlgebraBase.ident < x → KnuthSkillingAlgebraBase.ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebra.iterate_op x m < KnuthSkillingAlgebra.iterate_op a n ∧
      KnuthSkillingAlgebra.iterate_op a n < KnuthSkillingAlgebra.iterate_op y m
  /-- `KSSeparationStrict` implies `KSSeparation` by weakening the strict upper bound. -/
  separation := by
    intro a x y ha hx hy hxy
    rcases separation_strict (a := a) (x := x) (y := y) ha hx hy hxy with
      ⟨n, m, hm_pos, hlt, hgt⟩
    exact ⟨n, m, hm_pos, hlt, le_of_lt hgt⟩

namespace KSSeparationStrict

open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparationStrict α]

end KSSeparationStrict

namespace KSSeparation

open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α]

/-- If we can pick an intermediate point between any `ident < x < y`, then `KSSeparation` upgrades to
the strict variant `KSSeparationStrict`.

This is a weaker hypothesis than `[DenselyOrdered α]`: we only need density *above* `ident`, since
`KSSeparation` is only stated for positive `x,y`. -/
theorem toKSSeparationStrict_of_exists_between_pos
    (hBetween : ∀ {x y : α}, ident < x → x < y → ∃ z, x < z ∧ z < y) :
    KSSeparationStrict α := by
  classical
  refine ⟨?_⟩
  intro a x y ha hx hy hxy
  rcases hBetween (x := x) (y := y) hx hxy with ⟨z, hxz, hzy⟩
  have hz : ident < z := lt_trans hx hxz
  rcases (KSSeparation.separation (a := a) (x := x) (y := z) ha hx hz hxz) with
    ⟨n, m, hm_pos, hlt, hle⟩
  have hz_lt_y : iterate_op z m < iterate_op y m :=
    iterate_op_strictMono_base m hm_pos z y hzy
  have hlt' : iterate_op a n < iterate_op y m := lt_of_le_of_lt hle hz_lt_y
  exact ⟨n, m, hm_pos, hlt, hlt'⟩

/-- If the order on `α` is dense, then `KSSeparation` upgrades to the strict variant
`KSSeparationStrict`.

Paper cross-reference:
- `paper/ks-formalization.tex`, listing “Density implies strict separation” in Subsection
  “The Separation Type Classes” (Section `sec:main`).

This isolates an extra hypothesis that suffices to rule out the “upper-bound equality” corner case:
pick `z` with `x < z < y`, apply separation to `(x,z)`, then use `z^m < y^m` to make the upper
bound strict. -/
theorem toKSSeparationStrict_of_denselyOrdered [DenselyOrdered α] : KSSeparationStrict α := by
  exact
    toKSSeparationStrict_of_exists_between_pos (α := α)
      (hBetween := fun {x y} _hx hxy => exists_between hxy)

end KSSeparation

end Mettapedia.ProbabilityTheory.KnuthSkilling

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
## Commutation Helpers

These small lemmas are convenient when reasoning about “new atom commutes with old atoms” style
assumptions (see `RepresentationTheorem/Core/Induction/Goertzel.lean`).
-/

namespace KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-- `x` and `y` commute with respect to `KnuthSkillingAlgebraBase.op`. -/
def Commutes (x y : α) : Prop :=
  op x y = op y x

namespace Commutes

theorem symm {x y : α} (h : Commutes (α := α) x y) : Commutes (α := α) y x := by
  dsimp [Commutes] at h ⊢
  exact h.symm

theorem refl (x : α) : Commutes (α := α) x x :=
  rfl

theorem ident_left (x : α) : Commutes (α := α) ident x := by
  simp [Commutes, op_ident_left, op_ident_right]

theorem ident_right (x : α) : Commutes (α := α) x ident := by
  simp [Commutes, op_ident_left, op_ident_right]

/-- If `x` commutes with `y` and `z`, then it commutes with `y ⊕ z`. -/
theorem op_right {x y z : α} (hxy : Commutes (α := α) x y) (hxz : Commutes (α := α) x z) :
    Commutes (α := α) x (op y z) := by
  dsimp [Commutes] at hxy hxz ⊢
  calc
    op x (op y z) = op (op x y) z := by
      simp [op_assoc]
    _ = op (op y x) z := by
      simp [hxy]
    _ = op y (op x z) := by
      simp [op_assoc]
    _ = op y (op z x) := by
      simp [hxz]
    _ = op (op y z) x := by
      simp [op_assoc]

/-- If `y` commutes with `x` and `z`, then `y ⊕ z` commutes with `x`. -/
theorem op_left {x y z : α} (hyx : Commutes (α := α) y x) (hzx : Commutes (α := α) z x) :
    Commutes (α := α) (op y z) x := by
  exact (op_right (α := α) (x := x) (y := y) (z := z) hyx.symm hzx.symm).symm

end Commutes

/-- The set of elements commuting with a fixed `x`. -/
def centralizer (x : α) : Set α :=
  {y : α | Commutes (α := α) x y}

namespace centralizer

theorem mem_iff {x y : α} : y ∈ centralizer (α := α) x ↔ Commutes (α := α) x y := by
  rfl

theorem ident_mem (x : α) : ident ∈ centralizer (α := α) x :=
  Commutes.ident_right (α := α) x

theorem closed_op {x y z : α} (hy : y ∈ centralizer (α := α) x) (hz : z ∈ centralizer (α := α) x) :
    op y z ∈ centralizer (α := α) x :=
  Commutes.op_right (α := α) (x := x) (y := y) (z := z) hy hz

end centralizer

end KnuthSkillingAlgebra

end Mettapedia.ProbabilityTheory.KnuthSkilling
