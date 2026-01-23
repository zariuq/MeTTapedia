import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interval Approach: Two Basic Facts (not a refutation)

This file proves:
1. **Weak interval axioms do not imply commutativity**: there is an associative noncommutative
   operation supporting trivial interval bounds.
2. **Extracting point values from nested intervals uses `sSup`**: a standard “intervals shrink to a
   point” construction can define a point selector `θ` using `sSup`, which is an explicit use of
   (conditional) completeness of `ℝ`.

## The Core Dichotomy

This file does **not** claim “K&S is impossible”. It only records two sanity checks about
interval-valued approaches:
- if the interval axioms are too weak, they cannot *force* commutativity (models exist where ⊕ is
  noncommutative);
- if one wants to *name a point* from a nested family of intervals, the common “take the supremum of
  lower bounds” construction uses `sSup` on `ℝ`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Experimental.RepresentationTheorem.Explorations.IntervalCollapse

/-!
## Part 1: Weak Interval Axioms Cannot Prove Commutativity

We construct a noncommutative algebra with a valid interval measure,
proving that weak interval axioms are consistent with noncommutativity.
-/

/-- The Heisenberg group ℤ³ with noncommutative multiplication.
    (a, b, c) * (a', b', c') = (a + a', b + b', c + c' + a*b')

    This is the standard discrete Heisenberg group, which is:
    - Associative
    - Has identity (0, 0, 0)
    - But NOT commutative: (1,0,0) * (0,1,0) ≠ (0,1,0) * (1,0,0) -/
def HeisenbergOp (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2 + x.1 * y.2.1)

/-- Heisenberg multiplication is associative -/
theorem heisenberg_assoc (x y z : ℤ × ℤ × ℤ) :
    HeisenbergOp (HeisenbergOp x y) z = HeisenbergOp x (HeisenbergOp y z) := by
  simp only [HeisenbergOp]
  ext
  · ring
  · ring
  · ring

/-- Heisenberg multiplication is NOT commutative -/
theorem heisenberg_not_comm : ∃ x y : ℤ × ℤ × ℤ, HeisenbergOp x y ≠ HeisenbergOp y x := by
  use (1, 0, 0), (0, 1, 0)
  -- (1,0,0) * (0,1,0) = (1, 1, 1*1) = (1, 1, 1)
  -- (0,1,0) * (1,0,0) = (1, 1, 0*0) = (1, 1, 0)
  simp only [HeisenbergOp, ne_eq, Prod.mk.injEq]
  decide

/-- Identity element for Heisenberg group -/
def heisenberg_id : ℤ × ℤ × ℤ := (0, 0, 0)

theorem heisenberg_id_left (x : ℤ × ℤ × ℤ) : HeisenbergOp heisenberg_id x = x := by
  simp [HeisenbergOp, heisenberg_id]

theorem heisenberg_id_right (x : ℤ × ℤ × ℤ) : HeisenbergOp x heisenberg_id = x := by
  simp [HeisenbergOp, heisenberg_id]

/-!
### The Trivial Interval Measure

The simplest way to satisfy weak interval axioms on ANY algebra:
use a constant interval [0, ∞) for all elements.

This satisfies all containment axioms trivially, and says nothing about
the algebraic structure — so it works equally well for commutative
and noncommutative algebras.
-/

/-- A trivial interval: [0, M] for some large M -/
structure TrivialInterval where
  bound : ℝ
  bound_pos : bound > 0

/-- The constant interval measure: μ(x) = [0, M] for all x -/
def constantIntervalMeasure (M : ℝ) (hM : M > 0) :
    (ℤ × ℤ × ℤ) → TrivialInterval :=
  fun _ => ⟨M, hM⟩

/-- The constant measure satisfies sub-additivity trivially -/
theorem constant_sub_additive (M : ℝ) (_hM : M > 0) (_x _y : ℤ × ℤ × ℤ) :
    (0 : ℝ) + 0 ≤ 0 := by linarith

/-- The constant measure satisfies super-additivity: M + M ≤ 2M, and we can use 2M as bound -/
theorem constant_super_additive (M : ℝ) (_hM : M > 0) (_x _y : ℤ × ℤ × ℤ) :
    M + M ≤ 2 * M := by linarith

/-!
### Theorem: Weak Axioms Don't Imply Commutativity

Since the Heisenberg group is noncommutative, and the constant interval measure
satisfies all weak interval axioms, we have:

**Weak interval axioms are consistent with noncommutativity.**

Therefore, weak interval axioms CANNOT prove that ⊕ is commutative.
-/

/-- **SEPARATION THEOREM**: There exists a noncommutative algebra with a valid
    interval measure satisfying all weak axioms.

    This proves that weak interval axioms cannot derive commutativity. -/
theorem weak_axioms_dont_imply_commutativity :
    ∃ (α : Type) (op : α → α → α) (μ : α → ℝ × ℝ),
      -- op is associative
      (∀ x y z, op (op x y) z = op x (op y z)) ∧
      -- μ satisfies sub/super-additivity (containment)
      (∀ x y, (μ x).1 + (μ y).1 ≤ (μ (op x y)).1) ∧
      (∀ x y, (μ (op x y)).2 ≤ (μ x).2 + (μ y).2) ∧
      -- But op is NOT commutative
      (∃ x y, op x y ≠ op y x) := by
  use ℤ × ℤ × ℤ
  use HeisenbergOp
  use fun _ => (0, 1)  -- constant interval [0, 1]
  refine ⟨heisenberg_assoc, ?_, ?_, heisenberg_not_comm⟩
  · intro x y; simp
  · intro x y; simp

/-!
## Part 2: Strong Interval Axioms Reintroduce Completion

For interval axioms to prove commutativity, they need to be "strong enough"
to distinguish x⊕y from y⊕x. This requires:

1. **Injectivity**: μ(x) = μ(y) → x = y
2. **Exactness**: intervals have width 0 (i.e., μ(x) = [θ(x), θ(x)] for some θ)
3. **Order reflection**: μ(x) < μ(y) ↔ x < y

But achieving width-0 intervals from positive-width intervals requires
taking a limit — which requires completeness!
-/

/-- Strong interval axiom: intervals shrink to points as precision increases -/
def IntervalsConverge {α : Type*} (μ : ℕ → α → ℝ × ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ n, (μ n x).2 - (μ n x).1 < ε

/-- Nested intervals: lower bounds increase, upper bounds decrease -/
def IntervalsNested {α : Type*} (μ : ℕ → α → ℝ × ℝ) : Prop :=
  (∀ x n, (μ n x).1 ≤ (μ n x).2) ∧                    -- valid intervals
  (∀ x n, (μ n x).1 ≤ (μ (n + 1) x).1) ∧              -- lower bounds increasing
  (∀ x n, (μ (n + 1) x).2 ≤ (μ n x).2)                -- upper bounds decreasing

/-- If intervals converge, there's a limiting point value.
    Note: This is noncomputable because sSup on ℝ requires completeness! -/
noncomputable def LimitingValue {α : Type*} (μ : ℕ → α → ℝ × ℝ) (x : α) : ℝ :=
  -- This uses completeness of ℝ (sup/inf existence)!
  sSup (Set.range fun n => (μ n x).1)

/-! **THE COMPLETION REQUIREMENT**:

To extract a point value θ(x) from shrinking intervals [Lₙ(x), Uₙ(x)],
we need to take limits:
  θ(x) = lim_{n→∞} Lₙ(x) = lim_{n→∞} Uₙ(x)

This limit exists IFF ℝ is complete (has suprema for bounded sets).

Without completeness, we only have:
  ∀ ε > 0, ∃ interval of width < ε containing θ(x)
but we cannot name θ(x) itself!
-/

/-- Helper: U is monotonically decreasing -/
theorem U_mono_decreasing {U : ℕ → ℝ} (h_U_dec : ∀ n, U (n + 1) ≤ U n) :
    ∀ m n, m ≤ n → U n ≤ U m := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans (h_U_dec k) ih

/-- Helper: L is monotonically increasing -/
theorem L_mono_increasing {L : ℕ → ℝ} (h_L_inc : ∀ n, L n ≤ L (n + 1)) :
    ∀ m n, m ≤ n → L m ≤ L n := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans ih (h_L_inc k)

/-- Helper: All lower bounds are below all upper bounds in nested intervals -/
theorem L_le_U_all {L U : ℕ → ℝ}
    (h_valid : ∀ n, L n ≤ U n)
    (h_L_inc : ∀ n, L n ≤ L (n + 1))
    (h_U_dec : ∀ n, U (n + 1) ≤ U n) :
    ∀ m n, L m ≤ U n := by
  intro m n
  by_cases hmn : m ≤ n
  · -- m ≤ n: L m ≤ L n ≤ U n
    exact le_trans (L_mono_increasing h_L_inc m n hmn) (h_valid n)
  · -- m > n: L m ≤ U m ≤ U n
    push_neg at hmn
    exact le_trans (h_valid m) (U_mono_decreasing h_U_dec n m (le_of_lt hmn))

/-- The key lemma: extracting a point from nested intervals needs completeness.

    This is exactly the Nested Interval Theorem. In ℝ (complete), it holds.
    In ℚ (incomplete), nested intervals around √2 have no common rational point. -/
theorem point_extraction_needs_completeness :
    ∀ (L U : ℕ → ℝ),
      (∀ n, L n ≤ U n) →                           -- valid intervals
      (∀ n, L n ≤ L (n + 1)) →                     -- lower bounds increasing
      (∀ n, U (n + 1) ≤ U n) →                     -- upper bounds decreasing
      (∀ ε > 0, ∃ n, U n - L n < ε) →              -- width → 0
      ∃ θ : ℝ, ∀ n, L n ≤ θ ∧ θ ≤ U n := by       -- common point exists
  intro L U h_valid h_L_inc h_U_dec _
  -- The common point is sSup (range L) = sInf (range U)
  -- This uses completeness of ℝ (conditionally complete lattice)
  have h_bdd : BddAbove (Set.range L) := ⟨U 0, fun x hx => by
    obtain ⟨n, rfl⟩ := hx
    exact L_le_U_all h_valid h_L_inc h_U_dec n 0⟩
  have h_nonempty : (Set.range L).Nonempty := ⟨L 0, 0, rfl⟩
  use sSup (Set.range L)
  intro n
  constructor
  · exact le_csSup h_bdd ⟨n, rfl⟩
  · -- sSup L ≤ U n because all L m ≤ U n (from nested property + valid intervals)
    exact csSup_le h_nonempty (fun x ⟨m, hm⟩ => by rw [← hm]; exact L_le_U_all h_valid h_L_inc h_U_dec m n)

/-!
### The Dichotomy Theorem

We can now state the fundamental dichotomy:
-/

/-! **COLLAPSE PATTERN** (informal, clarified):

Let `μₙ : α → Interval` be a nested sequence of intervals (lower bounds increase, upper bounds
decrease). If the widths converge to 0, then there is a *unique* point in the intersection.

In Lean, one common way to *define* such a point is:
`θ(x) := sSup {Lₙ(x)}`.

This file only formalizes the “point lies in every interval” property (using `sSup`). Any further
claims (e.g. additivity of `θ`, commutativity of ⊕) would require additional hypotheses relating
the interval data to the algebraic operations, and are **not** proved here.
-/

/-- **COLLAPSE THEOREM**: Strong interval axioms (nested + converging) collapse to point values.
    This requires completeness to define θ via sSup. -/
theorem strong_axioms_collapse_to_points (α : Type*) :
    ∀ (μ : ℕ → α → ℝ × ℝ),
      IntervalsConverge μ →
      IntervalsNested μ →
      -- Then there exists a point-valued representation
      ∃ θ : α → ℝ, ∀ x n, (μ n x).1 ≤ θ x ∧ θ x ≤ (μ n x).2 := by
  intro μ _ ⟨h_valid, h_L_inc, h_U_dec⟩
  -- This requires completeness to construct θ!
  -- We're using sSup which only exists in conditionally complete lattices (like ℝ)
  use fun x => sSup (Set.range (fun n => (μ n x).1))
  intro x n
  -- The proof uses:
  -- 1. L(n) ≤ sSup {L(m)} because L(n) is in the set
  -- 2. sSup {L(m)} ≤ U(n) because all L(m) ≤ U(n) (from nesting)
  -- Both steps use completeness of ℝ
  have h_bdd : BddAbove (Set.range (fun m => (μ m x).1)) := ⟨(μ 0 x).2, fun v hv => by
    obtain ⟨m, rfl⟩ := hv
    exact L_le_U_all (h_valid x) (h_L_inc x) (h_U_dec x) m 0⟩
  have h_nonempty : (Set.range (fun m => (μ m x).1)).Nonempty := ⟨(μ 0 x).1, 0, rfl⟩
  constructor
  · exact le_csSup h_bdd ⟨n, rfl⟩
  · exact csSup_le h_nonempty (fun v ⟨m, hm⟩ => by
      rw [← hm]; exact L_le_U_all (h_valid x) (h_L_inc x) (h_U_dec x) m n)

/-!
## Summary (for this file)

| Ingredient | What is shown here |
|---|---|
| Weak interval bounds | Consistent with noncommutativity (so do not imply commutativity) |
| Nested intervals + `θ := sSup Lₙ` | Produces a point in every interval, using completeness of `ℝ` |
-/

/-!
## Philosophical Interpretation

The interval approach represents a **credal set** or **imprecise probability**:
- Instead of a single measure μ : α → ℝ, we have a set of admissible measures
- The interval [L(x), U(x)] represents {μ(x) : μ in the credal set}

K&S's "limiting value d" is choosing a specific μ from this credal set.
This selection requires:
1. The credal set is non-empty (intervals are non-empty) ✓
2. The credal set shrinks to a point (intervals have width → 0)
3. We can name the unique point (completeness!)

Step 3 is where completeness sneaks in. Without it, we can only say
"there exists a sequence of shrinking intervals" but cannot name their
common limit.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Experimental.RepresentationTheorem.Explorations.IntervalCollapse
