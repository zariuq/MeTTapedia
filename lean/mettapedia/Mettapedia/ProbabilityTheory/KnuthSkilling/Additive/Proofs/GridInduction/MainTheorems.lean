import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Main Theorems: What Is (and Is Not) Shown Here

This file collects a few clean, *formal* facts that are often relevant when analyzing
Knuth–Skilling Appendix A and related “avoid continuity / avoid completeness” narratives.

Important: **Nothing in this file is a formal refutation of Knuth–Skilling Appendix A as a
classical mathematical theorem.** Most results here are either:
- general facts about `ℝ` (e.g. density of `ℚ`), or
- demonstrations that *certain proof tactics / informal slogans* require extra hypotheses
  when made fully explicit in Lean.

## What this file actually proves

1. **Density sanity checks** (§1): Between any two distinct reals there lies a rational.
   This is used only to caution against “pick a δ small enough to avoid all rationals”
   style arguments *unless* one has a reason those rationals are irrelevant.

2. **Interval-to-point extraction uses `sSup`** (§2): If one models “approaching a value”
   via nested shrinking intervals, then extracting a point value as a supremum is an explicit
   use of conditional completeness of `ℝ`. This is a bookkeeping statement about the
   *formalization*, not a claim that K&S must (or must not) assume completeness elsewhere.

3. **Weak axioms admit noncommutative models** (§2.A): As a sanity check, there are
   associative noncommutative operations supporting trivial weak interval bounds. This shows
   that “associativity + monotonicity” alone does not force commutativity.

If you want a “K&S succeeds / K&S fails” statement, it needs to be phrased against the *actual*
assumptions used in the Appendix A development (see `.../Core/Induction/ThetaPrime.lean`), not
against generic interval constructions.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.MainTheorems

/-!
## §1: Density sanity checks

This section does **not** prove any obstruction theorem about K&S by itself. It only records
the basic fact that `ℚ` is dense in `ℝ`, which is often used to sanity-check arguments of the form
“choose δ so small that nothing interesting happens in (θ(x), θ(x)+δ)”.

Whether such a move is valid depends on *what is considered “interesting”* (e.g. the range of θ,
or a discrete/quantized subset), and that depends on additional hypotheses.
-/

/-- Between any two distinct reals lies a rational (`ℚ` is dense in `ℝ`).

This is a sanity check only: it blocks *only* arguments that require an interval in `ℝ` to
contain no rationals (or no values of some explicitly specified dense set). -/
theorem rational_density_barrier :
    ∀ x y : ℝ, x < y → ∃ q : ℚ, x < q ∧ (q : ℝ) < y :=
  fun _ _ hxy => exists_rat_btwn hxy

/-- Given `δ > 0`, the open interval `(θ x, θ x + δ)` contains a rational number.

This lemma *does not* say anything about the image of `θ`; it only supplies a rational point
in the interval. Any use of this fact in a K&S-style “δ-shift” argument must separately justify
why that rational point is relevant (e.g. by showing the image of `θ` is discrete/quantized). -/
theorem delta_shift_obstructed (θ : α → ℝ) (x : α) (δ : ℝ) (hδ : δ > 0) :
    ∃ q : ℚ, θ x < q ∧ (q : ℝ) < θ x + δ := by
  have h : θ x < θ x + δ := by linarith
  exact exists_rat_btwn h

/-!
### What this does *not* say

The density lemma does **not** imply that any δ-shift argument is invalid. It only says that
intervals in `ℝ` are never “empty of rationals”. If a δ-shift argument needs an interval to avoid
some *specific* set (e.g. the image of θ restricted to a grid, or integer multiples of a step),
then that avoidance must be proved from the relevant hypotheses (e.g. quantization or separation),
not from “δ is small”.
-/

/-!
## §2: Interval-to-point extraction uses `sSup`

This section formalizes a simple point: if one represents “an unknown real number” by a nested
sequence of shrinking intervals `(Lₙ(x), Uₙ(x))`, then extracting a point value via
`θ(x) := sSup {Lₙ(x)}` is an *explicit* use of conditional completeness of `ℝ`.

This is a statement about a particular formalization pattern. It is not, by itself, a proof that
K&S must assume completeness in their Appendix A argument.
-/

/-- Weak interval axioms: sub/super-additivity bounds -/
structure WeakIntervalAxioms (α : Type*) (op : α → α → α) (μ : α → ℝ × ℝ) : Prop where
  /-- Intervals are valid: lower ≤ upper -/
  valid : ∀ x, (μ x).1 ≤ (μ x).2
  /-- Sub-additivity: lower bounds add -/
  sub_add : ∀ x y, (μ x).1 + (μ y).1 ≤ (μ (op x y)).1
  /-- Super-additivity: upper bounds add -/
  super_add : ∀ x y, (μ (op x y)).2 ≤ (μ x).2 + (μ y).2

/-- Strong interval axioms: intervals converge to points -/
structure StrongIntervalAxioms (α : Type*) (μ : ℕ → α → ℝ × ℝ) : Prop where
  /-- Intervals are nested and valid -/
  valid : ∀ x n, (μ n x).1 ≤ (μ n x).2
  lower_inc : ∀ x n, (μ n x).1 ≤ (μ (n + 1) x).1
  upper_dec : ∀ x n, (μ (n + 1) x).2 ≤ (μ n x).2
  /-- Widths converge to zero -/
  converge : ∀ x ε, ε > 0 → ∃ n, (μ n x).2 - (μ n x).1 < ε

/-!
### What this section does prove

- Part A constructs an associative noncommutative operation with trivial weak interval bounds.
  This is a “don’t overclaim” sanity check: weak constraints do not force commutativity.
- Part B shows that extracting point values *by taking suprema* uses `sSup`.

Any stronger meta-claim (e.g. “no first-order axiom system can derive …”) is outside the scope
of what is proved here.
-/

/-- The Heisenberg group: associative but NOT commutative -/
def HeisenbergOp (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2 + x.1 * y.2.1)

/-- Part A: Weak axioms admit noncommutative models -/
theorem weak_axioms_admit_noncommutative :
    ∃ (α : Type) (op : α → α → α) (μ : α → ℝ × ℝ),
      -- op is associative
      (∀ x y z, op (op x y) z = op x (op y z)) ∧
      -- μ satisfies weak interval axioms
      WeakIntervalAxioms α op μ ∧
      -- But op is NOT commutative
      (∃ x y, op x y ≠ op y x) := by
  use ℤ × ℤ × ℤ, HeisenbergOp, fun _ => (0, 1)
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- Associativity
    intro x y z
    simp only [HeisenbergOp]
    ext <;> ring
  · -- Valid intervals
    intro _; norm_num
  · -- Sub-additivity
    intro _ _; norm_num
  · -- Super-additivity
    intro _ _; norm_num
  · -- Noncommutativity
    use (1, 0, 0), (0, 1, 0)
    simp only [HeisenbergOp, ne_eq, Prod.mk.injEq]
    decide

/-- Part B: Strong axioms require completeness to extract point values.
    Note: This definition uses sSup, which requires completeness of ℝ! -/
noncomputable def extractPointValue (μ : ℕ → α → ℝ × ℝ) (x : α) : ℝ :=
  sSup (Set.range (fun n => (μ n x).1))

/-- Helper: lower bounds are monotonically increasing -/
theorem lower_mono (μ : ℕ → α → ℝ × ℝ) (hS : StrongIntervalAxioms α μ) (x : α) :
    ∀ m n, m ≤ n → (μ m x).1 ≤ (μ n x).1 := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans ih (hS.lower_inc x k)

/-- Helper: upper bounds are monotonically decreasing -/
theorem upper_mono (μ : ℕ → α → ℝ × ℝ) (hS : StrongIntervalAxioms α μ) (x : α) :
    ∀ m n, m ≤ n → (μ n x).2 ≤ (μ m x).2 := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans (hS.upper_dec x k) ih

/-- Helper: all lower bounds ≤ all upper bounds -/
theorem lower_le_upper_all (μ : ℕ → α → ℝ × ℝ) (hS : StrongIntervalAxioms α μ) (x : α) :
    ∀ m k, (μ m x).1 ≤ (μ k x).2 := by
  intro m k
  by_cases hmk : m ≤ k
  · exact le_trans (lower_mono μ hS x m k hmk) (hS.valid x k)
  · push_neg at hmk
    exact le_trans (hS.valid x m) (upper_mono μ hS x k m (le_of_lt hmk))

theorem strong_axioms_yield_points (α : Type*) (μ : ℕ → α → ℝ × ℝ)
    (hS : StrongIntervalAxioms α μ) :
    ∃ θ : α → ℝ, ∀ x n, (μ n x).1 ≤ θ x ∧ θ x ≤ (μ n x).2 := by
  use extractPointValue μ
  intro x n
  -- Bounded above by U(0)
  have h_bdd : BddAbove (Set.range (fun m => (μ m x).1)) :=
    ⟨(μ 0 x).2, fun v ⟨m, hm⟩ => hm ▸ lower_le_upper_all μ hS x m 0⟩
  have h_ne : (Set.range (fun m => (μ m x).1)).Nonempty := ⟨(μ 0 x).1, 0, rfl⟩
  constructor
  · -- L(n) ≤ sSup {L(m)}
    exact le_csSup h_bdd ⟨n, rfl⟩
  · -- sSup {L(m)} ≤ U(n)
    exact csSup_le h_ne (fun v ⟨m, hm⟩ => hm ▸ lower_le_upper_all μ hS x m n)

/-!
### Summary (for this file)

| Pattern | What is shown here |
|---|---|
| Weak interval constraints | Do not force commutativity |
| Interval shrinking + `θ := sSup Lₙ` | Uses conditional completeness of `ℝ` |
-/

/-!
## §3: Notes

This file intentionally avoids presenting philosophical conclusions as theorems.
Any “steelmanned K&S” statement should be tied to the precise Lean assumptions used in the
Appendix A development (finite-grid representations + extension step + globalization), rather
than to generic interval reasoning alone.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.MainTheorems
