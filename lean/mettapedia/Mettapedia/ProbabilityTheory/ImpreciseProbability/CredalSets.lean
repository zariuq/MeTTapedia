import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Lattice

/-!
# Credal Sets: Interval Semantics from Families of Completions

This file develops a small, proof-agnostic interval/credal semantics layer.

The key idea is simple:

If a theory does not determine a unique real-valued interpretation `Θ`, then the
canonical semantics is the **set of values** an expression can take across all
compatible completions. For real-valued completions, that set induces an
interval via `sInf` / `sSup`.

This is useful both for general imprecise probability and for steelmanning
weaker or underdetermined representation theorems. The constructions here are
not tied to any particular K&S proof path.

## Main Results

1. `CredalAlgebra`: a lightweight interval-valued algebraic semantics
2. `IntervalAddSemantics`: the even lighter Minkowski-containment interface
3. `IntervalAddSemantics.ofThetaFamily`: canonical interval semantics from a
   nonempty family of additive completions
4. `collapse_theorem`: shrinking nested intervals collapse to point values in
   classical `ℝ`
-/

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

/-!
## §1: Credal Algebra — The Completion-Free Structure
-/

/-- An interval with lower ≤ upper -/
structure Interval where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper

/-- Interval width -/
def Interval.width (I : Interval) : ℝ := I.upper - I.lower

/-- Interval addition (Minkowski sum) -/
def Interval.add (I J : Interval) : Interval where
  lower := I.lower + J.lower
  upper := I.upper + J.upper
  valid := add_le_add I.valid J.valid

/-- Interval containment: I ⊆ J means J.lower ≤ I.lower and I.upper ≤ J.upper -/
def Interval.containedIn (I J : Interval) : Prop :=
  J.lower ≤ I.lower ∧ I.upper ≤ J.upper

instance : Add Interval := ⟨Interval.add⟩

/-- A credal algebra: an ordered associative operation with interval-valued measure -/
structure CredalAlgebra (α : Type*) where
  /-- The combining operation -/
  op : α → α → α
  /-- The interval-valued measure -/
  μ : α → Interval
  /-- Associativity -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- Containment: μ(x ⊕ y) is bounded by μ(x) + μ(y) -/
  containment : ∀ x y, (μ (op x y)).containedIn (μ x + μ y)
  /-- Order preservation on lower bounds -/
  order_lower : ∀ x y, (μ x).lower < (μ y).lower → (μ x).upper ≤ (μ y).lower

/-!
### Key Properties of Credal Algebras

Unlike classical probability, credal algebras:
1. Do NOT require exact point values
2. Do NOT require commutativity
3. Do NOT require completeness of ℝ
4. DO preserve the essential associative + containment structure
-/

/-- A lighter-weight “interval semantics” notion: interval-valued interpretation of a binary
operation, required only to satisfy the Minkowski containment law.

This is useful for steelmanning *weaker* axiom bundles: if the axioms do not determine a unique
point-valued Θ-representation, the natural semantics is a **set of completions** (a credal set),
which induces an **interval** for each term. The only generally valid law is containment:
`μ(x ⊕ y) ⊆ μ(x) + μ(y)`.

Unlike `CredalAlgebra`, this structure does **not** try to enforce additional order separation
properties between lower/upper bounds; those depend on the particular application domain. -/
structure IntervalAddSemantics (α : Type*) where
  /-- The combining operation -/
  op : α → α → α
  /-- Interval interpretation of elements -/
  μ : α → Interval
  /-- Associativity of the operation -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- Minkowski containment: the possible values of `x ⊕ y` lie in the Minkowski sum. -/
  containment : ∀ x y, (μ (op x y)).containedIn (μ x + μ y)

namespace IntervalAddSemantics

open Set

/-!
## Interval semantics from a family of point-valued completions

If a theory does not pin down a single point-valued representation `Θ`, the standard “weakness”
semantics is: interpret each expression by the **set of values it can take across all models**.
For real-valued models, this produces an interval by taking `sInf`/`sSup`.
-/

variable {α : Type*}

/-- The interval induced by a family of real-valued interpretations of `x`. -/
noncomputable def intervalOf (ι : Type*) [Nonempty ι] (Θ : ι → α → ℝ)
    (hBddBelow : ∀ x, BddBelow (range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (range fun i => Θ i x)) (x : α) : Interval :=
  { lower := sInf (range fun i => Θ i x)
    upper := sSup (range fun i => Θ i x)
    valid := by
      classical
      obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
      have hL : sInf (range fun i => Θ i x) ≤ Θ i0 x :=
        csInf_le (hBddBelow x) ⟨i0, rfl⟩
      have hU : Θ i0 x ≤ sSup (range fun i => Θ i x) :=
        le_csSup (hBddAbove x) ⟨i0, rfl⟩
      exact le_trans hL hU }

/-- Build `IntervalAddSemantics` from any nonempty family of point-valued additive models. -/
noncomputable def ofThetaFamily (op : α → α → α)
    (ι : Type*) [Nonempty ι]
    (Θ : ι → α → ℝ)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hAdd : ∀ i x y, Θ i (op x y) = Θ i x + Θ i y)
    (hBddBelow : ∀ x, BddBelow (range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (range fun i => Θ i x)) :
    IntervalAddSemantics α where
  op := op
  μ := intervalOf (ι := ι) (Θ := Θ) (hBddBelow := hBddBelow) (hBddAbove := hBddAbove)
  assoc := hAssoc
  containment := by
    intro x y
    dsimp [Interval.containedIn, Interval.add, intervalOf]
    constructor
    ·
      have hLower :
          sInf (range fun i => Θ i x) + sInf (range fun i => Θ i y) ≤
            sInf (range fun i => Θ i (op x y)) := by
        refine le_csInf ?_ ?_
        ·
          obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
          exact ⟨Θ i0 (op x y), ⟨i0, rfl⟩⟩
        · intro r hr
          rcases hr with ⟨i, rfl⟩
          have hx : sInf (range fun j => Θ j x) ≤ Θ i x :=
            csInf_le (hBddBelow x) ⟨i, rfl⟩
          have hy : sInf (range fun j => Θ j y) ≤ Θ i y :=
            csInf_le (hBddBelow y) ⟨i, rfl⟩
          simpa [hAdd i x y] using add_le_add hx hy
      exact hLower
    ·
      have hUpper :
          sSup (range fun i => Θ i (op x y)) ≤
            sSup (range fun i => Θ i x) + sSup (range fun i => Θ i y) := by
        refine csSup_le ?_ ?_
        ·
          obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
          exact ⟨Θ i0 (op x y), ⟨i0, rfl⟩⟩
        · intro r hr
          rcases hr with ⟨i, rfl⟩
          have hx : Θ i x ≤ sSup (range fun j => Θ j x) :=
            le_csSup (hBddAbove x) ⟨i, rfl⟩
          have hy : Θ i y ≤ sSup (range fun j => Θ j y) :=
            le_csSup (hBddAbove y) ⟨i, rfl⟩
          have : Θ i (op x y) ≤ sSup (range fun j => Θ j x) + sSup (range fun j => Θ j y) := by
            simpa [hAdd i x y] using add_le_add hx hy
          exact this
      exact hUpper

/-- Lower bounds are superadditive under the Minkowski containment law. -/
theorem lower_superadditive (S : IntervalAddSemantics α) (x y : α) :
    (S.μ x).lower + (S.μ y).lower ≤ (S.μ (S.op x y)).lower := by
  have h := (S.containment x y).1
  exact h

/-- Upper bounds are subadditive under the Minkowski containment law. -/
theorem upper_subadditive (S : IntervalAddSemantics α) (x y : α) :
    (S.μ (S.op x y)).upper ≤ (S.μ x).upper + (S.μ y).upper := by
  have h := (S.containment x y).2
  exact h

/-- Interval widths are subadditive under Minkowski containment. -/
theorem width_subadditive (S : IntervalAddSemantics α) (x y : α) :
    (S.μ (S.op x y)).width ≤ (S.μ x).width + (S.μ y).width := by
  have hU := sub_le_sub_right (upper_subadditive (S := S) x y) (S.μ (S.op x y)).lower
  have hL := sub_le_sub_left (lower_superadditive (S := S) x y) ((S.μ x).upper + (S.μ y).upper)
  have hUL :
      (S.μ (S.op x y)).upper - (S.μ (S.op x y)).lower ≤
        (S.μ x).upper + (S.μ y).upper - ((S.μ x).lower + (S.μ y).lower) := by
    exact le_trans hU hL
  have hUL' :
      (S.μ (S.op x y)).width ≤
        (S.μ x).upper + (S.μ y).upper - ((S.μ x).lower + (S.μ y).lower) := by
    simpa [Interval.width] using hUL
  have hrhs :
      (S.μ x).upper + (S.μ y).upper - ((S.μ x).lower + (S.μ y).lower) =
        (S.μ x).width + (S.μ y).width := by
    simp [Interval.width]
    ring
  simpa [hrhs] using hUL'

end IntervalAddSemantics

/-- If the family of completions is a singleton, the induced interval semantics is point-valued. -/
theorem intervalOf_unique {ι : Type*} [Subsingleton ι] [Nonempty ι]
    (Θ : ι → α → ℝ)
    (hBddBelow : ∀ x, BddBelow (Set.range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (Set.range fun i => Θ i x))
    (x : α) :
    (IntervalAddSemantics.intervalOf ι Θ hBddBelow hBddAbove x).lower =
      (IntervalAddSemantics.intervalOf ι Θ hBddBelow hBddAbove x).upper := by
  classical
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  have hEq : Set.range (fun i => Θ i x) = {Θ i0 x} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      have : i = i0 := Subsingleton.elim i i0
      simp [this]
    · intro hr
      rcases hr with rfl
      exact ⟨i0, rfl⟩
  simp [IntervalAddSemantics.intervalOf, hEq]

/-- The zero interval [0, 0] -/
def zeroInterval : Interval := ⟨0, 0, le_refl 0⟩

/-- The unit interval [0, 1] -/
def unitInterval : Interval := ⟨0, 1, by norm_num⟩

/-- A constant interval [c, c] -/
def constInterval (c : ℝ) : Interval := ⟨c, c, le_refl c⟩

/-!
## §2: The Trivial Credal Algebra (Existence Proof)
-/

/-- The trivial credal algebra on any monoid -/
def trivialCredalAlgebra (α : Type*) [AddMonoid α] : CredalAlgebra α where
  op := (· + ·)
  μ := fun _ => unitInterval
  assoc := add_assoc
  containment := fun _ _ => by
    unfold Interval.containedIn unitInterval HAdd.hAdd instHAdd Add.add instAddInterval Interval.add
    constructor <;> norm_num
  order_lower := fun _ _ h => by simp [unitInterval] at h

/-- Credal algebras exist -/
theorem credal_algebra_exists : ∃ (α : Type) (_ : CredalAlgebra α), True :=
  ⟨ℕ, trivialCredalAlgebra ℕ, trivial⟩

/-!
## §3: The Heisenberg Credal Algebra (Noncommutative Example)
-/

/-- Heisenberg group operation -/
def heisenbergOp (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2 + x.1 * y.2.1)

/-- The Heisenberg credal algebra -/
def heisenbergCredalAlgebra : CredalAlgebra (ℤ × ℤ × ℤ) where
  op := heisenbergOp
  μ := fun _ => unitInterval
  assoc := by
    intro x y z
    simp only [heisenbergOp]
    ring_nf
  containment := fun _ _ => by
    unfold Interval.containedIn unitInterval HAdd.hAdd instHAdd Add.add instAddInterval Interval.add
    constructor <;> norm_num
  order_lower := fun _ _ h => by simp [unitInterval] at h

/-- The Heisenberg credal algebra is noncommutative -/
theorem heisenberg_credal_not_comm :
    ∃ x y : ℤ × ℤ × ℤ, heisenbergCredalAlgebra.op x y ≠ heisenbergCredalAlgebra.op y x := by
  use (1, 0, 0), (0, 1, 0)
  simp only [heisenbergCredalAlgebra, heisenbergOp, ne_eq, Prod.mk.injEq]
  decide

/-!
## §4: Refined Credal Algebras (Shrinking Intervals)
-/

/-- A refined credal algebra: a sequence of interval measures with shrinking widths -/
structure RefinedCredalAlgebra (α : Type*) where
  /-- The combining operation -/
  op : α → α → α
  /-- Sequence of interval measures -/
  μ : ℕ → α → Interval
  /-- Associativity -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- Intervals are nested: lower bounds increase -/
  lower_mono : ∀ x n, (μ n x).lower ≤ (μ (n + 1) x).lower
  /-- Intervals are nested: upper bounds decrease -/
  upper_mono : ∀ x n, (μ (n + 1) x).upper ≤ (μ n x).upper
  /-- Widths converge to zero -/
  converge : ∀ x ε, ε > 0 → ∃ n, (μ n x).width < ε

/-!
## §5: The Collapse Theorem (Classical Recovery)
-/

/-- Extract the limiting point value using completeness (sSup) -/
noncomputable def limitingValue (R : RefinedCredalAlgebra α) (x : α) : ℝ :=
  sSup (Set.range (fun n => (R.μ n x).lower))

/-- Helper: lower bounds increase with index -/
theorem lower_increasing (R : RefinedCredalAlgebra α) (x : α) :
    ∀ m n, m ≤ n → (R.μ m x).lower ≤ (R.μ n x).lower := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans ih (R.lower_mono x k)

/-- Helper: upper bounds decrease with index -/
theorem upper_decreasing (R : RefinedCredalAlgebra α) (x : α) :
    ∀ m n, m ≤ n → (R.μ n x).upper ≤ (R.μ m x).upper := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans (R.upper_mono x k) ih

/-- Helper: lower bounds are bounded above by any upper bound -/
theorem lower_bdd_by_upper (R : RefinedCredalAlgebra α) (x : α) (n : ℕ) :
    ∀ m, (R.μ m x).lower ≤ (R.μ n x).upper := by
  intro m
  by_cases hmn : m ≤ n
  · exact le_trans (lower_increasing R x m n hmn) (R.μ n x).valid
  · push_neg at hmn
    exact le_trans (R.μ m x).valid (upper_decreasing R x n m (le_of_lt hmn))

/-- The Collapse Theorem: refined credal algebras yield point values via completeness -/
theorem collapse_theorem (R : RefinedCredalAlgebra α) :
    ∃ θ : α → ℝ, ∀ x n, (R.μ n x).lower ≤ θ x ∧ θ x ≤ (R.μ n x).upper := by
  use limitingValue R
  intro x n
  have h_bdd : BddAbove (Set.range (fun m => (R.μ m x).lower)) :=
    ⟨(R.μ 0 x).upper, fun v ⟨m, hm⟩ => hm ▸ lower_bdd_by_upper R x 0 m⟩
  have h_ne : (Set.range (fun m => (R.μ m x).lower)).Nonempty := ⟨(R.μ 0 x).lower, 0, rfl⟩
  constructor
  · exact le_csSup h_bdd ⟨n, rfl⟩
  · exact csSup_le h_ne (fun v ⟨m, hm⟩ => hm ▸ lower_bdd_by_upper R x n m)

/-!
## §6: Representation Strength Depends on Foundation

This file supports the following steelman:

- without enough completion/limit structure, a theory may determine only interval bounds;
- with a strong enough classical real line, shrinking interval semantics can collapse to
  point values.
-/

/-- The steelmanned theorem: completion-free semantics can remain credal, while stronger
foundations can collapse refined credal semantics to point values. -/
theorem steelmanned_KS :
    (∃ (α : Type) (C : CredalAlgebra α), ∃ x y, C.op x y ≠ C.op y x) ∧
    (∀ (α : Type*) (R : RefinedCredalAlgebra α),
      ∃ θ : α → ℝ, ∀ x n, (R.μ n x).lower ≤ θ x ∧ θ x ≤ (R.μ n x).upper) := by
  constructor
  · exact ⟨ℤ × ℤ × ℤ, heisenbergCredalAlgebra, heisenberg_credal_not_comm⟩
  · intro α R
    exact collapse_theorem R

end Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
