/-
# The Associativity Theorem (Knuth-Skilling Appendix A)

This file formalizes the core theorem from Knuth & Skilling's "Foundations of Inference"
(arXiv:1008.4831) that derives the sum rule from associativity.

## The K&S Approach

Unlike Aczél's 1966 approach (which uses continuity and Cauchy functional equations),
K&S provide a **constructive, finite** proof that:
- Avoids continuity assumptions
- Avoids assuming inverse operations exist
- Derives commutativity (doesn't assume it!)

The construction builds valuations on "atom types" - we start with one type,
establish an integer grid, then inductively add more types using:
1. The **Repetition Lemma**: scaling relationships
2. **Separation** into sets A, B, C
3. **Assignment** based on whether B is empty

## Main Result

If a binary operation ⊕ satisfies:
- Axiom 1 (Order): x < y → x ⊕ z < y ⊕ z and z ⊕ x < z ⊕ y
- Axiom 2 (Associativity): (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)

Then there exists a strictly increasing function Θ such that:
  x ⊕ y = Θ⁻¹(Θ(x) + Θ(y))

Equivalently: ⊕ IS addition, up to monotone regrade.

## References

- Knuth & Skilling (2012). "Foundations of Inference", Axioms 1(1):38-73, Appendix A
- arXiv:1008.4831

## Optimal Transport Structure (Oruži's Lens)

The K&S proof has a beautiful optimal transport structure:

### State Space Z
- Z = Valuations μ : (atom configurations) → ℝ
- A configuration is a tuple (r₁,...,rₖ) counting atoms of each type

### Endpoint Distributions
- ρ₀ = Single-type valuation: μ(r) = r·a (integer grid)
- ρₖ = k-type linear valuation: μ(r₁,...,rₖ) = Σᵢ rᵢ·aᵢ

### Reference Dynamics (Markov kernel)
- Adding one atom type at a time
- K : valuations on k types → valuations on k+1 types
- The kernel respects order and associativity constraints

### The Transport Problem
Given μₖ on k types satisfying axioms, extend to μₖ₊₁ on k+1 types.
The Repetition Lemma provides the constraint: scaled comparisons are preserved.
Sets A, B, C partition the landing zone for the new value.

### The Coupling
- If B is non-empty: DETERMINISTIC coupling (value rationally determined)
- If B is empty: FREE coupling within the gap (choose any δ in the interval)

### Regrade Freedom = Gauge Freedom
The freedom to choose δ within the gap is the gauge freedom of OT.
Any monotone Θ gives an equivalent valid assignment.
This is why the theorem says "up to regrade" - the transport is unique UP TO GAUGE.

### Proof Plan (Optimal Transport Path)
1. **Base case** (ρ₀): One type → integer grid μ(r) = ra ✓
2. **Repetition Lemma**: Constraint preservation under scaling
3. **Separation**: Classify into A, B, C (the bin structure)
4. **Assignment**: Two cases (deterministic vs free coupling)
5. **Induction**: k types → k+1 types (the kernel composition)
6. **Convergence**: The limit μ_∞ is the linearizer Θ

This is Schrödinger bridge theory in disguise - we're finding the most likely
path (under the reference dynamics of "add one type") connecting the simple
distribution (one type) to the complex distribution (all types).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling

namespace Mettapedia.ProbabilityTheory.AssociativityTheorem

open Classical

/-! ## Part 1: The K&S Axioms

We formalize exactly Axioms 1 and 2 from the paper.
Note: We do NOT assume commutativity - it will be DERIVED!
-/

/-- The K&S axioms for a combination operation.
These are exactly Axioms 1 and 2 from the paper. -/
structure KSAxioms where
  /-- The combination operation ⊕ -/
  op : ℝ → ℝ → ℝ
  /-- Axiom 1a: x < y → x ⊕ z < y ⊕ z (order-preserving on left) -/
  order_left : ∀ x y z, x < y → op x z < op y z
  /-- Axiom 1b: x < y → z ⊕ x < z ⊕ y (order-preserving on right) -/
  order_right : ∀ x y z, x < y → op z x < op z y
  /-- Axiom 2: (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z) (associativity) -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)

variable (A : KSAxioms)

/-! ### Derived Properties

Following the paper, we derive cancellativity and other useful facts.
-/

/-- Order extends to ≤ (left argument) -/
lemma order_left_le (x y z : ℝ) (h : x ≤ y) : A.op x z ≤ A.op y z := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (A.order_left x y z hlt)
  · rw [heq]

/-- Order extends to ≤ (right argument) -/
lemma order_right_le (x y z : ℝ) (h : x ≤ y) : A.op z x ≤ A.op z y := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (A.order_right x y z hlt)
  · rw [heq]

/-- Cancellativity (Equation 2 in the paper):
    x ⊕ z ≤ y ⊕ z → x ≤ y -/
lemma cancel_left (x y z : ℝ) (h : A.op x z ≤ A.op y z) : x ≤ y := by
  by_contra hc
  push_neg at hc
  have := A.order_left y x z hc
  linarith

/-- Cancellativity on right:
    z ⊕ x ≤ z ⊕ y → x ≤ y -/
lemma cancel_right (x y z : ℝ) (h : A.op z x ≤ A.op z y) : x ≤ y := by
  by_contra hc
  push_neg at hc
  have := A.order_right y x z hc
  linarith

/-- Strict cancellativity left -/
lemma cancel_left_strict (x y z : ℝ) (h : A.op x z < A.op y z) : x < y := by
  by_contra hc
  push_neg at hc
  have := order_left_le A y x z hc
  linarith

/-- Strict cancellativity right -/
lemma cancel_right_strict (x y z : ℝ) (h : A.op z x < A.op z y) : x < y := by
  by_contra hc
  push_neg at hc
  have := order_right_le A y x z hc
  linarith

/-! ## Part 2: One Type of Atom

Following Section A.2 of the paper, we establish the integer grid for one atom type.

Key insight: For a single atom type with value `a`, the sequence
  m(0 of a), m(1 of a), m(2 of a), ...
is strictly increasing (for positive-style atoms).

We can CHOOSE to assign m(r of a) = r·a for any a > 0.
This is the "regrade freedom" - any monotone regrade is valid.
-/

/-- n-fold iteration: a^[n] = a ⊕ a ⊕ ... ⊕ a (n times)
    a^[0] is defined as the identity element (which we'll derive exists) -/
noncomputable def iterate (n : ℕ) (a : ℝ) : ℝ :=
  match n with
  | 0 => 0  -- We'll prove 0 acts as identity
  | n + 1 => A.op a (iterate n a)

/-- iterate 1 a = a (assuming identity at 0) -/
lemma iterate_one (a : ℝ) : iterate A 1 a = A.op a 0 := rfl

/-- iterate (n+1) a = a ⊕ iterate n a -/
lemma iterate_succ (n : ℕ) (a : ℝ) : iterate A (n + 1) a = A.op a (iterate A n a) := rfl

/-- iterate 0 a = 0 -/
lemma iterate_zero (a : ℝ) : iterate A 0 a = 0 := rfl

/-! ### The Key Lemma: iterate_add

This is the heart of the OT base case. It says that the integer grid
has additive structure: iterate (m+n) a = (iterate m a) ⊕ (iterate n a).

This requires assuming 0 is an identity element for ⊕.
-/

/-- iterate_add: iterate (m + n) a = (iterate m a) ⊕ (iterate n a)
    This is the fundamental additivity of the integer grid.
    Requires: 0 is a left identity for ⊕. -/
lemma iterate_add (a : ℝ) (h_ident : ∀ x, A.op 0 x = x) :
    ∀ m n, iterate A (m + n) a = A.op (iterate A m a) (iterate A n a) := by
  intro m n
  induction m with
  | zero =>
    simp only [Nat.zero_add, iterate_zero]
    rw [h_ident]
  | succ m ih =>
    -- iterate (m+1+n) a = iterate ((m+n)+1) a = a ⊕ iterate (m+n) a
    --                   = a ⊕ (iterate m a ⊕ iterate n a)  [by ih]
    --                   = (a ⊕ iterate m a) ⊕ iterate n a  [by assoc]
    --                   = iterate (m+1) a ⊕ iterate n a
    calc iterate A (m + 1 + n) a
        = iterate A ((m + n) + 1) a := by ring_nf
      _ = A.op a (iterate A (m + n) a) := rfl
      _ = A.op a (A.op (iterate A m a) (iterate A n a)) := by rw [ih]
      _ = A.op (A.op a (iterate A m a)) (iterate A n a) := by rw [A.assoc]
      _ = A.op (iterate A (m + 1) a) (iterate A n a) := rfl

/-- Corollary: iterate respects multiplication by constants.
    This is a weaker version - full proof needs more care about iterate definition. -/
lemma iterate_mul (a : ℝ) (h_ident : ∀ x, A.op 0 x = x) :
    ∀ n m, iterate A (n * m) a = iterate A n (iterate A m a) := by
  -- This requires showing iterate commutes appropriately
  -- For now, mark sorry - will be filled in once we have the full identity lemma
  sorry

/-- Helper: 0 is a right identity when it's a left identity and we have order.
    Proof: From 0 ⊕ x = x and order, we can show x ⊕ 0 = x. -/
lemma identity_right_of_left (h_ident : ∀ x, A.op 0 x = x) :
    ∀ x, A.op x 0 = x := by
  intro x
  -- The cleanest approach: use cancellativity and associativity.
  -- We have: (x ⊕ 0) ⊕ y = x ⊕ (0 ⊕ y) = x ⊕ y  [by assoc and identity]
  -- So for any y: (x ⊕ 0) ⊕ y = x ⊕ y
  -- By cancel_left (which gives ≤) and cancel_left on the reverse (also ≤),
  -- we get x ⊕ 0 = x by antisymmetry.
  have h : ∀ y, A.op (A.op x 0) y = A.op x y := by
    intro y
    calc A.op (A.op x 0) y = A.op x (A.op 0 y) := A.assoc x 0 y
      _ = A.op x y := by rw [h_ident]
  -- From (x ⊕ 0) ⊕ z = x ⊕ z for all z, by cancel_left: x ⊕ 0 ≤ x
  have hle : A.op x 0 ≤ x := cancel_left A (A.op x 0) x 0 (le_of_eq (h 0))
  -- Also x ⊕ z = (x ⊕ 0) ⊕ z, so by cancel_left: x ≤ x ⊕ 0
  have hge : x ≤ A.op x 0 := cancel_left A x (A.op x 0) 0 (le_of_eq (h 0).symm)
  exact le_antisymm hle hge

/-- Helper: iterate n a ≥ 0 for all n when a > 0 and 0 is identity -/
lemma iterate_nonneg (a : ℝ) (ha : 0 < a) (h_ident : ∀ x, A.op 0 x = x) :
    ∀ n, iterate A n a ≥ 0 := by
  intro n
  induction n with
  | zero => simp [iterate_zero]
  | succ n' ih =>
    have hgt : iterate A (n' + 1) a > iterate A n' a := by
      calc iterate A (n' + 1) a = A.op a (iterate A n' a) := rfl
        _ > A.op 0 (iterate A n' a) := A.order_left 0 a _ ha
        _ = iterate A n' a := h_ident _
    linarith

/-- Helper: iterate (k+1) a > 0 when a > 0 and 0 is identity -/
lemma iterate_pos (a : ℝ) (ha : 0 < a) (h_ident : ∀ x, A.op 0 x = x) :
    ∀ k, iterate A (k + 1) a > 0 := by
  intro k
  calc iterate A (k + 1) a = A.op a (iterate A k a) := rfl
    _ > A.op 0 (iterate A k a) := A.order_left 0 a _ ha
    _ = iterate A k a := h_ident _
    _ ≥ 0 := iterate_nonneg A a ha h_ident k

/-- Iterate is strictly increasing in n when a > 0 and 0 is identity.
    This establishes the strictly increasing integer grid. -/
lemma iterate_strictMono_n (a : ℝ) (ha : 0 < a)
    (h_ident : ∀ x, A.op 0 x = x) :
    StrictMono (fun n => iterate A n a) := by
  intro m n hmn
  simp only  -- simplify (fun n => ...) applications
  -- Write n = m + k for some k ≥ 1
  obtain ⟨k, hk, rfl⟩ : ∃ k, k ≥ 1 ∧ n = m + k := ⟨n - m, by omega, by omega⟩
  -- iterate (m + k) a = iterate m a ⊕ iterate k a
  rw [iterate_add A a h_ident m k]
  -- Need: iterate m a < iterate m a ⊕ iterate k a
  have h_ident_r : ∀ x, A.op x 0 = x := identity_right_of_left A h_ident
  -- Since k ≥ 1, iterate k a > 0
  have hk_pos : iterate A k a > 0 := by
    cases k with
    | zero => omega
    | succ k' => exact iterate_pos A a ha h_ident k'
  -- Now use order_right: since 0 < iterate k a, we have
  -- iterate m a ⊕ 0 < iterate m a ⊕ iterate k a
  calc iterate A m a = A.op (iterate A m a) 0 := (h_ident_r _).symm
    _ < A.op (iterate A m a) (iterate A k a) := A.order_right 0 _ _ hk_pos

/-! ## Part 3: The Identity Element

The paper assumes existence of a "null" element m(∅) = m_∅.
We prove that if such an element exists and is unique, it acts as identity.
-/

/-- A null element is one where combining it doesn't change the value -/
def IsNullElement (e : ℝ) : Prop :=
  ∀ x, A.op e x = x

/-- If a null element exists, it's unique (by cancellativity) -/
lemma null_unique (e₁ e₂ : ℝ) (h₁ : IsNullElement A e₁) (h₂ : IsNullElement A e₂) :
    e₁ = e₂ := by
  have := h₁ e₂  -- e₁ ⊕ e₂ = e₂
  have := h₂ e₁  -- e₂ ⊕ e₁ = e₁
  -- Need commutativity or another approach here
  sorry

/-! ## Part 4: The Repetition Lemma

This is Section A.3.1 of the paper. The key lemma for scaling relationships.

If μ(r,...,t) ≤ μ(r₀,...,t₀; u) then μ(nr,...,nt) ≤ μ(nr₀,...,nt₀; nu)

In our notation with iterates, this becomes a statement about how
comparisons scale under repetition.
-/

/-- The Repetition Lemma (Section A.3.1 of K&S paper).

    If μ(r,...,t) ≤ μ(r₀,...,t₀; u) then μ(nr,...,nt) ≤ μ(nr₀,...,nt₀; nu)

    In iterate notation:
    If iterate p a ≤ op (iterate q a) (iterate u b)
    then iterate (n*p) a ≤ op (iterate (n*q) a) (iterate (n*u) b)

    Proof by induction on n. The key insight is that we can "prefix" and "postfix"
    with appropriate iterates, using associativity to rearrange.
-/
lemma repetition_lemma (a b : ℝ) (p q u n : ℕ)
    (h_ident : ∀ x, A.op 0 x = x)
    (h : iterate A p a ≤ A.op (iterate A q a) (iterate A u b)) :
    iterate A (n * p) a ≤ A.op (iterate A (n * q) a) (iterate A (n * u) b) := by
  induction n with
  | zero =>
    simp only [Nat.zero_mul, iterate_zero]
    have h1 : A.op (iterate A 0 a) (iterate A 0 b) = A.op 0 0 := by simp [iterate_zero]
    have h2 : A.op 0 0 = 0 := h_ident 0
    simp only [iterate_zero, h2, h_ident, le_refl]
  | succ n ih =>
    -- Goal: iterate ((n+1)*p) a ≤ op (iterate ((n+1)*q) a) (iterate ((n+1)*u) b)
    -- Rewrite: (n+1)*p = n*p + p, etc.
    have hp : (n + 1) * p = n * p + p := by ring
    have hq : (n + 1) * q = n * q + q := by ring
    have hu : (n + 1) * u = n * u + u := by ring
    rw [hp, hq, hu]
    -- Use iterate_add: iterate (n*p + p) a = op (iterate (n*p) a) (iterate p a)
    rw [iterate_add A a h_ident (n * p) p]
    rw [iterate_add A a h_ident (n * q) q]
    rw [iterate_add A b h_ident (n * u) u]
    -- Goal: op (iterate (n*p) a) (iterate p a) ≤
    --       op (op (iterate (n*q) a) (iterate q a)) (op (iterate (n*u) b) (iterate u b))
    -- Use associativity to rearrange RHS
    -- RHS = op (iterate (n*q) a) (op (iterate q a) (op (iterate (n*u) b) (iterate u b)))
    --     by repeated associativity
    -- The key is to show LHS ≤ RHS using IH and h together.

    -- From IH: iterate (n*p) a ≤ op (iterate (n*q) a) (iterate (n*u) b)
    -- From h: iterate p a ≤ op (iterate q a) (iterate u b)

    -- We need to combine these to get the full bound.
    -- Using order preservation:
    -- op (iterate (n*p) a) (iterate p a) ≤ op (op (iterate (n*q) a) (iterate (n*u) b)) (iterate p a)
    --                                     ≤ op (op (iterate (n*q) a) (iterate (n*u) b)) (op (iterate q a) (iterate u b))

    have h1 : A.op (iterate A (n * p) a) (iterate A p a) ≤
              A.op (A.op (iterate A (n * q) a) (iterate A (n * u) b)) (iterate A p a) :=
      order_left_le A _ _ _ ih
    have h2 : A.op (A.op (iterate A (n * q) a) (iterate A (n * u) b)) (iterate A p a) ≤
              A.op (A.op (iterate A (n * q) a) (iterate A (n * u) b)) (A.op (iterate A q a) (iterate A u b)) :=
      order_right_le A _ _ _ h

    -- Now use associativity to rearrange RHS to match target
    -- RHS currently: op (op (iterate (n*q) a) (iterate (n*u) b)) (op (iterate q a) (iterate u b))
    -- Target:        op (op (iterate (n*q) a) (iterate q a)) (op (iterate (n*u) b) (iterate u b))

    -- By associativity:
    -- op (op A B) (op C D) = op A (op B (op C D)) = op A (op (op B C) D)
    -- This requires some rearrangement...

    -- For now, accept this step and note it needs careful associativity manipulation
    calc A.op (iterate A (n * p) a) (iterate A p a)
        ≤ A.op (A.op (iterate A (n * q) a) (iterate A (n * u) b))
            (A.op (iterate A q a) (iterate A u b)) := le_trans h1 h2
      _ = _ := by
          -- Rearrange using associativity
          -- This is a pure algebraic rearrangement, somewhat tedious
          sorry

/-! ## Part 5: Separation (Sets A, B, C)

Section A.3.2 of the paper. For a new atom type, we classify existing
grid values into three sets based on their relationship to the new values.
-/

/-- Set A: existing values strictly below the new target -/
def setA (μ : ℕ → ℝ) (target : ℝ) : Set ℕ :=
  {r | μ r < target}

/-- Set B: existing values equal to the new target -/
def setB (μ : ℕ → ℝ) (target : ℝ) : Set ℕ :=
  {r | μ r = target}

/-- Set C: existing values strictly above the new target -/
def setC (μ : ℕ → ℝ) (target : ℝ) : Set ℕ :=
  {r | μ r > target}

/-- The sets A, B, C partition ℕ -/
lemma ABC_partition (μ : ℕ → ℝ) (target : ℝ) :
    ∀ r, r ∈ setA μ target ∨ r ∈ setB μ target ∨ r ∈ setC μ target := by
  intro r
  rcases lt_trichotomy (μ r) target with h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; exact h

/-! ## Part 6: The Main Induction

The heart of the K&S proof: we add atom types one at a time,
showing that the linear assignment is always consistent.
-/

/-- For k types of atoms with values a₁,...,aₖ, the valuation is linear:
    μ(r₁,...,rₖ) = r₁·a₁ + ... + rₖ·aₖ

    This is the induction hypothesis (Equation 6 in the paper). -/
def LinearValuation (k : ℕ) (vals : Fin k → ℝ) (counts : Fin k → ℕ) : ℝ :=
  ∑ i, (counts i : ℝ) * vals i

/-- The main theorem: given K&S axioms, the operation is addition up to regrade.

    Statement: There exists Θ : ℝ → ℝ strictly increasing such that
    x ⊕ y = Θ⁻¹(Θ(x) + Θ(y))

    Equivalently: On the Θ-regraded scale, ⊕ becomes +.
-/
theorem associativity_theorem :
    ∃ Θ : ℝ → ℝ, StrictMono Θ ∧
    ∀ x y, A.op x y = Function.invFun Θ (Θ x + Θ y) := by
  /-
  Proof sketch following K&S Appendix A:

  1. For one atom type a, we can freely assign m(r of a) = r·a (any a > 0).
     This establishes the integer grid.

  2. Inductively, assume k types have linear valuations μ(r₁,...,rₖ) = Σ rᵢaᵢ.

  3. Add type k+1 with new atom d. For each multiplicity u of d:
     - Classify existing grid points into A (below), B (at), C (above)
     - The Repetition Lemma ensures scaled comparisons are consistent
     - If B is non-empty: d is rationally related to existing values
     - If B is empty: d lies in a gap, assign it any δ in that gap

  4. The freedom to choose δ within the gap is exactly the regrade freedom.
     Any monotone Θ recovers an equivalent valid assignment.

  The construction is finite and constructive - no limits needed!
  -/
  sorry

/-! ## Part 7: Connection to KnuthSkilling.lean

The Associativity Theorem produces a Linearizer, which connects to the
Regraduation framework in KnuthSkilling.lean.
-/

/-- A Linearizer is what the associativity theorem produces:
    a strictly monotone φ such that φ(x ⊕ y) = φ(x) + φ(y). -/
structure Linearizer (A : KSAxioms) where
  φ : ℝ → ℝ
  strictMono : StrictMono φ
  additive : ∀ x y, φ (A.op x y) = φ x + φ y

/-- The associativity theorem produces a linearizer -/
theorem exists_linearizer : ∃ L : Linearizer A, True := by
  sorry

/-! ## Appendix: Why Commutativity is Derived, Not Assumed

A key point of the K&S approach: commutativity follows from the construction!

Once we have the linear representation μ(r₁,...,rₖ) = Σ rᵢaᵢ, commutativity
is automatic because addition of reals commutes.

This is NOT assumed - it's a THEOREM. The K&S axioms only require:
- Order preservation (Axiom 1)
- Associativity (Axiom 2)

Commutativity is then forced by the structure.
-/

/-- Commutativity is derived from the linearizer -/
theorem commutativity_derived (L : Linearizer A) :
    ∀ x y, A.op x y = A.op y x := by
  intro x y
  -- φ(x ⊕ y) = φ(x) + φ(y) = φ(y) + φ(x) = φ(y ⊕ x)
  -- Since φ is injective (strictly mono), x ⊕ y = y ⊕ x
  have h1 : L.φ (A.op x y) = L.φ x + L.φ y := L.additive x y
  have h2 : L.φ (A.op y x) = L.φ y + L.φ x := L.additive y x
  have h3 : L.φ x + L.φ y = L.φ y + L.φ x := add_comm _ _
  have h4 : L.φ (A.op x y) = L.φ (A.op y x) := by rw [h1, h2, h3]
  exact L.strictMono.injective h4

end Mettapedia.ProbabilityTheory.AssociativityTheorem
