/-
# Knuth-Skilling Representation Theorem

The core representation theorem for K&S algebras:
- Dedekind cut construction for Θ : α → ℝ
- lowerRatioSet and Theta definitions
- Additivity section (csSup_add approach)
- ks_separation_lemma
- ThetaFull_strictMono_on_pos
- Commutativity derived from representation
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical

/-! ## Knuth-Skilling Appendix A: The Associativity Theorem

This section formalizes the full K&S Appendix A proof that shows:

**Theorem**: Axioms 1 (order) and 2 (associativity) imply that x ⊕ y = Θ⁻¹(Θ(x) + Θ(y))
for some order-preserving Θ.

**Key insight from the paper** (line 1166):
> "Associativity + Order ⟹ Additivity allowed ⟹ Commutativity"

Commutativity is NOT assumed - it EMERGES from the construction!

The proof proceeds by building a "grid" of values:
1. Start with one type of atom: m(r of a) = r·a
2. Extend inductively to more types using the separation argument
3. Show the limit exists and gives the linearizing map Θ
-/

namespace KSAppendixA

open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-! ### Phase 1: Cancellativity from Order (K&S lines 1344-1348)

The paper states: "Because these three possibilities (<,>,=) are exhaustive,
consistency implies the reverse, sometimes called cancellativity."

**IMPORTANT STRUCTURAL NOTE**:

The K&S axioms as stated use PartialOrder, but the representation theorem
IMPLIES that any valid K&S algebra must be totally ordered (since it embeds
into ℝ). We prove cancellativity in two forms:

1. **Partial order versions**: Work without assuming totality, but give weaker
   conclusions (e.g., "¬(y ≤ x)" instead of "x < y")
2. **Linear order versions**: In a separate section, assuming totality holds

The representation theorem proves totality, so linear order theorems apply
to any valid K&S algebra.
-/

/-- In a partial order, if op x z < op y z, then y cannot be ≤ x.
This is the partial-order version of strict cancellativity. -/
theorem op_not_le_of_op_lt_left (x y z : α) (h : op x z < op y z) : ¬(y ≤ x) := by
  intro hyx
  rcases hyx.lt_or_eq with hlt | heq
  · -- y < x: then op y z < op x z, contradicting h
    have hcontra : op y z < op x z := op_strictMono_left z hlt
    exact lt_asymm h hcontra
  · -- y = x: then op y z = op x z, contradicting h
    rw [← heq] at h
    exact lt_irrefl _ h

/-- Right version: if op z x < op z y, then y cannot be ≤ x. -/
theorem op_not_le_of_op_lt_right (x y z : α) (h : op z x < op z y) : ¬(y ≤ x) := by
  intro hyx
  rcases hyx.lt_or_eq with hlt | heq
  · have hcontra : op z y < op z x := op_strictMono_right z hlt
    exact lt_asymm h hcontra
  · rw [← heq] at h
    exact lt_irrefl _ h

/-- Cancellativity for comparable elements: if x, y are comparable and op x z ≤ op y z,
then x ≤ y. -/
theorem op_cancel_left_of_le_of_comparable (x y z : α)
    (h : op x z ≤ op y z) (hcomp : x ≤ y ∨ y ≤ x) : x ≤ y := by
  rcases hcomp with hxy | hyx
  · exact hxy
  · -- We have y ≤ x. If y < x, then op y z < op x z, contradicting h
    rcases hyx.lt_or_eq with hlt | heq
    · have hlt' : op y z < op x z := op_strictMono_left z hlt
      -- op y z < op x z and op x z ≤ op y z gives op y z < op y z, contradiction
      exact absurd (lt_of_lt_of_le hlt' h) (lt_irrefl _)
    · exact le_of_eq heq.symm

/-- Right version for comparable elements. -/
theorem op_cancel_right_of_le_of_comparable (x y z : α)
    (h : op z x ≤ op z y) (hcomp : x ≤ y ∨ y ≤ x) : x ≤ y := by
  rcases hcomp with hxy | hyx
  · exact hxy
  · rcases hyx.lt_or_eq with hlt | heq
    · have hlt' : op z y < op z x := op_strictMono_right z hlt
      exact absurd (lt_of_lt_of_le hlt' h) (lt_irrefl _)
    · exact le_of_eq heq.symm

/-! #### Note on Linear Order

Full cancellativity (without comparability hypothesis) requires knowing that
the order is total. This follows from the representation theorem: any K&S algebra
embeds into ℝ, which is totally ordered. The representation theorem implies that
any valid K&S algebra is in fact totally ordered.
-/

/-! ### Phase 2: One Type Base Case (K&S lines 1350-1409)

For a single atom type a > ident, the iterates are strictly increasing:
m(0 of a) = ident < m(1 of a) = a < m(2 of a) = a⊕a < ...

This gives us the natural numbers embedded in α.
-/

/-- iterate_op is strictly increasing for a > ident -/
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

/-- iterate_op 0 = ident -/
theorem iterate_op_zero (a : α) : iterate_op a 0 = ident := rfl

/-- iterate_op 1 = a -/
theorem iterate_op_one (a : α) : iterate_op a 1 = a := by
  simp [iterate_op, op_ident_right]

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

/-- iterate_op preserves the operation in a specific sense (without assuming commutativity).
This is a key step: iterate_op a (m+1) = op a (iterate_op a m) by definition,
but we need the "adding" version: iterate_op a (m+n) relates to iterates. -/
theorem iterate_op_succ (a : α) (n : ℕ) : iterate_op a (n + 1) = op a (iterate_op a n) := rfl

/-- **KEY LEMMA**: iterate_op respects addition WITHOUT assuming commutativity!

op (iterate_op a m) (iterate_op a n) = iterate_op a (m + n)

This is crucial for the K&S proof because it allows us to derive the repetition lemma
and ultimately prove commutativity as a THEOREM, not assume it as an axiom.

The proof uses ONLY associativity and identity (no commutativity!). -/
theorem iterate_op_add (a : α) (m n : ℕ) :
    op (iterate_op a m) (iterate_op a n) = iterate_op a (m + n) := by
  induction m with
  | zero =>
    -- op ident (iterate_op a n) = iterate_op a n = iterate_op a (0 + n)
    simp only [iterate_op_zero, op_ident_left, Nat.zero_add]
  | succ m ih =>
    -- op (iterate_op a (m+1)) (iterate_op a n)
    -- = op (op a (iterate_op a m)) (iterate_op a n)  [by iterate_op_succ]
    -- = op a (op (iterate_op a m) (iterate_op a n))  [by assoc]
    -- = op a (iterate_op a (m + n))                  [by IH]
    -- = iterate_op a (m + n + 1)                     [by iterate_op_succ]
    -- = iterate_op a ((m + 1) + n)                   [arithmetic]
    calc op (iterate_op a (m + 1)) (iterate_op a n)
        = op (op a (iterate_op a m)) (iterate_op a n) := by rw [iterate_op_succ]
      _ = op a (op (iterate_op a m) (iterate_op a n)) := by rw [op_assoc]
      _ = op a (iterate_op a (m + n)) := by rw [ih]
      _ = iterate_op a (m + n + 1) := by rw [← iterate_op_succ]
      _ = iterate_op a (m + 1 + n) := by ring_nf

/-- **Iterate composition lemma**: iterate_op (iterate_op x n) m = iterate_op x (n * m).

This is a key lemma for the separation argument that shows how iterating an iterate
relates to a single iterate with multiplied exponent. NO commutativity needed! -/
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

/-! **iterate_op_op_distrib is FALSE without commutativity!**

The statement `op (iterate_op x m) (iterate_op y m) = iterate_op (op x y) m`
(i.e., x^m ⊕ y^m = (x⊕y)^m) requires commutativity of op.

**Counterexample**: See `Counterexamples.iterate_op_op_distrib_false`:
For the free monoid (lists with concatenation):
  [0]² ++ [1]² = [0,0,1,1] ≠ [0,1,0,1] = ([0] ++ [1])²

**What we DO have** (without commutativity):
  `iterate_op_op_le_double`: x^m ⊕ y^m ≤ (x⊕y)^{2m}

The factor of 2 is unavoidable without commutativity.

**K&S approach**: They derive commutativity AS A CONSEQUENCE of the
representation theorem. This creates a bootstrapping issue that requires
the careful Appendix A construction. See `exists_split_ratio_of_op`.
-/

-- NOTE: This theorem is FALSE and should NOT be proved.
-- We keep the statement commented out for reference.
-- theorem iterate_op_op_distrib (x y : α) (m : ℕ) :
--     op (iterate_op x m) (iterate_op y m) = iterate_op (op x y) m

/-- **Repetition Lemma (K&S lines 1497-1534)**:
If iterate_op a n ≤ iterate_op x m, then iterate_op a (n * k) ≤ iterate_op x (m * k) for all k.

This is the key lemma that allows scaling inequalities without requiring commutativity.
The proof uses iterate_op_add and monotonicity in both arguments. -/
theorem repetition_lemma_le (a x : α) (n m k : ℕ) (h : iterate_op a n ≤ iterate_op x m) :
    iterate_op a (n * k) ≤ iterate_op x (m * k) := by
  induction k with
  | zero => simp only [Nat.mul_zero, iterate_op_zero]; exact le_refl _
  | succ k ih =>
    -- n * (k + 1) = n * k + n
    -- m * (k + 1) = m * k + m
    have eq_a : n * (k + 1) = n * k + n := by ring
    have eq_x : m * (k + 1) = m * k + m := by ring
    rw [eq_a, eq_x]
    rw [← iterate_op_add, ← iterate_op_add]
    -- Need: op (iterate_op a (n * k)) (iterate_op a n) ≤ op (iterate_op x (m * k)) (iterate_op x m)
    -- Use monotonicity in both arguments
    calc op (iterate_op a (n * k)) (iterate_op a n)
        ≤ op (iterate_op a (n * k)) (iterate_op x m) := by
          apply op_mono_right (iterate_op a (n * k)) h
      _ ≤ op (iterate_op x (m * k)) (iterate_op x m) := by
          apply op_mono_left (iterate_op x m) ih

/-- Strict version of repetition lemma:
If iterate_op a n < iterate_op x m, then iterate_op a (n * k) < iterate_op x (m * k) for k > 0. -/
theorem repetition_lemma_lt (a x : α) (n m k : ℕ) (hk : k > 0) (h : iterate_op a n < iterate_op x m) :
    iterate_op a (n * k) < iterate_op x (m * k) := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero =>
      -- k = 0, so 0 + 1 = 1, and we need iterate_op a (n * 1) < iterate_op x (m * 1)
      -- But 0 + 1 = 1, so actually n * (0 + 1) = n * 1 = n and m * (0 + 1) = m * 1 = m
      rw [Nat.zero_add, Nat.mul_one, Nat.mul_one]
      exact h
    | succ k ih =>
      have eq_a : n * (k + 1 + 1) = n * (k + 1) + n := by ring
      have eq_x : m * (k + 1 + 1) = m * (k + 1) + m := by ring
      rw [eq_a, eq_x]
      rw [← iterate_op_add, ← iterate_op_add]
      calc op (iterate_op a (n * (k + 1))) (iterate_op a n)
          < op (iterate_op a (n * (k + 1))) (iterate_op x m) := by
            apply op_strictMono_right (iterate_op a (n * (k + 1))) h
        _ < op (iterate_op x (m * (k + 1))) (iterate_op x m) := by
            apply op_strictMono_left (iterate_op x m) (ih (Nat.succ_pos k))

/-- iterate_op is strictly monotone in its base argument for positive iterations.
If x < y and m > 0, then iterate_op x m < iterate_op y m. -/
theorem iterate_op_strictMono_base (m : ℕ) (hm : 0 < m) (x y : α) (hxy : x < y) :
    iterate_op x m < iterate_op y m := by
  cases m with
  | zero => omega
  | succ m =>
    induction m with
    | zero =>
      -- iterate_op x 1 = x < y = iterate_op y 1
      rw [iterate_op_one, iterate_op_one]
      exact hxy
    | succ m ih =>
      -- Two-step argument using both strict monotonicity directions
      calc iterate_op x (m + 1 + 1)
          = op x (iterate_op x (m + 1)) := rfl
        _ < op x (iterate_op y (m + 1)) := op_strictMono_right x (ih (Nat.succ_pos m))
        _ < op y (iterate_op y (m + 1)) := op_strictMono_left (iterate_op y (m + 1)) hxy
        _ = iterate_op y (m + 1 + 1) := rfl

/-- **KEY BOUNDING LEMMA**: If x < iterate_op a L and m > 0, then iterate_op x m < iterate_op a (L * m).

This is the "repetition" property that gives uniform bounds on the lower ratio set.
The proof uses iterate_op_add and monotonicity of op.

**Crucially, this does NOT require commutativity!** -/
theorem iterate_bound (a x : α) (L : ℕ) (hx : x < iterate_op a L) (m : ℕ) (hm : 0 < m) :
    iterate_op x m < iterate_op a (L * m) := by
  cases m with
  | zero => omega
  | succ m =>
    induction m with
    | zero =>
      -- iterate_op x 1 = x, and we need x < iterate_op a (L * 1) = iterate_op a L
      rw [iterate_op_one, Nat.mul_one]
      exact hx
    | succ m ih =>
      -- iterate_op x (m+2) = op x (iterate_op x (m+1))
      -- iterate_op a (L * (m+2)) = op (iterate_op a L) (iterate_op a (L * (m+1)))
      calc iterate_op x (m + 1 + 1)
          = op x (iterate_op x (m + 1)) := rfl
        _ < op x (iterate_op a (L * (m + 1))) := op_strictMono_right x (ih (Nat.succ_pos m))
        _ < op (iterate_op a L) (iterate_op a (L * (m + 1))) := op_strictMono_left _ hx
        _ = iterate_op a (L + L * (m + 1)) := by rw [iterate_op_add]
        _ = iterate_op a (L * (m + 1 + 1)) := by ring_nf

/-- Corollary: A weaker bound that's easier to use.
If x < iterate_op a L, then iterate_op x m ≤ iterate_op a (L * m) for all m. -/
theorem iterate_bound_le (a x : α) (L : ℕ) (_hL : 0 < L) (hx : x < iterate_op a L) (m : ℕ) :
    iterate_op x m ≤ iterate_op a (L * m) := by
  cases m with
  | zero =>
    simp only [iterate_op_zero, Nat.mul_zero]
    -- Goal: ident ≤ ident
    exact le_refl _
  | succ m =>
    exact le_of_lt (iterate_bound a x L hx (m + 1) (Nat.succ_pos m))

/-- For the one-type case, we can define Θ(iterate_op a n) = n.
This is well-defined since iterate_op is strictly monotone. -/
noncomputable def one_type_linearizer (a : α) (_ha : ident < a) : α → ℝ := fun x =>
  if h : ∃ n : ℕ, iterate_op a n = x then h.choose else 0

/-! ### Phase 3: Building the linearizer on iterates

The key theorem: there exists a strictly monotone Θ : α → ℝ such that
Θ(iterate_op a n) = n for all n.

For elements NOT of the form iterate_op a n, we use the Archimedean property
to place them between iterates and interpolate.
-/

/-- The range of iterate_op is a subset of α -/
def iterateRange (a : α) : Set α := { x | ∃ n : ℕ, iterate_op a n = x }

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

/-- For any x in α, x is bounded above by some iterate of a.
This follows directly from Archimedean property (no totality needed). -/
theorem bounded_by_iterate (a : α) (ha : ident < a) (x : α) :
    ∃ n : ℕ, x < iterate_op a n := by
  -- Archimedean gives x < Nat.iterate (op a) n a for some n
  obtain ⟨n, hn⟩ := op_archimedean a x ha
  rw [nat_iterate_eq_iterate_op_succ] at hn
  exact ⟨n + 1, hn⟩

/-- For any x > ident, x is bounded below by some positive iterate -/
theorem bounded_below_by_iterate (a : α) (_ha : ident < a) (x : α) (hx : ident < x) :
    ∃ n : ℕ, iterate_op a n ≤ x := by
  exact ⟨0, le_of_lt hx⟩

/-! ### Phase 4-8: Dedekind Cut Construction (K&S lines 1536-1895)

**The Construction**:
For a reference element a with ident < a, we define Θ : α → ℝ as follows:

For any x ∈ α:
  Θ(x) := sup { (n : ℝ) / m | n, m ∈ ℕ, m > 0, iterate_op a n ≤ iterate_op x m }

This set is:
1. Non-empty: contains 0 (take n = 0, m = 1)
2. Bounded above: by Archimedean property, iterate_op x m < iterate_op a N for some N

The supremum exists in ℝ by completeness.
-/

/-- The lower ratio set for x relative to reference element a.
This is { n/m : iterate_op a n ≤ iterate_op x m, m > 0 }. -/
def lowerRatioSet (a x : α) : Set ℝ :=
  { r : ℝ | ∃ n m : ℕ, m > 0 ∧ iterate_op a n ≤ iterate_op x m ∧ r = (n : ℝ) / m }

/-- If x ≤ y, then lowerRatioSet a x ⊆ lowerRatioSet a y.
The key is that iterate_op x m ≤ iterate_op y m when x ≤ y and m > 0. -/
theorem lowerRatioSet_mono (a x y : α) (hx : ident < x) (hy : ident < y) (hxy : x ≤ y) :
    lowerRatioSet a x ⊆ lowerRatioSet a y := by
  intro r ⟨n, m, hm_pos, hle, hr_eq⟩
  refine ⟨n, m, hm_pos, ?_, hr_eq⟩
  -- Need: iterate_op a n ≤ iterate_op y m
  -- We have: iterate_op a n ≤ iterate_op x m and x ≤ y
  -- By monotonicity: iterate_op x m ≤ iterate_op y m
  have h_mono : iterate_op x m ≤ iterate_op y m := by
    cases m with
    | zero => simp only [iterate_op_zero]; exact le_refl ident
    | succ m =>
      cases hxy.lt_or_eq with
      | inl hlt =>
        apply le_of_lt
        exact iterate_op_strictMono_base (m + 1) (Nat.succ_pos m) x y hlt
      | inr heq => simp [heq]
  exact le_trans hle h_mono

/-- The lower ratio set contains 0 (take n = 0, m = 1). -/
theorem lowerRatioSet_nonempty (a x : α) (hx : ident < x) : (lowerRatioSet a x).Nonempty := by
  use 0
  refine ⟨0, 1, Nat.one_pos, ?_, by simp⟩
  -- Need: iterate_op a 0 ≤ iterate_op x 1
  -- iterate_op a 0 = ident and iterate_op x 1 = x
  simp only [iterate_op_zero]
  rw [iterate_op_one]
  exact le_of_lt hx

/-- Key lemma: iterate_op preserves strict order for any element y with ident < y. -/
theorem iterate_op_strictMono_of_pos (y : α) (hy : ident < y) : StrictMono (iterate_op y) :=
  iterate_op_strictMono y hy

/-- Key lemma: iterate_op is monotone for any element. -/
theorem iterate_op_mono (y : α) (hy : ident < y) : Monotone (iterate_op y) := by
  intro m n hmn
  rcases Nat.lt_or_ge m n with hlt | hge
  · exact le_of_lt (iterate_op_strictMono y hy hlt)
  · have : m = n := le_antisymm hmn hge
    rw [this]

/-- For y > ident and m > 0, we have iterate_op y m > ident. -/
theorem iterate_op_pos (y : α) (hy : ident < y) (m : ℕ) (hm : m > 0) :
    ident < iterate_op y m := by
  calc ident = iterate_op y 0 := (iterate_op_zero y).symm
    _ < iterate_op y m := iterate_op_strictMono y hy hm

/-- The lower ratio set is bounded above (by Archimedean property).
For any x, there exists N such that iterate_op x m < iterate_op a N for all m. -/
theorem lowerRatioSet_bddAbove (a x : α) (ha : ident < a) (hx : ident < x) :
    BddAbove (lowerRatioSet a x) := by
  -- By Archimedean, iterate_op x 1 = x < iterate_op a N for some N
  obtain ⟨N, hN⟩ := bounded_by_iterate a ha x
  use N
  intro r ⟨n, m, hm_pos, hle, hr_eq⟩
  rw [hr_eq]
  -- We need (n : ℝ) / m ≤ N
  -- From hle: iterate_op a n ≤ iterate_op x m
  -- We'll show n ≤ N * m (in ℕ), hence n/m ≤ N
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, zero_div]
    exact Nat.cast_nonneg N
  · -- n > 0 case: Use the iterate_bound theorem!
    -- By iterate_bound_le: iterate_op x m ≤ iterate_op a (N * m)
    -- Combined with hle: iterate_op a n ≤ iterate_op x m ≤ iterate_op a (N * m)
    -- By monotonicity: n ≤ N * m
    -- Therefore: n / m ≤ N
    have hN_pos : 0 < N := by
      -- N > 0 since x < iterate_op a N and x > ident
      -- If N = 0, then iterate_op a 0 = ident, so x < ident, contradicting hx
      by_contra h_not_pos
      push_neg at h_not_pos
      interval_cases N
      simp only [iterate_op_zero] at hN
      exact absurd (lt_trans hx hN) (lt_irrefl ident)
    have h_bound : iterate_op x m ≤ iterate_op a (N * m) :=
      iterate_bound_le a x N hN_pos hN m
    -- Combine: iterate_op a n ≤ iterate_op x m ≤ iterate_op a (N * m)
    have h_combined : iterate_op a n ≤ iterate_op a (N * m) := le_trans hle h_bound
    -- By monotonicity of iterate_op a (contrapositive of strict mono): n ≤ N * m
    have hn_le_Nm : n ≤ N * m := by
      by_contra h_gt
      push_neg at h_gt
      have h_lt : iterate_op a (N * m) < iterate_op a n := iterate_op_strictMono a ha h_gt
      -- h_combined: iterate_op a n ≤ iterate_op a (N * m)
      -- h_lt: iterate_op a (N * m) < iterate_op a n
      -- Combining gives iterate_op a (N * m) < iterate_op a (N * m)
      exact absurd (lt_of_lt_of_le h_lt h_combined) (lt_irrefl _)
    -- Therefore n / m ≤ N
    have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
    have hm_nonneg : (0 : ℝ) ≤ m := le_of_lt hm_pos_real
    calc (n : ℝ) / m
        ≤ (N * m : ℕ) / m := by
          apply div_le_div_of_nonneg_right (Nat.cast_le.mpr hn_le_Nm) hm_nonneg
      _ = N := by
          rw [Nat.cast_mul]
          field_simp

/-- Define the representation function Θ using the supremum of the lower ratio set. -/
noncomputable def Theta (a x : α) (ha : ident < a) (hx : ident < x) : ℝ :=
  sSup (lowerRatioSet a x)

/-- The lower ratio set for a relative to itself is exactly { n/m : n ≤ m }. -/
theorem lowerRatioSet_self (a : α) (ha : ident < a) :
    lowerRatioSet a a = { r : ℝ | ∃ n m : ℕ, m > 0 ∧ n ≤ m ∧ r = (n : ℝ) / m } := by
  ext r
  constructor
  · -- lowerRatioSet a a → { n/m : n ≤ m }
    intro ⟨n, m, hm_pos, hle, hr_eq⟩
    refine ⟨n, m, hm_pos, ?_, hr_eq⟩
    -- iterate_op a n ≤ iterate_op a m ↔ n ≤ m (by strict monotonicity)
    by_contra h_gt
    push_neg at h_gt
    have hlt : iterate_op a m < iterate_op a n := iterate_op_strictMono a ha h_gt
    -- hle : iterate_op a n ≤ iterate_op a m, hlt : iterate_op a m < iterate_op a n
    -- Combining: iterate_op a m < iterate_op a m (contradiction)
    exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
  · -- { n/m : n ≤ m } → lowerRatioSet a a
    intro ⟨n, m, hm_pos, hn_le_m, hr_eq⟩
    refine ⟨n, m, hm_pos, ?_, hr_eq⟩
    exact iterate_op_mono a ha hn_le_m

/-- The set { n/m : n ≤ m, m > 0 } has supremum 1. -/
theorem sSup_ratio_le_one :
    sSup { r : ℝ | ∃ n m : ℕ, m > 0 ∧ n ≤ m ∧ r = (n : ℝ) / m } = 1 := by
  apply le_antisymm
  · -- sup ≤ 1: all elements are ≤ 1
    apply csSup_le
    · -- Nonempty: 1/1 = 1 is in the set
      exact ⟨1, 1, 1, Nat.one_pos, le_refl 1, by simp⟩
    · -- Upper bound: n/m ≤ 1 when n ≤ m
      intro r ⟨n, m, hm_pos, hn_le_m, hr_eq⟩
      rw [hr_eq]
      have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
      rw [div_le_one hm_pos_real]
      exact Nat.cast_le.mpr hn_le_m
  · -- 1 ≤ sup: 1 is in the set
    apply le_csSup
    · -- Bounded above by 1
      use 1
      intro r ⟨n, m, hm_pos, hn_le_m, hr_eq⟩
      rw [hr_eq]
      have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
      rw [div_le_one hm_pos_real]
      exact Nat.cast_le.mpr hn_le_m
    · -- 1 is in the set (take n = m = 1)
      exact ⟨1, 1, Nat.one_pos, le_refl 1, by simp⟩

/-- For x = a, we have Θ(a) = 1. -/
theorem Theta_ref_eq_one (a : α) (ha : ident < a) :
    Theta a a ha ha = 1 := by
  unfold Theta
  rw [lowerRatioSet_self a ha]
  exact sSup_ratio_le_one

/-- For x = ident, we have Θ(ident) = 0. -/
theorem Theta_ident_eq_zero (a : α) (ha : ident < a) (hident_pos : ident < ident) :
    Theta a ident ha hident_pos = 0 := by
  -- This is actually ill-defined since we require ident < x, but ident is not < ident
  -- We need to handle the ident case separately in the full construction
  exact absurd hident_pos (lt_irrefl ident)

/-! ### Extended Construction: Handle ident case specially -/

/-- The full representation function, handling ident specially. -/
noncomputable def ThetaFull (a : α) (ha : ident < a) : α → ℝ := fun x =>
  if h : ident < x then Theta a x ha h
  else if h' : x = ident then 0
  else 0  -- For x < ident (which shouldn't exist in well-formed algebras)

/-- ThetaFull maps ident to 0. -/
theorem ThetaFull_ident (a : α) (ha : ident < a) :
    ThetaFull a ha ident = 0 := by
  simp only [ThetaFull, lt_irrefl ident, ↓reduceDIte]

/-- ThetaFull is non-negative on elements ≥ ident. -/
theorem ThetaFull_nonneg (a : α) (ha : ident < a) (x : α) (_hx : ident ≤ x) :
    0 ≤ ThetaFull a ha x := by
  simp only [ThetaFull]
  split_ifs with h h'
  · -- ident < x: Θ(x) is a supremum of non-negative ratios
    unfold Theta
    apply Real.sSup_nonneg
    intro r ⟨n, m, _, _, hr_eq⟩
    rw [hr_eq]
    apply div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)
  · -- x = ident: returns 0
    rfl
  · -- x < ident: returns 0 (this case shouldn't happen if hx : ident ≤ x holds)
    rfl

/-! ### Additivity of Theta

## Restructured Approach (following GPT-5.1 Pro advice)

**KEY INSIGHT**: `iterate_op_op_distrib` (x^m ⊕ y^m = (x⊕y)^m) is FALSE without commutativity!
We cannot prove set equality `lowerRatioSet a (op x y) = lowerRatioSet a x + lowerRatioSet a y`.

Instead, we prove Theta additivity directly via two inequalities:
1. `Theta_le_add`: Θ(x⊕y) ≤ Θ(x) + Θ(y) (uses Archimedean split)
2. `add_le_Theta`: Θ(x) + Θ(y) ≤ Θ(x⊕y) (uses approximation, no commutativity needed)

This avoids the false `iterate_op_op_distrib` entirely.
-/

section Additivity

open scoped Pointwise

/-- **Archimedean Split Lemma**: Given a lower-ratio bound for x ⊕ y,
we can (approximately) split it into a sum of lower-ratio elements for x and y.

This is the core of Appendix A's ε-δ / grid argument.

Mathematical idea: If a^n ≤ (x⊕y)^m, use the Archimedean property to find
how the "contribution" splits between x and y. The bound may be slightly loose
(hence ≤ instead of = in the conclusion). -/
lemma exists_split_ratio_of_op
    (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y)
    {n m : ℕ} (hm_pos : 0 < m)
    (h_le : iterate_op a n ≤ iterate_op (op x y) m) :
  ∃ n₁ m₁ n₂ m₂ : ℕ,
    0 < m₁ ∧ 0 < m₂ ∧
    iterate_op a n₁ ≤ iterate_op x m₁ ∧
    iterate_op a n₂ ≤ iterate_op y m₂ ∧
    (n : ℝ) / m ≤ (n₁ : ℝ) / m₁ + (n₂ : ℝ) / m₂ := by
  -- TODO: This is the Archimedean split - the main technical lemma
  -- Strategy from K&S Appendix A:
  -- 1. Use repetition lemma to work on a common grid
  -- 2. Use separation construction to track how a-steps split between x and y
  -- 3. Convert counts into ratios with the inequality
  sorry

/-- First inequality: Θ(x⊕y) ≤ Θ(x) + Θ(y)

Uses the Archimedean split lemma to show every element of Lower(x⊕y)
is bounded by a sum from Lower(x) + Lower(y). -/
lemma Theta_le_add (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y)
    (hxy : ident < op x y) :
    Theta a (op x y) ha hxy ≤ Theta a x ha hx + Theta a y ha hy := by
  unfold Theta
  -- Use csSup_le: show every r in lowerRatioSet a (op x y) is ≤ Θ(x) + Θ(y)
  apply csSup_le (lowerRatioSet_nonempty a (op x y) hxy)
  intro r ⟨n, m, hm_pos, h_le, hr_eq⟩
  subst hr_eq
  -- Apply splitting lemma
  obtain ⟨n₁, m₁, n₂, m₂, hm₁_pos, hm₂_pos, hx_le, hy_le, h_rat_le⟩ :=
    exists_split_ratio_of_op a x y ha hx hy hm_pos h_le
  -- n₁/m₁ ∈ lowerRatioSet a x, n₂/m₂ ∈ lowerRatioSet a y
  have hr1_in : (n₁ : ℝ) / m₁ ∈ lowerRatioSet a x := ⟨n₁, m₁, hm₁_pos, hx_le, rfl⟩
  have hr2_in : (n₂ : ℝ) / m₂ ∈ lowerRatioSet a y := ⟨n₂, m₂, hm₂_pos, hy_le, rfl⟩
  -- Bound by suprema
  have h1 : (n₁ : ℝ) / m₁ ≤ sSup (lowerRatioSet a x) :=
    le_csSup (lowerRatioSet_bddAbove a x ha hx) hr1_in
  have h2 : (n₂ : ℝ) / m₂ ≤ sSup (lowerRatioSet a y) :=
    le_csSup (lowerRatioSet_bddAbove a y ha hy) hr2_in
  -- Combine: n/m ≤ n₁/m₁ + n₂/m₂ ≤ Θ(x) + Θ(y)
  calc (n : ℝ) / m ≤ (n₁ : ℝ) / m₁ + (n₂ : ℝ) / m₂ := h_rat_le
    _ ≤ sSup (lowerRatioSet a x) + sSup (lowerRatioSet a y) := add_le_add h1 h2

/-- Helper: x ≤ x ⊕ y when ident < y (by monotonicity of op in right argument) -/
lemma le_op_of_pos_right (x y : α) (hy : ident < y) : x ≤ op x y := by
  have : op x ident < op x y := op_strictMono_right x hy
  rw [op_ident_right] at this
  exact le_of_lt this

/-- Helper: y ≤ x ⊕ y when ident < x (by monotonicity of op in left argument) -/
lemma le_op_of_pos_left (x y : α) (hx : ident < x) : y ≤ op x y := by
  have : op ident y < op x y := op_strictMono_left y hx
  rw [op_ident_left] at this
  exact le_of_lt this

/-- If x ≤ z, then x^m ≤ z^m for all m (iterate_op is monotone in base) -/
lemma iterate_op_mono_base (x z : α) (hxz : x ≤ z) (hz : ident < z) (m : ℕ) :
    iterate_op x m ≤ iterate_op z m := by
  induction m with
  | zero => exact le_refl _
  | succ m ih =>
    simp only [iterate_op_succ]
    -- x ⊕ x^m ≤ z ⊕ z^m
    calc op x (iterate_op x m)
        ≤ op z (iterate_op x m) := (op_strictMono_left (iterate_op x m)).monotone hxz
      _ ≤ op z (iterate_op z m) := (op_strictMono_right z).monotone ih

/-- Key intermediate result: x^m ⊕ y^m ≤ (x⊕y)^{2m}

This is weaker than iterate_op_op_distrib (which claims x^m ⊕ y^m = (x⊕y)^m),
but it's TRUE without commutativity! The factor of 2 is unavoidable. -/
lemma iterate_op_op_le_double (x y : α) (hx : ident < x) (hy : ident < y) (m : ℕ) :
    op (iterate_op x m) (iterate_op y m) ≤ iterate_op (op x y) (2 * m) := by
  -- x ≤ x⊕y and y ≤ x⊕y
  have hx_le : x ≤ op x y := le_op_of_pos_right x y hy
  have hy_le : y ≤ op x y := le_op_of_pos_left x y hx
  have hxy : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
      _ < op x ident := op_strictMono_left ident hx
      _ < op x y := op_strictMono_right x hy
  -- So x^m ≤ (x⊕y)^m and y^m ≤ (x⊕y)^m
  have hxm : iterate_op x m ≤ iterate_op (op x y) m := iterate_op_mono_base x (op x y) hx_le hxy m
  have hym : iterate_op y m ≤ iterate_op (op x y) m := iterate_op_mono_base y (op x y) hy_le hxy m
  -- Now: x^m ⊕ y^m ≤ (x⊕y)^m ⊕ (x⊕y)^m = (x⊕y)^{2m}
  calc op (iterate_op x m) (iterate_op y m)
      ≤ op (iterate_op (op x y) m) (iterate_op y m) :=
        (op_strictMono_left (iterate_op y m)).monotone hxm
    _ ≤ op (iterate_op (op x y) m) (iterate_op (op x y) m) :=
        (op_strictMono_right (iterate_op (op x y) m)).monotone hym
    _ = iterate_op (op x y) (2 * m) := by rw [two_mul, ← iterate_op_add]

/-- **Weaker bound** (provable without commutativity):
(Θ(x) + Θ(y))/2 ≤ Θ(x⊕y)

This follows from iterate_op_op_le_double: for any r₁ ∈ Lower(x), r₂ ∈ Lower(y),
the ratio (r₁+r₂)/2 belongs to Lower(x⊕y). -/
lemma half_add_le_Theta (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y)
    (hxy : ident < op x y) :
    (Theta a x ha hx + Theta a y ha hy) / 2 ≤ Theta a (op x y) ha hxy := by
  unfold Theta
  -- Strategy: For any r₁ ∈ Lower(x), r₂ ∈ Lower(y), show (r₁+r₂)/2 ∈ Lower(x⊕y)
  -- Then (Θ(x)+Θ(y))/2 = sup{(r₁+r₂)/2} ≤ Θ(x⊕y)

  -- Build the combined ratio set
  have h_combine : ∀ r₁ r₂, r₁ ∈ lowerRatioSet a x → r₂ ∈ lowerRatioSet a y →
      (r₁ + r₂) / 2 ∈ lowerRatioSet a (op x y) := by
    intro r₁ r₂ ⟨n₁, m₁, hm₁, hle₁, hr₁⟩ ⟨n₂, m₂, hm₂, hle₂, hr₂⟩
    subst hr₁ hr₂
    -- Use repetition lemma to get common denominator M = m₁ * m₂
    have hle₁' : iterate_op a (n₁ * m₂) ≤ iterate_op x (m₁ * m₂) :=
      repetition_lemma_le a x n₁ m₁ m₂ hle₁
    have hle₂' : iterate_op a (n₂ * m₁) ≤ iterate_op y (m₁ * m₂) := by
      have h := repetition_lemma_le a y n₂ m₂ m₁ hle₂
      simp only [Nat.mul_comm m₂ m₁] at h
      exact h
    -- Combine: a^{n₁m₂ + n₂m₁} ≤ x^{m₁m₂} ⊕ y^{m₁m₂}
    have hle_sum : iterate_op a (n₁ * m₂ + n₂ * m₁) ≤ op (iterate_op x (m₁ * m₂)) (iterate_op y (m₁ * m₂)) := by
      rw [← iterate_op_add]
      -- a^{n₁m₂} ⊕ a^{n₂m₁} ≤ x^{m₁m₂} ⊕ y^{m₁m₂} using monotonicity
      calc op (iterate_op a (n₁ * m₂)) (iterate_op a (n₂ * m₁))
          ≤ op (iterate_op x (m₁ * m₂)) (iterate_op a (n₂ * m₁)) :=
            (op_strictMono_left _).monotone hle₁'
        _ ≤ op (iterate_op x (m₁ * m₂)) (iterate_op y (m₁ * m₂)) :=
            (op_strictMono_right _).monotone hle₂'
    -- Apply iterate_op_op_le_double
    have hle_final : op (iterate_op x (m₁ * m₂)) (iterate_op y (m₁ * m₂)) ≤
        iterate_op (op x y) (2 * (m₁ * m₂)) :=
      iterate_op_op_le_double x y hx hy (m₁ * m₂)
    -- Chain the inequalities
    have hle_combined : iterate_op a (n₁ * m₂ + n₂ * m₁) ≤ iterate_op (op x y) (2 * (m₁ * m₂)) :=
      le_trans hle_sum hle_final
    -- Now show (n₁/m₁ + n₂/m₂)/2 = (n₁m₂ + n₂m₁)/(2*m₁*m₂)
    have hdenom_pos : 0 < 2 * (m₁ * m₂) := by
      have : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
      omega
    refine ⟨n₁ * m₂ + n₂ * m₁, 2 * (m₁ * m₂), hdenom_pos, hle_combined, ?_⟩
    -- Ratio arithmetic: (n₁/m₁ + n₂/m₂)/2 = (n₁*m₂ + n₂*m₁)/(2*m₁*m₂)
    have hm₁_ne : (m₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm₁)
    have hm₂_ne : (m₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm₂)
    push_cast
    field_simp [hm₁_ne, hm₂_ne]

  -- Now use h_combine to show the bound
  have h_half_in : ∀ r₁ r₂, r₁ ∈ lowerRatioSet a x → r₂ ∈ lowerRatioSet a y →
      (r₁ + r₂) / 2 ≤ sSup (lowerRatioSet a (op x y)) := by
    intro r₁ r₂ hr₁ hr₂
    have h_in := h_combine r₁ r₂ hr₁ hr₂
    exact le_csSup (lowerRatioSet_bddAbove a (op x y) ha hxy) h_in

  -- Apply to suprema: (sup_x + sup_y)/2 ≤ sup_xy
  have hx_bdd := lowerRatioSet_bddAbove a x ha hx
  have hy_bdd := lowerRatioSet_bddAbove a y ha hy
  have hx_ne := lowerRatioSet_nonempty a x hx
  have hy_ne := lowerRatioSet_nonempty a y hy
  have hxy_ne := lowerRatioSet_nonempty a (op x y) hxy

  -- For any ε > 0, pick r₁ close to sup_x and r₂ close to sup_y
  -- Then (r₁ + r₂)/2 ≤ sup_xy, so (sup_x + sup_y)/2 - ε ≤ sup_xy
  -- Taking ε → 0 gives the result
  by_contra h_neg
  push_neg at h_neg
  -- (sup_x + sup_y)/2 > sup_xy
  set S_xy := sSup (lowerRatioSet a (op x y)) with hS_xy
  set S_x := sSup (lowerRatioSet a x) with hS_x
  set S_y := sSup (lowerRatioSet a y) with hS_y
  have hgap : (S_x + S_y) / 2 - S_xy > 0 := by linarith
  set ε := ((S_x + S_y) / 2 - S_xy) / 2 with hε
  have hε_pos : ε > 0 := by linarith
  -- Pick r₁ close to S_x and r₂ close to S_y
  obtain ⟨r₁, hr₁_in, hr₁_close⟩ := exists_lt_of_lt_csSup hx_ne (by linarith : S_x - ε < S_x)
  obtain ⟨r₂, hr₂_in, hr₂_close⟩ := exists_lt_of_lt_csSup hy_ne (by linarith : S_y - ε < S_y)
  -- Then (r₁ + r₂)/2 > S_xy
  have h1 : r₁ > S_x - ε := hr₁_close
  have h2 : r₂ > S_y - ε := hr₂_close
  have h3 : (r₁ + r₂) / 2 > (S_x - ε + S_y - ε) / 2 := by linarith
  have h4 : (S_x - ε + S_y - ε) / 2 = (S_x + S_y) / 2 - ε := by ring
  rw [h4] at h3
  have h5 : (S_x + S_y) / 2 - ε = S_xy + ε := by
    field_simp [hε]
    ring
  rw [h5] at h3
  -- So (r₁ + r₂)/2 > S_xy + ε > S_xy
  have h6 : (r₁ + r₂) / 2 > S_xy := by linarith
  -- But (r₁ + r₂)/2 ≤ S_xy by h_half_in
  have h7 := h_half_in r₁ r₂ hr₁_in hr₂_in
  linarith

/-- Second inequality: Θ(x) + Θ(y) ≤ Θ(x⊕y)

**STATUS**: This is the hardest remaining sorry.

**Mathematical analysis** (without commutativity):
Using iterate_op_op_le_double (x^m ⊕ y^m ≤ (x⊕y)^{2m}), we can only prove:
  (Θ(x) + Θ(y))/2 ≤ Θ(x⊕y)

The factor of 2 is **unavoidable** without commutativity:
- Counterexample: In the free monoid, [0]² ++ [1]² = [0,0,1,1] has length 4
  but ([0]++[1])² = [0,1,0,1] has length 4. The best bound is the 2m version.

**What we NEED** (for full equality):
1. Commutativity (which would give iterate_op_op_distrib), OR
2. The K&S Appendix A bootstrapping argument

**K&S approach**: They derive commutativity AS A CONSEQUENCE of a weaker
representation result, then use commutativity to prove full additivity.
The logical structure is:
  (weak representation) → (commutativity) → (strong additivity) → (full theorem)

For a complete formalization, we need to implement this bootstrapping. -/
lemma add_le_Theta (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y)
    (hxy : ident < op x y) :
    Theta a x ha hx + Theta a y ha hy ≤ Theta a (op x y) ha hxy := by
  -- Without commutativity, we can only prove half_add_le_Theta (factor of 2).
  -- The full proof requires K&S Appendix A bootstrapping.
  -- See the docstring above for the mathematical situation.
  sorry

/-- **Additivity of Theta**: Θ(x ⊕ y) = Θ(x) + Θ(y).

This is the key property that makes the representation theorem work.
Proved by combining the two inequalities. -/
theorem Theta_add (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y) :
    Theta a (op x y) ha (by {
      -- Show ident < x ⊕ y from ident < x and ident < y
      calc ident = op ident ident := (op_ident_left ident).symm
        _ < op x ident := op_strictMono_left ident hx
        _ < op x y := op_strictMono_right x hy
    }) = Theta a x ha hx + Theta a y ha hy := by
  have hxy : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
      _ < op x ident := op_strictMono_left ident hx
      _ < op x y := op_strictMono_right x hy
  apply le_antisymm
  · exact Theta_le_add a x y ha hx hy hxy
  · exact add_le_Theta a x y ha hx hy hxy

end Additivity

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

/-- **K&S Separation Lemma** (Paper lines 1536-1622)

For x < y (both > ident), there exist n, m such that:
  iterate_op x m < iterate_op a n ≤ iterate_op y m

This gives an element n/m that is in lowerRatioSet a y but NOT in lowerRatioSet a x.

**Proof idea**: The gap between iterate_op y m and iterate_op x m grows as m increases
(by strict monotonicity). By the Archimedean property, this gap eventually "contains"
at least one iterate of a. -/
theorem ks_separation_lemma (a x y : α) (ha : ident < a) (hx : ident < x)
    (hy : ident < y) (hxy : x < y) :
    ∃ n m : ℕ, m > 0 ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  -- By Archimedean, get the minimal N such that x < iterate_op a N
  obtain ⟨N, hN⟩ := bounded_by_iterate a ha x
  -- Case split: either iterate_op a N ≤ y (separation at m=1) or y < iterate_op a N
  rcases le_or_lt (iterate_op a N) y with h_sep | h_same
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
    obtain ⟨L, hL⟩ := bounded_by_iterate y hy a
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

    -- Key observation: We have gap_dominates giving y^{2L} > x^L ⊕ a.
    -- We'll use a larger m for witnesses where the gap is even bigger.
    -- Take m = 2L. Then find the crossing point for x^{2L}.

    have hL_pos : 0 < L := by
      by_contra h0
      have hL0 : L = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h0)
      subst hL0
      have h_ident_gt : ident > a := by simpa [iterate_op_zero] using hL
      exact (lt_asymm ha h_ident_gt).elim

    -- From gap_dominates at m = 2L: y^{3L} > x^{2L} ⊕ a
    have h_gap_3L : iterate_op y (3 * L) > op (iterate_op x (2 * L)) a := by
      conv_lhs => rw [show 3 * L = L + (2 * L) by omega]
      exact gap_dominates (2 * L) (by omega)

    -- Find the crossing point for x^{2L}
    obtain ⟨K2, hK2⟩ := bounded_by_iterate a ha (op (iterate_op x (2 * L)) a)

    let P2 : ℕ → Prop := fun k => iterate_op a k ≤ op (iterate_op x (2 * L)) a
    let n2 := Nat.findGreatest P2 K2

    have hP2_0 : P2 0 := by
      have h_id_le : ident ≤ iterate_op x (2 * L) := by
        cases L with
        | zero => omega  -- contradicts hL_pos
        | succ L' => exact le_of_lt (iterate_op_pos x hx _ (by omega))
      have h_lt : iterate_op x (2 * L) < op (iterate_op x (2 * L)) a := by
        simpa [op_ident_right] using (op_strictMono_right (iterate_op x (2 * L))) ha
      simpa [P2, iterate_op_zero] using le_of_lt (lt_of_le_of_lt h_id_le h_lt)

    have h_cross2 := findGreatest_crossing (P := P2) K2 hP2_0
    have hP2_n2 : iterate_op a n2 ≤ op (iterate_op x (2 * L)) a := h_cross2.1

    have h_not_P2_succ : ¬ P2 (n2 + 1) := by
      have h_not_P2_K2 : ¬ P2 K2 := not_le_of_gt hK2
      have hn2_lt_K2 : n2 < K2 := by
        by_contra h_ge
        push_neg at h_ge
        have hn2_le_K2 : n2 ≤ K2 := h_cross2.2.1
        have hn2_eq : n2 = K2 := Nat.le_antisymm hn2_le_K2 h_ge
        exact h_not_P2_K2 (by simpa [hn2_eq] using hP2_n2)
      exact h_cross2.2.2 (n2 + 1) (Nat.lt_succ_self n2) (Nat.succ_le_of_lt hn2_lt_K2)

    have h_crossing2 :
        iterate_op a n2 ≤ op (iterate_op x (2 * L)) a ∧ op (iterate_op x (2 * L)) a < iterate_op a (n2 + 1) :=
      ⟨hP2_n2, lt_of_not_ge h_not_P2_succ⟩

    -- Lower bound: x^{2L} < a^{n2+1}
    have hx2L_lt : iterate_op x (2 * L) < iterate_op a (n2 + 1) := by
      have h_lt : iterate_op x (2 * L) < op (iterate_op x (2 * L)) a := by
        simpa [op_ident_right] using (op_strictMono_right (iterate_op x (2 * L))) ha
      exact lt_trans h_lt h_crossing2.2

    -- Upper bound: a^{n2+1} ≤ y^{2L}
    -- We need a different approach since y^{2L} is from gap at m=L, not m=2L
    have h_gap_2L : iterate_op y (2 * L) > op (iterate_op x L) a := by
      conv_lhs => rw [show 2 * L = L + L by omega]
      exact gap_dominates L hL_pos

    have h_upper : iterate_op a (n2 + 1) ≤ iterate_op y (2 * L) := by
      -- We have: y^{2L} > x^L ⊕ a and a^{n2+1} > x^{2L} ⊕ a
      -- Since x^{2L} ⊕ a > x^L ⊕ a (by monotonicity), we can't directly compare.
      -- Need to use Case 2 bound: y < a^N to constrain the relationship.
      sorry  -- TODO: Bridge using y < a^N from Case 2

    have h_m_pos : 0 < 2 * L := by omega
    refine ⟨n2 + 1, 2 * L, h_m_pos, hx2L_lt, h_upper⟩

/-- Key consequence of separation: n/m is a strict upper bound for lowerRatioSet a x.
If iterate_op x m < iterate_op a n, then for any (n', m') with iterate_op a n' ≤ iterate_op x m',
we have n'/m' < n/m. -/
theorem separation_gives_strict_bound (a x : α) (ha : ident < a) (_hx : ident < x)
    (n m : ℕ) (hm : m > 0) (h_gap : iterate_op x m < iterate_op a n) :
    ∀ r ∈ lowerRatioSet a x, r < (n : ℝ) / m := by
  intro r ⟨n', m', hm'_pos, hle', hr_eq⟩
  rw [hr_eq]
  -- We want to show n'/m' < n/m, i.e., n' * m < n * m'.
  -- From: iterate_op a n' ≤ iterate_op x m' and iterate_op x m < iterate_op a n.
  -- Using the repetition lemmas:
  -- - From hle' (iterate_op a n' ≤ iterate_op x m'), scaling by m:
  --   iterate_op a (n' * m) ≤ iterate_op x (m' * m)
  -- - From h_gap (iterate_op x m < iterate_op a n), scaling by m':
  --   iterate_op x (m * m') < iterate_op a (n * m')
  -- Combining: iterate_op a (n' * m) ≤ iterate_op x (m * m') < iterate_op a (n * m')
  -- So n' * m < n * m' by strict monotonicity of iterate_op a.
  have h1 : iterate_op a (n' * m) ≤ iterate_op x (m' * m) := by
    -- Use repetition_lemma_le: if iterate_op a n' ≤ iterate_op x m', then
    -- iterate_op a (n' * m) ≤ iterate_op x (m' * m)
    exact repetition_lemma_le a x n' m' m hle'
  have h2 : iterate_op x (m * m') < iterate_op a (n * m') := by
    -- Use repetition_lemma_lt: if iterate_op x m < iterate_op a n, then
    -- iterate_op x (m * m') < iterate_op a (n * m')
    exact repetition_lemma_lt x a m n m' hm'_pos h_gap
  -- Now: iterate_op a (n' * m) ≤ iterate_op x (m' * m) = iterate_op x (m * m') < iterate_op a (n * m')
  have h_combined : iterate_op a (n' * m) < iterate_op a (n * m') := by
    rw [Nat.mul_comm m' m] at h1
    exact lt_of_le_of_lt h1 h2
  -- By strict monotonicity of iterate_op a: n' * m < n * m'
  have h_nm : n' * m < n * m' := by
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_ge : iterate_op a (n * m') ≤ iterate_op a (n' * m) := iterate_op_mono a ha h_not_lt
    exact absurd (lt_of_lt_of_le h_combined h_ge) (lt_irrefl _)
  -- Therefore n'/m' < n/m
  have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm'_pos_real : (0 : ℝ) < m' := Nat.cast_pos.mpr hm'_pos
  -- n'/m' < n/m ↔ n' * m < n * m' (cross multiply with positive denominators)
  have h_cross : (n' : ℝ) * m < (n : ℝ) * m' := by
    calc (n' : ℝ) * m = ((n' * m : ℕ) : ℝ) := by push_cast; ring
      _ < ((n * m' : ℕ) : ℝ) := Nat.cast_lt.mpr h_nm
      _ = (n : ℝ) * m' := by push_cast; ring
  -- n'/m' < n/m follows from cross multiplication: n' * m < n * m'
  -- a / b < c / d ↔ a * d < c * b when b, d > 0
  rw [div_lt_div_iff₀ hm'_pos_real hm_pos_real]
  exact h_cross

/-- ThetaFull is strictly monotone on elements > ident.
This is a key step toward the representation theorem.

With LinearOrder, we use the K&S separation lemma to find a ratio n/m
that separates the lower ratio sets. -/
theorem ThetaFull_strictMono_on_pos (a : α) (ha : ident < a) (x y : α)
    (hx : ident < x) (hy : ident < y) (hxy : x < y) :
    ThetaFull a ha x < ThetaFull a ha y := by
  simp only [ThetaFull, hx, hy, dif_pos]
  unfold Theta
  -- Key facts
  have hx_bdd := lowerRatioSet_bddAbove a x ha hx
  have hy_bdd := lowerRatioSet_bddAbove a y ha hy
  have hx_ne := lowerRatioSet_nonempty a x hx
  have hy_ne := lowerRatioSet_nonempty a y hy

  -- Get separation: n, m such that iterate_op x m < iterate_op a n ≤ iterate_op y m
  obtain ⟨n, m, hm_pos, h_gap, h_in_y⟩ := ks_separation_lemma a x y ha hx hy hxy

  -- n/m is in y's set
  have h_nm_in_y : (n : ℝ) / m ∈ lowerRatioSet a y := ⟨n, m, hm_pos, h_in_y, rfl⟩

  -- n/m is a strict upper bound for x's set
  have h_nm_bound : ∀ r ∈ lowerRatioSet a x, r < (n : ℝ) / m :=
    separation_gives_strict_bound a x ha hx n m hm_pos h_gap

  -- sSup(x) ≤ n/m ≤ sSup(y)
  have h_sup_x_le : sSup (lowerRatioSet a x) ≤ (n : ℝ) / m :=
    csSup_le hx_ne (fun r hr => le_of_lt (h_nm_bound r hr))
  have h_nm_le_sup_y : (n : ℝ) / m ≤ sSup (lowerRatioSet a y) := le_csSup hy_bdd h_nm_in_y

  -- Goal: sSup(lowerRatioSet a x) < sSup(lowerRatioSet a y)
  -- We have: sSup x ≤ n/m ≤ sSup y
  -- For strict: we show that y's set has an element strictly greater than n/m.

  -- By Archimedean applied to y, iterate_op y (m+1) > iterate_op y m ≥ iterate_op a n.
  -- Since iterate_op y grows faster than iterate_op a (both are Archimedean),
  -- there exists k ≥ 1 such that iterate_op a (n + k) ≤ iterate_op y (m+1).
  -- If k is large enough, (n+k)/(m+1) > n/m.

  -- For now, use the transitive chain: sSup x ≤ n/m < (better element) ≤ sSup y
  -- The existence of a better element follows from Archimedean + strict monotonicity.

  -- Claim: There exists n', m' with n'/m' > n/m and n'/m' ∈ lowerRatioSet a y.
  -- This follows from: iterate_op y (m+1) > iterate_op y m ≥ iterate_op a n,
  -- so some n+k satisfies iterate_op a (n+k) ≤ iterate_op y (m+1) with k > n/m.
  -- Two cases for proving strict inequality:
  -- Case A: h_in_y is strict (iterate_op a n < iterate_op y m) → we can find larger ratio
  -- Case B: h_in_y is equality → sSup (lowerRatioSet a x) < n/m is strict

  by_cases h_strict_in : iterate_op a n < iterate_op y m
  · -- Case A: iterate_op a n < iterate_op y m (strict)
    -- Use mathlib's exists_lt_of_lt_csSup to find the witness automatically
    -- Key: prove n/m < sSup(lowerRatioSet a y), then get r ∈ lowerRatioSet a y with n/m < r
    have h_lt_sup : (n : ℝ) / m < sSup (lowerRatioSet a y) := by
      -- We know n/m ≤ sSup from h_nm_le_sup_y
      -- For strict <, show n/m is not the supremum
      -- Since iterate_op a n < iterate_op y m (strict), we can fit a larger element
      apply lt_of_le_of_ne h_nm_le_sup_y
      intro h_eq
      -- Suppose n/m = sSup(lowerRatioSet a y). Then n/m is an upper bound.
      -- But iterate_op a n < iterate_op y m means we can fit a larger ratio:
      -- Either (n+1)/m works (if a^{n+1} ≤ y^m), or we use Archimedean growth
      by_cases h_n1 : iterate_op a (n + 1) ≤ iterate_op y m
      · -- (n+1)/m is in the set with ratio > n/m
        have h_in : ((n + 1 : ℕ) : ℝ) / m ∈ lowerRatioSet a y :=
          ⟨n + 1, m, hm_pos, h_n1, rfl⟩
        have h_gt : (n : ℝ) / m < ((n + 1 : ℕ) : ℝ) / m := by
          have hm_pos' : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
          rw [div_lt_div_iff₀ hm_pos' hm_pos']
          push_cast; nlinarith
        rw [h_eq] at h_gt
        exact absurd h_gt (not_lt.mpr (le_csSup hy_bdd h_in))
      · -- a^{n+1} > y^m, but by Archimedean on y, y^{m+1} > y^m
        -- and eventually some a^k ≤ y^{m+1} with k > n
        push_neg at h_n1
        have h_ym1 : iterate_op y m < iterate_op y (m + 1) :=
          iterate_op_strictMono y hy (by omega : m < m + 1)
        have h_strict : iterate_op a n < iterate_op y (m + 1) :=
          lt_trans h_strict_in h_ym1
        -- By bounded_by_iterate, ∃ K with y^{m+1} < a^K
        obtain ⟨K, hK⟩ := bounded_by_iterate a ha (iterate_op y (m + 1))
        -- So there's a k with n < k < K and a^k ≤ y^{m+1}
        -- giving ratio k/(m+1) > n/m (for large enough k)
        -- The details are complex, but this contradicts n/m being sup
        -- Finding the right witness k requires careful analysis of crossing points
        have : ∃ k, k > n ∧ iterate_op a k ≤ iterate_op y (m + 1) ∧ (k : ℝ) / (m + 1) > (n : ℝ) / m := by
          -- TODO: Use Nat.findGreatest to find max k with a^k ≤ y^{m+1}, then show k/(m+1) > n/m
          -- This requires proving the crossing point has the right ratio property
          sorry
        obtain ⟨k, _, hk_le, hk_ratio⟩ := this
        have h_in_k : (k : ℝ) / (m + 1) ∈ lowerRatioSet a y := by
          refine ⟨k, m + 1, by omega, hk_le, ?_⟩
          simp only [Nat.cast_add, Nat.cast_one]
        rw [h_eq] at hk_ratio
        exact absurd hk_ratio (not_lt.mpr (le_csSup hy_bdd h_in_k))
    -- Now use exists_lt_of_lt_csSup to get the witness
    obtain ⟨r, hr_in_y, hr_gt⟩ := exists_lt_of_lt_csSup hy_ne h_lt_sup
    calc sSup (lowerRatioSet a x)
        ≤ (n : ℝ) / m := h_sup_x_le
      _ < r := hr_gt
      _ ≤ sSup (lowerRatioSet a y) := le_csSup hy_bdd hr_in_y

  · -- Case B: iterate_op a n = iterate_op y m (exact equality)
    -- In this case, n/m IS the supremum of lowerRatioSet a y
    -- We show sSup (lowerRatioSet a x) < n/m directly
    push_neg at h_strict_in
    have h_eq : iterate_op a n = iterate_op y m := le_antisymm h_in_y h_strict_in

    -- n/m is the supremum of lowerRatioSet a y (since iterate_op a n = iterate_op y m)
    have h_nm_is_sup : sSup (lowerRatioSet a y) = (n : ℝ) / m := by
      apply le_antisymm
      · -- sSup ≤ n/m: every element is ≤ n/m
        apply csSup_le hy_ne
        intro r ⟨n', m', hm'_pos, hle', hr_eq⟩
        rw [hr_eq]
        -- Need n'/m' ≤ n/m, i.e., n' * m ≤ n * m'
        -- From hle': iterate_op a n' ≤ iterate_op y m'
        -- And from h_eq: iterate_op a n = iterate_op y m
        -- By scaling: iterate_op a (n * m') = iterate_op y (m * m')
        --            iterate_op a (n' * m) ≤ iterate_op y (m' * m)
        -- So iterate_op a (n' * m) ≤ iterate_op y (m' * m) = iterate_op a (n * m')
        -- By strict mono of iterate_op a: n' * m ≤ n * m'
        have h1 : iterate_op a (n' * m) ≤ iterate_op y (m' * m) :=
          repetition_lemma_le a y n' m' m hle'
        have h2 : iterate_op y (m' * m) = iterate_op a (n * m') := by
          calc iterate_op y (m' * m)
              = iterate_op y (m * m') := by ring_nf
            _ = iterate_op (iterate_op y m) m' := (iterate_op_mul y m m').symm
            _ = iterate_op (iterate_op a n) m' := by rw [h_eq]
            _ = iterate_op a (n * m') := iterate_op_mul a n m'
        -- Combine: iterate_op a (n' * m) ≤ iterate_op y (m' * m) = iterate_op a (n * m')
        have h_combined : iterate_op a (n' * m) ≤ iterate_op a (n * m') :=
          le_trans h1 (le_of_eq h2)
        -- By monotonicity of iterate_op a: n' * m ≤ n * m'
        have h_nm : n' * m ≤ n * m' := by
          by_contra h_not_le
          push_neg at h_not_le
          have h_gt : iterate_op a (n * m') < iterate_op a (n' * m) :=
            iterate_op_strictMono a ha h_not_le
          exact absurd (lt_of_lt_of_le h_gt h_combined) (lt_irrefl _)
        -- Convert to real division inequality
        have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
        have hm'_pos_real : (0 : ℝ) < m' := Nat.cast_pos.mpr hm'_pos
        rw [div_le_div_iff₀ hm'_pos_real hm_pos_real]
        calc (n' : ℝ) * m = ((n' * m : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((n * m' : ℕ) : ℝ) := Nat.cast_le.mpr h_nm
          _ = (n : ℝ) * m' := by push_cast; ring
      · -- n/m ≤ sSup: n/m is in the set
        exact le_csSup hy_bdd h_nm_in_y

    -- Now show sSup (lowerRatioSet a x) < n/m
    -- We have: ∀ r ∈ lowerRatioSet a x, r < n/m (from separation_gives_strict_bound)
    -- And lowerRatioSet a x ⊂ lowerRatioSet a y strictly (since x < y)
    -- The gap is witnessedby h_gap: iterate_op x m < iterate_op a n

    -- Key: the gap means lowerRatioSet a x is bounded away from n/m
    -- Since iterate_op x m < iterate_op a n = iterate_op y m, and x < y,
    -- there's a "gap" in the ratios

    have h_strict_bound : sSup (lowerRatioSet a x) < (n : ℝ) / m := by
      -- From h_gap: iterate_op x m < iterate_op a n, let n* = max{k : iterate_op a k ≤ iterate_op x m}.
      -- Then n* ≤ n - 1. For any (n', m') ∈ lowerRatioSet a x, by repetition:
      --   n' * m < (n* + 1) * m' ≤ n * m'
      -- So n'/m' ≤ n/m - 1/(m * m').
      -- The gap 1/(m * m') shrinks as m' grows, but m' is bounded by Archimedean:
      -- n'/m' ≤ N_x where x < iterate_op a N_x.
      -- The key is that this bound N_x < n/m when x < y and iterate_op a n = iterate_op y m.
      -- This follows from Θ(x) < Θ(y) = n/m in the eventual representation.
      -- TODO: Complete using the Archimedean bound argument (K&S Appendix A).
      sorry

    calc sSup (lowerRatioSet a x)
        < (n : ℝ) / m := h_strict_bound
      _ = sSup (lowerRatioSet a y) := h_nm_is_sup.symm

/-! ### Summary: Representation Theorem Infrastructure Status

**Proven**:
- `iterate_op_strictMono`: Iterates of a > ident form a strictly increasing chain
- `bounded_by_iterate`: Every element is bounded above by some iterate
- `lowerRatioSet_nonempty`: The lower ratio set is non-empty
- `lowerRatioSet_self`: For x = a, the lower ratio set is { n/m : n ≤ m }
- `sSup_ratio_le_one`: sup { n/m : n ≤ m } = 1
- `Theta_ref_eq_one`: Θ(a) = 1 for the reference element
- `ThetaFull_ident`: Θ(ident) = 0
- `commutativity_from_representation`: Commutativity follows from additivity

**Remaining** (with sorries):
- `lowerRatioSet_bddAbove`: Boundedness requires the K&S repetition lemma
- `ThetaFull_strictMono_on_pos`: Strict monotonicity of Θ
- `ks_representation_theorem`: Existence of additive representation

The key missing piece is the **repetition lemma** (K&S lines 1497-1534):
  If μ(r,...,t) ≤ μ(r₀,...,t₀; u), then μ(n·r,...,n·t) ≤ μ(n·r₀,...,n·t₀; n·u)

This lemma allows us to:
1. Bound the lower ratio set uniformly (proving it's bounded above)
2. Show that Θ respects the operation (additivity)
3. Derive strict monotonicity from the construction
-/

/-! ### Phase 9: Commutativity Derived from Additivity (K&S lines 1448-1453, 1160-1166)

**KEY INSIGHT FROM K&S**: Commutativity is NOT an axiom - it's DERIVED!

The paper states (line 1166):
> "Associativity + Order ⟹ Additivity allowed ⟹ Commutativity"

The derivation:
1. From ks_representation_theorem, get Θ with Θ(x ⊕ y) = Θ(x) + Θ(y)
2. Since + is commutative on ℝ: Θ(x ⊕ y) = Θ(x) + Θ(y) = Θ(y) + Θ(x) = Θ(y ⊕ x)
3. Since Θ is strictly monotone, it's injective
4. Therefore: x ⊕ y = y ⊕ x
-/

/-- Commutativity follows from the existence of an additive ORDER EMBEDDING.

**Key insight**: For partial orders, we need Θ to be an ORDER EMBEDDING
(both order-preserving AND order-reflecting), not just strictly monotone.
This ensures Θ is injective: if Θ(a) = Θ(b), then a ≤ b and b ≤ a, so a = b.

The K&S representation theorem constructs such an embedding into ℝ. -/
theorem commutativity_from_representation (Θ : α → ℝ)
    (hΘ_le : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b)  -- Order embedding (preserves AND reflects ≤)
    (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y) :
    ∀ x y : α, op x y = op y x := by
  intro x y
  -- Θ(x ⊕ y) = Θ(x) + Θ(y) = Θ(y) + Θ(x) = Θ(y ⊕ x)
  have h1 : Θ (op x y) = Θ x + Θ y := hΘ_add x y
  have h2 : Θ (op y x) = Θ y + Θ x := hΘ_add y x
  have h3 : Θ x + Θ y = Θ y + Θ x := add_comm (Θ x) (Θ y)
  have h4 : Θ (op x y) = Θ (op y x) := by rw [h1, h2, h3]
  -- Θ is injective (order embedding into ℝ)
  -- If Θ(a) = Θ(b), then Θ(a) ≤ Θ(b) and Θ(b) ≤ Θ(a), so a ≤ b and b ≤ a, so a = b
  have h_inj : Function.Injective Θ := by
    intro a b hab
    have h_ab : a ≤ b := (hΘ_le a b).mpr (le_of_eq hab)
    have h_ba : b ≤ a := (hΘ_le b a).mpr (le_of_eq hab.symm)
    exact le_antisymm h_ab h_ba
  exact h_inj h4

/-- Full commutativity theorem: Once we prove the representation theorem
(with order embedding, not just strict monotonicity), commutativity follows. -/
theorem commutativity_derived
    (h_rep : ∃ (Θ : α → ℝ), (∀ a b, a ≤ b ↔ Θ a ≤ Θ b) ∧ Θ ident = 0 ∧ ∀ x y, Θ (op x y) = Θ x + Θ y) :
    ∀ x y : α, op x y = op y x := by
  obtain ⟨Θ, hΘ_le, _, hΘ_add⟩ := h_rep
  exact commutativity_from_representation Θ hΘ_le hΘ_add

end KSAppendixA

end Mettapedia.ProbabilityTheory.KnuthSkilling
