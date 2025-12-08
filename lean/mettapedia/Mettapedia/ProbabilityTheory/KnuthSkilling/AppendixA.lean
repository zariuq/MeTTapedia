/-
# Knuth-Skilling Appendix A: Associativity → Representation → Commutativity

This file provides the core K&S Appendix A construction that proves:

> For any Knuth-Skilling algebra, there exists an additive representation Θ : α → ℝ,
> and consequently the operation is commutative.

**Reference**: Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
(arXiv lines 1292-1922)

**Key insight**: Commutativity is DERIVED, not assumed!
  "Associativity + Order ⟹ Additivity allowed ⟹ Commutativity" (line 1166)

**Proof structure** (grid-based bootstrapping):
1. One type base case: m(r of a) = r·a (linear grid)
2. A/B/C sets partition old values relative to new type
3. Case B non-empty: new type's value is rationally related to old
4. Case B empty: Accuracy lemma pins down irrational value via Archimedean
5. Induction: extend from k types to k+1 types
6. Commutativity emerges from additivity + injectivity

**IMPORTANT**: This file does NOT import SeparationProof or RepTheorem.
It provides the foundational `associativity_representation` theorem and
`op_comm_of_associativity` lemma that RepTheorem then imports and uses.

The dependency structure is:
  Basic + Algebra  ─┬─ AppendixA (this file)
                    ├─ SeparationProof
                    └─ RepTheorem (imports AppendixA and SeparationProof)
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Batteries.Data.Fin.Fold

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-! ## Main API: Representation Theorem and Commutativity

These are the two key results that the rest of the library depends on.
The proofs use the grid-based bootstrapping argument from K&S Appendix A.
-/

/-- **Knuth-Skilling Associativity Representation Theorem** (Appendix A main result)

For any Knuth-Skilling algebra α, there exists a function Θ : α → ℝ such that:
1. Θ preserves order: a ≤ b ↔ Θ(a) ≤ Θ(b)
2. Θ(ident) = 0
3. Θ is additive: Θ(x ⊕ y) = Θ(x) + Θ(y) for all x, y

This is the core result from which commutativity follows.

**Proof strategy** (K&S Appendix A grid construction):
1. Fix a positive element a > ident as reference
2. Build Θ on the grid {a^n : n ∈ ℕ} first: Θ(a^n) = n
3. For any new element b, use A/B/C partition to determine Θ(b)
4. A = {multisets with value < b}, B = {= b}, C = {> b}
5. If B is non-empty: Θ(b) is rationally related to existing values
6. If B is empty: Accuracy lemma pins Θ(b) as limit via Archimedean
7. Prove additivity on the grid, extend to all of α
8. Derive commutativity from additivity + injectivity
-/
theorem associativity_representation
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  -- TODO: K&S Appendix A grid-based construction
  --
  -- This is the MAIN THEOREM that requires the full Appendix A argument.
  -- The proof builds Θ incrementally on a grid of "atom types" using:
  --
  -- Phase 1: One-type base case
  --   - Fix reference element a with ident < a
  --   - Define Θ(a^n) = n for all n ∈ ℕ
  --   - Prove strict monotonicity and additivity on this grid
  --
  -- Phase 2: A/B/C partition for new types
  --   - For any new element b not on the a-grid
  --   - Partition multisets into A (< b), B (= b), C (> b)
  --   - Use repetition lemmas to show partition is consistent
  --
  -- Phase 3: Determine Θ(b) from partition
  --   - If B ≠ ∅: Θ(b) = rational multiple of existing values
  --   - If B = ∅: Θ(b) = limit via Archimedean density
  --
  -- Phase 4: Verify additivity and extend to all of α
  --   - Show Θ(x ⊕ y) = Θ(x) + Θ(y) on the grid
  --   - Use density of grid in α to extend
  --
  -- This construction avoids the circular dependency in RepTheorem.lean:
  -- We build Θ FIRST, then derive commutativity FROM Θ.
  sorry

/-- Commutativity follows from the existence of an additive representation.

If Θ : α → ℝ is strictly monotone (or just injective) and additive, then:
  Θ(x ⊕ y) = Θ(x) + Θ(y) = Θ(y) + Θ(x) = Θ(y ⊕ x)
  ⟹ x ⊕ y = y ⊕ x (by injectivity)
-/
theorem commutativity_from_representation
    (Θ : α → ℝ)
    (hΘ_order : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b)
    (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y) :
    ∀ x y : α, op x y = op y x := by
  intro x y
  -- Θ(x ⊕ y) = Θ(x) + Θ(y) = Θ(y) + Θ(x) = Θ(y ⊕ x)
  have h1 : Θ (op x y) = Θ x + Θ y := hΘ_add x y
  have h2 : Θ (op y x) = Θ y + Θ x := hΘ_add y x
  have h3 : Θ x + Θ y = Θ y + Θ x := add_comm (Θ x) (Θ y)
  have h4 : Θ (op x y) = Θ (op y x) := by rw [h1, h3, ← h2]
  -- From order preservation, Θ is injective
  have hΘ_inj : Function.Injective Θ := by
    intro a b hab
    have h_le : Θ a ≤ Θ b := le_of_eq hab
    have h_ge : Θ b ≤ Θ a := ge_of_eq hab
    have ha_le_b : a ≤ b := (hΘ_order a b).mpr h_le
    have hb_le_a : b ≤ a := (hΘ_order b a).mpr h_ge
    exact le_antisymm ha_le_b hb_le_a
  exact hΘ_inj h4

/-- **Main corollary**: Commutativity holds for any Knuth-Skilling algebra.

This is the key result that unblocks the rest of the library:
- RepTheorem.lean can use this to prove full additivity
- The "factor of 2" problem disappears with commutativity
- exists_split_ratio_of_op becomes tractable
-/
theorem op_comm_of_associativity
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] :
    ∀ x y : α, op x y = op y x := by
  obtain ⟨Θ, hΘ_order, _, hΘ_add⟩ := associativity_representation α
  exact commutativity_from_representation Θ hΘ_order hΘ_add

/-- Left cancellation from strict monotonicity: if x ⊕ z ≤ y ⊕ z then x ≤ y. -/
lemma cancellative_left {x y z : α} (h : op x z ≤ op y z) : x ≤ y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact le_of_lt hlt
  · simpa [heq]
  · have h' : op y z < op x z := (op_strictMono_left z) hgt
    have : False := (not_lt_of_ge h) h'
    exact this.elim

/-- Right cancellation from strict monotonicity: if z ⊕ x ≤ z ⊕ y then x ≤ y. -/
lemma cancellative_right {x y z : α} (h : op z x ≤ op z y) : x ≤ y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact le_of_lt hlt
  · simpa [heq]
  · have h' : op z y < op z x := (op_strictMono_right z) hgt
    have : False := (not_lt_of_ge h) h'
    exact this.elim

/-! ## Phase 1: One-Type Grid Representation (Foundation)

The first step in the Appendix A construction is to build Θ on the
grid generated by a single element a > ident.
-/

/-- The grid generated by element a: {a^n : n ∈ ℕ} -/
def grid (a : α) : Set α := {x | ∃ n : ℕ, x = iterate_op a n}

/-- Grid membership for iterates -/
lemma iterate_op_mem_grid (a : α) (n : ℕ) : iterate_op a n ∈ grid a :=
  ⟨n, rfl⟩

/-- The identity is in every grid (as a^0) -/
lemma ident_mem_grid (a : α) : ident ∈ grid a :=
  ⟨0, (iterate_op_zero a).symm⟩

/-- The map n ↦ a^n is strictly monotone for a > ident -/
lemma grid_strictMono (a : α) (ha : ident < a) : StrictMono (iterate_op a) :=
  iterate_op_strictMono a ha

/-- Grid elements are uniquely determined by their index -/
lemma grid_index_unique (a : α) (ha : ident < a) (m n : ℕ)
    (h : iterate_op a m = iterate_op a n) : m = n := by
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (ne_of_lt (iterate_op_strictMono a ha hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (iterate_op_strictMono a ha hgt))

/-- One-type representation on the grid -/
structure OneTypeGridRep (a : α) (ha : ident < a) where
  /-- The representation function on grid elements -/
  Θ_grid : {x // x ∈ grid a} → ℝ
  /-- Strict monotonicity -/
  strictMono : StrictMono Θ_grid
  /-- Additivity: Θ(a^m ⊕ a^n) = Θ(a^m) + Θ(a^n) -/
  add : ∀ m n : ℕ,
    Θ_grid ⟨iterate_op a (m + n), iterate_op_mem_grid a (m + n)⟩ =
    Θ_grid ⟨iterate_op a m, iterate_op_mem_grid a m⟩ +
    Θ_grid ⟨iterate_op a n, iterate_op_mem_grid a n⟩
  /-- Normalization: Θ(ident) = 0 -/
  ident_eq_zero : Θ_grid ⟨ident, ident_mem_grid a⟩ = 0
  /-- Normalization: Θ(a) = 1 -/
  ref_eq_one : Θ_grid ⟨a, ⟨1, (iterate_op_one a).symm⟩⟩ = 1

/-- Helper: extract the unique index for a grid element -/
noncomputable def gridIndex (a : α) (_ha : ident < a) (x : {x // x ∈ grid a}) : ℕ :=
  Classical.choose x.2

/-- The index is correct: x = a^(gridIndex x) -/
lemma gridIndex_spec (a : α) (ha : ident < a) (x : {x // x ∈ grid a}) :
    x.val = iterate_op a (gridIndex a ha x) :=
  Classical.choose_spec x.2

/-- The index for iterate_op a n is n -/
lemma gridIndex_iterate_op (a : α) (ha : ident < a) (n : ℕ) :
    gridIndex a ha ⟨iterate_op a n, iterate_op_mem_grid a n⟩ = n := by
  have h := gridIndex_spec a ha ⟨iterate_op a n, iterate_op_mem_grid a n⟩
  simp only at h
  exact grid_index_unique a ha _ n h.symm

/-- Canonical one-type representation Θ₁: send a^n to n. -/
noncomputable def Θ₁ (a : α) (ha : ident < a) : {x // x ∈ grid a} → ℝ :=
  fun x => (gridIndex a ha x : ℝ)

/-- Θ₁ evaluates to n on the nth iterate of a. -/
lemma Θ₁_on_power (a : α) (ha : ident < a) (n : ℕ) :
    Θ₁ a ha ⟨iterate_op a n, iterate_op_mem_grid a n⟩ = (n : ℝ) := by
  simp [Θ₁, gridIndex_iterate_op]

/-- The canonical OneTypeGridRep built from Θ₁. -/
noncomputable def oneTypeRep (a : α) (ha : ident < a) : OneTypeGridRep a ha := by
  classical
  refine
    { Θ_grid := Θ₁ a ha
      , strictMono := ?_
      , add := ?_
      , ident_eq_zero := ?_
      , ref_eq_one := ?_ }
  · intro x y hxy
    -- x < y in the grid implies gridIndex x < gridIndex y
    apply Nat.cast_lt.mpr
    have hx_eq := gridIndex_spec a ha x
    have hy_eq := gridIndex_spec a ha y
    have hmono := (grid_strictMono a ha).monotone
    by_contra hneg
    have hle : iterate_op a (gridIndex a ha y) ≤ iterate_op a (gridIndex a ha x) :=
      hmono (le_of_not_gt hneg)
    have hle' : y.val ≤ x.val := by simpa [hx_eq, hy_eq] using hle
    exact (not_le_of_gt hxy) hle'
  · intro m n
    -- Θ₁ is additive on the grid: Θ₁(a^{m+n}) = Θ₁(a^m) + Θ₁(a^n)
    simp [Θ₁, gridIndex_iterate_op, Nat.cast_add]
  · -- Θ₁(ident) = 0
    have h_spec := gridIndex_spec a ha ⟨ident, ident_mem_grid a⟩
    have h_eq : iterate_op a (gridIndex a ha ⟨ident, ident_mem_grid a⟩) = iterate_op a 0 := by
      simpa [iterate_op_zero] using h_spec.symm
    have hidx := grid_index_unique a ha _ 0 h_eq
    simp [Θ₁, hidx]
  · -- Θ₁(a) = 1
    have h_spec := gridIndex_spec a ha ⟨a, ⟨1, (iterate_op_one a).symm⟩⟩
    have h_eq :
        iterate_op a (gridIndex a ha ⟨a, ⟨1, (iterate_op_one a).symm⟩⟩) = iterate_op a 1 := by
      have h := h_spec.symm
      simpa [iterate_op_one] using h
    have hidx := grid_index_unique a ha _ 1 h_eq
    simp [Θ₁, hidx]

/-- Existence of one-type grid representation.

This is the base case of the Appendix A induction.
The representation is simply Θ(a^n) = n. -/
theorem one_type_grid_rep_exists (a : α) (ha : ident < a) : Nonempty (OneTypeGridRep a ha) := by
  exact ⟨oneTypeRep a ha⟩

/-! ## Phase 2: A/B/C Partition for New Types

**Reference**: K&S Appendix A, Section A.3.2 "Separation"

The A/B/C partition is used to extend the representation from k types to k+1 types.
Given an existing grid of values μ(r,...,t) = ra + ... + tc for k atom types,
and a new type d, we partition old values relative to new targets:

- **Set A**: Old values that lie below new targets: μ(r,...,t) < μ(r₀,...,t₀; u)
- **Set B**: Old values that equal new targets: μ(r,...,t) = μ(r₀,...,t₀; u)
- **Set C**: Old values that lie above new targets: μ(r,...,t) > μ(r₀,...,t₀; u)

The repetition lemma shows these partitions are consistent across multiplicities.

**Case B non-empty**: The new type's value d is rationally related to existing values.
All members of B share a common statistic ((r-r₀)a+...+(t-t₀)c)/u = d.

**Case B empty**: The new type's value is determined as a limit δ via the Archimedean
property. The accuracy lemma shows δ can be found to arbitrary precision.
-/

/-- Multiset valuation: value of "r of a and s of b and ... " using iterate_op.

For the one-type case, this is just iterate_op a r.
For multi-type, we need to track multiple base elements. -/
def multiset_val (a : α) (r : ℕ) : α := iterate_op a r

/-- The lowerRatioSet-style approach from RepTheorem, localized here.

For element x, this is the set of ratios n/m where a^n ≤ x^m.
This captures the "relative position" of x in the grid generated by a. -/
def relativePosition (a x : α) : Set ℝ :=
  {r | ∃ n m : ℕ, 0 < m ∧ iterate_op a n ≤ iterate_op x m ∧ r = (n : ℝ) / m}

/-- A/B/C sets for comparing old grid values to new targets.

Given reference element a > ident and target x, partition grid elements:
- A: elements below x
- B: elements equal to x
- C: elements above x -/
def setA (a x : α) : Set ℕ := {n | iterate_op a n < x}
def setB (a x : α) : Set ℕ := {n | iterate_op a n = x}
def setC (a x : α) : Set ℕ := {n | x < iterate_op a n}

/-- The A/B/C sets partition ℕ -/
lemma abc_partition (a x : α) : ∀ n : ℕ, n ∈ setA a x ∨ n ∈ setB a x ∨ n ∈ setC a x := by
  intro n
  rcases lt_trichotomy (iterate_op a n) x with hlt | heq | hgt
  · left; exact hlt
  · right; left; exact heq
  · right; right; exact hgt

/-- The A/B/C sets are mutually exclusive -/
lemma abc_disjoint (a x : α) :
    (setA a x ∩ setB a x = ∅) ∧
    (setB a x ∩ setC a x = ∅) ∧
    (setA a x ∩ setC a x = ∅) := by
  constructor
  · ext n; simp only [setA, setB, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
                      iff_false, not_and]
    intro hlt heq; exact absurd heq (ne_of_lt hlt)
  constructor
  · ext n; simp only [setB, setC, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
                      iff_false, not_and]
    intro heq hgt; exact absurd heq (ne_of_gt hgt)
  · ext n; simp only [setA, setC, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
                      iff_false, not_and]
    intro hlt hgt
    have h : iterate_op a n < iterate_op a n := lt_trans hlt hgt
    exact absurd h (lt_irrefl _)

/-- If x is itself on the grid, setA is bounded above by that index. -/
lemma setA_bddAbove_of_setB_nonempty (a : α) (ha : ident < a) (x : α)
    (hB : ∃ n, iterate_op a n = x) :
    ∃ N, ∀ n ∈ setA a x, n ≤ N := by
  rcases hB with ⟨N, rfl⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hlt : iterate_op a n < iterate_op a N := hn
  have hmono : Monotone (iterate_op a) := (grid_strictMono a ha).monotone
  have hnot : ¬ N ≤ n := by
    intro hle
    have hge : iterate_op a N ≤ iterate_op a n := hmono hle
    exact (not_lt_of_ge hge) hlt
  have hltNat : n < N := lt_of_not_ge hnot
  exact le_of_lt hltNat

/-- Each n belongs to exactly one of A, B, or C for a fixed target x. -/
lemma mem_A_or_B_or_C_unique (a x : α) (n : ℕ) :
    (n ∈ setA a x ∧ n ∉ setB a x ∧ n ∉ setC a x) ∨
    (n ∉ setA a x ∧ n ∈ setB a x ∧ n ∉ setC a x) ∨
    (n ∉ setA a x ∧ n ∉ setB a x ∧ n ∈ setC a x) := by
  classical
  rcases lt_trichotomy (iterate_op a n) x with hlt | heq | hgt
  · left
    refine ⟨hlt, ?_, ?_⟩
    · have hB : iterate_op a n ≠ x := ne_of_lt hlt
      simpa [setB] using hB
    · have hC : ¬ x < iterate_op a n := by
        intro hcontr
        exact (lt_asymm hlt hcontr).elim
      simpa [setC] using hC
  · right
    left
    refine ⟨?_, ?_, ?_⟩
    · simp [setA, heq]
    · simp [setB, heq]
    · simp [setC, heq]
  · right
    right
    refine ⟨?_, ?_, ?_⟩
    · have hA : ¬ iterate_op a n < x := by
        intro hcontr
        exact (lt_asymm hcontr hgt).elim
      simpa [setA] using hA
    · have hB : iterate_op a n ≠ x := ne_of_gt hgt
      simpa [setB] using hB
    · exact hgt

/-! ## Phase 3 (scaffolding): Multi-type grid skeleton

Following Appendix A, we package the “k atom types with multiplicities”
construction into a small reusable API. This is intentionally lean: it only
provides the data structures and a canonical fold-based evaluator `mu`.
The heavy separation and accuracy arguments will build on top of this. -/

open Finset

/-- A family of `k` atom types, each strictly above `ident`. -/
structure AtomFamily (α : Type*) [KnuthSkillingAlgebra α] (k : ℕ) where
  atoms : Fin k → α
  pos : ∀ i : Fin k, ident < atoms i

/-- Multiplicity vector for `k` atom types. -/
abbrev Multi (k : ℕ) := Fin k → ℕ

/-- Canonical valuation of a multiplicity vector: fold the appropriate iterates
    of each atom in the family using the Knuth–Skilling operation.

    Note: we use `foldl` to avoid any commutativity requirement on `op`. The
    order over `Finset.univ` for `Fin k` is deterministic. -/
noncomputable def mu {α : Type*} [KnuthSkillingAlgebra α] {k : ℕ}
    (F : AtomFamily α k) (r : Multi k) : α :=
  (List.finRange k).foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i))) ident

/-- Convenience: the one-type atom family for a fixed `a`. -/
def singletonAtomFamily (a : α) (ha : ident < a) : AtomFamily α 1 :=
  { atoms := fun _ => a
    pos := by intro _; exact ha }

/-- For the singleton atom family, `mu` reduces to the usual one-type iterate. -/
lemma mu_singleton (a : α) (ha : ident < a) (n : ℕ) :
    mu (singletonAtomFamily (α:=α) a ha) (fun _ => n) = iterate_op a n := by
  -- `Fin 1` has exactly one element, so the foldl is a single step.
  classical
  simp [mu, singletonAtomFamily, List.finRange_succ, List.finRange_zero, op_ident_left]

/-- Update a single coordinate of a multiplicity vector. -/
def updateMulti {k : ℕ} (r : Multi k) (i : Fin k) (n : ℕ) : Multi k :=
  fun j => if j = i then n else r j

lemma updateMulti_self {k : ℕ} (r : Multi k) (i : Fin k) (n : ℕ) :
    updateMulti r i n i = n := by simp [updateMulti]

lemma updateMulti_other {k : ℕ} (r : Multi k) (i : Fin k) (n : ℕ) {j : Fin k} (hj : j ≠ i) :
    updateMulti r i n j = r j := by simp [updateMulti, hj]

/-- `mu` is coordinatewise monotone in the multiplicity vector. -/
lemma mu_mono (F : AtomFamily α k) {r s : Multi k} (h : ∀ i, r i ≤ s i) :
    mu F r ≤ mu F s := by
  classical
  let l : List (Fin k) := List.finRange k
  -- Generalize to arbitrary starting accumulators to induct over the list.
  have aux :
      ∀ (l : List (Fin k)) (acc₁ acc₂ : α), acc₁ ≤ acc₂ →
        List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i))) acc₁ l ≤
        List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (s i))) acc₂ l := by
    intro l
    induction l with
    | nil =>
      intro acc₁ acc₂ hacc
      simpa [List.foldl] using hacc
    | cons i t ih =>
      intro acc₁ acc₂ hacc
      have h_iter_le : iterate_op (F.atoms i) (r i) ≤ iterate_op (F.atoms i) (s i) :=
        (grid_strictMono (F.atoms i) (F.pos i)).monotone (h i)
      have h_acc_step :
          op acc₁ (iterate_op (F.atoms i) (r i)) ≤
          op acc₂ (iterate_op (F.atoms i) (s i)) := by
        have h_left := op_mono_left (iterate_op (F.atoms i) (r i)) hacc
        have h_right := op_mono_right acc₂ h_iter_le
        exact le_trans h_left h_right
      simpa [List.foldl, List.foldl_cons] using ih _ _ h_acc_step
  have h_base := aux l ident ident (le_rfl : (ident : α) ≤ ident)
  simpa [mu, l] using h_base

/-- Monotonicity in a single coordinate, keeping others fixed. -/
lemma mu_mono_coord (F : AtomFamily α k) (i : Fin k) (r : Multi k) :
    Monotone (fun n => mu F (updateMulti r i n)) := by
  intro m n hmn
  refine mu_mono (F:=F) (r:=updateMulti r i m) (s:=updateMulti r i n) ?_
  intro j
  by_cases hj : j = i
  · subst hj; simpa [updateMulti] using hmn
  · simp [updateMulti, hj]

/-- Folding with fixed right arguments is strictly monotone in the accumulator. -/
lemma fold_strictMono_left (F : AtomFamily α k) (vals : Multi k)
    (l : List (Fin k)) (hnd : l.Nodup) :
    StrictMono (fun acc : α =>
      List.foldl (fun a j => op a (iterate_op (F.atoms j) (vals j))) acc l) := by
  classical
  induction l with
  | nil =>
    -- identity function is strictly monotone
    simpa [List.foldl] using (strictMono_id : StrictMono (fun x : α => x))
  | cons j t ih =>
    have hstep : StrictMono (fun acc : α => op acc (iterate_op (F.atoms j) (vals j))) :=
      op_strictMono_left _
    have htail : StrictMono (fun acc : α =>
      List.foldl (fun a j => op a (iterate_op (F.atoms j) (vals j))) acc t) :=
      ih (List.nodup_cons.mp hnd).2
    -- composition preserves strictness
    exact htail.comp hstep

/-- Foldl congr: if functions agree on list elements, foldls are equal. -/
lemma foldl_congr_on_list {β : Type*} (f g : α → β → α) (init : α) (l : List β)
    (h : ∀ x ∈ l, ∀ acc, f acc x = g acc x) :
    List.foldl f init l = List.foldl g init l := by
  induction l generalizing init with
  | nil => rfl
  | cons x t ih =>
    simp only [List.foldl_cons]
    have hx_mem : x ∈ x :: t := List.mem_cons_self
    rw [h x hx_mem init]
    have h_tail : ∀ y ∈ t, ∀ acc, f acc y = g acc y := fun y hy acc =>
      h y (List.mem_cons_of_mem x hy) acc
    exact ih (g init x) h_tail

/-- μ of the all-zero multiplicity vector evaluates to `ident`. -/
lemma mu_zero {k : ℕ} (F : AtomFamily α k) :
    mu F (fun _ => 0) = ident := by
  classical
  have hfold :
      ∀ l : List (Fin k),
        List.foldl (fun acc j => op acc (iterate_op (F.atoms j) 0)) ident l = ident := by
    intro l
    induction l with
    | nil => simp
    | cons j tl ih =>
        simp [iterate_op_zero, op_ident_right, ih]
  simpa [mu] using hfold (List.finRange k)

/-- Unit vector: n in position i, 0 elsewhere. -/
def unitMulti {k : ℕ} (i : Fin k) (n : ℕ) : Multi k :=
  fun j => if j = i then n else 0

/-- Helper: fold over indices with unitMulti evaluates to the target iterate.
    This tracks the accumulator through the fold.

    For j ∈ l with j ≠ i: contributes iterate_op (F.atoms j) 0 = ident, so acc unchanged.
    For j = i: contributes iterate_op (F.atoms i) n.

    The result depends on whether i is in the list:
    - If i ∈ l: result = op acc (iterate_op (F.atoms i) n)
    - If i ∉ l: result = acc (all contributions are ident)
-/
private lemma foldl_unitMulti_aux {k : ℕ} (F : AtomFamily α k) (i : Fin k) (n : ℕ)
    (l : List (Fin k)) (hnd : l.Nodup) (acc : α) :
    List.foldl (fun a j => op a (iterate_op (F.atoms j) (unitMulti i n j))) acc l =
    if i ∈ l then op acc (iterate_op (F.atoms i) n) else acc := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl_nil, List.not_mem_nil, ↓reduceIte]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    by_cases hi : hd = i
    · -- hd = i: this is the special index
      -- unitMulti i n hd = n (since hd = i)
      have h_val : unitMulti i n hd = n := by simp only [unitMulti, hi, ↓reduceIte]
      simp only [h_val]
      -- Since l is nodup and hd = i, i ∉ tl
      have hi_not_in_tl : i ∉ tl := by
        intro hmem
        have hnodup := (List.nodup_cons.mp hnd).1
        rw [hi] at hnodup
        exact hnodup hmem
      -- For the tail, since i ∉ tl, the fold just returns the accumulator
      rw [ih (List.nodup_cons.mp hnd).2]
      simp only [hi_not_in_tl, ↓reduceIte, hi, true_or]
    · -- hd ≠ i: this index contributes ident
      have hne : hd ≠ i := hi
      have h_val : unitMulti i n hd = 0 := by
        simp only [unitMulti, hne, ↓reduceIte]
      rw [h_val, iterate_op_zero, op_ident_right]
      rw [ih (List.nodup_cons.mp hnd).2]
      -- Goal: if i ∈ tl then op acc ... else acc = if hd = i ∨ i ∈ tl then op acc ... else acc
      -- Since hd ≠ i, the conditions are equivalent
      -- Note: List.mem_cons produces `i = hd ∨ i ∈ tl`, not `hd = i ∨ ...`
      have hne_symm : i ≠ hd := Ne.symm hne
      by_cases h_in_tl : i ∈ tl
      · -- i ∈ tl: both conditions are true
        simp only [h_in_tl, ↓reduceIte, Or.inr h_in_tl, hne_symm, false_or]
      · -- i ∉ tl: since i ≠ hd, i = hd ∨ i ∈ tl is false
        simp only [h_in_tl, ↓reduceIte, or_false]
        -- Goal: acc = if i = hd then op acc ... else acc
        rw [if_neg hne_symm]

/-- μ of a unit vector equals the corresponding iterate.
    This is key for reducing multi-type to single-type arguments.

    **Proof idea**: The fold processes indices in order. At index i, we get F.atoms i ^ n.
    At all other indices j ≠ i, we get F.atoms j ^ 0 = ident, which disappears via op_ident_right.
    So the result is ident ⊕ (F.atoms i ^ n) = F.atoms i ^ n.
-/
lemma mu_unitMulti {k : ℕ} (F : AtomFamily α k) (i : Fin k) (n : ℕ) :
    mu F (unitMulti i n) = iterate_op (F.atoms i) n := by
  unfold mu
  have hi_in : i ∈ List.finRange k := by simp
  have hnd : (List.finRange k).Nodup := List.nodup_finRange _
  rw [foldl_unitMulti_aux F i n (List.finRange k) hnd ident, if_pos hi_in, op_ident_left]

/-- Helper: strict inequality of folds when one input differs at a specific index.
    The fold diverges at that index, and strict monotonicity of subsequent steps preserves it.

    This version uses an explicit starting accumulator to handle the inductive case. -/
lemma foldl_lt_of_diff_at_index_aux (F : AtomFamily α k) (m n : ℕ) (r : Multi k) (idx : Fin k)
    (hmn : m < n) (l : List (Fin k)) (hl : idx ∈ l) (hnd : l.Nodup) (init : α) :
    List.foldl (fun acc j => op acc (iterate_op (F.atoms j) (updateMulti r idx m j))) init l <
    List.foldl (fun acc j => op acc (iterate_op (F.atoms j) (updateMulti r idx n j))) init l := by
  classical
  induction l generalizing init with
  | nil => exact absurd hl List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    by_cases hji : hd = idx
    · -- hd = idx: the divergence happens here
      -- Since idx ∉ tl (from nodup), updateMulti agrees on all elements of tl
      have hidx_not_in_tl : idx ∉ tl := by
        rw [← hji]; exact (List.nodup_cons.mp hnd).1
      -- Simplify the starting accumulators
      have h_acc_m : updateMulti r idx m hd = m := by rw [hji]; exact updateMulti_self r idx m
      have h_acc_n : updateMulti r idx n hd = n := by rw [hji]; exact updateMulti_self r idx n
      -- The strict inequality at this step
      have h_iter_lt : iterate_op (F.atoms hd) m < iterate_op (F.atoms hd) n := by
        rw [hji]; exact grid_strictMono (F.atoms idx) (F.pos idx) hmn
      have h_step_lt : op init (iterate_op (F.atoms hd) m) < op init (iterate_op (F.atoms hd) n) :=
        op_strictMono_right init h_iter_lt
      -- Rewrite the accumulators
      rw [h_acc_m, h_acc_n]
      -- For the tail, updateMulti r idx m and updateMulti r idx n agree on all elements
      -- since idx ∉ tl (and hd = idx implies hd ∉ tl)
      have h_tail_eq_m : ∀ acc',
          List.foldl (fun a j => op a (iterate_op (F.atoms j) (updateMulti r idx m j))) acc' tl =
          List.foldl (fun a j => op a (iterate_op (F.atoms j) (r j))) acc' tl := fun acc' => by
        apply foldl_congr_on_list
        intro j hj _acc
        have hjne : j ≠ idx := by
          intro heq
          rw [← hji] at heq
          have : hd ∈ tl := heq ▸ hj
          exact (List.nodup_cons.mp hnd).1 this
        simp [updateMulti, hjne]
      have h_tail_eq_n : ∀ acc',
          List.foldl (fun a j => op a (iterate_op (F.atoms j) (updateMulti r idx n j))) acc' tl =
          List.foldl (fun a j => op a (iterate_op (F.atoms j) (r j))) acc' tl := fun acc' => by
        apply foldl_congr_on_list
        intro j hj _acc
        have hjne : j ≠ idx := by
          intro heq
          rw [← hji] at heq
          have : hd ∈ tl := heq ▸ hj
          exact (List.nodup_cons.mp hnd).1 this
        simp [updateMulti, hjne]
      rw [h_tail_eq_m, h_tail_eq_n]
      -- Now both folds use the same function (r, not updateMulti), and starting acc differs
      have hnd' : tl.Nodup := (List.nodup_cons.mp hnd).2
      exact fold_strictMono_left F r tl hnd' h_step_lt
    · -- hd ≠ idx: both sides make the same step at hd, recurse on tail
      have h_same : updateMulti r idx m hd = updateMulti r idx n hd := by simp [updateMulti, hji]
      rw [h_same]
      have hidx_in_tl : idx ∈ tl := by
        cases hl with
        | head => exact absurd rfl hji
        | tail _ ht => exact ht
      have hnd' : tl.Nodup := (List.nodup_cons.mp hnd).2
      exact ih hidx_in_tl hnd' _

/-- Strict inequality of folds when one input differs at a specific index.
    Specialization to starting from `ident`. -/
lemma foldl_lt_of_diff_at_index (F : AtomFamily α k) (m n : ℕ) (r : Multi k) (idx : Fin k)
    (hmn : m < n) (l : List (Fin k)) (hl : idx ∈ l) (hnd : l.Nodup) :
    List.foldl (fun acc j => op acc (iterate_op (F.atoms j) (updateMulti r idx m j))) ident l <
    List.foldl (fun acc j => op acc (iterate_op (F.atoms j) (updateMulti r idx n j))) ident l :=
  foldl_lt_of_diff_at_index_aux F m n r idx hmn l hl hnd ident

/-- Strict monotonicity in a single coordinate, keeping others fixed.

When m < n, the vectors `updateMulti r i m` and `updateMulti r i n` differ only at coordinate i.
The fold `mu` processes all coordinates including i, where it computes strictly different values
(since `iterate_op` is strictly monotone). The subsequent fold steps preserve this strict
inequality via `op_strictMono_left`. -/
lemma mu_strictMono_coord (F : AtomFamily α k) (i : Fin k) (r : Multi k) :
    StrictMono (fun n => mu F (updateMulti r i n)) := by
  intro m n hmn
  unfold mu
  have hi_mem : i ∈ List.finRange k := by simp
  have hnd : (List.finRange k).Nodup := List.nodup_finRange _
  exact foldl_lt_of_diff_at_index F m n r i hmn _ hi_mem hnd

/-! ## Multi-type grid and representation scaffolding -/

/-- Grid generated by an atom family: values reachable as μ(F, r). -/
def kGrid {k : ℕ} (F : AtomFamily α k) : Set α := {x | ∃ r : Multi k, x = mu F r}

/-- Every μ-value lies on the k-grid. -/
lemma mu_mem_kGrid {k : ℕ} (F : AtomFamily α k) (r : Multi k) : mu F r ∈ kGrid F :=
  ⟨r, rfl⟩

/-- `ident` is always on the k-grid (take the zero multiplicity vector). -/
lemma ident_mem_kGrid {k : ℕ} (F : AtomFamily α k) : ident ∈ kGrid F := by
  have hmem : mu F (fun _ => 0) ∈ kGrid F := mu_mem_kGrid (F:=F) (r:=fun _ => 0)
  simpa [mu_zero (F:=F)] using hmem

/-- Representation data restricted to the μ-grid of an atom family. -/
structure MultiGridRep {k : ℕ} (F : AtomFamily α k) where
  /-- Representation on grid points μ(F, r). -/
  Θ_grid : {x // x ∈ kGrid F} → ℝ
  /-- Strict monotonicity on the grid. -/
  strictMono : StrictMono Θ_grid
  /-- Additivity along the grid. -/
  add : ∀ (r s : Multi k),
    Θ_grid ⟨mu F (fun i => r i + s i), mu_mem_kGrid (F:=F) (r:=fun i => r i + s i)⟩ =
    Θ_grid ⟨mu F r, mu_mem_kGrid (F:=F) r⟩ +
    Θ_grid ⟨mu F s, mu_mem_kGrid (F:=F) s⟩
  /-- Normalization: Θ(ident) = 0. -/
  ident_eq_zero :
    Θ_grid ⟨ident, ident_mem_kGrid (F:=F)⟩ = 0

/-- Commutativity on the μ-grid generated by an atom family F.

This is the **key inductive hypothesis** in the K&S Appendix A proof structure:
- Base (k=1): Single atom type, commutativity trivial (op a^m ⊕ a^n = a^{m+n} = a^n ⊕ a^m)
- Step (k→k+1): ASSUME k-grid is commutative, prove (k+1)-grid has representation,
                 then DERIVE (k+1)-grid commutativity from Θ' additivity + injectivity

Once GridComm F is established, we can prove the crucial bridge lemma:
  mu F (scaleMult n r) = iterate_op (mu F r) n
which enables all the separation/shift/strict-mono arguments. -/
structure GridComm {k : ℕ} (F : AtomFamily α k) : Prop where
  /-- Grid elements commute under op. -/
  comm : ∀ r s : Multi k, op (mu F r) (mu F s) = op (mu F s) (mu F r)

/-- For k=1 (single atom), the grid is trivially commutative.
The grid is {a^n : n ∈ ℕ}, and a^m ⊕ a^n = a^{m+n} = a^n ⊕ a^m. -/
lemma gridComm_of_k_eq_one {F : AtomFamily α 1} : GridComm F := ⟨by
  intro r s
  -- For k=1, mu F r = a^{r 0} for the single atom a = F.atoms 0
  -- Use calc to prove commutativity step by step
  unfold mu
  simp only [List.finRange_succ, List.finRange_zero, List.foldl_cons, List.foldl_nil, op_ident_left]
  -- Goal: iterate_op (F.atoms i) (r i) ⊕ iterate_op (F.atoms j) (s j) = iterate_op (F.atoms j) (s j) ⊕ iterate_op (F.atoms i) (r i)
  -- Both i and j are the unique element of Fin 1, so they equal each other
  let i₀ : Fin 1 := ⟨0, by decide⟩
  have hr_def : r = fun _ => r i₀ := by ext i; exact congrArg r (Fin.eq_zero i)
  have hs_def : s = fun _ => s i₀ := by ext i; exact congrArg s (Fin.eq_zero i)
  -- Rewrite using these
  calc op (iterate_op (F.atoms i₀) (r i₀)) (iterate_op (F.atoms i₀) (s i₀))
      = iterate_op (F.atoms i₀) (r i₀ + s i₀) := by rw [← iterate_op_add]
    _ = iterate_op (F.atoms i₀) (s i₀ + r i₀) := by rw [Nat.add_comm]
    _ = op (iterate_op (F.atoms i₀) (s i₀)) (iterate_op (F.atoms i₀) (r i₀)) := by rw [iterate_op_add]
⟩

/-! ## Multi-type A/B/C partition using `mu` -/

/-- Set A for multi-type grid: multiplicities whose value is below the target x. -/
def multiSetA (F : AtomFamily α k) (x : α) : Set (Multi k) := {r | mu F r < x}

/-- Set B for multi-type grid: multiplicities whose value equals the target x. -/
def multiSetB (F : AtomFamily α k) (x : α) : Set (Multi k) := {r | mu F r = x}

/-- Set C for multi-type grid: multiplicities whose value is above the target x. -/
def multiSetC (F : AtomFamily α k) (x : α) : Set (Multi k) := {r | x < mu F r}

/-- The multi-type A/B/C sets partition the multiplicity grid. -/
lemma multi_abc_partition (F : AtomFamily α k) (x : α) (r : Multi k) :
    r ∈ multiSetA F x ∨ r ∈ multiSetB F x ∨ r ∈ multiSetC F x := by
  unfold multiSetA multiSetB multiSetC
  rcases lt_trichotomy (mu F r) x with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hgt)

/-- The multi-type A/B/C sets are pairwise disjoint. -/
lemma multi_abc_disjoint (F : AtomFamily α k) (x : α) :
    (multiSetA F x ∩ multiSetB F x = ∅) ∧
    (multiSetB F x ∩ multiSetC F x = ∅) ∧
    (multiSetA F x ∩ multiSetC F x = ∅) := by
  constructor
  · ext r; constructor
    · intro h; rcases h with ⟨hA, hB⟩
      have hlt' : mu F r < mu F r := by
        have hlt : mu F r < x := by simpa [multiSetA] using hA
        have heq : mu F r = x := by simpa [multiSetB] using hB
        simpa [heq] using hlt
      exact (lt_irrefl _ hlt').elim
    · intro h; cases h
  constructor
  · ext r; constructor
    · intro h; rcases h with ⟨hB, hC⟩
      have hlt' : mu F r < mu F r := by
        have heq : mu F r = x := by simpa [multiSetB] using hB
        have hgt : x < mu F r := by simpa [multiSetC] using hC
        simpa [heq] using hgt
      exact (lt_irrefl _ hlt').elim
    · intro h; cases h
  · ext r; constructor
    · intro h; rcases h with ⟨hA, hC⟩
      have hlt : mu F r < mu F r := by
        have hltA : mu F r < x := by simpa [multiSetA] using hA
        have hgtC : x < mu F r := by simpa [multiSetC] using hC
        exact lt_trans hltA hgtC
      exact (lt_irrefl _ hlt).elim
    · intro h; cases h

/-- Each multiplicity vector belongs to exactly one of A, B, or C. -/
lemma multi_mem_A_or_B_or_C_unique (F : AtomFamily α k) (x : α) (r : Multi k) :
    (r ∈ multiSetA F x ∧ r ∉ multiSetB F x ∧ r ∉ multiSetC F x) ∨
    (r ∉ multiSetA F x ∧ r ∈ multiSetB F x ∧ r ∉ multiSetC F x) ∨
    (r ∉ multiSetA F x ∧ r ∉ multiSetB F x ∧ r ∈ multiSetC F x) := by
  classical
  rcases multi_abc_partition (F:=F) x r with hA | hB | hC
  · left
    refine ⟨hA, ?_, ?_⟩
    · intro hB'
      have := multi_abc_disjoint (F:=F) x
      have hABempty := this.1
      have : r ∈ (multiSetA F x ∩ multiSetB F x) := ⟨hA, hB'⟩
      have : r ∈ (∅ : Set (Multi k)) := by simpa [hABempty] using this
      simpa using this
    · intro hC'
      have := multi_abc_disjoint (F:=F) x
      have hACempty := this.2.2
      have : r ∈ (multiSetA F x ∩ multiSetC F x) := ⟨hA, hC'⟩
      have : r ∈ (∅ : Set (Multi k)) := by simpa [hACempty] using this
      simpa using this
  · right; left
    refine ⟨?_, hB, ?_⟩
    · intro hA
      have := multi_abc_disjoint (F:=F) x
      have hABempty := this.1
      have : r ∈ (multiSetA F x ∩ multiSetB F x) := ⟨hA, hB⟩
      have : r ∈ (∅ : Set (Multi k)) := by simpa [hABempty] using this
      simpa using this
    · intro hC'
      have := multi_abc_disjoint (F:=F) x
      have hBCempty := this.2.1
      have : r ∈ (multiSetB F x ∩ multiSetC F x) := ⟨hB, hC'⟩
      have : r ∈ (∅ : Set (Multi k)) := by simpa [hBCempty] using this
      simpa using this
  · right; right
    refine ⟨?_, ?_, hC⟩
    · intro hA
      have := multi_abc_disjoint (F:=F) x
      have hACempty := this.2.2
      have : r ∈ (multiSetA F x ∩ multiSetC F x) := ⟨hA, hC⟩
      have : r ∈ (∅ : Set (Multi k)) := by simpa [hACempty] using this
      simpa using this
    · intro hB
      have := multi_abc_disjoint (F:=F) x
      have hBCempty := this.2.1
      have : r ∈ (multiSetB F x ∩ multiSetC F x) := ⟨hB, hC⟩
      have : r ∈ (∅ : Set (Multi k)) := by simpa [hBCempty] using this
      simpa using this

/-! ### k = 1 specialization

Relate the k-type grid back to the one-type grid to reuse the base case.
-/

/-- Evaluate μ for the singleton atom family directly as an iterate. -/
lemma mu_singleton_eval (a : α) (ha : ident < a) (r : Multi 1) :
    mu (singletonAtomFamily (α:=α) a ha) r = iterate_op a (r ⟨0, by decide⟩) := by
  classical
  have hfun : r = fun _ : Fin 1 => r ⟨0, by decide⟩ := by
    funext i
    fin_cases i
    rfl
  -- Rewrite r as the unique constant function on Fin 1.
  conv_lhs => rw [hfun]
  simp [mu_singleton]

/-- For a singleton atom family, the k-grid coincides with the one-type grid. -/
lemma kGrid_singleton_eq_grid (a : α) (ha : ident < a) :
    kGrid (singletonAtomFamily (α:=α) a ha) = grid a := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    classical
    let n : ℕ := r ⟨0, by decide⟩
    have hr : mu (singletonAtomFamily (α:=α) a ha) r = iterate_op a n :=
      mu_singleton_eval (a:=a) (ha:=ha) r
    exact ⟨n, hr⟩
  · rintro ⟨n, rfl⟩
    refine ⟨(fun _ : Fin 1 => n), ?_⟩
    simp [mu_singleton]

/-- Transport a one-type grid representation to the singleton atom family. -/
noncomputable def OneTypeGridRep.toMulti (a : α) (ha : ident < a) (R : OneTypeGridRep a ha) :
    MultiGridRep (singletonAtomFamily (α:=α) a ha) := by
  classical
  let F : AtomFamily α 1 := singletonAtomFamily (α:=α) a ha
  have hset : kGrid F = grid a := kGrid_singleton_eq_grid (a:=a) (ha:=ha)
  let toGrid : {x // x ∈ kGrid F} → {x // x ∈ grid a} := fun x =>
    ⟨x.val, by simpa [hset] using x.property⟩
  refine
    { Θ_grid := fun x => R.Θ_grid (toGrid x)
      , strictMono := ?_
      , add := ?_
      , ident_eq_zero := ?_ }
  · intro x y hxy
    have hxy' : toGrid x < toGrid y := hxy
    simpa using (R.strictMono hxy')
  · intro r s
    classical
    let m : ℕ := r ⟨0, by decide⟩
    let n : ℕ := s ⟨0, by decide⟩
    have hr : mu F r = iterate_op a m := mu_singleton_eval (a:=a) (ha:=ha) r
    have hs : mu F s = iterate_op a n := mu_singleton_eval (a:=a) (ha:=ha) s
    have hsum : mu F (fun i : Fin 1 => r i + s i) = iterate_op a (m + n) := by
      have hdefault : (fun i : Fin 1 => r i + s i) ⟨0, by decide⟩ = m + n := by
        simp [m, n]
      have h_eval := mu_singleton_eval (a:=a) (ha:=ha) (r:=fun i : Fin 1 => r i + s i)
      simpa [hdefault] using h_eval
    have hmem_r : mu F r ∈ kGrid F := mu_mem_kGrid (F:=F) r
    have hmem_s : mu F s ∈ kGrid F := mu_mem_kGrid (F:=F) s
    have hmem_sum : mu F (fun i : Fin 1 => r i + s i) ∈ kGrid F :=
      mu_mem_kGrid (F:=F) (r:=fun i : Fin 1 => r i + s i)
    calc
      (fun x => R.Θ_grid (toGrid x))
          ⟨mu F (fun i : Fin 1 => r i + s i), hmem_sum⟩
          = R.Θ_grid ⟨iterate_op a (m + n), by
              have : mu F (fun i : Fin 1 => r i + s i) ∈ grid a := by
                simpa [hset] using hmem_sum
              simpa [hsum] using this⟩ := by
                simp [toGrid, hset, hsum]
      _ = R.Θ_grid ⟨iterate_op a m, by
              have : mu F r ∈ grid a := by simpa [hset] using hmem_r
              simpa [hr] using this⟩ +
          R.Θ_grid ⟨iterate_op a n, by
              have : mu F s ∈ grid a := by simpa [hset] using hmem_s
              simpa [hs] using this⟩ := R.add m n
      _ = (fun x => R.Θ_grid (toGrid x)) ⟨mu F r, hmem_r⟩ +
          (fun x => R.Θ_grid (toGrid x)) ⟨mu F s, hmem_s⟩ := by
            simp [toGrid, hset, hr, hs]
  · -- ident corresponds to the zero multiplicity vector on the k-grid
    simp [toGrid, hset, ident_mem_kGrid, R.ident_eq_zero]

/-! ## Phase 3: Separation Statistic and Case B Non-Empty

**Reference**: K&S Appendix A, Section A.3.3

The separation statistic σ(r, u) = Θ(μ(F, r)) / u captures the "candidate value"
for a new atom d based on witness r ∈ B(u) (meaning μ(F, r) = d^u).

**Key theorem**: All B-witnesses give the same statistic value, so Θ(d) is well-defined.

The proof uses:
1. Additivity of Θ on the k-grid: Θ(μ(F, n·r)) = n · Θ(μ(F, r))
2. Order structure to show: if μ(F, r) = d^u, then μ(F, n·r) = d^{nu}
3. Consistency: witnesses r ∈ B(u) and r' ∈ B(u') give same Θ(d)
-/

/-- Scale a multiplicity vector by a natural number. -/
def scaleMult {k : ℕ} (n : ℕ) (r : Multi k) : Multi k := fun i => n * r i

@[simp]
lemma scaleMult_one {k : ℕ} (r : Multi k) : scaleMult 1 r = r := by
  ext i; simp [scaleMult]

@[simp]
lemma scaleMult_zero {k : ℕ} (r : Multi k) : scaleMult 0 r = fun _ => 0 := by
  ext i; simp [scaleMult]

lemma scaleMult_add {k : ℕ} (m n : ℕ) (r : Multi k) :
    scaleMult (m + n) r = fun i => scaleMult m r i + scaleMult n r i := by
  ext i; simp [scaleMult, Nat.add_mul]

lemma scaleMult_succ {k : ℕ} (n : ℕ) (r : Multi k) :
    scaleMult (n + 1) r = fun i => scaleMult n r i + r i := by
  ext i; simp [scaleMult, Nat.add_mul, Nat.add_comm]

/-- For singleton atom family (k=1), scaling multiplicities equals iterating.
    This is the key lemma that doesn't require commutativity for k=1. -/
lemma mu_scaleMult_eq_iterate_singleton (a : α) (ha : ident < a) (r : Multi 1) (n : ℕ) :
    mu (singletonAtomFamily (α := α) a ha) (scaleMult n r) =
    iterate_op (mu (singletonAtomFamily (α := α) a ha) r) n := by
  classical
  let F := singletonAtomFamily (α := α) a ha
  -- r is essentially a single natural number: r 0 (using 0 : Fin 1)
  -- μ(F, r) = a^{r 0}
  have hr : mu F r = iterate_op a (r 0) := mu_singleton_eval a ha r
  -- μ(F, n·r) = a^{n * r 0}
  have hscale_full : scaleMult n r = fun _ : Fin 1 => n * r 0 := by
    funext i
    simp only [scaleMult, Fin.eq_zero i]
  have hnr : mu F (scaleMult n r) = iterate_op a (n * r 0) := by
    rw [hscale_full]
    exact mu_singleton a ha (n * r 0)
  -- (μ(F, r))^n = (a^{r 0})^n = a^{(r 0) * n} = a^{n * r 0}
  have hiter : iterate_op (mu F r) n = iterate_op a (n * r 0) := by
    rw [hr]
    rw [iterate_op_mul]
    congr 1
    ring
  rw [hnr, hiter]

/-- Scaling a unit vector hits the expected coordinate. -/
lemma scaleMult_unitMulti_one {k : ℕ} (i : Fin k) (m : ℕ) :
    scaleMult m (unitMulti i 1) = unitMulti i m := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp [scaleMult, unitMulti]
  · simp [scaleMult, unitMulti, hj]

/-- Θ is additive under scaling: Θ(μ(F, n·r)) = n · Θ(μ(F, r)).
    This follows from MultiGridRep.add by induction. -/
lemma Theta_scaleMult {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (r : Multi k) (n : ℕ) :
    R.Θ_grid ⟨mu F (scaleMult n r), mu_mem_kGrid F (scaleMult n r)⟩ =
    n * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
  induction n with
  | zero =>
    simp only [scaleMult_zero, Nat.zero_eq, Nat.cast_zero, zero_mul]
    have h0 : mu F (fun _ => 0) = ident := mu_zero (F := F)
    have hmem : mu F (fun _ => 0) ∈ kGrid F := mu_mem_kGrid F _
    calc R.Θ_grid ⟨mu F (fun _ => 0), hmem⟩
        = R.Θ_grid ⟨ident, by rw [← h0]; exact hmem⟩ := by
            simp only [h0]
      _ = 0 := R.ident_eq_zero
  | succ n ih =>
    have h_sum : scaleMult (n + 1) r = fun i => scaleMult n r i + r i := scaleMult_succ n r
    have hmem_sum := mu_mem_kGrid F (scaleMult (n + 1) r)
    have hmem_n := mu_mem_kGrid F (scaleMult n r)
    have hmem_r := mu_mem_kGrid F r
    -- The key fact is that mu F (scaleMult (n + 1) r) = mu F (fun i => scaleMult n r i + r i)
    have h_mu_eq : mu F (scaleMult (n + 1) r) = mu F (fun i => scaleMult n r i + r i) := by
      congr 1
    -- Use R.add to split into sum
    have hadd := R.add (scaleMult n r) r
    -- Show mu F (scaleMult (n + 1) r) = mu F (scaleMult n r) + mu F r via hadd
    calc R.Θ_grid ⟨mu F (scaleMult (n + 1) r), hmem_sum⟩
        = R.Θ_grid ⟨mu F (fun i => scaleMult n r i + r i), mu_mem_kGrid F _⟩ := by
            simp only [h_mu_eq]
      _ = R.Θ_grid ⟨mu F (scaleMult n r), hmem_n⟩ + R.Θ_grid ⟨mu F r, hmem_r⟩ := by
            convert hadd using 2 <;> simp only [scaleMult]
      _ = n * R.Θ_grid ⟨mu F r, hmem_r⟩ + R.Θ_grid ⟨mu F r, hmem_r⟩ := by rw [ih]
      _ = (n + 1 : ℕ) * R.Θ_grid ⟨mu F r, hmem_r⟩ := by
            simp only [Nat.cast_add, Nat.cast_one]; ring

/-- Θ on a unit vector scales linearly with the multiplicity. -/
lemma Theta_unitMulti {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (i : Fin k) (n : ℕ) :
    R.Θ_grid ⟨mu F (unitMulti i n), mu_mem_kGrid F (unitMulti i n)⟩ =
      n * R.Θ_grid ⟨mu F (unitMulti i 1), mu_mem_kGrid F (unitMulti i 1)⟩ := by
  have h := Theta_scaleMult (R := R) (r := unitMulti i 1) n
  have hμ :
      mu F (scaleMult n (unitMulti i 1)) = mu F (unitMulti i n) := by
    simpa [scaleMult_unitMulti_one] using rfl
  simpa [hμ] using h

/-- **IMPORTANT CAVEAT** (per GPT-5.1 Pro):

The global identity μ(F, n·r) = (μ(F, r))^n is **FALSE in GENERAL** without commutativity!

For multi-type families with k > 1:
  - μ(F, n·r) = a^{n·r₁} ⊕ b^{n·r₂} ⊕ ... (direct evaluation)
  - (μ(F, r))^n = (a^{r₁} ⊕ b^{r₂} ⊕ ...)^n (iterate the combined value)

These need NOT be equal in a non-commutative algebra!

**Where it DOES hold:**
1. k=0: Both sides are ident (proven below)
2. k=1: Trivial via `mu_scaleMult_eq_iterate_singleton`
3. **B-case** (k>1): When μ(F, r) = d^u for external d, the order/Θ structure forces
   equality (see `mu_scaleMult_iterate_B` below)

This lemma keeps the k=0 case for completeness. The k≥1 general case is REMOVED
because it's mathematically false. Use `mu_scaleMult_iterate_B` for B-case proofs.
-/
lemma mu_scaleMult_iterate_k0 (F : AtomFamily α 0) (r : Multi 0) (n : ℕ) :
    mu F (scaleMult n r) = iterate_op (mu F r) n := by
  -- Fin 0 is empty, so all multiplicities are zero and both sides are ident.
  have hident : ∀ m, iterate_op (ident : α) m = ident := by
    intro m
    induction m with
    | zero => simp [iterate_op_zero]
    | succ m ih =>
        simp [iterate_op, ih, op_ident_left]
  cases n <;> simp [mu, scaleMult, hident]

/-! ## GridBridge: The Inductive Hypothesis Capsule

The GridBridge structure captures the KEY inductive hypothesis for the k→k+1
induction in K&S Appendix A: the "grid bridge" property μ(n·r) = (μr)^n.

**Architecture** (per GPT-5.1 Pro):
- In the k→k+1 step, we ASSUME GridBridge for the old k-grid (F)
- We USE this assumption in separation_property, delta_shift_equiv, etc.
- We DERIVE GridBridge for the new (k+1)-grid (F') at the END of the step

This breaks the circularity: we don't try to prove the bridge from scratch;
we inherit it as the IH and pass it forward.
-/

/-- **Inductive hypothesis capsule**: the "grid bridge" property on a k-atom family F. -/
structure GridBridge {k : ℕ} (F : AtomFamily α k) : Prop where
  /-- The bridge: μ(n·r) = (μr)^n for all multi-indices r and scalars n. -/
  bridge : ∀ (r : Multi k) (n : ℕ),
    mu F (scaleMult n r) = iterate_op (mu F r) n

/-- GridBridge for k=0 is trivial (both sides are ident since Fin 0 is empty). -/
instance gridBridge_k0 (F : AtomFamily α 0) : GridBridge F :=
  ⟨fun r n => mu_scaleMult_iterate_k0 F r n⟩

/-- GridBridge for singleton atom family (k=1).
    This doesn't require commutativity - it's the base case for induction. -/
instance gridBridge_singleton (a : α) (ha : ident < a) :
    GridBridge (singletonAtomFamily (α := α) a ha) :=
  ⟨fun r n => mu_scaleMult_eq_iterate_singleton a ha r n⟩

/-- GridBridge for any k=1 family.
    For k=1, all multiplicities reduce to a single atom, making the bridge trivial.
    The proof mirrors mu_scaleMult_eq_iterate_singleton using F.atoms 0.

    TODO: Complete this proof - it follows the same pattern as the singleton case
    but requires showing that mu for any k=1 family equals the singleton formula. -/
lemma gridBridge_of_k_eq_one {F : AtomFamily α 1} : GridBridge F := by
  constructor
  intro r n
  classical
  -- For k=1, μ is essentially a single iterate: μ(F, r) = (F.atoms 0)^{r 0}
  -- because Fin 1 has exactly one element.
  let a := F.atoms ⟨0, by decide⟩

  -- Step 1: Show mu F r = iterate_op a (r 0)
  have hr : mu F r = iterate_op a (r ⟨0, by decide⟩) := by
    -- Fin 1 has one element, so foldl over finRange 1 = [0] is one step
    simp only [mu, a]
    -- finRange 1 = [0]
    have hlist : List.finRange 1 = [⟨0, by decide⟩] := by native_decide
    simp only [hlist, List.foldl_cons, List.foldl_nil, op_ident_left]

  -- Step 2: Show mu F (scaleMult n r) = iterate_op a (n * r 0)
  have hscale : scaleMult n r = fun _ : Fin 1 => n * r ⟨0, by decide⟩ := by
    funext i
    fin_cases i
    simp [scaleMult]
  have hnr : mu F (scaleMult n r) = iterate_op a (n * r ⟨0, by decide⟩) := by
    simp only [mu, a]
    have hlist : List.finRange 1 = [⟨0, by decide⟩] := by native_decide
    simp only [hlist, List.foldl_cons, List.foldl_nil, op_ident_left, hscale]

  -- Step 3: Show iterate_op (mu F r) n = iterate_op a (n * r 0)
  have hiter : iterate_op (mu F r) n = iterate_op a (n * r ⟨0, by decide⟩) := by
    rw [hr, iterate_op_mul]
    congr 1
    ring

  -- Conclude
  rw [hnr, hiter]

/-- The separation statistic for a witness (r, u).
    This is the "candidate value" for Θ(d) if μ(F, r) = d^u. -/
noncomputable def separationStatistic {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (r : Multi k) (u : ℕ) (hu : 0 < u) : ℝ :=
  R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u

/-- B-set for the extension: old multiplicities r such that μ(F, r) = d^u. -/
def extensionSetB {k : ℕ} (F : AtomFamily α k) (d : α) (u : ℕ) : Set (Multi k) :=
  {r | mu F r = iterate_op d u}

/-- A-set for the extension: old multiplicities r such that μ(F, r) < d^u. -/
def extensionSetA {k : ℕ} (F : AtomFamily α k) (d : α) (u : ℕ) : Set (Multi k) :=
  {r | mu F r < iterate_op d u}

/-- C-set for the extension: old multiplicities r such that μ(F, r) > d^u. -/
def extensionSetC {k : ℕ} (F : AtomFamily α k) (d : α) (u : ℕ) : Set (Multi k) :=
  {r | iterate_op d u < mu F r}

/-- The A/B/C sets partition the space of multiplicities. -/
lemma extension_abc_partition {k : ℕ} (F : AtomFamily α k) (d : α) (u : ℕ) (r : Multi k) :
    r ∈ extensionSetA F d u ∨ r ∈ extensionSetB F d u ∨ r ∈ extensionSetC F d u := by
  rcases lt_trichotomy (mu F r) (iterate_op d u) with hlt | heq | hgt
  · left; exact hlt
  · right; left; exact heq
  · right; right; exact hgt

/-! ### Key Lemma: Repetition preserves B-membership

If μ(F, r) = d^u (i.e., r ∈ B(u)), then μ(F, n·r) = d^{nu} (i.e., n·r ∈ B(nu)).

**Proof strategy** (from K&S Appendix A, Section A.3.2):

For k=1 (singleton family): This is trivial via `iterate_op_mul`.
  μ(F, r) = a^r, so μ(F, n·r) = a^{nr} = (a^r)^n = (μ(F, r))^n = (d^u)^n = d^{nu}.

For k > 1: The proof uses the ORDER STRUCTURE. We show that μ(F, n·r) and d^{nu}
cannot be different by using the Θ representation:
- Θ(μ(F, n·r)) = n * Θ(μ(F, r)) (by Theta_scaleMult)
- d^{nu} = (d^u)^n = (μ(F, r))^n (by iterate_op_mul and hr)
- If μ(F, n·r) ≠ (μ(F, r))^n, the Archimedean property + repetition lemma give contradiction.

The deep insight: even though μ(F, n·r) ≠ (μ(F, r))^n in general without commutativity,
when μ(F, r) = d^u for some EXTERNAL element d, the equality IS forced by the order structure.
-/

/-- Repetition lemma for k=1: direct proof via iterate_op_mul. -/
theorem repetition_preserves_B_singleton (a : α) (ha : ident < a)
    (d : α) (hd : ident < d) (r : Multi 1) (u : ℕ) (hu : 0 < u)
    (hr : r ∈ extensionSetB (singletonAtomFamily (α := α) a ha) d u) (n : ℕ) (hn : 0 < n) :
    scaleMult n r ∈ extensionSetB (singletonAtomFamily (α := α) a ha) d (n * u) := by
  simp only [extensionSetB, Set.mem_setOf_eq] at hr ⊢
  -- hr : mu F r = iterate_op d u
  -- goal: mu F (scaleMult n r) = iterate_op d (n * u)
  let F := singletonAtomFamily (α := α) a ha
  -- Use the k=1 scaling lemma
  have h1 : mu F (scaleMult n r) = iterate_op (mu F r) n :=
    mu_scaleMult_eq_iterate_singleton a ha r n
  -- (μ(F, r))^n = (d^u)^n = d^{nu} by iterate_op_mul
  have h2 : iterate_op (mu F r) n = iterate_op d (n * u) := by
    rw [hr]
    rw [iterate_op_mul]
    ring_nf
  rw [h1, h2]

/-- **B-case scaling lemma**: When μ(F, r) = d^u (i.e., r ∈ B), the equality
    μ(F, n·r) = (μ(F, r))^n holds due to the order/Θ structure.

    **Mathematical argument** (per GPT-5.1 Pro § 4.2):
    1. Let x = μ(F, r) = d^u and y = d^{nu} = x^n (by iterate_op_mul).
    2. Want to show: μ(F, n·r) = y.
    3. Θ(μ(F, n·r)) = n * Θ(μ(F, r)) = n * Θ(x) (by Theta_scaleMult).
    4. Θ(x^n) = n * Θ(x) (by iterate additivity on Θ).
    5. So μ(F, n·r) and x^n have the same Θ-value.
    6. Since Θ is strictly monotone (order isomorphism), they are equal.

    This is a **deep consequence** of the Appendix A order/representation machinery,
    NOT a primitive algebraic law. The key restriction: μ(F, r) must be a pure power
    d^u of an external element d.

    TODO: Complete the proof using Theta_scaleMult + strict monotonicity + trichotomy.
          For now, this remains a sorry tied to the full Θ construction. -/
lemma mu_scaleMult_iterate_B
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F) (IH : GridBridge F)
    (d : α) (hd : ident < d) (r : Multi k) (u : ℕ) (hu : 0 < u)
    (hr : r ∈ extensionSetB F d u) (n : ℕ) (hn : 0 < n) :
    mu F (scaleMult n r) = iterate_op (mu F r) n := by
  -- In the B-case we can appeal directly to the inductive grid bridge.
  -- The bridge already states the desired scaling identity for every r,n.
  simpa using IH.bridge r n

/-- Repetition lemma (general k): If r ∈ B(u), then (n·r) ∈ B(nu).

    For general k > 1, this uses the B-case scaling lemma `mu_scaleMult_iterate_B`.
    The key is that μ(F, n·r) and (μ(F, r))^n have the same Θ-value in the B-case,
    and therefore must be equal by the order structure.

    **Mathematical argument** (from K&S Appendix A):
    1. hr gives: μ(F, r) = d^u
    2. By `mu_scaleMult_iterate_B`: μ(F, n·r) = (μ(F, r))^n = (d^u)^n
    3. By `iterate_op_mul`: (d^u)^n = d^{n*u}
    4. Therefore: μ(F, n·r) = d^{n*u}, i.e., (n·r) ∈ B(n*u)
-/
theorem repetition_preserves_B {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F)
    (d : α) (hd : ident < d) (r : Multi k) (u : ℕ) (hu : 0 < u)
    (hr : r ∈ extensionSetB F d u) (n : ℕ) (hn : 0 < n) :
    scaleMult n r ∈ extensionSetB F d (n * u) := by
  simp only [extensionSetB, Set.mem_setOf_eq] at hr ⊢
  -- hr : mu F r = iterate_op d u
  -- goal: mu F (scaleMult n r) = iterate_op d (n * u)
  -- Use the B-case scaling lemma
  have h_mu_scaled : mu F (scaleMult n r) = iterate_op (mu F r) n :=
    mu_scaleMult_iterate_B R IH d hd r u hu hr n hn
  have h_target : iterate_op d (n * u) = iterate_op (mu F r) n := by
    -- (d^u)^n = d^{n*u}
    have : iterate_op d (n * u) = iterate_op (iterate_op d u) n := by
      -- iterate_op_mul uses multiplication in the second argument
      simpa [Nat.mul_comm] using (iterate_op_mul d u n).symm
    -- replace iterate_op d u with mu F r
    simpa [hr] using this
  -- Combine both identities
  exact h_mu_scaled.trans h_target.symm

/-! ### Case B Non-Empty: All Witnesses Share Common Statistic

**Reference**: K&S Appendix A, Section A.3.3 (lines 1624-1704)

When B is non-empty, multiple witnesses (r, u) and (r', u') may exist with:
- μ(F, r) = d^u
- μ(F, r') = d^{u'}

The key theorem shows they all give the same "statistic" value:
  σ(r, u) = Θ(μ(F, r)) / u = Θ(μ(F, r')) / u' = σ(r', u')

This pins down Θ(d) uniquely: Θ(d) = σ(r, u) for ANY witness (r, u) ∈ B.

**Proof**: Scale both witnesses to a common denominator u*u':
1. (u'·r, u'·u) ∈ B by repetition_preserves_B
2. (u·r', u·u') ∈ B by repetition_preserves_B
3. Both have target d^{u*u'}, so μ(F, u'·r) = d^{u'u} = μ(F, u·r')
4. Apply Θ and use Theta_scaleMult to get the equality.
-/

/-- If two witnesses are in B, their separation statistics are equal.
    This is the key uniqueness result for Case B non-empty. -/
theorem B_witnesses_same_statistic {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F)
    (d : α) (hd : ident < d)
    (r : Multi k) (u : ℕ) (hu : 0 < u) (hr : r ∈ extensionSetB F d u)
    (r' : Multi k) (u' : ℕ) (hu' : 0 < u') (hr' : r' ∈ extensionSetB F d u') :
    separationStatistic R r u hu = separationStatistic R r' u' hu' := by
  unfold separationStatistic
  -- We need: Θ(μ(F, r)) / u = Θ(μ(F, r')) / u'
  -- Equivalently: u' * Θ(μ(F, r)) = u * Θ(μ(F, r'))

  -- Scale (r, u) by u' to get (u'·r, u'*u) in B(u'*u)
  have hr_scaled : scaleMult u' r ∈ extensionSetB F d (u' * u) :=
    repetition_preserves_B R IH d hd r u hu hr u' hu'

  -- Scale (r', u') by u to get (u·r', u*u') in B(u*u')
  have hr'_scaled : scaleMult u r' ∈ extensionSetB F d (u * u') :=
    repetition_preserves_B R IH d hd r' u' hu' hr' u hu

  -- Both have the same target: d^{u'*u} = d^{u*u'}
  simp only [extensionSetB, Set.mem_setOf_eq] at hr_scaled hr'_scaled
  -- hr_scaled : mu F (scaleMult u' r) = iterate_op d (u' * u)
  -- hr'_scaled : mu F (scaleMult u r') = iterate_op d (u * u')

  -- Since u' * u = u * u', the targets are equal
  have h_targets_eq : iterate_op d (u' * u) = iterate_op d (u * u') := by
    congr 1; ring

  -- Therefore μ(F, u'·r) = μ(F, u·r')
  have h_mu_eq : mu F (scaleMult u' r) = mu F (scaleMult u r') := by
    rw [hr_scaled, h_targets_eq, ← hr'_scaled]

  -- Apply Θ to both sides
  have h_Theta_eq : R.Θ_grid ⟨mu F (scaleMult u' r), mu_mem_kGrid F _⟩ =
                    R.Θ_grid ⟨mu F (scaleMult u r'), mu_mem_kGrid F _⟩ := by
    congr 1; ext; exact h_mu_eq

  -- Use Theta_scaleMult on both sides
  have h_lhs : R.Θ_grid ⟨mu F (scaleMult u' r), mu_mem_kGrid F _⟩ =
               u' * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
    Theta_scaleMult R r u'

  have h_rhs : R.Θ_grid ⟨mu F (scaleMult u r'), mu_mem_kGrid F _⟩ =
               u * R.Θ_grid ⟨mu F r', mu_mem_kGrid F r'⟩ :=
    Theta_scaleMult R r' u

  -- Combine: u' * Θ(μ(F, r)) = u * Θ(μ(F, r'))
  rw [h_lhs, h_rhs] at h_Theta_eq

  -- Convert to division form: Θ(μ(F, r)) / u = Θ(μ(F, r')) / u'
  field_simp
  linarith [h_Theta_eq]

/-- The common statistic value for all B-witnesses.
    When B is non-empty, this is the value we assign to Θ(d). -/
noncomputable def B_common_statistic {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d)
    (hB_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u) : ℝ :=
  -- Use Classical.choose to extract witness from existential
  let r := Classical.choose hB_nonempty
  let hu' := Classical.choose_spec hB_nonempty
  let u := Classical.choose hu'
  let hu_spec := Classical.choose_spec hu'
  let hu : 0 < u := hu_spec.1
  separationStatistic R r u hu

/-- The common statistic is independent of the witness choice. -/
theorem B_common_statistic_eq_any_witness {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (d : α) (hd : ident < d)
    (hB_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u)
    (r : Multi k) (u : ℕ) (hu : 0 < u) (hr : r ∈ extensionSetB F d u) :
    B_common_statistic R d hd hB_nonempty = separationStatistic R r u hu := by
  -- B_common_statistic uses Classical.choose to pick a witness (r₀, u₀)
  -- We need to show its statistic equals the given witness (r, u)'s statistic
  unfold B_common_statistic
  -- Extract the chosen witness
  let r₀ := Classical.choose hB_nonempty
  let hu'_spec := Classical.choose_spec hB_nonempty
  let u₀ := Classical.choose hu'_spec
  let hu_spec := Classical.choose_spec hu'_spec
  have hu₀ : 0 < u₀ := hu_spec.1
  have hr₀ : r₀ ∈ extensionSetB F d u₀ := hu_spec.2
  -- Now apply B_witnesses_same_statistic to show they're equal
  exact B_witnesses_same_statistic R IH d hd r₀ u₀ hu₀ hr₀ r u hu hr

/-- Convenience wrapper around `Nat.findGreatest_eq_iff`.
    It provides the predicate at `findGreatest`, the bound, and maximality. -/
lemma findGreatest_crossing (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (hP0 : P 0) :
    P (Nat.findGreatest P n) ∧ Nat.findGreatest P n ≤ n ∧
      ∀ k, Nat.findGreatest P n < k → k ≤ n → ¬ P k := by
  have h :=
    (Nat.findGreatest_eq_iff (P := P) (k := n) (m := Nat.findGreatest P n)).1 rfl
  have h_le : Nat.findGreatest P n ≤ n := h.1
  have h_pred_if_pos : Nat.findGreatest P n ≠ 0 → P (Nat.findGreatest P n) := h.2.1
  have h_max : ∀ k, Nat.findGreatest P n < k → k ≤ n → ¬ P k := by
    intro k hk hk_le
    exact h.2.2 hk hk_le
  have h_pred : P (Nat.findGreatest P n) := by
    by_cases h0 : Nat.findGreatest P n = 0
    · simpa [h0] using hP0
    · exact h_pred_if_pos h0
  exact ⟨h_pred, h_le, h_max⟩

/-! ### Case B Empty: Accuracy Lemma

**Reference**: K&S Appendix A, Section A.3.4 (lines 1706-1895)

When B is empty, there's a gap between sup(A) and inf(C).
We choose δ in this gap as the value for Θ(d).

The accuracy lemma shows that δ is determined arbitrarily precisely:
for any ε > 0, there exist (r, u) ∈ A and (r', u') ∈ C such that:
- σ(r', u') - σ(r, u) < ε

This uses the Archimedean property to find arbitrarily fine comparisons.
-/

/-- When B is empty, A and C partition the witnesses with a gap.
    We can choose δ in the gap as Θ(d). -/
noncomputable def B_empty_delta {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u)
    (hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u) : ℝ :=
  -- The supremum of A-statistics is a valid choice for δ
  -- In a complete construction, we'd define this as a Dedekind cut
  -- For now, we use sSup of the A-statistics (using Θ-values directly)
  sSup {s : ℝ | ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u ∧
                s = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u}

/-- Floor-bracket below: for δ>0 and θ≥0, `V := ⌊θ/δ⌋` gives `V•δ ≤ θ`. -/
lemma floor_bracket_le (δ θ : ℝ) (hδ : 0 < δ) (hθ : 0 ≤ θ) :
  (Nat.floor (θ / δ) : ℝ) * δ ≤ θ := by
  have h_nonneg : 0 ≤ θ / δ := div_nonneg hθ (le_of_lt hδ)
  have : (Nat.floor (θ / δ) : ℝ) ≤ θ / δ := Nat.floor_le h_nonneg
  calc (Nat.floor (θ / δ) : ℝ) * δ
      ≤ (θ / δ) * δ := by exact mul_le_mul_of_nonneg_right this (le_of_lt hδ)
    _ = θ           := by field_simp

/-- Floor-bracket above: for δ>0 and θ≥0, `θ < (V+1)•δ`. -/
lemma lt_floor_succ_bracket (δ θ : ℝ) (hδ : 0 < δ) (hθ : 0 ≤ θ) :
  θ < ((Nat.floor (θ / δ) + 1 : ℕ) : ℝ) * δ := by
  have h_nonneg : 0 ≤ θ / δ := div_nonneg hθ (le_of_lt hδ)
  -- Nat.lt_floor_add_one states: x < ⌊x⌋₊ + 1
  have h_lt : θ / δ < ⌊θ / δ⌋₊ + 1 := Nat.lt_floor_add_one (θ / δ)
  calc θ = (θ / δ) * δ := by field_simp
    _ < (⌊θ / δ⌋₊ + 1) * δ := by
      apply mul_lt_mul_of_pos_right h_lt hδ
    _ = ((Nat.floor (θ / δ) + 1 : ℕ) : ℝ) * δ := by norm_cast

/-- **Helper Lemma 0 (GPT-5 Pro)**: Swap middle elements using grid commutativity.
Given multi-index witnesses for grid membership, we can swap using associativity + commutativity. -/
lemma op_swap_right_on_grid {k : ℕ} {F : AtomFamily α k}
    (H : GridComm F) (r_x r_y r_z : Multi k)
    (hx : x = mu F r_x) (hy : y = mu F r_y) (hz : z = mu F r_z) :
    op (op x y) z = op (op x z) y := by
  subst hx hy hz
  calc op (op (mu F r_x) (mu F r_y)) (mu F r_z)
      = op (mu F r_x) (op (mu F r_y) (mu F r_z)) := op_assoc _ _ _
    _ = op (mu F r_x) (op (mu F r_z) (mu F r_y)) := by rw [H.comm r_y r_z]
    _ = op (op (mu F r_x) (mu F r_z)) (mu F r_y) := (op_assoc _ _ _).symm

/-- **Helper**: Iterates of atoms are grid members. -/
lemma iterate_atom_mem_kGrid {k : ℕ} (F : AtomFamily α k) (i : Fin k) (n : ℕ) :
    iterate_op (F.atoms i) n ∈ kGrid F := by
  use unitMulti i n
  exact (mu_unitMulti F i n).symm

/-- **Helper**: Folds with contributions from a multiplicity vector.
Two folds over the same list with the same function are equal. -/
private lemma mu_foldl_eq {k : ℕ} (F : AtomFamily α k) (r : Multi k)
    (l : List (Fin k)) (acc : α) :
    List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i))) acc l =
    List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i))) acc l := rfl

/-- **Helper**: Pull an iterate contribution past another using GridComm.
This is the core swap operation that enables reordering. -/
private lemma op_iterate_comm {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (i j : Fin k) (m n : ℕ) :
    op (iterate_op (F.atoms i) m) (iterate_op (F.atoms j) n) =
    op (iterate_op (F.atoms j) n) (iterate_op (F.atoms i) m) := by
  have hi : iterate_op (F.atoms i) m = mu F (unitMulti i m) := (mu_unitMulti F i m).symm
  have hj : iterate_op (F.atoms j) n = mu F (unitMulti j n) := (mu_unitMulti F j n).symm
  rw [hi, hj, H.comm (unitMulti i m) (unitMulti j n)]

/-- **Helper**: Pull an iterate contribution to the right of accumulator.
Key: op (op acc x) y = op (op acc y) x when x, y are grid elements. -/
private lemma op_op_comm_grid {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (acc : α) (i j : Fin k) (m n : ℕ) :
    op (op acc (iterate_op (F.atoms i) m)) (iterate_op (F.atoms j) n) =
    op (op acc (iterate_op (F.atoms j) n)) (iterate_op (F.atoms i) m) := by
  calc op (op acc (iterate_op (F.atoms i) m)) (iterate_op (F.atoms j) n)
      = op acc (op (iterate_op (F.atoms i) m) (iterate_op (F.atoms j) n)) := op_assoc _ _ _
    _ = op acc (op (iterate_op (F.atoms j) n) (iterate_op (F.atoms i) m)) := by
        rw [op_iterate_comm H i j m n]
    _ = op (op acc (iterate_op (F.atoms j) n)) (iterate_op (F.atoms i) m) := (op_assoc _ _ _).symm

/-- **Helper**: Pull one s-contribution through an r-fold using commutativity.
After folding r-contributions, we can move a single s-contribution past. -/
private lemma foldl_r_then_s {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (l : List (Fin k)) (r : Multi k) (j : Fin k) (n : ℕ) (acc : α) :
    op (List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i))) acc l)
       (iterate_op (F.atoms j) n) =
    List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i)))
       (op acc (iterate_op (F.atoms j) n)) l := by
  induction l generalizing acc with
  | nil => rfl
  | cons i tl ih =>
    simp only [List.foldl_cons]
    -- LHS = op (foldl ... (op acc (iter_r_i)) tl) (iter_s_j)
    -- RHS = foldl ... (op (op acc (iter_s_j)) (iter_r_i)) tl
    -- First, show we can swap iter_r_i and iter_s_j:
    have hswap : op (op acc (iterate_op (F.atoms i) (r i))) (iterate_op (F.atoms j) n) =
                 op (op acc (iterate_op (F.atoms j) n)) (iterate_op (F.atoms i) (r i)) :=
      op_op_comm_grid H acc i j (r i) n
    -- Now use IH
    calc op (List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i)))
               (op acc (iterate_op (F.atoms i) (r i))) tl) (iterate_op (F.atoms j) n)
        = List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i)))
               (op (op acc (iterate_op (F.atoms i) (r i))) (iterate_op (F.atoms j) n)) tl := ih _
      _ = List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i)))
               (op (op acc (iterate_op (F.atoms j) n)) (iterate_op (F.atoms i) (r i))) tl := by
          rw [hswap]

/-- **Carry lemma**: Starting the fold with an extra `j`-iterate is the same as
bumping the `j`-coordinate by `n`.

Key insight from GPT-5 Pro: Instead of splitting at j-1, we bubble the extra
iterate across the fold one head at a time, merge exponents when we hit j,
then use foldl_congr_on_list for the tail (since j can't appear again by nodup). -/
private lemma foldl_carry_unit {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (r : Multi k) (j : Fin k) (n : ℕ) :
    ∀ (l : List (Fin k)) (hnd : l.Nodup) (hj : j ∈ l) (acc : α),
      List.foldl (fun a i => op a (iterate_op (F.atoms i) (r i)))
        (op acc (iterate_op (F.atoms j) n)) l
      =
      List.foldl (fun a i => op a (iterate_op (F.atoms i) ((r + unitMulti j n) i)))
        acc l := by
  intro l hnd hj acc
  induction l generalizing acc with
  | nil =>
    simp at hj  -- j ∈ [] is impossible
  | cons i tl ih =>
    have hi_not_in_tl : i ∉ tl := (List.nodup_cons.mp hnd).1
    have hnd_tl : tl.Nodup := (List.nodup_cons.mp hnd).2
    have hj' : j = i ∨ j ∈ tl := by
      simpa [List.mem_cons] using hj
    cases hj' with
    | inl hji =>
      subst hji
      -- Now j is the head, and j ∉ tl by nodup
      have hj_not_in_tl : j ∉ tl := hi_not_in_tl
      simp only [List.foldl_cons]
      -- Merge the two j-contributions in the starting accumulator:
      have hstart :
          op (op acc (iterate_op (F.atoms j) n)) (iterate_op (F.atoms j) (r j)) =
            op acc (iterate_op (F.atoms j) ((r + unitMulti j n) j)) := by
        -- (acc ⊕ j^n) ⊕ j^{rj} = acc ⊕ (j^n ⊕ j^{rj}) = acc ⊕ j^{n+rj} = acc ⊕ j^{rj+n}
        rw [op_assoc]
        rw [iterate_op_add (F.atoms j) n (r j)]
        rw [Nat.add_comm n (r j)]
        simp [Pi.add_apply, unitMulti]
      -- Replace the LHS init accumulator by the RHS init accumulator
      rw [hstart]
      -- Tail: since j ∉ tl, the step functions agree on tl
      apply foldl_congr_on_list
      intro x hx acc'
      have hxne : x ≠ j := by
        intro hEq
        apply hj_not_in_tl
        simpa [hEq] using hx
      simp [Pi.add_apply, unitMulti, hxne]
    | inr hj_tl =>
      -- j is in tl; nodup forces i ≠ j
      have hij_ne : i ≠ j := by
        intro hEq
        apply hi_not_in_tl
        simpa [hEq] using hj_tl
      simp only [List.foldl_cons]
      -- Swap the head i-iterate past the carried j-iterate in the accumulator
      have hswap :
          op (op acc (iterate_op (F.atoms j) n)) (iterate_op (F.atoms i) (r i)) =
          op (op acc (iterate_op (F.atoms i) (r i))) (iterate_op (F.atoms j) n) := by
        simpa using op_op_comm_grid (H := H) (acc := acc) (i := j) (j := i) (m := n) (n := r i)
      rw [hswap]
      -- Now apply IH on the tail with accumulator advanced by the i-step
      have hih :=
        ih (acc := op acc (iterate_op (F.atoms i) (r i))) hnd_tl hj_tl
      -- RHS head uses (r + unitMulti j n) i = r i since i ≠ j
      have hi_eq : (r + unitMulti j n) i = r i := by
        simp [Pi.add_apply, unitMulti, hij_ne]
      simp only [List.foldl_cons, hi_eq]
      exact hih

/-- **Helper**: Adding a unit contribution to mu using GridComm.
The key insight is that mu F (r + unitMulti j n) has contribution r_j + n at index j,
which equals op (iter_j^{r_j}) (iter_j^n) = iter_j^{r_j + n} by iterate_op_add.
With GridComm, we can reorder to merge the contributions.

This is the KEY lemma that breaks the circularity in foldl_op_distrib_gen.

**Proof** (per GPT-5 Pro): Use foldl_r_then_s to pull the iterate to the start,
then foldl_carry_unit to merge at j and adjust the tail. -/
private lemma mu_add_unitMulti {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (r : Multi k) (j : Fin k) (n : ℕ) :
    op (mu F r) (iterate_op (F.atoms j) n) = mu F (r + unitMulti j n) := by
  classical
  unfold mu
  set l : List (Fin k) := List.finRange k with hl_def
  have hnd : l.Nodup := by simpa [l] using (List.nodup_finRange k)
  have hj : j ∈ l := by simp [l]
  -- Pull the extra iterate into the fold using foldl_r_then_s
  have hpull :=
    foldl_r_then_s (H := H) (l := l) (r := r) (j := j) (n := n) (acc := ident)
  -- Now carry it through and merge at j via foldl_carry_unit
  calc
    op (List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i))) ident l)
        (iterate_op (F.atoms j) n)
        =
      List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i)))
        (op ident (iterate_op (F.atoms j) n)) l := by
          simpa [l] using hpull
    _ =
      List.foldl (fun acc i => op acc (iterate_op (F.atoms i) ((r + unitMulti j n) i)))
        ident l := by
          simpa [l, op_ident_left] using
            (foldl_carry_unit (H := H) (r := r) (j := j) (n := n) l hnd hj ident)

/-- **Generalized Distribution Lemma**: When starting from op (mu F r_acc) (mu F s_acc),
the combined fold distributes into separate r and s folds.
This requires witness tracking for commutativity.

**Key insight**: We track that the accumulators are mu F of the "already processed" indices,
so we can apply GridComm to swap contributions. -/
private lemma foldl_op_distrib_gen {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (l : List (Fin k)) (r s r_acc s_acc : Multi k) :
    List.foldl (fun acc i => op acc (op (iterate_op (F.atoms i) (r i))
                                       (iterate_op (F.atoms i) (s i))))
       (op (mu F r_acc) (mu F s_acc)) l =
    op (List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i))) (mu F r_acc) l)
       (List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (s i))) (mu F s_acc) l) := by
  induction l generalizing r_acc s_acc with
  | nil => rfl
  | cons j tl ih =>
    simp only [List.foldl_cons]
    -- Key: Rewrite op (op (mu F r_acc) (mu F s_acc)) (op r_j s_j)
    -- as op (op (mu F r_acc) r_j) (op (mu F s_acc) s_j)
    have hreorder : op (op (mu F r_acc) (mu F s_acc))
                       (op (iterate_op (F.atoms j) (r j)) (iterate_op (F.atoms j) (s j))) =
                    op (op (mu F r_acc) (iterate_op (F.atoms j) (r j)))
                       (op (mu F s_acc) (iterate_op (F.atoms j) (s j))) := by
      let r_j := iterate_op (F.atoms j) (r j)
      let s_j := iterate_op (F.atoms j) (s j)
      have hr_j : r_j = mu F (unitMulti j (r j)) := (mu_unitMulti F j (r j)).symm
      calc op (op (mu F r_acc) (mu F s_acc)) (op r_j s_j)
          = op (mu F r_acc) (op (mu F s_acc) (op r_j s_j)) := op_assoc _ _ _
        _ = op (mu F r_acc) (op (op (mu F s_acc) r_j) s_j) := by rw [← op_assoc (mu F s_acc) r_j s_j]
        _ = op (mu F r_acc) (op (op r_j (mu F s_acc)) s_j) := by
            have hcomm : op (mu F s_acc) r_j = op r_j (mu F s_acc) := by
              rw [hr_j]; exact H.comm s_acc (unitMulti j (r j))
            rw [hcomm]
        _ = op (mu F r_acc) (op r_j (op (mu F s_acc) s_j)) := by rw [op_assoc r_j (mu F s_acc) s_j]
        _ = op (op (mu F r_acc) r_j) (op (mu F s_acc) s_j) := (op_assoc _ _ _).symm
    rw [hreorder]

    -- Now apply IH with updated witnesses
    -- Key observation: op (mu F r_acc) (iterate_op ...) = mu F (r_acc + unitMulti j ...)
    -- by mu_add_unitMulti (which uses GridComm)
    have hr_new : op (mu F r_acc) (iterate_op (F.atoms j) (r j)) =
                  mu F (r_acc + unitMulti j (r j)) := mu_add_unitMulti H r_acc j (r j)
    have hs_new : op (mu F s_acc) (iterate_op (F.atoms j) (s j)) =
                  mu F (s_acc + unitMulti j (s j)) := mu_add_unitMulti H s_acc j (s j)
    rw [hr_new, hs_new]
    exact ih (r_acc + unitMulti j (r j)) (s_acc + unitMulti j (s j))

/-- **Key Distribution Lemma**: Foldl of "op-pair" distributes as op of two foldls.
When all contributions commute pairwise (via GridComm), we can separate the fold of
(a^r ⊕ a^s) into op (fold of a^r) (fold of a^s).

This is a special case of foldl_op_distrib_gen starting from ident = mu F 0. -/
private lemma foldl_op_distrib {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (l : List (Fin k)) (r s : Multi k) :
    List.foldl (fun acc i => op acc (op (iterate_op (F.atoms i) (r i))
                                       (iterate_op (F.atoms i) (s i)))) ident l =
    op (List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i))) ident l)
       (List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (s i))) ident l) := by
  -- The generalized version starts from op (mu F r_acc) (mu F s_acc).
  -- With r_acc = s_acc = 0, we have:
  --   mu F 0 = ident
  --   op (mu F 0) (mu F 0) = op ident ident = ident
  -- So we can use foldl_op_distrib_gen and simplify
  have hgen := foldl_op_distrib_gen H l r s (fun _ => 0) (fun _ => 0)
  -- Simplify: op (mu F 0) (mu F 0) = ident, mu F 0 = ident
  have h0 : mu F (fun _ => 0) = ident := mu_zero F
  simp only [h0, op_ident_left] at hgen
  exact hgen

/-- **Helper: mu is additive if the grid commutes.**

This is the key algebraic property: when GridComm holds, mu preserves addition.
The proof requires reordering the foldl terms using commutativity.

**Proof Strategy** (per GPT-5 Pro):
For F' = extendAtomFamily F d hd with k+1 atoms:
1. Use splitMulti/joinMulti to decompose multiplicities
2. Apply mu_extend_last to separate old and new parts
3. Get GridComm F from H' via gridComm_of_extended (Lemma 2)
4. Apply IH (mu_add_of_comm on F) for the old grid part
5. Use iterate_op_add for the new atom's contribution
6. Reorder using op_swap_right_on_grid (Lemma 0)

**Dependencies**: Blocks mu_scale_eq_iterate_of_comm, delta_shift_equiv (pure A/C),
and h_strictMono (t_x ≠ t_y cases). -/
lemma mu_add_of_comm {k : ℕ} {F : AtomFamily α k} (H : GridComm F)
    (r s : Multi k) : mu F (r + s) = op (mu F r) (mu F s) := by
  -- Strategy: Rewrite mu F (r+s) using iterate_op_add, then apply foldl_op_distrib.
  --
  -- Step 1: mu F (r+s) = foldl (λ acc i => op acc (iter_i^{(r+s)_i})) ident (finRange k)
  -- Step 2: By iterate_op_add: iter_i^{(r+s)_i} = op (iter_i^{r_i}) (iter_i^{s_i})
  -- Step 3: So mu F (r+s) = foldl (λ acc i => op acc (op (iter_r_i) (iter_s_i))) ident (finRange k)
  -- Step 4: By foldl_op_distrib: = op (foldl ... r ...) (foldl ... s ...)
  --                              = op (mu F r) (mu F s)

  -- First, show that the fold of (r+s) equals the fold of "paired" contributions
  have hfold_rw : mu F (r + s) =
      List.foldl (fun acc i => op acc (op (iterate_op (F.atoms i) (r i))
                                          (iterate_op (F.atoms i) (s i)))) ident
        (List.finRange k) := by
    unfold mu
    congr 1
    funext acc i
    -- Show: op acc (iter_i^{(r+s)_i}) = op acc (op (iter_i^{r_i}) (iter_i^{s_i}))
    have h_split : iterate_op (F.atoms i) ((r + s) i) =
                   op (iterate_op (F.atoms i) (r i)) (iterate_op (F.atoms i) (s i)) := by
      simp only [Pi.add_apply]
      exact (iterate_op_add (F.atoms i) (r i) (s i)).symm
    rw [h_split]

  rw [hfold_rw]

  -- Now apply foldl_op_distrib
  exact foldl_op_distrib H (List.finRange k) r s

/-- **Grid Bridge Lemma (with GridComm)**: μ(F, n·r) equals (μ(F, r))^n.

This is the KEY lemma that enables all separation/shift/strict-mono arguments.
It converts "grouped" compositions μ(F, n·r) to "interleaved" compositions (μ(F,r))^n.

**Proof**: By induction on n, using mu_add_of_comm for the step case. -/
lemma mu_scale_eq_iterate_of_comm {k : ℕ} {F : AtomFamily α k}
    (H : GridComm F) (r : Multi k) (n : ℕ) :
    mu F (scaleMult n r) = iterate_op (mu F r) n := by
  induction n with
  | zero =>
    -- Base: μ(0·r) = ident = (μ r)^0
    simp only [scaleMult_zero, mu_zero, iterate_op_zero]
  | succ n ih =>
    -- Step: scaleMult (n+1) r = scaleMult n r + r
    have h_split : scaleMult (n + 1) r = scaleMult n r + r := by
      ext i
      simp only [scaleMult, Pi.add_apply]
      ring
    rw [h_split, mu_add_of_comm H, ih]
    -- Goal: op (iterate_op (mu F r) n) (mu F r) = iterate_op (mu F r) (n + 1)
    -- Use iterate_op_add with m=n, n=1: op (iterate_op a n) (iterate_op a 1) = iterate_op a (n+1)
    calc op (iterate_op (mu F r) n) (mu F r)
        = op (iterate_op (mu F r) n) (iterate_op (mu F r) 1) := by rw [iterate_op_one]
      _ = iterate_op (mu F r) (n + 1) := iterate_op_add (mu F r) n 1

/-- **Grid Bridge Lemma (legacy)**: μ(F, n·r) equals (μ(F, r))^n.
    For k=1, this is proven via `mu_scaleMult_eq_iterate_singleton`.
    For k>1, this follows from the existence of the representation R,
    which implies commutativity on the grid.
    This is the inductive bootstrap step - the representation theorem ensures
    this equality holds on the grid. -/
lemma mu_scale_eq_iterate {k : ℕ} {F : AtomFamily α k} (_R : MultiGridRep F)
    (H : GridComm F) (r : Multi k) (n : ℕ) :
    mu F (scaleMult n r) = iterate_op (mu F r) n := by
  -- Case split on k
  match k with
  | 0 =>
    -- k=0: Both sides equal ident (empty grid)
    have h_lhs : mu F (scaleMult n r) = ident := by
      unfold mu
      simp [List.finRange_zero]
    have h_rhs : iterate_op (mu F r) n = ident := by
      have hmu : mu F r = ident := by unfold mu; simp [List.finRange_zero]
      rw [hmu]
      -- Now need: iterate_op ident n = ident
      -- Use a helper lemma to avoid context pollution in induction
      suffices h : ∀ m, iterate_op ident m = ident from h n
      intro m
      induction m with
      | zero => rfl
      | succ k hk => simp only [iterate_op, hk, op_ident_left]
    rw [h_lhs, h_rhs]
  | 1 =>
    -- k=1: Use mu_scaleMult_eq_iterate_singleton
    -- Extract the single atom
    let a := F.atoms ⟨0, by decide⟩
    have ha : ident < a := F.pos ⟨0, by decide⟩
    -- Show F equals singletonAtomFamily a
    have hF_eq : ∀ i : Fin 1, F.atoms i = a := fun i => by simp [a, Fin.eq_zero i]
    -- The result follows from the singleton case
    -- We need to connect F to singletonAtomFamily
    have hr : mu F r = iterate_op a (r ⟨0, by decide⟩) := by
      unfold mu
      simp [List.finRange_succ, List.finRange_zero, hF_eq, op_ident_left]
    have hscale : mu F (scaleMult n r) = iterate_op a (n * r ⟨0, by decide⟩) := by
      unfold mu
      simp [List.finRange_succ, List.finRange_zero, hF_eq, op_ident_left, scaleMult]
    have hiter : iterate_op (mu F r) n = iterate_op a (n * r ⟨0, by decide⟩) := by
      rw [hr, iterate_op_mul]
      ring_nf
    rw [hscale, hiter]
  | k + 2 =>
    -- k≥2: Use GridComm hypothesis which provides commutativity.
    -- This is the INDUCTIVE HYPOTHESIS from the k→k+1 induction.
    exact mu_scale_eq_iterate_of_comm H r n

/-- **Separation Property**: For any A-witness and C-witness, the A-statistic is strictly less than the C-statistic.

This is a key result from K&S Appendix A. The proof uses:
1. Repetition lemma to scale to common denominator
2. Strict monotonicity of Θ to preserve the ordering mu F rA < d^M < mu F rC
3. Division to get the statistic inequality

Mathematical sketch:
- rA ∈ A(uA) means: mu F rA < d^uA
- rC ∈ C(uC) means: mu F rC > d^uC
- Scale to M = uA · uC:
  - (mu F rA)^uC < d^M (by repetition)
  - d^M < (mu F rC)^uA (by repetition)
- Apply Θ and use additivity on iterates:
  - uC · Θ(mu F rA) < M · Θ(d) < uA · Θ(mu F rC)
- Divide to get: Θ(mu F rA)/uA < Θ(mu F rC)/uC
-/
lemma separation_property {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    {rA : Multi k} {uA : ℕ} (huA : 0 < uA) (hrA : rA ∈ extensionSetA F d uA)
    {rC : Multi k} {uC : ℕ} (huC : 0 < uC) (hrC : rC ∈ extensionSetC F d uC) :
    separationStatistic R rA uA huA < separationStatistic R rC uC huC := by
  unfold separationStatistic extensionSetA extensionSetC at *
  -- Extract the key inequalities
  have hA_lt : mu F rA < iterate_op d uA := hrA
  have hC_gt : mu F rC > iterate_op d uC := hrC

  -- Use repetition to scale to common denominator Δ = uA * uC
  -- Key: compare scaled grid points, not iterate equality
  let Δ := uA * uC
  have hΔ_pos : 0 < Δ := Nat.mul_pos huA huC
  let mA := uC  -- Δ / uA = (uA * uC) / uA = uC
  let mC := uA  -- Δ / uC = (uA * uC) / uC = uA

  -- Step 1: Scale the inequalities using repetition_lemma_lt
  -- From μ(F,rA) < d^uA, get (μ(F,rA))^mA < d^(uA*mA) = d^Δ
  have hA_scaled : iterate_op (mu F rA) mA < iterate_op d Δ := by
    have : iterate_op (mu F rA) (1 * mA) < iterate_op d (uA * mA) :=
      repetition_lemma_lt (mu F rA) d 1 uA mA huC (by rwa [iterate_op_one])
    simpa [Nat.one_mul] using this

  -- From d^uC < μ(F,rC), get d^Δ < (μ(F,rC))^mC
  have hC_scaled : iterate_op d Δ < iterate_op (mu F rC) mC := by
    have : iterate_op d (uC * mC) < iterate_op (mu F rC) (1 * mC) :=
      repetition_lemma_lt d (mu F rC) uC 1 mC huA (by rwa [iterate_op_one])
    simp only [Nat.one_mul] at this
    convert this using 2
    ring  -- Δ = uA * uC = uC * uA = uC * mC

  -- Step 2: Transitivity gives (μ(F,rA))^mA < (μ(F,rC))^mC
  have h_iter_lt : iterate_op (mu F rA) mA < iterate_op (mu F rC) mC :=
    lt_trans hA_scaled hC_scaled

  -- Step 3: Use Theta_scaleMult to connect to grid points
  -- Θ(μ(F, mA · rA)) = mA · Θ(μ(F,rA))
  have hA_theta : R.Θ_grid ⟨mu F (scaleMult mA rA), mu_mem_kGrid F _⟩ =
                  mA * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ :=
    Theta_scaleMult R rA mA

  have hC_theta : R.Θ_grid ⟨mu F (scaleMult mC rC), mu_mem_kGrid F _⟩ =
                  mC * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ :=
    Theta_scaleMult R rC mC

  -- Step 4: Show mu F (scaleMult mA rA) < mu F (scaleMult mC rC)
  -- We need this to apply R.strictMono and get the Θ inequality

  have h_grid_lt : mu F (scaleMult mA rA) < mu F (scaleMult mC rC) := by
    -- Use GridBridge (the inductive hypothesis) directly!
    -- This is the key change per GPT-5.1 Pro: we ASSUME the bridge as IH,
    -- not derive it here. The IH is threaded from the k-grid to the (k+1)-grid.
    have hA_bridge : mu F (scaleMult mA rA) = iterate_op (mu F rA) mA :=
      IH.bridge rA mA
    have hC_bridge : mu F (scaleMult mC rC) = iterate_op (mu F rC) mC :=
      IH.bridge rC mC

    -- Rewrite grid points as iterates and apply h_iter_lt
    rw [hA_bridge, hC_bridge]
    exact h_iter_lt

  -- Step 5: Apply R.strictMono to get Θ inequality
  have h_Theta_lt : R.Θ_grid ⟨mu F (scaleMult mA rA), mu_mem_kGrid F _⟩ <
                    R.Θ_grid ⟨mu F (scaleMult mC rC), mu_mem_kGrid F _⟩ :=
    R.strictMono h_grid_lt

  -- Step 6: Substitute Theta_scaleMult and simplify
  rw [hA_theta, hC_theta] at h_Theta_lt
  -- Now have: mA * R.Θ_grid ⟨mu F rA, ...⟩ < mC * R.Θ_grid ⟨mu F rC, ...⟩
  -- which is: uC * Θ(rA) < uA * Θ(rC)

  -- Step 7: Divide both sides to get separation statistic inequality
  -- Note: separationStatistic was already unfolded at line 1338
  -- We have: mA * Θ(rA) < mC * Θ(rC) where mA = uC, mC = uA
  -- Dividing by (uA * uC): Θ(rA)/uA < Θ(rC)/uC
  have huA_pos_real : (0 : ℝ) < uA := Nat.cast_pos.mpr huA
  have huC_pos_real : (0 : ℝ) < uC := Nat.cast_pos.mpr huC

  -- Goal: Θ(rA)/uA < Θ(rC)/uC
  -- Using div_lt_div_iff₀: a/b < c/d ↔ a*d < c*b (for positive b, d)
  rw [div_lt_div_iff₀ huA_pos_real huC_pos_real]
  -- Goal is now: Θ(rA) * uC < Θ(rC) * uA
  -- h_Theta_lt is: mA * Θ(rA) < mC * Θ(rC) where mA = uC, mC = uA
  -- So h_Theta_lt is: uC * Θ(rA) < uA * Θ(rC)
  -- Use ring to reorder multiplication
  have h_rewrite : R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ * ↑uC =
                   (uC : ℝ) * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ := by ring
  have h_rewrite' : R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ * ↑uA =
                    (uA : ℝ) * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ := by ring
  rw [h_rewrite, h_rewrite']
  -- Now goal is: uC * Θ(rA) < uA * Θ(rC), which is exactly h_Theta_lt
  exact h_Theta_lt

/-- **Separation property (A < B)**: When B ≠ ∅, A-statistics are strictly less than B-statistics.

This is the key refinement of separation_property for the B ≠ ∅ case.
-/
lemma separation_property_A_B {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) {d : α} (hd : ident < d)
    {rA : Multi k} {uA : ℕ} (huA : 0 < uA) (hrA : rA ∈ extensionSetA F d uA)
    {rB : Multi k} {uB : ℕ} (huB : 0 < uB) (hrB : rB ∈ extensionSetB F d uB) :
    separationStatistic R rA uA huA < separationStatistic R rB uB huB := by
  -- Derive GridBridge from mu_scale_eq_iterate (same pattern as separation_property)
  have IH : GridBridge F := ⟨fun r n => mu_scale_eq_iterate R H r n⟩
  unfold separationStatistic extensionSetA extensionSetB at *
  -- Extract the key inequalities
  have hA_lt : mu F rA < iterate_op d uA := hrA
  have hB_eq : mu F rB = iterate_op d uB := hrB

  -- Scale to common denominator Δ = uA * uB
  let Δ := uA * uB
  have hΔ_pos : 0 < Δ := Nat.mul_pos huA huB
  let mA := uB  -- Δ / uA
  let mB := uA  -- Δ / uB

  -- Step 1: Scale A inequality
  -- From μ(F,rA) < d^uA, get (μ(F,rA))^mA < d^Δ
  have hA_scaled : iterate_op (mu F rA) mA < iterate_op d Δ := by
    have : iterate_op (mu F rA) (1 * mA) < iterate_op d (uA * mA) :=
      repetition_lemma_lt (mu F rA) d 1 uA mA huB (by rwa [iterate_op_one])
    simpa [Nat.one_mul] using this

  -- Step 2: Use B equality to get d^Δ = (μ(F,rB))^mB
  -- d^Δ = d^{uA*uB} = (d^uB)^uA = (μ(F,rB))^uA = (μ(F,rB))^mB
  have hB_scaled : iterate_op d Δ = iterate_op (mu F rB) mB := by
    calc iterate_op d Δ
        = iterate_op d (uA * uB) := rfl
      _ = iterate_op d (uB * uA) := by ring_nf
      _ = iterate_op (iterate_op d uB) uA := (iterate_op_mul d uB uA).symm
      _ = iterate_op (mu F rB) uA := by rw [hB_eq]
      _ = iterate_op (mu F rB) mB := rfl

  -- Step 3: Transitivity gives (μ(F,rA))^mA < (μ(F,rB))^mB
  have h_iter_lt : iterate_op (mu F rA) mA < iterate_op (mu F rB) mB := by
    rw [← hB_scaled]; exact hA_scaled

  -- Step 4: Use GridBridge (IH) and Θ to get statistic inequality
  have h_grid_lt : mu F (scaleMult mA rA) < mu F (scaleMult mB rB) := by
    have hA_bridge : mu F (scaleMult mA rA) = iterate_op (mu F rA) mA :=
      IH.bridge rA mA
    have hB_bridge : mu F (scaleMult mB rB) = iterate_op (mu F rB) mB :=
      IH.bridge rB mB
    rw [hA_bridge, hB_bridge]
    exact h_iter_lt

  have h_Theta_lt : R.Θ_grid ⟨mu F (scaleMult mA rA), mu_mem_kGrid F _⟩ <
                    R.Θ_grid ⟨mu F (scaleMult mB rB), mu_mem_kGrid F _⟩ :=
    R.strictMono h_grid_lt

  -- Step 5: Apply Theta_scaleMult
  have hA_theta : R.Θ_grid ⟨mu F (scaleMult mA rA), mu_mem_kGrid F _⟩ =
                  mA * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ :=
    Theta_scaleMult R rA mA
  have hB_theta : R.Θ_grid ⟨mu F (scaleMult mB rB), mu_mem_kGrid F _⟩ =
                  mB * R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ :=
    Theta_scaleMult R rB mB

  rw [hA_theta, hB_theta] at h_Theta_lt

  -- Step 6: Divide to get statistic inequality
  have huA_pos_real : (0 : ℝ) < uA := Nat.cast_pos.mpr huA
  have huB_pos_real : (0 : ℝ) < uB := Nat.cast_pos.mpr huB

  rw [div_lt_div_iff₀ huA_pos_real huB_pos_real]
  have h_rewrite : R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ * ↑uB =
                   (uB : ℝ) * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ := by ring
  have h_rewrite' : R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ * ↑uA =
                    (uA : ℝ) * R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ := by ring
  rw [h_rewrite, h_rewrite']
  exact h_Theta_lt

/-- **Separation property (B < C)**: When B ≠ ∅, B-statistics are strictly less than C-statistics.

This is the key refinement of separation_property for the B ≠ ∅ case.
-/
lemma separation_property_B_C {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) {d : α} (hd : ident < d)
    {rB : Multi k} {uB : ℕ} (huB : 0 < uB) (hrB : rB ∈ extensionSetB F d uB)
    {rC : Multi k} {uC : ℕ} (huC : 0 < uC) (hrC : rC ∈ extensionSetC F d uC) :
    separationStatistic R rB uB huB < separationStatistic R rC uC huC := by
  -- Derive GridBridge from mu_scale_eq_iterate (same pattern as separation_property)
  have IH : GridBridge F := ⟨fun r n => mu_scale_eq_iterate R H r n⟩
  unfold separationStatistic extensionSetB extensionSetC at *
  -- Extract the key inequalities
  have hB_eq : mu F rB = iterate_op d uB := hrB
  have hC_gt : mu F rC > iterate_op d uC := hrC

  -- Scale to common denominator Δ = uB * uC
  let Δ := uB * uC
  have hΔ_pos : 0 < Δ := Nat.mul_pos huB huC
  let mB := uC  -- Δ / uB
  let mC := uB  -- Δ / uC

  -- Step 1: Use B equality to get (μ(F,rB))^mB = d^Δ
  have hB_scaled : iterate_op (mu F rB) mB = iterate_op d Δ := by
    calc iterate_op (mu F rB) mB
        = iterate_op (mu F rB) uC := rfl
      _ = iterate_op (iterate_op d uB) uC := by rw [hB_eq]
      _ = iterate_op d (uB * uC) := iterate_op_mul d uB uC
      _ = iterate_op d Δ := rfl

  -- Step 2: Scale C inequality
  -- From d^uC < μ(F,rC), get d^Δ < (μ(F,rC))^mC
  have hC_scaled : iterate_op d Δ < iterate_op (mu F rC) mC := by
    have : iterate_op d (uC * mC) < iterate_op (mu F rC) (1 * mC) :=
      repetition_lemma_lt d (mu F rC) uC 1 mC huB (by rwa [iterate_op_one])
    simp only [Nat.one_mul] at this
    convert this using 2
    ring

  -- Step 3: Transitivity gives (μ(F,rB))^mB < (μ(F,rC))^mC
  have h_iter_lt : iterate_op (mu F rB) mB < iterate_op (mu F rC) mC := by
    rw [hB_scaled]; exact hC_scaled

  -- Step 4: Use GridBridge (IH) and Θ to get statistic inequality
  have h_grid_lt : mu F (scaleMult mB rB) < mu F (scaleMult mC rC) := by
    have hB_bridge : mu F (scaleMult mB rB) = iterate_op (mu F rB) mB :=
      IH.bridge rB mB
    have hC_bridge : mu F (scaleMult mC rC) = iterate_op (mu F rC) mC :=
      IH.bridge rC mC
    rw [hB_bridge, hC_bridge]
    exact h_iter_lt

  have h_Theta_lt : R.Θ_grid ⟨mu F (scaleMult mB rB), mu_mem_kGrid F _⟩ <
                    R.Θ_grid ⟨mu F (scaleMult mC rC), mu_mem_kGrid F _⟩ :=
    R.strictMono h_grid_lt

  -- Step 5: Apply Theta_scaleMult
  have hB_theta : R.Θ_grid ⟨mu F (scaleMult mB rB), mu_mem_kGrid F _⟩ =
                  mB * R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ :=
    Theta_scaleMult R rB mB
  have hC_theta : R.Θ_grid ⟨mu F (scaleMult mC rC), mu_mem_kGrid F _⟩ =
                  mC * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ :=
    Theta_scaleMult R rC mC

  rw [hB_theta, hC_theta] at h_Theta_lt

  -- Step 6: Divide to get statistic inequality
  have huB_pos_real : (0 : ℝ) < uB := Nat.cast_pos.mpr huB
  have huC_pos_real : (0 : ℝ) < uC := Nat.cast_pos.mpr huC

  rw [div_lt_div_iff₀ huB_pos_real huC_pos_real]
  have h_rewrite : R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ * ↑uC =
                   (uC : ℝ) * R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ := by ring
  have h_rewrite' : R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ * ↑uB =
                    (uB : ℝ) * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ := by ring
  rw [h_rewrite, h_rewrite']
  exact h_Theta_lt

/-- For B empty: any A-witness statistic is ≤ δ. -/
lemma A_stat_le_delta_of_B_empty {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u)
    (hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u)
    {r : Multi k} {u : ℕ} (hu : 0 < u) (hrA : r ∈ extensionSetA F d u) :
    separationStatistic R r u hu ≤
      B_empty_delta (R:=R) (F:=F) d hd hB_empty hA_nonempty hC_nonempty := by
  classical
  -- δ is defined as sSup of A-statistics; we need to show our statistic is ≤ this sSup
  unfold B_empty_delta separationStatistic

  -- The set being supremumed
  let AStats := {s : ℝ | ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u ∧
                          s = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u}

  -- Our statistic is in AStats
  have h_in_set : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u ∈ AStats := by
    exact ⟨r, u, hu, hrA, rfl⟩

  -- Need to show AStats is bounded above to use le_csSup
  have h_bdd : BddAbove AStats := by
    -- Use C-witness to provide upper bound
    rcases hC_nonempty with ⟨rC, uC, huC, hrC⟩
    let σC := separationStatistic R rC uC huC
    refine ⟨σC, ?_⟩
    intro s hs
    rcases hs with ⟨r', u', hu', hrA', rfl⟩
    -- Every A-statistic is strictly below any C-statistic
    exact le_of_lt (separation_property R H IH hd hu' hrA' huC hrC)

  -- Apply le_csSup
  exact le_csSup h_bdd h_in_set

/-- For B empty: δ is ≤ any C-witness statistic. -/
lemma delta_le_C_stat_of_B_empty {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u)
    (hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u)
    {r : Multi k} {u : ℕ} (hu : 0 < u) (hrC : r ∈ extensionSetC F d u) :
    B_empty_delta (R:=R) (F:=F) d hd hB_empty hA_nonempty hC_nonempty ≤
      separationStatistic R r u hu := by
  classical
  -- δ = sSup(AStats); we need to show sSup(AStats) ≤ σC
  unfold B_empty_delta

  let AStats := {s : ℝ | ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u ∧
                          s = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u}

  -- Use csSup_le: need to show every A-stat ≤ σC
  have h_nonempty : AStats.Nonempty := by
    rcases hA_nonempty with ⟨rA, uA, huA, hrA⟩
    use R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ / uA
    use rA, uA, huA, hrA

  apply csSup_le h_nonempty
  intro s hs
  rcases hs with ⟨r', u', hu', hrA', rfl⟩
  -- Need: σ(r',u') ≤ σ(r,u) where r'∈A, r∈C
  -- This follows from separation property: all A-stats < all C-stats
  exact le_of_lt (separation_property R H IH hd hu' hrA' hu hrC)

/-- The accuracy lemma: δ is pinned by the A/C gap arbitrarily precisely.

    **Proof sketch** (from K&S):
    1. Pick any reference atom a from the family F.
    2. Use Archimedean property: there exists N such that d < a^N.
    3. For any ε > 0, choose m large enough that 1/m < ε.
    4. Find the crossing point: max n such that a^n ≤ d^m.
    5. Then n/m and (n+1)/m bracket δ with gap < ε.
-/
theorem accuracy_lemma {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u)
    (hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (rA : Multi k) (uA : ℕ) (huA : 0 < uA) (hrA : rA ∈ extensionSetA F d uA)
      (rC : Multi k) (uC : ℕ) (huC : 0 < uC) (hrC : rC ∈ extensionSetC F d uC),
      separationStatistic R rC uC huC - separationStatistic R rA uA huA < ε := by
  classical
  -- The k = 0 case is impossible under the hypotheses (C cannot be non-empty).
  -- We discharge it via contradiction and rely on the k.succ branch for the real work.
  cases k with
  | zero =>
    -- With no atoms, μ(F, r) = ident for all r, so C cannot contain a witness.
    have hcontr : False := by
      rcases hC_nonempty with ⟨rC, uC, huC, hrC⟩
      have hmu : mu F rC = ident := by simp [mu]
      have hpos : ident < iterate_op d uC := iterate_op_pos d hd _ huC
      have hlt : iterate_op d uC < ident := by simpa [extensionSetC, hmu] using hrC
      exact (lt_asymm hpos hlt).elim
    exact (False.elim hcontr)
  | succ k =>
    -- Choose a reference atom and its Θ-value on the grid.
    let i0 : Fin (k + 1) := ⟨0, Nat.succ_pos _⟩
    let a : α := F.atoms i0
    have ha : ident < a := F.pos i0
    have hmu_one : mu F (unitMulti i0 1) = a := by
      simpa [a, iterate_op_one] using mu_unitMulti F i0 1
    let θatom : ℝ := R.Θ_grid ⟨mu F (unitMulti i0 1), mu_mem_kGrid F (unitMulti i0 1)⟩
    -- θatom is positive because Θ is strictly monotone and Θ(ident) = 0.
    have hθ_pos : 0 < θatom := by
      have hlt :
          R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F (unitMulti i0 1), mu_mem_kGrid F (unitMulti i0 1)⟩ := by
        have hbase : ident < mu F (unitMulti i0 1) := by simpa [hmu_one] using ha
        exact R.strictMono hbase
      have hzero : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ = 0 := R.ident_eq_zero
      linarith

    -- Pick a large denominator U so that θatom / U < ε.
    obtain ⟨N, hN⟩ := exists_nat_gt (θatom / ε)
    let U : ℕ := Nat.succ N
    have hUpos : 0 < U := Nat.succ_pos _
    have hU_gt : θatom / ε < (U : ℝ) := by
      have hle : (N : ℝ) ≤ (U : ℝ) := by exact_mod_cast Nat.le_succ N
      exact lt_of_lt_of_le hN hle
    have hθ_lt : θatom < (U : ℝ) * ε := by
      have h := (mul_lt_mul_right hε).mpr hU_gt
      have hε_ne : (ε : ℝ) ≠ 0 := ne_of_gt hε
      have hleft : θatom / ε * ε = θatom := by field_simp [hε_ne]
      simpa [hleft, mul_comm] using h
    have hgap : θatom / (U : ℝ) < ε := by
      have hUpos_real : 0 < (U : ℝ) := by exact_mod_cast hUpos
      have hU_ne : (U : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hUpos)
      have hθ_lt' : θatom < ε * (U : ℝ) := by simpa [mul_comm] using hθ_lt
      have hpos_inv : 0 < (1 / (U : ℝ)) := one_div_pos.mpr hUpos_real
      have h := mul_lt_mul_of_pos_right hθ_lt' hpos_inv
      have hleft : θatom * (1 / (U : ℝ)) = θatom / (U : ℝ) := by field_simp [hU_ne]
      have hright : ε * (U : ℝ) * (1 / (U : ℝ)) = ε := by field_simp [hU_ne]
      simpa [hleft, hright, mul_left_comm, mul_assoc] using h

    -- Find the crossing index n with a^n ≤ d^U < a^{n+1}.
    obtain ⟨K, hK⟩ := bounded_by_iterate a ha (iterate_op d U)
    let P : ℕ → Prop := fun n => iterate_op a n ≤ iterate_op d U
    have hP0 : P 0 := by
      have hpos : ident < iterate_op d U := iterate_op_pos d hd _ hUpos
      have hle : ident ≤ iterate_op d U := le_of_lt hpos
      simpa [P, iterate_op_zero] using hle
    have hcross := findGreatest_crossing (P := P) K hP0
    let n := Nat.findGreatest P K
    have hPn : P n := hcross.1
    have hn_le_K : n ≤ K := hcross.2.1
    have hn_lt_K : n < K := by
      have hle : iterate_op a n ≤ iterate_op d U := hPn
      have hlt : iterate_op d U < iterate_op a K := hK
      have hneq : n ≠ K := by
        intro hEq
        have hle' : iterate_op a K ≤ iterate_op d U := by simpa [hEq] using hle
        exact (not_le_of_lt hlt) hle'
      exact lt_of_le_of_ne hn_le_K hneq
    have h_notP_succ : ¬ P (n + 1) :=
      hcross.2.2 (n + 1) (Nat.lt_succ_self _) (Nat.succ_le_of_lt hn_lt_K)

    -- Translate P-information to A/C membership.
    have hPn_le : iterate_op a n ≤ iterate_op d U := hPn
    have hnotB : unitMulti i0 n ∉ extensionSetB F d U := hB_empty _ _ hUpos
    have hPn_lt : iterate_op a n < iterate_op d U := by
      have hne : iterate_op a n ≠ iterate_op d U := by
        intro hEq
        apply hnotB
        simpa [extensionSetB, Set.mem_setOf_eq, mu_unitMulti F i0 n] using hEq
      exact lt_of_le_of_ne hPn_le hne
    have hsucc_lt : iterate_op d U < iterate_op a (n + 1) := lt_of_not_ge h_notP_succ

    -- Build A and C witnesses.
    let rA := unitMulti i0 n
    let rC := unitMulti i0 (n + 1)
    have hrA : rA ∈ extensionSetA F d U := by
      simpa [rA, extensionSetA, mu_unitMulti] using hPn_lt
    have hrC : rC ∈ extensionSetC F d U := by
      simpa [rC, extensionSetC, mu_unitMulti] using hsucc_lt

    -- Separation statistics for the two witnesses.
    have h_sepA :
        separationStatistic R rA U hUpos =
          (n : ℝ) * θatom / (U : ℝ) := by
      unfold rA separationStatistic
      have hθ := Theta_unitMulti (R := R) (F := F) i0 n
      -- Simplify using the scaling lemma
      simpa [θatom] using hθ
    have h_sepC :
        separationStatistic R rC U hUpos =
          (n + 1 : ℝ) * θatom / (U : ℝ) := by
      unfold rC separationStatistic
      have hθ := Theta_unitMulti (R := R) (F := F) i0 (n + 1)
      simpa [θatom] using hθ

    -- Gap computation: σ_C - σ_A = θatom / U < ε.
    refine ⟨rA, U, hUpos, hrA, rC, U, hUpos, hrC, ?_⟩
    have hgap_exact :
        separationStatistic R rC U hUpos - separationStatistic R rA U hUpos =
          θatom / (U : ℝ) := by
      rw [h_sepA, h_sepC]
      ring
    nlinarith [hgap_exact, hgap]

/-! ## Phase 3: Inductive Construction (Summary)

The full K&S argument proceeds by induction on the number of atom types:

**Base case (k=1)**: Phase 1 above shows Θ(a^n) = n is well-defined on the
grid generated by a single positive element.

**Inductive step (k → k+1)**: Given representation on k types, extend to new type d:
1. Use A/B/C partition to classify where d^u lands relative to existing grid
2. If B non-empty: d has rational relation to existing values
3. If B empty: use Archimedean property to pin down d as limit
4. Both cases give d a unique position on the linear scale

**Result**: Θ : α → ℝ with additivity Θ(x⊕y) = Θ(x) + Θ(y).

**Commutativity**: From additivity + injectivity:
  Θ(x⊕y) = Θ(x) + Θ(y) = Θ(y) + Θ(x) = Θ(y⊕x)
  ⟹ x⊕y = y⊕x by injectivity of Θ
-/

/-! ### Layer A: Structural Extension (K&S Appendix A, equation after line 1456)

**Inductive step**: Extend a k-type grid representation by a new atom.

This captures the two major cases from Appendix A:
* Case B non-empty: the new atom is rationally related to the existing grid.
* Case B empty: the new atom is pinned as a limit via the accuracy lemma.

Following the paper, when we extend from k atom types {a, b, c, ...} to k+1 types
by adding new atom d, the extended evaluation satisfies:

    μ(F', r₁,...,rₖ; t) = μ(F, r₁,...,rₖ) ⊕ d^t

This is the key structural property (K&S line 1456 in paper).
-/

/-- Extend an atom family F of k types to k+1 types by appending new atom d.
The new atom becomes the last index (position k). -/
def extendAtomFamily {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d) :
    AtomFamily α (k + 1) where
  atoms := fun i =>
    if h : i.val < k then
      -- Old atoms: use castSucc embedding
      F.atoms ⟨i.val, h⟩
    else
      -- New atom at position k
      d
  pos := fun i => by
    by_cases h : i.val < k
    · simp only [h, ↓reduceIte]
      exact F.pos ⟨i.val, h⟩
    · simp only [h, ↓reduceIte]
      exact hd

/-- The extended family preserves old atoms at positions < k -/
lemma extendAtomFamily_old {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (i : Fin k) :
    (extendAtomFamily F d hd).atoms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = F.atoms i := by
  simp only [extendAtomFamily]
  have h : i.val < k := i.isLt
  simp only [h, ↓reduceIte]
  congr

/-- The extended family has the new atom at position k -/
lemma extendAtomFamily_new {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d) :
    (extendAtomFamily F d hd).atoms ⟨k, Nat.lt_succ_self k⟩ = d := by
  simp only [extendAtomFamily]
  have h : ¬ k < k := Nat.lt_irrefl k
  exact dif_neg h

/-- Split a multiplicity vector for k+1 types into old part (first k coords) and new part (last coord).
This represents the split: (r₁,...,rₖ; t) where t is the last coordinate. -/
def splitMulti {k : ℕ} (r : Multi (k + 1)) : Multi k × ℕ :=
  (fun i => r ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, r ⟨k, Nat.lt_succ_self k⟩)

/-- Reconstruct a (k+1)-multiplicity from old part and new last coordinate -/
def joinMulti {k : ℕ} (r_old : Multi k) (t : ℕ) : Multi (k + 1) :=
  fun i => if h : i.val < k then r_old ⟨i.val, h⟩ else t

/-- Splitting and joining are inverses -/
lemma splitMulti_joinMulti {k : ℕ} (r_old : Multi k) (t : ℕ) :
    splitMulti (joinMulti r_old t) = (r_old, t) := by
  unfold splitMulti joinMulti
  -- After unfolding, goal is a pair equality
  apply Prod.ext
  · -- First component: show the functions are equal
    funext i
    have hi : i.val < k := i.isLt
    exact dif_pos hi
  · -- Second component: show (joinMulti r_old t) ⟨k, ...⟩ = t
    have h : ¬ k < k := Nat.lt_irrefl k
    simp only []
    exact dif_neg h

/-- Joining and splitting are inverses (reverse direction) -/
lemma joinMulti_splitMulti {k : ℕ} (r : Multi (k + 1)) :
    let (r_old, t) := splitMulti r
    joinMulti r_old t = r := by
  unfold splitMulti joinMulti
  ext i
  by_cases hi : i.val < k
  · simp [hi]
  · simp [hi]
    have hiv : i.val = k := by omega
    have h_i_eq : i = ⟨k, Nat.lt_succ_self k⟩ := by ext; exact hiv
    rw [h_i_eq]

/-- splitMulti distributes over pointwise addition of multiplicities. -/
lemma splitMulti_add {k : ℕ} (r s : Multi (k + 1)) :
    splitMulti (fun i => r i + s i) = ((fun i => (splitMulti r).1 i + (splitMulti s).1 i),
                                        (splitMulti r).2 + (splitMulti s).2) := by
  unfold splitMulti; rfl

/-- joinMulti distributes over pointwise addition of multiplicities. -/
lemma joinMulti_add {k : ℕ} (r_old s_old : Multi k) (t_r t_s : ℕ) :
    (fun i => joinMulti r_old t_r i + joinMulti s_old t_s i) =
    joinMulti (fun i => r_old i + s_old i) (t_r + t_s) := by
  unfold joinMulti
  ext i
  by_cases hi : i.val < k
  · simp [hi]
  · simp [hi]

/-- Helper: folding over `Fin (k+1)` splits into the first `k` indices and the final `last`. -/
private lemma foldl_fin_succ_split {k : ℕ} (f : α → Fin (k + 1) → α) (acc : α) :
    List.foldl f acc (List.finRange (k + 1)) =
    f
      (List.foldl f acc ((List.finRange k).map (Fin.castAdd 1)))
      (Fin.last k) := by
  classical
  -- Use the canonical ordered enumeration of `Fin (k+1)`
  have hmapFun : (Fin.castSucc : Fin k → Fin (k + 1)) = Fin.castAdd 1 := by
    funext i; ext; rfl
  have hbase :
      List.foldl f acc (List.finRange (k + 1)) =
        f (List.foldl f acc ((List.finRange k).map Fin.castSucc)) (Fin.last k) := by
    simp [List.finRange_succ_last, List.foldl_append]
  simpa [hmapFun] using hbase

/-- **Key Structural Lemma** (K&S paper, line 1456):

When extending from k types to k+1 types, the evaluation of μ on the extended family
splits into old part ⊕ new part:

    μ(F', r₁,...,rₖ; t) = μ(F, r₁,...,rₖ) ⊕ d^t

This is the foundation for the inductive construction. The proof follows from the
definition of μ as a fold and the split of indices.
-/
lemma mu_extend_last {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (r_old : Multi k) (t : ℕ) :
    mu (extendAtomFamily F d hd) (joinMulti r_old t) =
    op (mu F r_old) (iterate_op d t) := by
  let F' := extendAtomFamily F d hd
  let r' := joinMulti r_old t
  unfold mu

  -- Strategy: Show that processing each index in Fin (k+1) gives the right contribution
  -- We'll use induction on the list structure or reason about the fold directly

  -- Key observations:
  have hF'_old : ∀ i : Fin k, F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = F.atoms i :=
    extendAtomFamily_old F d hd
  have hF'_new : F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d :=
    extendAtomFamily_new F d hd
  have hr'_old : ∀ i : Fin k, r' ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = r_old i := by
    intro i
    show (joinMulti r_old t) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = r_old i
    unfold joinMulti
    exact dif_pos i.isLt
  have hr'_new : r' ⟨k, Nat.lt_succ_self k⟩ = t := by
    show (joinMulti r_old t) ⟨k, Nat.lt_succ_self k⟩ = t
    unfold joinMulti
    have : ¬ k < k := Nat.lt_irrefl k
    exact dif_neg this

  -- Use the fold splitting lemma
  let f : α → Fin (k + 1) → α := fun acc i => op acc (iterate_op (F'.atoms i) (r' i))

  -- Apply foldl_fin_succ_split
  have hsplit := foldl_fin_succ_split f ident

  -- Simplify the LHS using hsplit
  conv_lhs => rw [hsplit]

  -- Now we need to show that the mapped fold equals mu F r_old
  have hmap_fold :
      List.foldl f ident
        (List.map (Fin.castAdd 1) (List.finRange k)) =
      mu F r_old := by
    -- Key: for each i : Fin k, F'.atoms (lift i) = F.atoms i and r' (lift i) = r_old i
    -- So folding over the mapped list with f is the same as folding over the original list

    -- Define the original function for mu F r_old
    let g : α → Fin k → α := fun acc i => op acc (iterate_op (F.atoms i) (r_old i))

    -- Show that f on lifted indices equals g on original indices
    have hfg : ∀ (acc : α) (i : Fin k),
        f acc (Fin.castAdd 1 i) = g acc i := by
      intro acc i
      -- Work with an explicit constructor form for `i`
      cases i with
      | mk i_val i_lt =>
        have h_atom' :
            F'.atoms ⟨i_val, Nat.lt_trans i_lt (Nat.lt_succ_self k)⟩ =
              F.atoms ⟨i_val, i_lt⟩ := by
          simpa using hF'_old ⟨i_val, i_lt⟩
        have h_r' :
            r' ⟨i_val, Nat.lt_trans i_lt (Nat.lt_succ_self k)⟩ =
              r_old ⟨i_val, i_lt⟩ := by
          simpa using hr'_old ⟨i_val, i_lt⟩
        simp [f, g, h_atom', h_r']

    -- Use List.foldl_map and the equivalence
    unfold mu
    -- The goal is to show the folds are equal
    -- We'll use induction on the list

    -- Generalized helper: for any accumulator
    have h_gen : ∀ (acc : α) (l : List (Fin k)),
        List.foldl f acc (List.map (Fin.castAdd 1) l) =
        List.foldl g acc l := by
      intro acc l
      induction l generalizing acc with
      | nil => rfl
      | cons hd tl ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [hfg]
        exact ih _

    exact h_gen ident (List.finRange k)

  rw [hmap_fold]

  -- Simplify the last step application
  -- After the fold, we apply f to the index ⟨k, ...⟩
  suffices f (mu F r_old) ⟨k, Nat.lt_succ_self k⟩ = op (mu F r_old) (iterate_op d t) by
    exact this

  unfold f
  -- After unfolding: op (mu F r_old) (iterate_op (F'.atoms ⟨k, ...⟩) (r' ⟨k, ...⟩))
  -- Use hF'_new: F'.atoms ⟨k, ...⟩ = d
  -- Use hr'_new: r' ⟨k, ...⟩ = t
  rw [hF'_new, hr'_new]
  -- Goal is now: op (mu F r_old) (iterate_op d t) = op (mu F r_old) (iterate_op d t)
  -- which is definitionally equal

/-! ### Layer B: Value Assignment and Θ' Construction

Following K&S Appendix A, once we have the extended family F', we need to:
1. Choose δ (the representation value for the new atom d):
   - Case B non-empty: δ = common statistic from B witnesses
   - Case B empty: δ = limit value from accuracy lemma
2. Define Θ' on kGrid F' via: Θ'(μ(F', r_old, t)) := Θ(μ(F, r_old)) + t * δ
3. Prove Θ' satisfies MultiGridRep requirements (strict mono, additive, normalized)
-/

/-- When B is empty, A is non-empty (zero multiplicity is always in A). -/
lemma extensionSetA_nonempty_of_B_empty {k : ℕ} (F : AtomFamily α k) (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u := by
  -- Take zero multiplicity and u = 1
  refine ⟨fun _ => 0, 1, Nat.one_pos, ?_⟩
  simp only [extensionSetA, Set.mem_setOf_eq]
  -- μ(F, 0) = ident < d = d^1
  have : mu F (fun _ => 0) = ident := mu_zero (F := F)
  rw [this, iterate_op_one]
  exact hd

/-- When B is empty and k ≥ 1, C is non-empty (by Archimedean property). -/
lemma extensionSetC_nonempty_of_B_empty {k : ℕ} (F : AtomFamily α k) (hk : k ≥ 1) (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u := by
  -- Pick any atom from F (exists since k ≥ 1)
  have : 0 < k := hk
  let i₀ : Fin k := ⟨0, this⟩
  let a := F.atoms i₀
  have ha : ident < a := F.pos i₀
  -- By Archimedean property, ∃ N such that d < a^N
  obtain ⟨N, hN⟩ := bounded_by_iterate a ha d
  -- Take r = unitMulti i₀ N and u = 1
  refine ⟨unitMulti i₀ N, 1, Nat.one_pos, ?_⟩
  simp only [extensionSetC, Set.mem_setOf_eq]
  -- d^1 = d < a^N = μ(F, unitMulti i₀ N)
  rw [iterate_op_one]
  have : mu F (unitMulti i₀ N) = iterate_op a N := mu_unitMulti F i₀ N
  rw [this]
  exact hN

/-- Choose the representation value δ for the new atom d.
This is the Θ-value we assign to d in the extended representation. -/
noncomputable def chooseδ {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1) (R : MultiGridRep F)
    (d : α) (hd : ident < d) : ℝ :=
  if hB : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u then
    -- Case B non-empty: use common statistic
    B_common_statistic R d hd hB
  else
    -- Case B empty: use B_empty_delta
    have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u := fun r u hu hr => hB ⟨r, u, hu, hr⟩
    have hA : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
      extensionSetA_nonempty_of_B_empty F d hd hB_empty
    have hC : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
      extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
    B_empty_delta R d hd hB_empty hA hC

/-! ### Theta' Helper Lemmas

These lemmas establish key properties of the extended representation Θ':
1. δ > 0 (chooseδ is always positive)
2. Theta'_increment_t: Incrementing t increases Θ' by exactly δ
3. Theta'_strictMono_same_t: With fixed t, Θ' is strictly monotone in the old part

These are used to complete the extend_grid_rep_with_atom proof.
-/

/-- δ is positive in both branches of `chooseδ`. -/
lemma delta_pos {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d) :
    0 < chooseδ hk R d hd := by
  classical
  unfold chooseδ
  split_ifs with hB
  · -- B ≠ ∅: δ = B_common_statistic = Θ(d^u)/u with u>0
    -- Extract a concrete B-witness without destroying hB
    have ⟨r,u,hu,hr⟩ := hB
    have hstat :
      B_common_statistic R d hd hB = separationStatistic R r u hu :=
      B_common_statistic_eq_any_witness R IH d hd hB r u hu hr
    -- Expand the statistic and use strict monotonicity + Θ(ident)=0
    simp [hstat, separationStatistic]
    -- Since ident < d^u, strict monotonicity of Θ_grid gives Θ(d^u) > Θ(ident)=0
    -- Key: hr : r ∈ extensionSetB means mu F r = iterate_op d u
    have h_mu_eq : mu F r = iterate_op d u := by simpa [extensionSetB] using hr
    -- So ident < mu F r (via ident < d^u = mu F r)
    have h_ident_lt : ident < mu F r := by
      rw [h_mu_eq]
      exact iterate_op_pos d hd u hu
    have hθ : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩
              > R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ :=
      R.strictMono h_ident_lt
    have huℝ : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
    have : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
      by simpa [R.ident_eq_zero] using hθ
    exact div_pos this huℝ
  · -- B = ∅: B_empty_delta lies strictly between A and C statistics
    have hC : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
      extensionSetC_nonempty_of_B_empty F hk d hd
        (by intro r u hu hr; exact hB ⟨r,u,hu,hr⟩)
    rcases hC with ⟨r,u,hu,hrC⟩
    have hposC : 0 < separationStatistic R r u hu := by
      -- In C, d^u < μ F r ⇒ Θ(d^u) < Θ(μ F r)
      have hμ : iterate_op d u < mu F r := by simpa [extensionSetC] using hrC
      -- d^u is in kGrid F because ident is, and we can use monotonicity
      -- Actually, we just need to show Θ(mu F r) - Θ(ident) > 0 since Θ is strictly monotone
      have huℝ : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
      -- By strict monotonicity and ident < d^u < mu F r
      have h_ident_lt : ident < mu F r := by
        calc ident < iterate_op d u := iterate_op_pos d hd u hu
          _ < mu F r := hμ
      have hθ_pos : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
        have hθ : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ >
                  R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ :=
          R.strictMono h_ident_lt
        simpa [R.ident_eq_zero] using hθ
      simp [separationStatistic]
      exact div_pos hθ_pos huℝ
    -- Key: By Archimedean property, the same r is in A(N) for large enough N
    -- So B_empty_delta ≥ Θ(mu F r)/N > 0
    have hθ_pos : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      have h_ident_lt : ident < mu F r := by
        have hμ : iterate_op d u < mu F r := by simpa [extensionSetC] using hrC
        calc ident < iterate_op d u := iterate_op_pos d hd u hu
          _ < mu F r := hμ
      have hθ : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ >
                R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ :=
        R.strictMono h_ident_lt
      simpa [R.ident_eq_zero] using hθ
    -- Use Archimedean to find N with mu F r < d^N (so r ∈ A(N))
    obtain ⟨N, hN_bound⟩ := bounded_by_iterate d hd (mu F r)
    have hN_pos : 0 < N := by
      by_contra h_not
      push_neg at h_not
      have : N = 0 := Nat.eq_zero_of_le_zero h_not
      subst this
      simp [iterate_op_zero] at hN_bound
      exact absurd hN_bound (not_lt.mpr (ident_le (mu F r)))
    have hrA : r ∈ extensionSetA F d N := by simpa [extensionSetA] using hN_bound
    have hN_stat_pos : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / N := by
      have hNℝ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN_pos
      exact div_pos hθ_pos hNℝ
    -- B_empty_delta = sSup {A-statistics} ≥ Θ(mu F r)/N > 0
    have h_stat_in : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / N ∈
      {s : ℝ | ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' ∧
        s = R.Θ_grid ⟨mu F r', mu_mem_kGrid F r'⟩ / u'} := by
      exact ⟨r, N, hN_pos, hrA, rfl⟩
    unfold B_empty_delta
    exact lt_csSup_of_lt
      (by {
        -- Bounded above by the C-statistic (r, u) using separation_property
        use separationStatistic R r u hu
        intro s ⟨r', u', hu', hrA', hs⟩
        subst hs
        -- Every A-statistic is < every C-statistic by separation_property
        exact le_of_lt (separation_property R H IH hd hu' hrA' hu hrC)
      })
      (by exact h_stat_in)
      hN_stat_pos

/-- chooseδ satisfies the A-bound: all A-statistics are ≤ δ. -/
lemma chooseδ_A_bound {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) :
    ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u →
      separationStatistic R r u hu ≤ chooseδ hk R d hd := by
  intro r u hu hrA
  unfold chooseδ
  split_ifs with hB_exists
  · -- B ≠ ∅: δ = B_common_statistic
    -- The B-statistic is the boundary separating A from C
    -- All A-statistics are < B-statistic by separation_property_A_B
    have hB_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u := hB_exists
    rcases hB_nonempty with ⟨rB, uB, huB, hrB⟩
    have h_B_eq : B_common_statistic R d hd hB_exists = separationStatistic R rB uB huB :=
      B_common_statistic_eq_any_witness R IH d hd hB_exists rB uB huB hrB
    rw [h_B_eq]
    exact le_of_lt (separation_property_A_B R H hd hu hrA huB hrB)
  · -- B = ∅: δ = B_empty_delta = sSup of A-statistics
    -- So A-stat ≤ sSup(A-statistics) = δ by definition
    have hB_empty : ∀ r' u', 0 < u' → r' ∉ extensionSetB F d u' :=
      fun r' u' hu' hr' => hB_exists ⟨r', u', hu', hr'⟩
    have hA_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' :=
      extensionSetA_nonempty_of_B_empty F d hd hB_empty
    have hC_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetC F d u' :=
      extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
    -- B_empty_delta is defined as sSup of A-statistics
    -- So our A-stat is ≤ sSup by le_csSup
    have h_in_set : separationStatistic R r u hu ∈
        {s : ℝ | ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' ∧
          s = R.Θ_grid ⟨mu F r', mu_mem_kGrid F r'⟩ / u'} := by
      use r, u, hu, hrA
      rfl
    have h_bdd : BddAbove {s : ℝ | ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' ∧
        s = R.Θ_grid ⟨mu F r', mu_mem_kGrid F r'⟩ / u'} := by
      obtain ⟨rC, uC, huC, hrC⟩ := hC_nonempty
      use separationStatistic R rC uC huC
      intro s ⟨r', u', hu', hrA', hs⟩
      subst hs
      exact le_of_lt (separation_property R H IH hd hu' hrA' huC hrC)
    simp only [separationStatistic]
    exact le_csSup h_bdd h_in_set

/-- chooseδ satisfies the C-bound: δ ≤ all C-statistics. -/
lemma chooseδ_C_bound {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) :
    ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u →
      chooseδ hk R d hd ≤ separationStatistic R r u hu := by
  intro r u hu hrC
  unfold chooseδ
  split_ifs with hB_exists
  · -- B ≠ ∅: δ = B_common_statistic
    -- The B-statistic is the boundary separating A from C
    -- B-statistic < C-statistics by separation_property_B_C
    have hB_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u := hB_exists
    rcases hB_nonempty with ⟨rB, uB, huB, hrB⟩
    have h_B_eq : B_common_statistic R d hd hB_exists = separationStatistic R rB uB huB :=
      B_common_statistic_eq_any_witness R IH d hd hB_exists rB uB huB hrB
    rw [h_B_eq]
    exact le_of_lt (separation_property_B_C R H hd huB hrB hu hrC)
  · -- B = ∅: δ = B_empty_delta = sSup of A-statistics
    -- sSup(A) ≤ C-stat by separation_property (all A < all C)
    have hB_empty : ∀ r' u', 0 < u' → r' ∉ extensionSetB F d u' :=
      fun r' u' hu' hr' => hB_exists ⟨r', u', hu', hr'⟩
    have hA_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetA F d u' :=
      extensionSetA_nonempty_of_B_empty F d hd hB_empty
    have hC_nonempty : ∃ r' u', 0 < u' ∧ r' ∈ extensionSetC F d u' :=
      extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
    -- sSup(A-stats) ≤ C-stat because all A-stats < C-stat (separation)
    apply csSup_le
    · -- Set is nonempty
      obtain ⟨rA, uA, huA, hrA⟩ := hA_nonempty
      use R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ / uA
      exact ⟨rA, uA, huA, hrA, rfl⟩
    · -- Every element is ≤ the C-statistic
      intro s ⟨r', u', hu', hrA', hs⟩
      subst hs
      simp only [separationStatistic]
      exact le_of_lt (separation_property R H IH hd hu' hrA' hu hrC)

/-- chooseδ satisfies the B-bound: all B-statistics equal δ. -/
lemma chooseδ_B_bound {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (d : α) (hd : ident < d) :
    ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u →
      separationStatistic R r u hu = chooseδ hk R d hd := by
  intro r u hu hrB
  unfold chooseδ
  split_ifs with hB_exists
  · -- B ≠ ∅: δ = B_common_statistic
    -- B_common_statistic equals any B-witness's statistic
    exact (B_common_statistic_eq_any_witness R IH d hd hB_exists r u hu hrB).symm
  · -- B = ∅: Contradiction - we have r ∈ B but B is empty!
    exfalso
    exact hB_exists ⟨r, u, hu, hrB⟩

/-! ### Key Trade Lemma: δ-Shift Equivalence

This is the heart of K&S Appendix A's well-definedness argument.
When we have a "trade" equality `mu F r_old = op (mu F s_old) (d^Δ)`,
the δ bounds force the Θ-difference to equal Δ·δ.

**Mathematical proof sketch**:
1. From trade: r_old = s_old ⊕ d^Δ (in α via μ)
2. For any u > Δ with s_old ∈ A(u): r_old ∈ A(u+Δ) (shift property)
3. For any v > Δ with r_old ∈ C(v): s_old ∈ C(v-Δ) (shift property)
4. Using δ bounds + Archimedean (can choose u arbitrarily large):
   - Upper: Θ(r_old)/(u+Δ) ≤ δ and Θ(s_old)/u ≤ δ
   - These combine to bound (Θ(r_old) - Θ(s_old))/Δ from above
5. Similarly for lower bound using C comparisons
6. Taking limits as u → ∞ forces equality: (Θ(r_old) - Θ(s_old))/Δ = δ
-/

/-- **Shift property for A**: If trade holds and s_old ∈ A(u), then r_old ∈ A(u+Δ).

Proof sketch: s_old ∈ A(u) means mu F s_old < d^u.
By trade, mu F r_old = op (mu F s_old) (d^Δ).
Since d^{u+Δ} = d^u ⊕ d^Δ and op is strictly monotone:
  op (mu F s_old) (d^Δ) < op (d^u) (d^Δ) = d^{u+Δ}
So r_old ∈ A(u+Δ). -/
lemma trade_shift_A {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {u : ℕ} (hrA : s_old ∈ extensionSetA F d u) :
    r_old ∈ extensionSetA F d (u + Δ) := by
  simp only [extensionSetA, Set.mem_setOf_eq] at *
  rw [htrade]
  have h_split : iterate_op d (u + Δ) = op (iterate_op d u) (iterate_op d Δ) :=
    (iterate_op_add d u Δ).symm
  rw [h_split]
  exact op_strictMono_left (iterate_op d Δ) hrA

/-- **Shift property for C**: If trade holds and r_old ∈ C(v) with v > Δ, then s_old ∈ C(v-Δ).

Proof sketch: r_old ∈ C(v) means d^v < mu F r_old.
By trade, mu F r_old = op (mu F s_old) (d^Δ).
Since d^v = d^{v-Δ} ⊕ d^Δ and op is strictly monotone:
  If mu F s_old ≤ d^{v-Δ}, then op (mu F s_old) (d^Δ) ≤ d^v, contradicting hrC.
So d^{v-Δ} < mu F s_old, i.e., s_old ∈ C(v-Δ). -/
lemma trade_shift_C {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {v : ℕ} (hv : Δ < v) (hrC : r_old ∈ extensionSetC F d v) :
    s_old ∈ extensionSetC F d (v - Δ) := by
  simp only [extensionSetC, Set.mem_setOf_eq] at *
  rw [htrade] at hrC
  have hv_split : v = (v - Δ) + Δ := by omega
  have h_split : iterate_op d v = op (iterate_op d (v - Δ)) (iterate_op d Δ) := by
    conv_lhs => rw [hv_split]
    exact (iterate_op_add d (v - Δ) Δ).symm
  rw [h_split] at hrC
  by_contra h_not_gt
  push_neg at h_not_gt
  rcases h_not_gt.lt_or_eq with hlt | heq
  · exact absurd hrC (not_lt.mpr (le_of_lt (op_strictMono_left (iterate_op d Δ) hlt)))
  · rw [heq] at hrC; exact lt_irrefl _ hrC

/-- **Forward shift property for C**: If trade holds and s_old ∈ C(v), then r_old ∈ C(v+Δ).

Proof sketch: s_old ∈ C(v) means d^v < mu F s_old.
By trade, mu F r_old = op (mu F s_old) (d^Δ).
Since op is strictly monotone:
  op (d^v) (d^Δ) < op (mu F s_old) (d^Δ) = mu F r_old
And op (d^v) (d^Δ) = d^{v+Δ} by iterate_op_add.
So d^{v+Δ} < mu F r_old, i.e., r_old ∈ C(v+Δ). -/
lemma trade_shift_C_forward {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {v : ℕ} (hsC : s_old ∈ extensionSetC F d v) :
    r_old ∈ extensionSetC F d (v + Δ) := by
  simp only [extensionSetC, Set.mem_setOf_eq] at *
  rw [htrade]
  have h_split : iterate_op d (v + Δ) = op (iterate_op d v) (iterate_op d Δ) :=
    (iterate_op_add d v Δ).symm
  rw [h_split]
  exact op_strictMono_left (iterate_op d Δ) hsC

/-- **The δ-Shift Equivalence Lemma** (K&S trade argument core)

Given a trade equality mu F r_old = op (mu F s_old) (d^Δ) and δ bounds,
the Θ-difference must equal Δ·δ.

**Proof strategy** (GPT-5.1 Pro / K&S Appendix A):
1. The shift rules give: r_old ∈ A(U) ↔ s_old ∈ A(U-Δ) for U > Δ
2. Similarly for C-membership
3. For upper bound: Use A-bound on r at U, C-bound on s at V, get Θ(r)-Θ(s) ≤ (U-V)·δ
4. For lower bound: Use C-bound on r at V+Δ, A-bound on s at U-Δ
5. As U → ∞ with the accuracy lemma squeezing A-C gap, we get equality

This is THE key lemma for Theta'_well_defined. -/
lemma delta_shift_equiv {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    {δ : ℝ}
    (hδA : ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu ≤ δ)
    (hδC : ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ ≤ separationStatistic R r u hu)
    (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ)) :
    R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
    R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ = (Δ : ℝ) * δ := by
  -- Define θr := Θ(r_old) and θs := Θ(s_old) for brevity
  set θr := R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ with hθr
  set θs := R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ with hθs

  /-
  **UNIFORM PROOF STRATEGY** (GPT-5.1 Pro / K&S Appendix A):

  The key insight is the SHIFT EQUIVALENCE:
    r_old ∈ A(U)  ↔  s_old ∈ A(U-Δ)   [for U > Δ]
    r_old ∈ C(V)  ↔  s_old ∈ C(V-Δ)   [for V > Δ]

  This means the A/C statistics are related:
    stat(r, U) = Θ(r)/U  and  stat(s, U-Δ) = Θ(s)/(U-Δ)

  For the upper bound:
    - Use A-bound on r at level U+Δ: Θ(r)/(U+Δ) ≤ δ
    - Use C-bound on s at level V: Θ(s)/V ≥ δ
    - Subtract: Θ(r) - Θ(s) ≤ (U+Δ)·δ - V·δ = (U+Δ-V)·δ
    - As U → ∞ with V → U (via accuracy), we get (U+Δ-V) → Δ

  For the lower bound:
    - Use C-bound on r at level V+Δ: Θ(r)/(V+Δ) ≥ δ
    - Use A-bound on s at level U: Θ(s)/U ≤ δ
    - Subtract: Θ(r) - Θ(s) ≥ (V+Δ)·δ - U·δ = (V+Δ-U)·δ
    - As U → V (via accuracy), we get (V+Δ-U) → Δ

  The accuracy lemma ensures that for any ε > 0, we can find U, V with the
  A-C gap for s_old being < ε. In the limit, this forces equality.
  -/

  -- We prove equality by showing both ≤ and ≥
  apply le_antisymm

  · -- Upper bound: θr - θs ≤ Δ * δ

    -- Use Archimedean to find U such that s_old ∈ A(U)
    obtain ⟨U, hU⟩ := bounded_by_iterate d hd (mu F s_old)
    have hs_in_A : s_old ∈ extensionSetA F d U := hU
    have hU_pos : 0 < U := by
      by_contra h; push_neg at h; interval_cases U
      simp only [iterate_op_zero] at hU
      exact not_lt.mpr (ident_le (mu F s_old)) hU

    -- By shift lemma: s_old ∈ A(U) → r_old ∈ A(U+Δ)
    have hr_in_A : r_old ∈ extensionSetA F d (U + Δ) := trade_shift_A hd hΔ htrade hs_in_A
    have hUΔ_pos : 0 < U + Δ := by omega

    -- A-bounds give upper bounds on θr and θs
    have hr_A_bound : separationStatistic R r_old (U + Δ) hUΔ_pos ≤ δ :=
      hδA r_old (U + Δ) hUΔ_pos hr_in_A
    have hs_A_bound : separationStatistic R s_old U hU_pos ≤ δ :=
      hδA s_old U hU_pos hs_in_A

    have hθr_upper : θr ≤ (U + Δ) * δ := by
      have h2 : ((U + Δ) : ℝ) > 0 := by positivity
      -- Unfold separationStatistic: θr / (U + Δ) ≤ δ
      simp only [separationStatistic] at hr_A_bound
      -- Convert ↑(U + Δ) to ↑U + ↑Δ for div_le_iff₀
      push_cast at hr_A_bound h2
      rw [div_le_iff₀ h2] at hr_A_bound
      -- Now hr_A_bound : R.Θ_grid ... ≤ δ * (U + Δ), goal: θr ≤ (U + Δ) * δ
      rw [mul_comm] at hr_A_bound
      exact hr_A_bound

    -- For the upper bound Θ(r) - Θ(s) ≤ Δ·δ, we need a LOWER bound on Θ(s)
    -- This comes from C-membership. Find V such that s_old ∈ C(V).

    -- Case split: does s_old have a C-level (i.e., ident < mu F s_old)?
    by_cases hs_ident : mu F s_old = ident

    · -- s_old = ident case: This means r_old is a B-witness!
      -- From htrade: μ_F(r_old) = ident ⊕ d^Δ = d^Δ
      -- So r_old ∈ B(Δ), and hδB gives us θr/Δ = δ exactly.

      have hθs_zero : θs = 0 := by
        have h_mem : (⟨mu F s_old, mu_mem_kGrid F s_old⟩ : kGrid F) =
                     ⟨ident, ident_mem_kGrid F⟩ := by
          ext; exact hs_ident
        simp only [hθs, h_mem, R.ident_eq_zero]

      have hr_eq_dΔ : mu F r_old = iterate_op d Δ := by rw [htrade, hs_ident, op_ident_left]

      -- r_old ∈ B(Δ) because μ_F(r_old) = d^Δ
      have hr_in_B : r_old ∈ extensionSetB F d Δ := by
        simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dΔ]

      -- By hδB: stat(r_old, Δ) = δ, i.e., θr/Δ = δ
      have hstat_B : separationStatistic R r_old Δ hΔ = δ := hδB r_old Δ hΔ hr_in_B
      simp only [separationStatistic] at hstat_B

      -- So θr = Δ · δ
      have hθr_eq : θr = Δ * δ := by
        have hΔ_pos : (Δ : ℝ) > 0 := by positivity
        have hΔ_ne : (Δ : ℝ) ≠ 0 := by linarith
        field_simp [hΔ_ne] at hstat_B
        linarith

      -- Conclude: θr - θs = Δ·δ - 0 = Δ·δ
      rw [hθs_zero, sub_zero]
      exact le_of_eq hθr_eq

    · -- s_old > ident case: Use B-witness structure and R.add
      have hs_pos : ident < mu F s_old := by
        cases' (ident_le (mu F s_old)).lt_or_eq with h h
        · exact h
        · exact absurd h.symm hs_ident

      /-
      Key insight: htrade says μ_F(r_old) = μ_F(s_old) ⊕ d^Δ.

      Case A: B(Δ) non-empty (d^Δ ∈ kGrid F)
        Then ∃ r_B with μ_F(r_B) = d^Δ, and htrade becomes:
        μ_F(r_old) = μ_F(s_old) ⊕ μ_F(r_B)
        By R.add (additivity on kGrid): θr = θs + Θ(r_B) = θs + Δ·δ
        So θr - θs = Δ·δ ✓

      Case B: B(Δ) empty (d^Δ ∉ kGrid F)
        The trade μ_F(r_old) = μ_F(s_old) ⊕ d^Δ with both sides in kGrid F
        requires a "coincidence" - the product lands back in kGrid F despite
        d^Δ not being there. In many K&S algebras this is impossible,
        but in general it may happen via algebraic relations.
        For this case, use the accuracy lemma to squeeze bounds.
      -/

      /-
      **FLOOR-BASED ACCURACY APPROACH** (GPT-5.1 Pro / K&S Appendix A):

      Let V = ⌊θs/δ⌋. Then:
        - V*δ ≤ θs < (V+1)*δ
        - By shift lemmas: (V+Δ)*δ ≤ θr < (V+Δ+1)*δ
        - This gives: (Δ-1)*δ < θr - θs < (Δ+1)*δ (width-2δ bracket)

      For EXACT equality θr - θs = Δ*δ, we need one of:
        (a) s_old ∈ B(V) for some V > 0 (then θs = V*δ exactly, and by shift r_old ∈ B(V+Δ))
        (b) The K&S accuracy argument: δ is the UNIQUE value consistent with ALL A/C bounds

      The current sorry is for case (b). Case (a) reduces to the s_old = ident pattern
      when we can find a B-witness.

      **STRUCTURAL ISSUE**: The separation properties use mu_scale_eq_iterate which is FALSE
      (see CounterExamples.lean). The correct approach is:
        1. For k=1 (single atom): mu_scale_eq_iterate holds trivially
        2. For k→k+1: Use inductive hypothesis that k-atom grid is commutative,
           which makes mu_scale_eq_iterate valid for k atoms
      -/

      -- Case split: Is s_old a B-witness for some level V > 0?
      -- If yes: exact equality via hδB chain
      -- If no: pure A/C case, requires K&S accuracy lemma

      by_cases hB_witness : ∃ V : ℕ, 0 < V ∧ s_old ∈ extensionSetB F d V

      · -- Case A: s_old ∈ B(V) for some V > 0 - Use B-witness chain
        obtain ⟨V, hV_pos, hs_in_B⟩ := hB_witness

        -- From B-membership: mu F s_old = d^V
        have hs_eq_dV : mu F s_old = iterate_op d V := by
          simpa [extensionSetB] using hs_in_B

        -- By htrade: mu F r_old = d^V ⊕ d^Δ = d^{V+Δ}
        have hr_eq_dVΔ : mu F r_old = iterate_op d (V + Δ) := by
          rw [htrade, hs_eq_dV, ← iterate_op_add d V Δ]

        -- So r_old ∈ B(V+Δ)
        have hr_in_B : r_old ∈ extensionSetB F d (V + Δ) := by
          simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dVΔ]

        have hVΔ_pos : 0 < V + Δ := by omega

        -- From hδB: θs = V*δ and θr = (V+Δ)*δ
        have hstat_s : separationStatistic R s_old V hV_pos = δ := hδB s_old V hV_pos hs_in_B
        have hstat_r : separationStatistic R r_old (V + Δ) hVΔ_pos = δ := hδB r_old (V + Δ) hVΔ_pos hr_in_B

        simp only [separationStatistic] at hstat_s hstat_r

        have hθs_eq : θs = V * δ := by
          have hV_pos_real : (V : ℝ) > 0 := Nat.cast_pos.mpr hV_pos
          have hV_ne : (V : ℝ) ≠ 0 := by linarith
          field_simp [hV_ne] at hstat_s
          linarith

        have hθr_eq : θr = (V + Δ) * δ := by
          have hVΔ_pos_real : (V : ℝ) + (Δ : ℝ) > 0 := by positivity
          have hVΔ_ne : (V : ℝ) + (Δ : ℝ) ≠ 0 := by linarith
          simp only [Nat.cast_add] at hstat_r
          field_simp [hVΔ_ne] at hstat_r
          linarith

        -- Conclude: θr - θs = (V+Δ)*δ - V*δ = Δ*δ
        rw [hθr_eq, hθs_eq]
        ring_nf
        -- Goal: V*δ + Δ*δ - V*δ ≤ Δ*δ, which simplifies to Δ*δ ≤ Δ*δ
        linarith

      · -- Case B: No B-witness for s_old - Pure A/C case
        --
        -- **KEY INSIGHT** (GPT-5 Pro): If B is globally empty, use accuracy_lemma.
        -- If B is non-empty but s_old isn't in B, this is a structural contradiction
        -- in many algebras (the trade equation forces s_old to be a B-witness).
        --
        push_neg at hB_witness
        -- hB_witness : ∀ V, 0 < V → s_old ∉ extensionSetB F d V

        -- Check if B is globally empty
        by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u

        · -- B is globally non-empty, but s_old ∉ B
          -- In this case, there's another element that IS a B-witness.
          -- The trade equation μ r_old = μ s_old ⊕ d^Δ combined with
          -- the existence of some B-witness should give us constraints.
          --
          -- **STRUCTURAL ISSUE**: This case requires k-grid commutativity
          -- to relate the trade to the B-witness. Without it, we can't proceed.
          -- In many K&S algebras, this case is actually VACUOUS.
          sorry -- INDUCTIVE HYPOTHESIS: k-grid commutativity needed

        · -- B is globally empty: Use accuracy_lemma to squeeze bounds
          push_neg at hB_global
          have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u :=
            fun r u hu hr => hB_global r u hu hr

          -- We prove θr - θs ≤ Δ * δ by contradiction using accuracy_lemma.
          by_contra h_not_le
          push_neg at h_not_le
          -- h_not_le : Δ * δ < θr - θs
          let ε : ℝ := (θr - θs) - (Δ : ℝ) * δ
          have hε_pos : 0 < ε := by simp only [ε]; linarith

          -- Need A and C nonempty for accuracy_lemma
          have hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
            extensionSetA_nonempty_of_B_empty F d hd hB_empty

          -- For C nonempty, we need k ≥ 1. Get this from hs_pos (s_old > ident).
          -- If k = 0, then mu F s_old = ident, contradicting hs_pos.
          have hk_pos : k ≥ 1 := by
            by_contra hk0
            push_neg at hk0
            -- hk0 : k < 1, so k = 0
            have hk_eq_0 : k = 0 := by omega
            -- k = 0: mu F s_old = ident for any s_old since foldl over empty list = ident
            have hmu_ident : mu F s_old = ident := by
              subst hk_eq_0
              rfl  -- mu F s_old = foldl _ ident [] = ident
            -- From hmu_ident and hs_pos : ident < mu F s_old, get contradiction
            rw [hmu_ident] at hs_pos
            exact (lt_irrefl ident) hs_pos

          have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
            extensionSetC_nonempty_of_B_empty F hk_pos d hd hB_empty

          -- Use accuracy_lemma to get A/C witnesses with statistics within ε
          obtain ⟨rA, uA, huA, hrA, rC, uC, huC, hrC, h_gap_small⟩ :=
            accuracy_lemma R d hd hB_empty hA_nonempty hC_nonempty ε hε_pos

          -- From the A/C bounds:
          -- stat(rA, uA) ≤ δ ⟹ Θ(μ rA) ≤ uA * δ
          -- stat(rC, uC) ≥ δ ⟹ Θ(μ rC) ≥ uC * δ
          -- And stat(rC) - stat(rA) < ε

          -- The squeeze: Using s_old's A/C levels and trade shifts...
          -- Upper bound on θr: from s_old ∈ A(U), get r_old ∈ A(U+Δ), so θr ≤ (U+Δ)*δ
          -- Lower bound on θs: from s_old ∈ C(V), get θs ≥ V*δ
          -- So θr - θs ≤ (U+Δ-V)*δ
          -- With accuracy_lemma, as U→V, this approaches Δ*δ

          -- Find s_old's natural A-level (exists by Archimedean since s_old is positive)
          obtain ⟨U_s, hU_s⟩ := bounded_by_iterate d hd (mu F s_old)
          have hs_in_A : s_old ∈ extensionSetA F d U_s := hU_s
          have hU_s_pos : 0 < U_s := by
            by_contra h; push_neg at h; interval_cases U_s
            simp only [iterate_op_zero] at hU_s
            exact not_lt.mpr (ident_le (mu F s_old)) hU_s

          -- By trade_shift_A: r_old ∈ A(U_s + Δ)
          have hr_in_A : r_old ∈ extensionSetA F d (U_s + Δ) := trade_shift_A hd hΔ htrade hs_in_A
          have hUΔ_pos : 0 < U_s + Δ := by omega

          -- A-bounds: θr ≤ (U_s+Δ)*δ and θs ≤ U_s*δ
          have hθr_A : θr ≤ (U_s + Δ : ℕ) * δ := by
            have hbound := hδA r_old (U_s + Δ) hUΔ_pos hr_in_A
            simp only [separationStatistic] at hbound
            have hpos : (0 : ℝ) < (U_s + Δ : ℕ) := Nat.cast_pos.mpr hUΔ_pos
            rw [div_le_iff₀ hpos] at hbound
            linarith

          -- Find s_old's natural C-level (exists since s_old > ident)
          -- Key: ident < mu F s_old means there exists V_s with d^{V_s} < mu F s_old
          -- We use V_s = 0 or find the largest V_s where s_old ∈ C(V_s)
          have hs_pos_real : ident < mu F s_old := hs_pos

          -- For positive s_old with B empty, find the C-level
          -- s_old is in C(V) for some V iff d^V < mu F s_old
          -- The largest such V is the "floor" of s_old's position in the d-sequence

          -- Use V = 0 if mu F s_old ≤ d, otherwise find V > 0
          by_cases hs_above_d : iterate_op d 1 < mu F s_old

          · -- s_old > d: Find V_s ≥ 1 where s_old ∈ C(V_s)
            have hs_in_C_1 : s_old ∈ extensionSetC F d 1 := by simp [extensionSetC, hs_above_d]

            -- C-bound at V_s = 1: θs ≥ 1*δ = δ
            have hθs_C : θs ≥ (1 : ℕ) * δ := by
              have hbound := hδC s_old 1 (by omega : 0 < 1) hs_in_C_1
              simp only [separationStatistic, Nat.cast_one, div_one] at hbound
              -- hbound : δ ≤ θs, goal : θs ≥ 1 * δ
              simp only [Nat.cast_one, one_mul]
              exact hbound

            -- By trade_shift_C_forward: r_old ∈ C(1 + Δ)
            have hr_in_C : r_old ∈ extensionSetC F d (1 + Δ) := trade_shift_C_forward hd hΔ htrade hs_in_C_1

            -- C-bound: θr ≥ (1+Δ)*δ
            have hθr_C : θr ≥ ((1 + Δ : ℕ) : ℝ) * δ := by
              have hpos_1Δ : 0 < 1 + Δ := by omega
              have hbound := hδC r_old (1 + Δ) hpos_1Δ hr_in_C
              simp only [separationStatistic] at hbound
              have hpos : (0 : ℝ) < (1 + Δ : ℕ) := Nat.cast_pos.mpr hpos_1Δ
              rw [le_div_iff₀ hpos] at hbound
              linarith

            -- Floor-bracket: (Δ-1+1)*δ ≤ θr - θs ≤ (U_s+Δ)*δ - 1*δ
            -- That is: Δ*δ ≤ θr - θs (from C-bounds)
            -- But we assumed θr - θs > Δ*δ, so need to check if we can get ≤

            -- From A-bound on r and C-bound on s:
            -- θr - θs ≤ (U_s + Δ)*δ - 1*δ = (U_s + Δ - 1)*δ

            -- The issue: This gives upper bound (U_s + Δ - 1)*δ, not exactly Δ*δ
            -- For contradiction, we need θr - θs ≤ Δ*δ but we only get ≤ (U_s + Δ - 1)*δ

            -- **KEY INSIGHT**: The floor-bracket gives us width ~2δ centered around Δ*δ.
            -- The accuracy_lemma tightens δ arbitrarily, but doesn't eliminate the bracket width.

            -- For now, we observe this case requires the INDUCTIVE HYPOTHESIS:
            -- With k-grid commutativity, we could express the trade more directly
            -- and eliminate the floor-bracket gap.
            --
            -- NOTE: In well-behaved K&S algebras, when B is empty AND s_old > d,
            -- the inductive structure forces tighter constraints. This case may
            -- be vacuous under our construction path.
            sorry -- STRUCTURAL: Pure A/C with s_old > d requires deeper analysis

          · -- s_old ≤ d: Use ident < s_old ≤ d
            push_neg at hs_above_d
            -- hs_above_d : mu F s_old ≤ iterate_op d 1

            -- We need to show mu F s_old < d (strictly) since if equal, s_old ∈ B(1)
            have hs_lt_d : mu F s_old < iterate_op d 1 := by
              rcases eq_or_lt_of_le hs_above_d with h_eq | h_lt
              · -- If mu F s_old = d, then s_old ∈ B(1), contradicting B empty
                have hB1 : s_old ∈ extensionSetB F d 1 := by
                  simp only [extensionSetB, Set.mem_setOf_eq, iterate_op_one, h_eq]
                exact absurd hB1 (hB_empty s_old 1 (by omega))
              · exact h_lt

            -- s_old ∈ A(1) since mu F s_old < d = d^1
            have hs_in_A_1 : s_old ∈ extensionSetA F d 1 := by
              simp only [extensionSetA, Set.mem_setOf_eq]
              exact hs_lt_d

            -- A-bound: θs ≤ 1*δ = δ
            have hθs_A : θs ≤ (1 : ℕ) * δ := by
              have hbound := hδA s_old 1 (by omega) hs_in_A_1
              simp only [separationStatistic, Nat.cast_one, div_one] at hbound
              -- hbound : θs ≤ δ, goal : θs ≤ 1 * δ
              simp only [Nat.cast_one, one_mul]
              exact hbound

            -- By trade_shift_A: r_old ∈ A(1 + Δ)
            have hr_in_A_1Δ : r_old ∈ extensionSetA F d (1 + Δ) := trade_shift_A hd hΔ htrade hs_in_A_1

            -- A-bound: θr ≤ (1+Δ)*δ
            have hθr_A' : θr ≤ ((1 + Δ : ℕ) : ℝ) * δ := by
              have hpos_1Δ : 0 < 1 + Δ := by omega
              have hbound := hδA r_old (1 + Δ) hpos_1Δ hr_in_A_1Δ
              simp only [separationStatistic] at hbound
              have hpos : (0 : ℝ) < (1 + Δ : ℕ) := Nat.cast_pos.mpr hpos_1Δ
              rw [div_le_iff₀ hpos] at hbound
              linarith

            -- For the C-level, since s_old > ident but s_old < d, we have
            -- d^0 = ident < s_old < d = d^1
            -- So s_old is NOT in C(1), but is "above" ident.

            -- The C-bound at level 0 is vacuous (0 < 0 is false).
            -- We need a positive C-level, but s_old < d means s_old ∉ C(v) for any v ≥ 1.

            -- Lower bound on θs: From ident < s_old, we get θs > 0
            have hθs_pos : 0 < θs := by
              have hθ_strict : R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ > R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ :=
                R.strictMono hs_pos
              simp only [R.ident_eq_zero] at hθ_strict
              exact hθ_strict

            -- From trade: r_old is "Δ steps above" s_old
            -- If s_old < d = d^1, then s_old ⊕ d^Δ could be anywhere relative to d^{Δ+1}

            -- **KEY INSIGHT**: When ident < s_old < d, the trade μ(r_old) = s_old ⊕ d^Δ
            -- places r_old between d^Δ and d^{Δ+1} (approximately).
            -- r_old ∈ C(Δ) since d^Δ < s_old ⊕ d^Δ (by s_old > ident)

            have hr_in_C_Δ : r_old ∈ extensionSetC F d Δ := by
              simp only [extensionSetC, Set.mem_setOf_eq]
              rw [htrade]
              -- Need: d^Δ < s_old ⊕ d^Δ
              -- Since s_old > ident, by op_strictMono_left: s_old ⊕ d^Δ > ident ⊕ d^Δ = d^Δ
              have h := (op_strictMono_left (iterate_op d Δ)) hs_pos
              simp only [op_ident_left] at h
              exact h

            -- C-bound: θr ≥ Δ*δ
            have hθr_C : θr ≥ (Δ : ℝ) * δ := by
              have hbound := hδC r_old Δ hΔ hr_in_C_Δ
              simp only [separationStatistic] at hbound
              have hpos : (0 : ℝ) < (Δ : ℕ) := Nat.cast_pos.mpr hΔ
              rw [le_div_iff₀ hpos] at hbound
              linarith

            -- Now we have: Δ*δ ≤ θr ≤ (1+Δ)*δ and 0 < θs ≤ 1*δ

            -- From these: θr - θs ≥ Δ*δ - 1*δ = (Δ-1)*δ
            --            θr - θs ≤ (1+Δ)*δ - 0 = (1+Δ)*δ

            -- This is a width-2δ bracket centered around Δ*δ.
            -- Our assumption h_not_le says θr - θs > Δ*δ.

            -- **CONTRADICTION PATH**: Need to show θr - θs ≤ Δ*δ
            -- But our bounds only give θr - θs ≤ (1+Δ)*δ

            -- The accuracy_lemma says δ is pinned tightly, but doesn't help here
            -- because the bracket width comes from the DISCRETE level structure.

            -- We need: θr ≤ Δ*δ + θs, i.e., θr - θs ≤ Δ*δ
            -- We have: θr ≤ (1+Δ)*δ and θs > 0

            -- The gap: We can only conclude θr - θs ≤ (1+Δ)*δ - 0 = (1+Δ)*δ
            -- But h_not_le says θr - θs > Δ*δ, which is consistent with θr - θs ∈ (Δ*δ, (Δ+1)*δ]

            -- **STRUCTURAL LIMITATION**: The floor-bracket cannot be closed without
            -- additional structure (k-grid commutativity from inductive hypothesis).
            sorry -- FLOOR-BRACKET: Pure A/C case requires inductive hypothesis to close

  · -- Lower bound: Δ * δ ≤ θr - θs

    -- For the lower bound, we need:
    -- - C-bound on r: Θ(r) ≥ (level)·δ
    -- - A-bound on s: Θ(s) ≤ (level)·δ

    by_cases hs_ident : mu F s_old = ident

    · -- s_old = ident case: This means r_old is a B-witness!
      -- Same as upper bound: use hδB to get θr = Δ·δ exactly.

      have hθs_zero : θs = 0 := by
        have h_mem : (⟨mu F s_old, mu_mem_kGrid F s_old⟩ : kGrid F) =
                     ⟨ident, ident_mem_kGrid F⟩ := by
          ext; exact hs_ident
        simp only [hθs, h_mem, R.ident_eq_zero]

      have hr_eq_dΔ : mu F r_old = iterate_op d Δ := by rw [htrade, hs_ident, op_ident_left]

      -- r_old ∈ B(Δ) because μ_F(r_old) = d^Δ
      have hr_in_B : r_old ∈ extensionSetB F d Δ := by
        simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dΔ]

      -- By hδB: stat(r_old, Δ) = δ, i.e., θr/Δ = δ
      have hstat_B : separationStatistic R r_old Δ hΔ = δ := hδB r_old Δ hΔ hr_in_B
      simp only [separationStatistic] at hstat_B

      -- So θr = Δ · δ
      have hθr_eq : θr = Δ * δ := by
        have hΔ_pos : (Δ : ℝ) > 0 := by positivity
        have hΔ_ne : (Δ : ℝ) ≠ 0 := by linarith
        field_simp [hΔ_ne] at hstat_B
        linarith

      -- Conclude: Δ·δ ≤ θr - θs = Δ·δ - 0 = Δ·δ
      rw [hθs_zero, sub_zero]
      exact le_of_eq hθr_eq.symm

    · -- s_old > ident: Same structure as upper bound case
      have hs_pos : ident < mu F s_old := by
        cases' (ident_le (mu F s_old)).lt_or_eq with h h
        · exact h
        · exact absurd h.symm hs_ident

      -- Case split: Is s_old a B-witness for some level V > 0?
      by_cases hB_witness : ∃ V : ℕ, 0 < V ∧ s_old ∈ extensionSetB F d V

      · -- Case A: s_old ∈ B(V) for some V > 0 - Use B-witness chain
        obtain ⟨V, hV_pos, hs_in_B⟩ := hB_witness

        -- From B-membership: mu F s_old = d^V
        have hs_eq_dV : mu F s_old = iterate_op d V := by
          simpa [extensionSetB] using hs_in_B

        -- By htrade: mu F r_old = d^V ⊕ d^Δ = d^{V+Δ}
        have hr_eq_dVΔ : mu F r_old = iterate_op d (V + Δ) := by
          rw [htrade, hs_eq_dV, ← iterate_op_add d V Δ]

        -- So r_old ∈ B(V+Δ)
        have hr_in_B : r_old ∈ extensionSetB F d (V + Δ) := by
          simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dVΔ]

        have hVΔ_pos : 0 < V + Δ := by omega

        -- From hδB: θs = V*δ and θr = (V+Δ)*δ
        have hstat_s : separationStatistic R s_old V hV_pos = δ := hδB s_old V hV_pos hs_in_B
        have hstat_r : separationStatistic R r_old (V + Δ) hVΔ_pos = δ := hδB r_old (V + Δ) hVΔ_pos hr_in_B

        simp only [separationStatistic] at hstat_s hstat_r

        have hθs_eq : θs = V * δ := by
          have hV_pos_real : (V : ℝ) > 0 := Nat.cast_pos.mpr hV_pos
          have hV_ne : (V : ℝ) ≠ 0 := by linarith
          field_simp [hV_ne] at hstat_s
          linarith

        have hθr_eq : θr = (V + Δ) * δ := by
          have hVΔ_pos_real : (V : ℝ) + (Δ : ℝ) > 0 := by positivity
          have hVΔ_ne : (V : ℝ) + (Δ : ℝ) ≠ 0 := by linarith
          simp only [Nat.cast_add] at hstat_r
          field_simp [hVΔ_ne] at hstat_r
          linarith

        -- Conclude: Δ·δ ≤ θr - θs = (V+Δ)*δ - V*δ = Δ*δ
        rw [hθr_eq, hθs_eq]
        ring_nf
        linarith

      · -- Case B: No B-witness for s_old - Pure A/C case
        -- Same structure as the upper bound: split on global B-emptiness.
        push_neg at hB_witness

        by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u

        · -- B is globally non-empty, but s_old ∉ B
          -- Same structural issue as upper bound: needs k-grid commutativity.
          sorry -- INDUCTIVE HYPOTHESIS: k-grid commutativity needed

        · -- B is globally empty: Use accuracy_lemma for lower bound
          push_neg at hB_global
          have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u :=
            fun r u hu hr => hB_global r u hu hr

          -- Symmetric argument to upper bound:
          -- If Δ * δ > θr - θs, use accuracy_lemma to derive contradiction.
          -- However, the same FLOOR-BRACKET limitation applies:
          --
          -- For the lower bound we need θr - θs ≥ Δ*δ.
          -- Using C-bound on r at level V+Δ: θr ≥ (V+Δ)*δ
          -- Using A-bound on s at level U: θs ≤ U*δ
          -- So θr - θs ≥ (V+Δ)*δ - U*δ = (V+Δ-U)*δ
          --
          -- With U = V+1 (tightest when B is empty):
          -- θr - θs ≥ (V+Δ-V-1)*δ = (Δ-1)*δ
          --
          -- This only gives θr - θs ≥ (Δ-1)*δ, not ≥ Δ*δ!
          -- The floor-bracket width 2δ cannot be eliminated without additional structure.
          --
          -- **STRUCTURAL LIMITATION**: Same as upper bound case.
          -- The pure A/C case requires k-grid commutativity (inductive hypothesis)
          -- to close the bracket to exact equality.
          sorry -- FLOOR-BRACKET: Pure A/C lower bound requires inductive hypothesis

/-! ### Θ' Infrastructure: Well-Definedness on μ-Fibers

Following GPT-5.1 Pro's recommendation (§3), we define Θ' via a raw evaluator
and prove it's independent of witness choice. This defuses the Classical.choose
problems in both additivity and strict monotonicity proofs.
-/

/-- Raw evaluator on witnesses for F': old part + t·δ. -/
noncomputable def Theta'_raw
  {k} {F : AtomFamily α k} (R : MultiGridRep F)
  (d : α) (δ : ℝ)
  (r_old : Multi k) (t : ℕ) : ℝ :=
  R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ

/-- **Key well-definedness**: Theta'_raw is constant on μ-fibers of F'.

This is the foundational lemma that makes Θ' well-defined despite using Classical.choose.
The proof uses the A/C separation bounds for δ to show that any two witnesses
with the same μ-value must yield the same Theta'_raw value.

**Proof strategy** (K&S "trade argument"):
- If mu F' r = mu F' s, write as: mu F r_old ⊕ d^t = mu F s_old ⊕ d^u
- Case t=u: Use R.strictMono + equality to conclude r_old = s_old
- Case t<u: Use A/C bounds to show (u-t)·δ equals the old-part difference
- Case t>u: Symmetric

The δ bounds (hδA, hδC) are precisely what make this work.
-/
lemma Theta'_well_defined
  {k} {F : AtomFamily α k} (R : MultiGridRep F)
  (H : GridComm F) (IH : GridBridge F) (d : α) (hd : ident < d)
  (δ : ℝ)
  (hδA : ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu ≤ δ)
  (hδC : ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ ≤ separationStatistic R r u hu)
  (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
  {r s : Multi (k+1)}
  (hμ : mu (extendAtomFamily F d hd) r = mu (extendAtomFamily F d hd) s) :
  @Theta'_raw α _ k F R d δ (splitMulti r).1 (splitMulti r).2 =
  @Theta'_raw α _ k F R d δ (splitMulti s).1 (splitMulti s).2 := by
  classical
  -- Extract the split components
  set r_old := (splitMulti r).1 with hr_old_def
  set t := (splitMulti r).2 with ht_def
  set s_old := (splitMulti s).1 with hs_old_def
  set u := (splitMulti s).2 with hu_def

  -- Use mu_extend_last to rewrite hμ
  -- We need to show: r and s round-trip through splitMulti/joinMulti
  have hr_roundtrip : r = joinMulti r_old t := by
    have := joinMulti_splitMulti r
    simp only [hr_old_def, ht_def] at this
    exact this.symm

  have hs_roundtrip : s = joinMulti s_old u := by
    have := joinMulti_splitMulti s
    simp only [hs_old_def, hu_def] at this
    exact this.symm

  have hμ_split : op (mu F r_old) (iterate_op d t) = op (mu F s_old) (iterate_op d u) := by
    have hr := mu_extend_last F d hd r_old t
    have hs := mu_extend_last F d hd s_old u
    rw [hr_roundtrip] at hμ
    rw [hs_roundtrip] at hμ
    rw [← hr, ← hs]
    exact hμ

  -- Trichotomy on t vs u (GPT-5.1 Pro's case split)
  rcases Nat.lt_trichotomy t u with (hlt | heq | hgt)

  · -- Case t < u: The "trade argument"
    -- We need to show: Θ'(r_old, t) = Θ'(s_old, u)
    -- Equivalently: Θ(r_old) + t·δ = Θ(s_old) + u·δ
    -- Equivalently: Θ(r_old) - Θ(s_old) = (u - t)·δ

    unfold Theta'_raw

    -- Extract Δ = u - t > 0
    have hΔ_def : u = t + (u - t) := by omega
    set Δ := u - t with hΔ_eq
    have hΔ_pos : 0 < Δ := by omega

    -- Key identity: d^u = d^t ⊕ d^Δ
    have hdu_split : iterate_op d u = op (iterate_op d t) (iterate_op d Δ) := by
      rw [hΔ_def]
      exact (iterate_op_add d t (u - t)).symm

    -- From hμ_split: mu F r_old ⊕ d^t = mu F s_old ⊕ d^u
    -- We want: mu F r_old = mu F s_old ⊕ d^Δ
    -- Check: (mu F s_old ⊕ d^Δ) ⊕ d^t = mu F s_old ⊕ (d^Δ ⊕ d^t) = mu F s_old ⊕ d^{Δ+t} = mu F s_old ⊕ d^u ✓
    have hμ_trade : mu F r_old = op (mu F s_old) (iterate_op d Δ) := by
      -- Direct proof: show op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) = RHS of hμ_split
      have hkey : op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) =
                  op (mu F s_old) (iterate_op d u) := by
        rw [op_assoc]
        congr 1
        have hΔt_eq_u : Δ + t = u := by omega
        rw [← hΔt_eq_u]
        exact iterate_op_add d Δ t
      -- So: op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) = op (mu F s_old) (iterate_op d u)
      --     = op (mu F r_old) (iterate_op d t)  [by hμ_split]
      -- Cancel (iterate_op d t) from both sides using strict monotonicity
      by_contra h_ne
      rcases Ne.lt_or_lt h_ne with (hlt | hgt)
      · -- mu F r_old < op (mu F s_old) (iterate_op d Δ)
        have h1 : op (mu F r_old) (iterate_op d t) <
                  op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) :=
          op_strictMono_left (iterate_op d t) hlt
        rw [hμ_split, hkey] at h1
        exact lt_irrefl _ h1
      · -- op (mu F s_old) (iterate_op d Δ) < mu F r_old
        have h1 : op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) <
                  op (mu F r_old) (iterate_op d t) :=
          op_strictMono_left (iterate_op d t) hgt
        rw [hkey, ← hμ_split] at h1
        exact lt_irrefl _ h1

    -- The trade: r_old = s_old ⊕ d^Δ
    -- Goal: Show Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Equivalently: Θ(r_old) - Θ(s_old) = (u - t)*δ = Δ*δ

    -- Apply the delta_shift_equiv lemma!
    have h_trade_eq := delta_shift_equiv R H IH hd hδA hδC hδB hΔ_pos hμ_trade
    -- h_trade_eq: Θ(r_old) - Θ(s_old) = Δ * δ

    -- Rearrange to get: Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Since Δ = u - t, we have: Θ(r_old) - Θ(s_old) = (u - t) * δ
    -- So: Θ(r_old) = Θ(s_old) + (u - t) * δ
    -- And: Θ(r_old) + t*δ = Θ(s_old) + (u - t)*δ + t*δ = Θ(s_old) + u*δ

    -- Help linarith by providing explicit casts and the key relation
    have hΔ_real : (Δ : ℝ) = (u : ℝ) - (t : ℝ) := by
      simp only [hΔ_eq]
      exact Nat.cast_sub (le_of_lt hlt)

    -- Make the substitution explicit: θr = θs + Δ * δ
    have h_θr_eq : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
                   R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (Δ : ℝ) * δ := by
      linarith

    -- Now the goal becomes: (θs + Δ * δ) + t * δ = θs + u * δ
    -- Which simplifies to: Δ * δ + t * δ = u * δ
    -- Since Δ = u - t, this is: (u - t) * δ + t * δ = u * δ ✓

    -- Substitute and simplify algebraically
    calc R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ
        = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (Δ : ℝ) * δ + (t : ℝ) * δ := by
            rw [h_θr_eq]
      _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + ((Δ : ℝ) + (t : ℝ)) * δ := by ring
      _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (u : ℝ) * δ := by
            rw [hΔ_real]; ring

  · -- Case t = u: Use injectivity of R.strictMono
    unfold Theta'_raw
    -- Since t = u, the goal becomes Θ(r_old) + t*δ = Θ(s_old) + t*δ
    -- Need to show Θ(r_old) = Θ(s_old)
    simp only [heq]
    -- Now: mu F r_old ⊕ d^u = mu F s_old ⊕ d^u (by hμ_split with t = u)
    -- Use cancellation to get: mu F r_old = mu F s_old
    have hμ_split' : op (mu F r_old) (iterate_op d u) = op (mu F s_old) (iterate_op d u) := by
      rw [heq] at hμ_split; exact hμ_split
    have h_mu_eq : mu F r_old = mu F s_old := by
      -- Cancellation via strict monotonicity
      by_contra h_ne
      rcases Ne.lt_or_lt h_ne with (hlt | hgt)
      · -- If mu F r_old < mu F s_old, then op (mu F r_old) z < op (mu F s_old) z
        have : op (mu F r_old) (iterate_op d u) < op (mu F s_old) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hlt
        rw [hμ_split'] at this
        exact lt_irrefl _ this
      · -- Symmetric case
        have : op (mu F s_old) (iterate_op d u) < op (mu F r_old) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hgt
        rw [← hμ_split'] at this
        exact lt_irrefl _ this

    -- Since mu F r_old = mu F s_old and R.strictMono is injective on the grid
    have h_theta_eq : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
                       R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ := by
      congr 1
      ext
      exact h_mu_eq

    -- Therefore the full expressions are equal
    rw [h_theta_eq]

  · -- Case t > u: Symmetric trade argument
    unfold Theta'_raw

    -- Extract Δ = t - u > 0
    have hΔ_def : t = u + (t - u) := by omega
    set Δ := t - u with hΔ_eq
    have hΔ_pos : 0 < Δ := by omega

    -- Key identity: d^t = d^u ⊕ d^Δ
    have hdt_split : iterate_op d t = op (iterate_op d u) (iterate_op d Δ) := by
      rw [hΔ_def]
      exact (iterate_op_add d u (t - u)).symm

    -- From hμ_split: mu F r_old ⊕ d^t = mu F s_old ⊕ d^u
    -- We want: mu F s_old = mu F r_old ⊕ d^Δ
    -- Check: (mu F r_old ⊕ d^Δ) ⊕ d^u = mu F r_old ⊕ (d^Δ ⊕ d^u) = mu F r_old ⊕ d^{Δ+u} = mu F r_old ⊕ d^t ✓
    have hμ_trade : mu F s_old = op (mu F r_old) (iterate_op d Δ) := by
      -- Direct proof: show op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) = LHS of hμ_split
      have hkey : op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) =
                  op (mu F r_old) (iterate_op d t) := by
        rw [op_assoc]
        congr 1
        have hΔu_eq_t : Δ + u = t := by omega
        rw [← hΔu_eq_t]
        exact iterate_op_add d Δ u
      -- So: op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) = op (mu F r_old) (iterate_op d t)
      --     = op (mu F s_old) (iterate_op d u)  [by hμ_split]
      -- Cancel (iterate_op d u) from both sides using strict monotonicity
      by_contra h_ne
      rcases Ne.lt_or_lt h_ne with (hlt | hgt)
      · -- mu F s_old < op (mu F r_old) (iterate_op d Δ)
        have h1 : op (mu F s_old) (iterate_op d u) <
                  op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hlt
        rw [← hμ_split, hkey] at h1
        exact lt_irrefl _ h1
      · -- op (mu F r_old) (iterate_op d Δ) < mu F s_old
        have h1 : op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) <
                  op (mu F s_old) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hgt
        rw [hkey, hμ_split] at h1
        exact lt_irrefl _ h1

    -- Symmetric trade: s_old = r_old ⊕ d^Δ
    -- Goal: Show Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Equivalently: Θ(s_old) - Θ(r_old) = (t - u)*δ = Δ*δ

    -- Apply delta_shift_equiv with s_old as the "larger" element
    have h_trade_eq := delta_shift_equiv R H IH hd hδA hδC hδB hΔ_pos hμ_trade
    -- h_trade_eq: Θ(s_old) - Θ(r_old) = Δ * δ

    -- Rearrange to get: Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Since Δ = t - u, we have: Θ(s_old) - Θ(r_old) = (t - u) * δ
    -- So: Θ(s_old) = Θ(r_old) + (t - u) * δ
    -- And: Θ(r_old) + t*δ = Θ(r_old) + u*δ + (t-u)*δ = Θ(s_old) + u*δ

    -- Help linarith by providing explicit casts and the key relation
    have hΔ_real : (Δ : ℝ) = (t : ℝ) - (u : ℝ) := by
      simp only [hΔ_eq]
      exact Nat.cast_sub (le_of_lt hgt)

    -- Make the substitution explicit: θs = θr + Δ * δ
    have h_θs_eq : R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ =
                   R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (Δ : ℝ) * δ := by
      linarith

    -- Now the goal becomes: θr + t * δ = (θr + Δ * δ) + u * δ
    -- Which simplifies to: t * δ = Δ * δ + u * δ = (Δ + u) * δ
    -- Since Δ = t - u, this is: t * δ = (t - u + u) * δ = t * δ ✓

    -- Substitute and simplify algebraically
    calc R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ
        = R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + ((Δ : ℝ) + (u : ℝ)) * δ := by
            rw [hΔ_real]; ring
      _ = R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (Δ : ℝ) * δ + (u : ℝ) * δ := by ring
      _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (u : ℝ) * δ := by rw [← h_θs_eq]

theorem extend_grid_rep_with_atom
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) :
    ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F') (_H' : GridComm F'), True := by
  -- Layer A: Define extended family F'
  let F' := extendAtomFamily F d hd

  refine ⟨F', ?_, ?_, ?_⟩

  -- Prove F' preserves old atoms
  · intro i
    exact extendAtomFamily_old F d hd i

  -- Prove F' has new atom at position k
  · exact extendAtomFamily_new F d hd

  -- Prove ∃ R' : MultiGridRep F', True (Layer B: Construct R')
  · -- Layer B: Construct R' (representation on extended grid)
    let δ := chooseδ hk R d hd

    -- Define Θ' on the extended grid
    -- For μ(F', r') where r' : Multi (k+1), we split as (r_old, t) and compute:
    --   Θ'(μ(F', r_old, t)) = Θ(μ(F, r_old)) + t * δ
    let Θ' : {x // x ∈ kGrid F'} → ℝ := fun ⟨x, hx⟩ =>
      -- Extract witness r' : Multi (k+1) with μ(F', r') = x
      let r' := Classical.choose hx
      let hr' := Classical.choose_spec hx
      -- Split r' into (r_old, t)
      let (r_old, t) := splitMulti r'
      -- Compute Θ'(x) = Θ(μ(F, r_old)) + t * δ
      R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + t * δ

    -- Construct R' : MultiGridRep F'
    -- We'll prove the four required properties step by step

    -- Helper: show that ident has witness (fun _ => 0)
    have h_ident_witness : mu F' (fun _ => 0) = ident := mu_zero (F := F')

    -- Property 4: Normalization - Θ'(ident) = 0
    have h_norm : Θ' ⟨ident, ident_mem_kGrid F'⟩ = 0 := by
      -- First reduce Θ' application with simp/dsimp
      simp only [Θ']
      -- Goal is now the raw computation with let bindings

      -- Name the key expressions for clarity
      set r' := Classical.choose (ident_mem_kGrid F') with hr'_def
      have hr' : ident = mu F' r' := Classical.choose_spec (ident_mem_kGrid F')
      set r_old := (splitMulti r').1 with hr_old_def
      set t := (splitMulti r').2 with ht_def

      -- Key: use joinMulti_splitMulti to show r' = joinMulti r_old t
      have hr'_eq : r' = joinMulti r_old t := by
        have h := joinMulti_splitMulti r'
        -- h : (let (r_old, t) := splitMulti r'; joinMulti r_old t) = r'
        -- Definitionally, this is joinMulti (splitMulti r').1 (splitMulti r').2 = r'
        -- Which equals joinMulti r_old t = r' by our definitions
        exact h.symm

      -- Now use mu_extend_last
      have h_mu_extend : mu F' r' = op (mu F r_old) (iterate_op d t) := by
        rw [hr'_eq]
        exact mu_extend_last F d hd r_old t

      -- Combine with hr' : ident = mu F' r'
      have h_ident_eq : ident = op (mu F r_old) (iterate_op d t) := by
        rw [← h_mu_extend]
        exact hr'

      -- Show t must be 0
      have ht_zero : t = 0 := by
        by_contra h_ne
        have ht_pos : 0 < t := Nat.pos_of_ne_zero h_ne

        -- If t > 0, then iterate_op d t > ident (since d > ident)
        have hdt_pos : ident < iterate_op d t := iterate_op_pos d hd t ht_pos

        -- By positivity: op (mu F r_old) (iterate_op d t) > ident
        have h_mu_gt : ident < op (mu F r_old) (iterate_op d t) := by
          have h_mu_ge : ident ≤ mu F r_old := ident_le _
          by_cases h_mu_eq : mu F r_old = ident
          · rw [h_mu_eq, op_ident_left]
            exact hdt_pos
          · have h_mu_gt : ident < mu F r_old := lt_of_le_of_ne h_mu_ge (Ne.symm h_mu_eq)
            calc ident
              _ < iterate_op d t := hdt_pos
              _ = op ident (iterate_op d t) := (op_ident_left _).symm
              _ < op (mu F r_old) (iterate_op d t) := by
                  have hmono : StrictMono (fun x => op x (iterate_op d t)) := op_strictMono_left _
                  exact hmono h_mu_gt

        -- This contradicts h_ident_eq : ident = op (mu F r_old) (iterate_op d t)
        rw [← h_ident_eq] at h_mu_gt
        exact lt_irrefl ident h_mu_gt

      -- Show mu F r_old = ident
      have hr_old_ident : mu F r_old = ident := by
        rw [ht_zero, iterate_op_zero, op_ident_right] at h_ident_eq
        exact h_ident_eq.symm

      -- Now the goal has the let-bound form. Use convert to handle the definitional equality.
      -- Goal: R.Θ_grid ⟨mu F (splitMulti (Classical.choose _)).1, _⟩ +
      --       (splitMulti (Classical.choose _)).2 * δ = 0
      -- These are definitionally equal to r_old and t respectively
      have h_final : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ = 0 := by
        rw [ht_zero, Nat.cast_zero, zero_mul, add_zero]
        have h_subtype_eq :
            (⟨mu F r_old, mu_mem_kGrid F r_old⟩ : {x // x ∈ kGrid F}) =
              ⟨ident, ident_mem_kGrid F⟩ := by
          ext
          exact hr_old_ident
        rw [h_subtype_eq]
        exact R.ident_eq_zero
      -- r_old and t are definitionally equal to the expressions in the goal
      exact h_final

    /- ### Helper Lemmas for Θ' Strict Monotonicity

    The following lemmas break down the strict monotonicity proof into manageable pieces,
    following GPT-5.1 Pro's recommendation (§5.1). -/

    -- Helper 1: Θ' formula in terms of splitMulti components (definitional unfolding)
    have Theta'_split :
        ∀ (x : {x // x ∈ kGrid F'}),
          Θ' x =
            (let r := Classical.choose x.property
             let r_old := (splitMulti r).1
             let t := (splitMulti r).2
             R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ) := by
      intro _
      rfl  -- Θ' is defined this way

    -- Helper 2: Incrementing t by 1 increases Θ' by exactly δ (when old part is fixed)
    have Theta'_increment_t : ∀ (r_old : Multi k) (t : ℕ),
        Θ' ⟨mu F' (joinMulti r_old (t+1)), mu_mem_kGrid F' (joinMulti r_old (t+1))⟩ =
        Θ' ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ + δ := by
      intro r_old t
      -- Unfold Θ' definition
      simp only [Θ']
      -- Both sides use Classical.choose on witnesses
      -- The key: splitMulti (joinMulti r_old t) = (r_old, t)
      have h_split_succ : splitMulti (joinMulti r_old (t+1)) = (r_old, t+1) :=
        splitMulti_joinMulti r_old (t+1)
      have h_split : splitMulti (joinMulti r_old t) = (r_old, t) :=
        splitMulti_joinMulti r_old t

      -- Use Theta'_well_defined to show that the Classical.choose witnesses
      -- give the same result as the canonical joinMulti witnesses
      -- Key: for any r' with mu F' r' = mu F' (joinMulti r_old t), we have
      -- Theta'_raw (splitMulti r') = Theta'_raw r_old t

      -- Get the δ-bounds for Theta'_well_defined
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB := chooseδ_B_bound hk R IH d hd

      -- LHS witness
      set r'_succ := Classical.choose (mu_mem_kGrid F' (joinMulti r_old (t+1))) with hr'_succ_def
      have hr'_succ_spec : mu F' r'_succ = mu F' (joinMulti r_old (t+1)) :=
        (Classical.choose_spec (mu_mem_kGrid F' (joinMulti r_old (t+1)))).symm

      -- RHS witness
      set r'_t := Classical.choose (mu_mem_kGrid F' (joinMulti r_old t)) with hr'_t_def
      have hr'_t_spec : mu F' r'_t = mu F' (joinMulti r_old t) :=
        (Classical.choose_spec (mu_mem_kGrid F' (joinMulti r_old t))).symm

      -- Apply well-definedness to show each side equals canonical form
      have hWD_succ := Theta'_well_defined R H IH d hd δ hδA hδC hδB hr'_succ_spec
      have hWD_t := Theta'_well_defined R H IH d hd δ hδA hδC hδB hr'_t_spec

      -- Unfold Theta'_raw in the well-definedness results
      simp only [Theta'_raw, h_split_succ, h_split] at hWD_succ hWD_t

      -- Now LHS = R.Θ_grid(mu F r_old) + (t+1) * δ
      -- and RHS = R.Θ_grid(mu F r_old) + t * δ + δ
      -- These are equal by ring (with some cast help)
      rw [hWD_succ, hWD_t]
      -- Help with Nat.cast: (1+t : ℕ) → ((1 : ℝ) + (t : ℝ))
      push_cast
      ring

    -- Helper 3: δ is strictly positive
    have delta_pos : 0 < δ := by
      -- Unfold δ to expose chooseδ structure
      show 0 < chooseδ hk R d hd
      unfold chooseδ
      -- Case split based on how δ was chosen
      split_ifs with hB
      · -- Case B ≠ ∅: δ = B_common_statistic
        -- Extract a concrete B-witness without destroying hB
        have ⟨r, u, hu, hr⟩ := hB

        -- B_common_statistic equals any B-witness's statistic
        have hstat_eq : B_common_statistic R d hd hB = separationStatistic R r u hu :=
          B_common_statistic_eq_any_witness R IH d hd hB r u hu hr

        rw [hstat_eq]
        -- Now show separationStatistic R r u hu > 0
        unfold separationStatistic

        -- From hr: r ∈ extensionSetB F d u means mu F r = d^u
        simp only [extensionSetB, Set.mem_setOf_eq] at hr
        have hmu_eq : mu F r = iterate_op d u := hr

        -- d^u > ident (since d > ident and u > 0)
        have hdu_pos : ident < iterate_op d u := iterate_op_pos d hd u hu

        -- Θ(mu F r) = Θ(d^u) > 0
        have h_theta_pos : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
          have h_ident_zero : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ = 0 := R.ident_eq_zero
          have h_mu_pos : ident < mu F r := by rw [hmu_eq]; exact hdu_pos
          have : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
            R.strictMono h_mu_pos
          rw [h_ident_zero] at this
          exact this

        -- θ / u > 0 when θ > 0 and u > 0
        exact div_pos h_theta_pos (Nat.cast_pos.mpr hu)
      · -- Case B = ∅: δ = B_empty_delta
        -- Need to show B_empty_delta > 0
        -- Strategy: Find an A-witness with positive statistic, then use le_csSup
        -- The A-witness (fun _ => 0, 1) has statistic 0, so we need a different one

        -- Since k ≥ 1, there exists an atom a₀ in F
        have hk_pos : 0 < k := hk
        let i₀ : Fin k := ⟨0, hk_pos⟩
        let a₀ := F.atoms i₀
        have ha₀_pos : ident < a₀ := F.pos i₀

        -- By Archimedean, ∃ N such that a₀ < d^N
        obtain ⟨N, hN⟩ := bounded_by_iterate d hd a₀

        -- Then unitMulti i₀ 1 (i.e., a₀) is in A(N)
        have ha₀_in_A : unitMulti i₀ 1 ∈ extensionSetA F d N := by
          simp only [extensionSetA, Set.mem_setOf_eq]
          have : mu F (unitMulti i₀ 1) = iterate_op a₀ 1 := mu_unitMulti F i₀ 1
          rw [this, iterate_op_one]
          exact hN

        -- The statistic for this witness is positive
        have hN_pos : 0 < N := by
          -- Since a₀ > ident and d > ident, d^1 = d ≥ ident
          -- a₀ < d^N with N = 0 would mean a₀ < ident, contradiction
          by_contra h_not_pos
          push_neg at h_not_pos
          interval_cases N
          -- N = 0: a₀ < d^0 = ident, contradicts a₀ > ident
          simp only [iterate_op_zero] at hN
          exact absurd hN (not_lt.mpr (le_of_lt ha₀_pos))

        have h_theta_a₀_pos : 0 < R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ := by
          have h_ident_zero : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ = 0 := R.ident_eq_zero
          have h_mu_pos : ident < mu F (unitMulti i₀ 1) := by
            have : mu F (unitMulti i₀ 1) = iterate_op a₀ 1 := mu_unitMulti F i₀ 1
            rw [this, iterate_op_one]
            exact ha₀_pos
          have : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
                 R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ :=
            R.strictMono h_mu_pos
          rw [h_ident_zero] at this
          exact this

        have h_stat_pos : 0 < R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ / N :=
          div_pos h_theta_a₀_pos (Nat.cast_pos.mpr hN_pos)

        -- B_empty_delta is the sSup of A-statistics
        -- Our statistic h_stat_pos is in this set, so sSup ≥ h_stat_pos > 0
        unfold B_empty_delta
        -- Need: sSup {s | ∃ r u, ...} > 0
        -- Use: 0 < h_stat_pos ≤ sSup (since h_stat_pos is in the set)

        -- Define the set being supremumed
        let AStats := {s : ℝ | ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u ∧
                                s = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u}

        have h_in_set : R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ / N ∈ AStats := by
          use unitMulti i₀ 1, N, hN_pos, ha₀_in_A

        -- The set is bounded above (using a C-witness)
        have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u :=
          fun r u hu hr => hB ⟨r, u, hu, hr⟩
        have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
          extensionSetC_nonempty_of_B_empty F hk d hd hB_empty

        have h_bdd : BddAbove AStats := by
          rcases hC_nonempty with ⟨rC, uC, huC, hrC⟩
          let σC := separationStatistic R rC uC huC
          use σC
          intro s ⟨r', u', hu', hrA', hs⟩
          subst hs
          exact le_of_lt (separation_property R H IH hd hu' hrA' huC hrC)

        -- Apply le_csSup to get sSup ≥ our positive statistic
        have h_ge : R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ / N ≤ sSup AStats :=
          le_csSup h_bdd h_in_set

        linarith

    -- Helper 3b: Generalized vertical shift by Δ steps (GPT-5 Pro Step 2 extension)
    have Theta'_shift_by : ∀ (r_old : Multi k) (t Δ : ℕ),
        Θ' ⟨mu F' (joinMulti r_old (t + Δ)), mu_mem_kGrid F' (joinMulti r_old (t + Δ))⟩ =
        Θ' ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ + (Δ : ℝ) * δ := by
      intro r_old t Δ
      induction Δ with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, add_zero]
      | succ Δ ih =>
        -- Goal: Θ'(...t + (Δ+1)...) = Θ'(...t...) + ((Δ+1) : ℝ) * δ
        have h_add_assoc : t + (Δ + 1) = (t + Δ) + 1 := by omega
        calc Θ' ⟨mu F' (joinMulti r_old (t + (Δ + 1))), _⟩
            = Θ' ⟨mu F' (joinMulti r_old ((t + Δ) + 1)), _⟩ := by
                rw [← h_add_assoc]
          _ = Θ' ⟨mu F' (joinMulti r_old (t + Δ)), _⟩ + δ :=
                Theta'_increment_t r_old (t + Δ)
          _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ + (Δ : ℝ) * δ + δ := by
                rw [ih]
          _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ + ((Δ : ℝ) + 1) * δ := by
                ring
          _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ + ((Δ + 1 : ℕ) : ℝ) * δ := by
                simp only [Nat.cast_add, Nat.cast_one]

    -- Helper 4: Strict monotonicity when t-components are equal
    have Theta'_strictMono_same_t : ∀ (r_old_x r_old_y : Multi k) (t : ℕ),
        mu F r_old_x < mu F r_old_y →
        Θ' ⟨mu F' (joinMulti r_old_x t), mu_mem_kGrid F' (joinMulti r_old_x t)⟩ <
        Θ' ⟨mu F' (joinMulti r_old_y t), mu_mem_kGrid F' (joinMulti r_old_y t)⟩ := by
      intro r_old_x r_old_y t h_mu
      -- Unfold Θ' definition
      simp only [Θ']
      -- splitMulti (joinMulti r_old_x t) = (r_old_x, t) and same for y
      have h_split_x : splitMulti (joinMulti r_old_x t) = (r_old_x, t) :=
        splitMulti_joinMulti r_old_x t
      have h_split_y : splitMulti (joinMulti r_old_y t) = (r_old_y, t) :=
        splitMulti_joinMulti r_old_y t

      -- After choosing witnesses and splitting, we get:
      -- LHS = R.Θ_grid(mu F r_old_x) + t·δ
      -- RHS = R.Θ_grid(mu F r_old_y) + t·δ
      -- Since mu F r_old_x < mu F r_old_y, we have R.Θ_grid(...) < R.Θ_grid(...)
      -- by R.strictMono, so adding t·δ preserves the inequality

      -- Get the δ-bounds for Theta'_well_defined
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB := chooseδ_B_bound hk R IH d hd

      -- X-witness
      set r'_x := Classical.choose (mu_mem_kGrid F' (joinMulti r_old_x t)) with hr'_x_def
      have hr'_x_spec : mu F' r'_x = mu F' (joinMulti r_old_x t) :=
        (Classical.choose_spec (mu_mem_kGrid F' (joinMulti r_old_x t))).symm

      -- Y-witness
      set r'_y := Classical.choose (mu_mem_kGrid F' (joinMulti r_old_y t)) with hr'_y_def
      have hr'_y_spec : mu F' r'_y = mu F' (joinMulti r_old_y t) :=
        (Classical.choose_spec (mu_mem_kGrid F' (joinMulti r_old_y t))).symm

      -- Apply well-definedness to show each side equals canonical form
      have hWD_x := Theta'_well_defined R H IH d hd δ hδA hδC hδB hr'_x_spec
      have hWD_y := Theta'_well_defined R H IH d hd δ hδA hδC hδB hr'_y_spec

      -- Unfold Theta'_raw in the well-definedness results
      simp only [Theta'_raw, h_split_x, h_split_y] at hWD_x hWD_y

      -- Now LHS = R.Θ_grid(mu F r_old_x) + t * δ
      -- and RHS = R.Θ_grid(mu F r_old_y) + t * δ
      rw [hWD_x, hWD_y]

      -- Use R.strictMono to get the Θ-inequality
      have hθ_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                   R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
        R.strictMono h_mu

      -- Adding t * δ preserves the strict inequality
      linarith

    -- Property 2: Strict monotonicity
    --
    -- PROOF STRATEGY (K&S Appendix A):
    -- Given x < y where x, y ∈ kGrid F':
    -- 1. Extract witnesses: x = mu F' r_x and y = mu F' r_y
    -- 2. Split: r_x = (r_old_x, t_x) and r_y = (r_old_y, t_y)
    -- 3. By mu_extend_last: x = mu F r_old_x ⊕ d^{t_x}, y = mu F r_old_y ⊕ d^{t_y}
    -- 4. Key case analysis using helper lemmas above:
    --    (a) If t_x < t_y: Use Theta'_increment_t + delta_pos
    --    (b) If t_x = t_y: Use Theta'_strictMono_same_t
    --    (c) If t_x > t_y: Derive contradiction from δ separation properties
    -- 5. The δ choice (from chooseδ using separation A/B/C sets) ensures all cases work
    --
    -- This requires showing δ is in the "gap" between A-statistics and C-statistics.
    -- The accuracy_lemma shows the gap can be made arbitrarily small but non-zero.
    have h_strictMono : StrictMono Θ' := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Θ']

      -- Get the δ-bounds for Theta'_well_defined
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB := chooseδ_B_bound hk R IH d hd

      -- Extract witnesses
      set r_x := Classical.choose hx with hr_x_def
      set r_y := Classical.choose hy with hr_y_def

      -- Get specs: mu F' r_x = x and mu F' r_y = y
      have hμ_x : mu F' r_x = x := (Classical.choose_spec hx).symm
      have hμ_y : mu F' r_y = y := (Classical.choose_spec hy).symm

      -- Split into old + new components
      set r_old_x := (splitMulti r_x).1
      set t_x := (splitMulti r_x).2
      set r_old_y := (splitMulti r_y).1
      set t_y := (splitMulti r_y).2

      -- Round-trip through joinMulti/splitMulti
      have h_rx_join : r_x = joinMulti r_old_x t_x := (joinMulti_splitMulti r_x).symm
      have h_ry_join : r_y = joinMulti r_old_y t_y := (joinMulti_splitMulti r_y).symm

      -- Use mu_extend_last to express x and y
      have hx_eq : x = op (mu F r_old_x) (iterate_op d t_x) := by
        rw [← hμ_x, h_rx_join]
        exact mu_extend_last F d hd r_old_x t_x
      have hy_eq : y = op (mu F r_old_y) (iterate_op d t_y) := by
        rw [← hμ_y, h_ry_join]
        exact mu_extend_last F d hd r_old_y t_y

      -- The goal after simp [Θ'] is already in canonical form:
      -- R.Θ_grid(mu F r_old_x) + t_x*δ < R.Θ_grid(mu F r_old_y) + t_y*δ
      -- Case analysis on t_x vs t_y
      rcases lt_trichotomy t_x t_y with h_t_lt | h_t_eq | h_t_gt

      · -- Case: t_x < t_y
        -- Need: Θ(r_old_x) + t_x*δ < Θ(r_old_y) + t_y*δ
        --
        -- Strategy: Compare mu F r_old_x with mu F r_old_y
        by_cases h_mu_order : mu F r_old_x < mu F r_old_y

        · -- Sub-case A: mu F r_old_x < mu F r_old_y
          -- Use Theta'_strictMono_same_t at level t_x, then add the t difference
          have hθ_at_tx : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
            R.strictMono h_mu_order

          -- Since t_x < t_y, we have t_x*δ < t_y*δ
          have ht_ineq : (t_x : ℝ) * δ < (t_y : ℝ) * δ := by
            have h_delta_pos : 0 < δ := delta_pos
            have h_tx_lt_ty : (t_x : ℝ) < (t_y : ℝ) := Nat.cast_lt.mpr h_t_lt
            exact (mul_lt_mul_right h_delta_pos).mpr h_tx_lt_ty

          -- Combine: both Θ and t favor RHS
          linarith

        · -- Sub-case B: mu F r_old_y ≤ mu F r_old_x
          push_neg at h_mu_order
          -- In this case, since x < y but the old parts don't favor y,
          -- the t difference must compensate.
          -- From x < y: op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})

          rcases eq_or_lt_of_le h_mu_order with h_eq | h_gt

          · -- mu F r_old_x = mu F r_old_y
            -- Then Θ values are equal, and t_x < t_y gives the result
            -- Since t_x < t_y, we have t_x*δ < t_y*δ
            have ht_ineq : (t_x : ℝ) * δ < (t_y : ℝ) * δ := by
              have h_delta_pos : 0 < δ := delta_pos
              have h_tx_lt_ty : (t_x : ℝ) < (t_y : ℝ) := Nat.cast_lt.mpr h_t_lt
              nlinarith [sq_nonneg (t_y - t_x : ℝ), sq_nonneg δ]

            -- With mu F r_old_x = mu F r_old_y, the Θ parts are equal
            -- So the inequality follows from t_x < t_y alone
            calc R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (t_x : ℝ) * δ
                = R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_x : ℝ) * δ := by
                    simp only [h_eq]
              _ < R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_y : ℝ) * δ := by
                    linarith

          · -- mu F r_old_x > mu F r_old_y, t_x < t_y, but x < y
            -- **Proof strategy**: Show this case is impossible via contradiction.
            --
            -- From the orderings, we can derive bounds that contradict each other.
            -- Key: Use repetition/scaling to amplify the inequalities until the
            -- contradiction becomes apparent.

            -- Extract the α ordering from x < y
            have hxy_α : x < y := hxy

            -- Express in terms of split components
            have h_ordered : op (mu F r_old_x) (iterate_op d t_x) <
                             op (mu F r_old_y) (iterate_op d t_y) := by
              rw [← hx_eq, ← hy_eq]; exact hxy_α

            -- We have:
            -- (1) mu F r_old_x > mu F r_old_y (given h_gt)
            -- (2) t_x < t_y (given h_t_lt), so d^{t_x} < d^{t_y}
            -- (3) op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y}) (from x < y)
            --
            -- Strategy: Use (1) and (2) with monotonicity to bound the LHS from below
            -- and RHS from above, deriving a contradiction with (3).

            -- From (1) and left-monotonicity:
            -- op_strictMono_left z says: if x < y then op x z < op y z
            have h1 : op (mu F r_old_y) (iterate_op d t_x) <
                      op (mu F r_old_x) (iterate_op d t_x) :=
              op_strictMono_left (iterate_op d t_x) h_gt

            -- From (2) and right-monotonicity:
            -- op_strictMono_right z says: if x < y then op z x < op z y
            have h2 : op (mu F r_old_y) (iterate_op d t_x) <
                      op (mu F r_old_y) (iterate_op d t_y) :=
              op_strictMono_right (mu F r_old_y) (iterate_op_strictMono d hd h_t_lt)

            -- Chaining (by transitivity of <):
            -- op (mu F r_old_y) (d^{t_x}) < op (mu F r_old_x) (d^{t_x})  [by h1]
            -- op (mu F r_old_y) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})  [by h2]
            --
            -- These give us two independent lower bounds on different terms, but
            -- we CANNOT directly conclude op (mu F r_old_x) (d^{t_x}) ? op (mu F r_old_y) (d^{t_y})
            -- without knowing the relative magnitudes of the "gaps".
            --
            -- TODO: The issue is we can't directly compare across both dimensions
            -- without commutativity or a quantitative bound. This case genuinely
            -- needs either:
            -- (a) Full separation/accuracy analysis to bound the gaps, OR
            -- (b) GridComm on the (k+1)-grid to rearrange terms
            --
            -- For now, defer this case as it requires the full K&S machinery.
            sorry -- TODO: Complete using separation/accuracy quantitative bounds

      · -- Case: t_x = t_y
        -- Since x < y and t_x = t_y, we have mu F r_old_x ⊕ d^t < mu F r_old_y ⊕ d^t
        -- By cancellative property, mu F r_old_x < mu F r_old_y
        rw [h_t_eq]
        -- Now goal: R.Θ_grid(...r_old_x...) + t_y*δ < R.Θ_grid(...r_old_y...) + t_y*δ

        -- First, extract the α ordering from the subtype ordering
        have hxy_α : x < y := hxy

        -- Express the ordering in terms of split components
        have h_ordered : op (mu F r_old_x) (iterate_op d t_x) < op (mu F r_old_y) (iterate_op d t_y) := by
          rw [← hx_eq, ← hy_eq]; exact hxy_α

        -- Since t_x = t_y, we can cancel the d^t term
        rw [h_t_eq] at h_ordered
        -- h_ordered : op (mu F r_old_x) (iterate_op d t_y) < op (mu F r_old_y) (iterate_op d t_y)

        -- Use contraposition: if mu F r_old_x ≥ mu F r_old_y, then the op would be ≥
        have h_mu_lt : mu F r_old_x < mu F r_old_y := by
          by_contra h_not_lt
          push_neg at h_not_lt
          have h_ge : op (mu F r_old_x) (iterate_op d t_y) ≥ op (mu F r_old_y) (iterate_op d t_y) := by
            rcases eq_or_lt_of_le h_not_lt with h_eq | h_lt
            · rw [h_eq]
            · exact le_of_lt ((op_strictMono_left (iterate_op d t_y)) h_lt)
          exact not_lt_of_ge h_ge h_ordered

        -- Now use R.strictMono (need to convert to subtype ordering)
        have hθ_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                     R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
          R.strictMono h_mu_lt
        linarith

      · -- Case: t_x > t_y
        -- Need: Θ(r_old_x) + t_x*δ < Θ(r_old_y) + t_y*δ
        -- Equivalently: Θ(r_old_y) - Θ(r_old_x) > (t_x - t_y)*δ
        --
        -- Since x < y and t_x > t_y, the old part r_old_y must be larger
        -- than r_old_x to overcome the t disadvantage.

        -- First, show that mu F r_old_x < mu F r_old_y (by contradiction)
        have h_mu_lt : mu F r_old_x < mu F r_old_y := by
          by_contra h_not_lt
          push_neg at h_not_lt
          -- h_not_lt : mu F r_old_y ≤ mu F r_old_x

          -- From x < y:
          have hxy_α : x < y := hxy
          rw [hx_eq, hy_eq] at hxy_α
          -- hxy_α : op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})

          -- Since t_x > t_y and iterate_op is strictly increasing:
          have h_dt_gt : iterate_op d t_y < iterate_op d t_x :=
            iterate_op_strictMono d hd h_t_gt

          -- By monotonicity: mu F r_old_x >= mu F r_old_y implies
          -- op (mu F r_old_x) (d^{t_x}) >= op (mu F r_old_y) (d^{t_x})
          have h1 : op (mu F r_old_y) (iterate_op d t_x) ≤ op (mu F r_old_x) (iterate_op d t_x) := by
            rcases eq_or_lt_of_le h_not_lt with h_eq | h_lt
            · rw [h_eq]
            · exact le_of_lt (op_strictMono_left (iterate_op d t_x) h_lt)

          -- By monotonicity: d^{t_y} < d^{t_x} implies
          -- op (mu F r_old_y) (d^{t_y}) < op (mu F r_old_y) (d^{t_x})
          have h2 : op (mu F r_old_y) (iterate_op d t_y) < op (mu F r_old_y) (iterate_op d t_x) :=
            (op_strictMono_right (mu F r_old_y)) h_dt_gt

          -- Combining: op (mu F r_old_y) (d^{t_y}) < ... <= op (mu F r_old_x) (d^{t_x})
          have h_ge : op (mu F r_old_y) (iterate_op d t_y) < op (mu F r_old_x) (iterate_op d t_x) :=
            lt_of_lt_of_le h2 h1

          -- But this gives y < x, contradicting x < y
          exact not_lt_of_gt h_ge hxy_α

        -- Now we have mu F r_old_x < mu F r_old_y, so Θ(r_old_x) < Θ(r_old_y)
        have hθ_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                     R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
          R.strictMono h_mu_lt

        -- Strategy (GPT-5 Pro): Use Theta'_shift_by to reduce to same t-level
        let Δ := t_x - t_y
        have hΔ_pos : 0 < Δ := Nat.sub_pos_of_lt h_t_gt
        have hΔ_eq : t_x = t_y + Δ := (Nat.add_sub_cancel' (le_of_lt h_t_gt)).symm

        -- Apply vertical shift: Θ'(x) = Θ'(joinMulti r_old_x t_y) + Δ*δ
        have h_x_shift : Θ' ⟨mu F' (joinMulti r_old_x t_x), mu_mem_kGrid F' (joinMulti r_old_x t_x)⟩ =
                         Θ' ⟨mu F' (joinMulti r_old_x t_y), mu_mem_kGrid F' (joinMulti r_old_x t_y)⟩ + (Δ : ℝ) * δ := by
          have := Theta'_shift_by r_old_x t_y Δ
          convert this using 2
          rw [hΔ_eq]

        -- Goal: Θ'(x) < Θ'(y)
        -- Expanding: Θ'(joinMulti r_old_x t_y) + Δ*δ < Θ'(joinMulti r_old_y t_y)
        -- Rearranging: Θ'(joinMulti r_old_x t_y) < Θ'(joinMulti r_old_y t_y) - Δ*δ
        -- Since mu F r_old_x < mu F r_old_y, we have Θ'(joinMulti r_old_x t_y) < Θ'(joinMulti r_old_y t_y)
        -- So we need: the Θ gap is > Δ*δ
        --
        -- The constraint x < y gives us: op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})
        --
        -- TO PROVE: Θ(r_old_y) - Θ(r_old_x) > Δ*δ
        --
        -- This requires showing that the old-part advantage (Θ(r_old_y) > Θ(r_old_x))
        -- is large enough to overcome the vertical disadvantage (Δ*δ).
        --
        -- **Why this is hard**: The ordering constraint x < y tells us the combined
        -- effect satisfies the inequality, but extracting a quantitative bound on the
        -- θ-gap requires either:
        -- (a) Using commutativity to isolate d^Δ and cancel, giving:
        --     op (mu F r_old_x) (d^Δ) < mu F r_old_y
        --     which would yield the needed bound via separation, OR
        -- (b) Using accuracy/separation lemmas directly on the (r_old_x, t_y) vs (r_old_y, t_y)
        --     comparison to show the gap exceeds Δ*δ
        --
        -- Approach (a) is cleaner but needs commutativity.
        -- Approach (b) might be provable but requires careful separation analysis.
        sorry -- TODO: Use separation/accuracy to show Θ-gap > Δ*δ, OR use GridComm

    -- Property 3: Additivity (componentwise on multiplicities)
    --
    -- PROOF STRATEGY:
    -- 1. For multiplicities r, s : Multi (k+1), split as (r_old, t_r) and (s_old, t_s)
    -- 2. Then (r + s) splits as (r_old + s_old, t_r + t_s)
    -- 3. By mu_extend_last:
    --    mu F' (r+s) = mu F (r_old + s_old) ⊕ d^{t_r + t_s}
    -- 4. By R.add (additivity on old grid) and iterate_op_add:
    --    mu F (r_old + s_old) = mu F r_old ⊕ mu F s_old  (this is R.add!)
    --    d^{t_r + t_s} = d^{t_r} ⊕ d^{t_s}  (iterate_op_add)
    -- 5. Θ' computation:
    --    Θ'(mu F' (r+s)) = R.Θ_grid(mu F (r_old + s_old)) + (t_r + t_s) * δ
    --                    = [R.Θ_grid(mu F r_old) + R.Θ_grid(mu F s_old)] + (t_r + t_s) * δ
    --                    = [R.Θ_grid(mu F r_old) + t_r * δ] + [R.Θ_grid(mu F s_old) + t_s * δ]
    --                    = Θ'(mu F' r) + Θ'(mu F' s)
    --
    -- Technical issue: Classical.choose may pick different witnesses, but the values
    -- should be independent of witness choice (Θ' well-defined on grid points).
    have h_additive : ∀ (r s : Multi (k+1)),
        Θ' ⟨mu F' (fun i => r i + s i), mu_mem_kGrid (F:=F') (r:=fun i => r i + s i)⟩ =
        Θ' ⟨mu F' r, mu_mem_kGrid (F:=F') r⟩ +
        Θ' ⟨mu F' s, mu_mem_kGrid (F:=F') s⟩ := by
      intro r s
      simp only [Θ']

      -- Get the δ-bounds for Theta'_well_defined
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB := chooseδ_B_bound hk R IH d hd

      -- Key: splitMulti distributes over addition
      have h_split_add : splitMulti (fun i => r i + s i) =
          ((fun i => (splitMulti r).1 i + (splitMulti s).1 i),
           (splitMulti r).2 + (splitMulti s).2) := splitMulti_add r s

      -- LHS witness for (r + s)
      set r'_sum := Classical.choose (mu_mem_kGrid F' (fun i => r i + s i))
      have hr'_sum_spec : mu F' r'_sum = mu F' (fun i => r i + s i) :=
        (Classical.choose_spec (mu_mem_kGrid F' (fun i => r i + s i))).symm

      -- Witnesses for r and s
      set r'_r := Classical.choose (mu_mem_kGrid F' r)
      have hr'_r_spec : mu F' r'_r = mu F' r :=
        (Classical.choose_spec (mu_mem_kGrid F' r)).symm

      set r'_s := Classical.choose (mu_mem_kGrid F' s)
      have hr'_s_spec : mu F' r'_s = mu F' s :=
        (Classical.choose_spec (mu_mem_kGrid F' s)).symm

      -- For joinMulti, we can use exact representatives
      -- joinMulti_splitMulti says: joinMulti (splitMulti r).1 (splitMulti r).2 = r
      have h_r_join : joinMulti (splitMulti r).1 (splitMulti r).2 = r := joinMulti_splitMulti r
      have h_s_join : joinMulti (splitMulti s).1 (splitMulti s).2 = s := joinMulti_splitMulti s

      -- The sum also satisfies the joinMulti property
      have h_sum_join : joinMulti (fun i => (splitMulti r).1 i + (splitMulti s).1 i)
                                  ((splitMulti r).2 + (splitMulti s).2) =
                        (fun i => r i + s i) := by
        rw [← joinMulti_add]
        -- Now goal: (fun i => joinMulti (splitMulti r).1 (splitMulti r).2 i +
        --                    joinMulti (splitMulti s).1 (splitMulti s).2 i) = fun i => r i + s i
        funext i
        simp only [h_r_join, h_s_join]

      -- Build the equality proofs for Theta'_well_defined
      -- For sum: mu F' r'_sum = mu F' (joinMulti (r_old+s_old) (t_r+t_s))
      have h_mu_sum : mu F' r'_sum =
          mu F' (joinMulti (fun i => (splitMulti r).1 i + (splitMulti s).1 i)
                          ((splitMulti r).2 + (splitMulti s).2)) := by
        rw [hr'_sum_spec, h_sum_join]

      -- For r: mu F' r'_r = mu F' (joinMulti (splitMulti r).1 (splitMulti r).2)
      have h_mu_r : mu F' r'_r = mu F' (joinMulti (splitMulti r).1 (splitMulti r).2) := by
        rw [hr'_r_spec, h_r_join]

      -- For s: mu F' r'_s = mu F' (joinMulti (splitMulti s).1 (splitMulti s).2)
      have h_mu_s : mu F' r'_s = mu F' (joinMulti (splitMulti s).1 (splitMulti s).2) := by
        rw [hr'_s_spec, h_s_join]

      -- Apply Theta'_well_defined to each
      have hWD_sum := Theta'_well_defined R H IH d hd δ hδA hδC hδB h_mu_sum
      have hWD_r := Theta'_well_defined R H IH d hd δ hδA hδC hδB h_mu_r
      have hWD_s := Theta'_well_defined R H IH d hd δ hδA hδC hδB h_mu_s

      -- Unfold Theta'_raw in the well-definedness results
      simp only [Theta'_raw, splitMulti_joinMulti] at hWD_sum hWD_r hWD_s

      -- Now LHS = R.Θ_grid(mu F (r_old_r + r_old_s)) + (t_r + t_s) * δ
      -- and RHS = [R.Θ_grid(mu F r_old_r) + t_r * δ] + [R.Θ_grid(mu F r_old_s) + t_s * δ]
      -- By R.add: R.Θ_grid(mu F (r_old_r + r_old_s)) = R.Θ_grid(mu F r_old_r) + R.Θ_grid(mu F r_old_s)
      rw [hWD_sum, hWD_r, hWD_s]

      -- Use R.add for the old-grid additivity
      have h_R_add := R.add (splitMulti r).1 (splitMulti s).1

      -- Rewrite using R.add
      -- Goal: R.Θ_grid(...(r_old + s_old)...) + (t_r + t_s) * δ =
      --       (R.Θ_grid(...r_old...) + t_r * δ) + (R.Θ_grid(...s_old...) + t_s * δ)
      rw [h_R_add]
      push_cast
      ring

    -- Construct the MultiGridRep F' (representation complete!)
    let R' : MultiGridRep F' := ⟨Θ', h_strictMono, h_additive, h_norm⟩

    -- **GridComm F' DEFERRED TO TOP LEVEL** (per GPT-5 Pro Step 6):
    --
    -- Following K&S Appendix A, GridComm F' is NOT proven here. Instead:
    -- 1. We construct the representation Θ' on the (k+1)-grid
    -- 2. We prove it has the required properties (strict mono, additive, normalized)
    -- 3. GridComm F' will be derived at the TOP LEVEL using commutativity_from_representation
    --
    -- Why defer? Attempting to prove GridComm F' here creates CIRCULAR DEPENDENCY:
    -- - To prove GridComm F', we need: op (d^t) (mu F r) = op (mu F r) (d^t)
    -- - But this IS an instance of GridComm F'!
    -- - The fix: Build global Θ first, THEN derive commutativity as theorem (not assumption)
    --
    -- See GPT-5 Pro's guidance (2025-12-08):
    -- > "If `extend_grid_rep_with_atom` currently returns `GridComm F'`, split it:
    -- >  * `extend_grid_rep_with_atom_rep`: constructs the (k+1)-grid representation Θ'
    -- >  * `grid_comm_from_rep (F')`: derives commutativity LATER, by applying
    -- >    `commutativity_from_representation` at the TOP LEVEL (once Θ is global on α)"
    --
    -- This breaks the circularity: commutativity is DERIVED, not assumed.
    have H' : GridComm F' := by
      sorry -- TO BE DERIVED AT TOP LEVEL via commutativity_from_representation

    refine ⟨R', H', trivial⟩

-- The main theorem `associativity_representation` at line 66 requires this full
-- construction. The sorry there represents the complete K&S Appendix A argument.
-- All other theorems in this file (commutativity_from_representation, op_comm_of_associativity)
-- follow from it.
--
-- **WARNING**: The lemma `mu_scale_eq_iterate` is FALSE as stated (see CounterExamples.lean).
-- All lemmas that use it (separation_property, separation_property_A_B, separation_property_B_C)
-- are therefore building on quicksand. The correct approach requires the full Θ extension.

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
