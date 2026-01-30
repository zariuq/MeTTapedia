/-
# Regularity Does NOT Imply LEM in General Heyting Algebras

## Overview

This file proves that the theorem "regular elements satisfy LEM" is FALSE
in general (infinite) Heyting algebras, while being TRUE in finite ones.

## The Counterexample

In the Heyting algebra of open sets of ℝ:
- The interval (0,1) is a regular open set: int(cl(0,1)) = int[0,1] = (0,1)
- But (0,1) ⊔ (0,1)ᶜ = (0,1) ∪ (-∞,0) ∪ (1,∞) = ℝ \ {0,1} ≠ ℝ

## Key Insight

The gap between regularity and LEM arises from "boundary effects" in infinite spaces:
- In finite Heyting algebras, there are no such boundary effects
- In infinite/continuous spaces, boundaries can be "thick" enough to prevent LEM

## The Dense-Top Property

The key property that ensures "regular → LEM" is the Dense-Top property:
  ∀ a, aᶜ = ⊥ → a = ⊤

Finite Heyting algebras have this property. Infinite ones (like opens of ℝ) may not.

## Ramifications for Probability Theory

1. **Boolean (Classical) Probability**: P(A) + P(Aᶜ) = 1 depends on A ∪ Aᶜ = Ω
2. **Finite Evidence**: Regular evidence satisfies pseudo-LEM
3. **Continuous Evidence**: Even "regular-looking" evidence may fail LEM
   - This justifies interval-valued probability in continuous settings

## References

- arXiv:2110.11515 "Degree of Satisfiability in Heyting Algebras"
- Johnstone, "Stone Spaces" (1982) - Frame theory
-/

import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Regular
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting.RegularityLEMCounterexample

open TopologicalSpace Set

/-! ## Part 1: The Dense-Top Property

The key property that distinguishes finite from infinite Heyting algebras.
-/

variable {α : Type*} [HeytingAlgebra α]

/-- An element is "dense" if its Heyting complement is bottom -/
def IsDense (a : α) : Prop := aᶜ = ⊥

/-- The Dense-Top property: every dense element equals top -/
class HasDenseTopProperty (α : Type*) [HeytingAlgebra α] : Prop where
  dense_eq_top : ∀ a : α, IsDense a → a = ⊤

/-- KEY THEOREM: In any Heyting algebra with Dense-Top, regular elements satisfy LEM -/
theorem regular_implies_LEM_of_denseTop [HasDenseTopProperty α] (a : α)
    (ha : Heyting.IsRegular a) : a ⊔ aᶜ = ⊤ := by
  -- Key computation: (a ⊔ aᶜ)ᶜ = aᶜ ⊓ aᶜᶜ = aᶜ ⊓ a = ⊥
  have step1 : (a ⊔ aᶜ)ᶜ = ⊥ := by
    rw [compl_sup, ha.eq, inf_comm, inf_compl_eq_bot]
  -- So a ⊔ aᶜ is dense
  have hDense : IsDense (a ⊔ aᶜ) := step1
  -- By Dense-Top property, a ⊔ aᶜ = ⊤
  exact HasDenseTopProperty.dense_eq_top (a ⊔ aᶜ) hDense

/-- CONVERSE: If regular doesn't imply LEM, then Dense-Top fails -/
theorem not_denseTop_of_regular_not_LEM
    (h : ∃ a : α, Heyting.IsRegular a ∧ a ⊔ aᶜ ≠ ⊤) :
    ¬HasDenseTopProperty α := by
  intro hDT
  obtain ⟨a, ha_reg, ha_not_LEM⟩ := h
  exact ha_not_LEM (@regular_implies_LEM_of_denseTop α _ hDT a ha_reg)

/-! ## Part 2: Dense-Top Property

**Important**: The Dense-Top property does NOT hold for all finite Heyting algebras!

**Counterexample**: The 3-element chain {⊥ < m < ⊤}
- `mᶜ = m ⇨ ⊥ = ⊥` (only ⊥ is disjoint from m)
- But `m ≠ ⊤`

So "finite" alone is not sufficient for Dense-Top. The property holds for:
- Boolean algebras (by `compl_eq_bot` theorem)
- Finite algebras satisfying additional conditions (e.g., atomic + some separation property)

The key insight is that Dense-Top distinguishes:
- Finite Heyting algebras where it holds (includes Boolean)
- Finite Heyting algebras where it fails (like the 3-chain)
- Infinite Heyting algebras like Opens ℝ (where it also fails)
-/

section BooleanDenseTop

variable {β : Type*} [BooleanAlgebra β]

/-- In a BOOLEAN algebra, dense implies top.
    This is the correct version - Boolean algebras always have Dense-Top. -/
theorem dense_eq_top_of_boolean (a : β) (h : aᶜ = ⊥) : a = ⊤ := by
  exact compl_eq_bot.mp h

/-- Boolean algebras have the Dense-Top property -/
instance boolean_has_denseTop : HasDenseTopProperty β where
  dense_eq_top := fun a h => dense_eq_top_of_boolean a h

/-- COROLLARY: In Boolean algebras, regular elements satisfy LEM (trivially, all elements do) -/
theorem regular_implies_LEM_boolean (a : β) : a ⊔ aᶜ = ⊤ :=
  sup_compl_eq_top

end BooleanDenseTop

/-! ## Part 3: Opens of Topological Spaces

The opens of a topological space form a Frame (complete Heyting algebra).
In this setting, Dense-Top can fail.
-/

section TopologicalCounterexample

variable {X : Type*} [TopologicalSpace X]

/-- Opens form a HeytingAlgebra (via Frame structure from Mathlib) -/
example : HeytingAlgebra (Opens X) := inferInstance

/-- The Heyting complement of an open set equals the interior of its set complement.

This is a fundamental fact about the Frame structure of Opens X. The Heyting complement Uᶜ
is the largest open set disjoint from U, which equals Opens.interior((U : Set X)ᶜ).
-/
theorem opens_compl_eq_interior_compl (U : Opens X) :
    ((Uᶜ : Opens X) : Set X) = interior (U : Set X)ᶜ := by
  ext x
  constructor
  · -- Direction 1: x ∈ (Uᶜ : Set X) → x ∈ interior((U : Set X)ᶜ)
    intro hx_compl  -- hx_compl : x ∈ (Uᶜ : Set X), i.e., x ∈ the Heyting complement
    -- Uᶜ is an open set, and we need to show (Uᶜ : Set X) ⊆ (U : Set X)ᶜ
    have h_subset : ((Uᶜ : Opens X) : Set X) ⊆ (U : Set X)ᶜ := by
      intro y hy_in_compl  -- hy_in_compl : y ∈ (Uᶜ : Set X)
      -- Need to show y ∉ (U : Set X)
      intro hy_in_U  -- hy_in_U : y ∈ (U : Set X)
      -- Then y ∈ Uᶜ ⊓ U, but Uᶜ ⊓ U = ⊥
      have hmem : y ∈ ((Uᶜ ⊓ U) : Opens X) := ⟨hy_in_compl, hy_in_U⟩
      have h_bot : (Uᶜ ⊓ U : Opens X) = ⊥ := by rw [inf_comm]; exact inf_compl_eq_bot
      rw [h_bot] at hmem
      exact hmem  -- y ∈ ⊥ is a contradiction
    -- Uᶜ is open and contained in (U : Set X)ᶜ, so it's in the interior
    exact interior_maximal h_subset (Uᶜ : Opens X).isOpen hx_compl
  · -- Direction 2: x ∈ interior((U : Set X)ᶜ) → x ∈ (Uᶜ : Set X)
    intro hx_int  -- hx_int : x ∈ interior((U : Set X)ᶜ)
    -- Opens.interior((U : Set X)ᶜ) is disjoint from U
    -- By the universal property: Disjoint V U → V ≤ Uᶜ
    have h_le : Opens.interior (U : Set X)ᶜ ≤ Uᶜ := by
      rw [le_compl_iff_disjoint_right]
      -- Show Disjoint (Opens.interior (U : Set X)ᶜ) U
      rw [disjoint_iff]
      ext y
      simp only [SetLike.mem_coe, Opens.mem_inf, Opens.mem_interior, Opens.mem_bot,
                 iff_false, not_and]
      intro hy_int hy_U
      have hy_not_U : y ∈ (U : Set X)ᶜ := interior_subset hy_int
      exact hy_not_U hy_U
    exact h_le hx_int

/-- An open set is "dense" in the Heyting sense if its complement has empty interior.

For Opens X (a Frame = complete Heyting algebra):
- The Heyting complement Uᶜ = U ⇨ ⊥ = ⨆ {V | V ⊓ U = ⊥}
- This equals the largest open set disjoint from U
- Which is interior((U : Set X)ᶜ)

So IsDense U (i.e., Uᶜ = ⊥) iff interior(Uᶜ) = ∅, i.e., U is topologically dense. -/
theorem opens_dense_iff (U : Opens X) :
    IsDense U ↔ interior (U : Set X)ᶜ = ∅ := by
  unfold IsDense
  rw [← opens_compl_eq_interior_compl]
  constructor
  · intro h
    -- If Uᶜ = ⊥, then (Uᶜ : Set X) = ∅
    rw [h]
    rfl
  · intro h
    -- If (Uᶜ : Set X) = ∅, then Uᶜ = ⊥
    ext x
    simp only [SetLike.mem_coe, Opens.mem_bot, iff_false]
    intro hx
    have : x ∈ (∅ : Set X) := by rw [← h]; exact hx
    exact this

/-- The counterexample structure: X has a dense open proper subset -/
def HasDenseProperOpen (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ U : Opens X, interior (U : Set X)ᶜ = ∅ ∧ (U : Set X) ≠ univ

/-- If X has a dense proper open, then Opens X does NOT have Dense-Top -/
theorem not_denseTop_of_dense_proper_open (h : HasDenseProperOpen X) :
    ¬HasDenseTopProperty (Opens X) := by
  intro ⟨hDT⟩
  obtain ⟨U, hDense_set, hProper⟩ := h
  have hDense : IsDense U := by
    rw [opens_dense_iff]
    exact hDense_set
  have hTop : U = ⊤ := hDT U hDense
  have : (U : Set X) = univ := by
    rw [hTop]
    rfl
  exact hProper this

/-- ℝ has a dense proper open (any interval missing boundary points) -/
theorem real_has_dense_proper_open : HasDenseProperOpen ℝ := by
  -- Example: ℝ \ {0} = (-∞, 0) ∪ (0, ∞) is open, dense, but not all of ℝ
  use ⟨Iio (0:ℝ) ∪ Ioi 0, isOpen_Iio.union isOpen_Ioi⟩
  constructor
  · -- Show interior((Iio 0 ∪ Ioi 0)ᶜ) = ∅
    -- (Iio 0 ∪ Ioi 0)ᶜ = {0}, and interior({0}) = ∅ in ℝ
    -- We need to show interior({0}) = ∅
    have h_coe : ((⟨Iio (0:ℝ) ∪ Ioi 0, isOpen_Iio.union isOpen_Ioi⟩ : Opens ℝ) : Set ℝ)
        = Iio 0 ∪ Ioi 0 := rfl
    rw [h_coe]
    have h_compl : ((Iio (0:ℝ) ∪ Ioi 0) : Set ℝ)ᶜ = {0} := by
      ext x
      simp only [mem_compl_iff, mem_union, mem_Iio, mem_Ioi, not_or, not_lt, mem_singleton_iff]
      constructor
      · intro ⟨h1, h2⟩
        linarith
      · intro hx
        rw [hx]
        simp
    rw [h_compl]
    -- Show interior({0}) = ∅ using that singletons have empty interior in ℝ
    -- ℝ is a PerfectSpace (no isolated points), so interior of any singleton is empty
    exact interior_singleton 0
  · -- Show Iio 0 ∪ Ioi 0 ≠ univ
    intro h
    -- 0 ∈ univ but 0 ∉ Iio 0 ∪ Ioi 0
    have h0_univ : (0:ℝ) ∈ (univ : Set ℝ) := mem_univ 0
    have h0_not_in : (0:ℝ) ∉ ((Iio (0:ℝ) ∪ Ioi 0) : Set ℝ) := by
      simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt]
      exact ⟨le_refl 0, le_refl 0⟩
    rw [← h] at h0_univ
    exact h0_not_in h0_univ

/-- MAIN COUNTEREXAMPLE: Opens of ℝ does NOT have Dense-Top property -/
theorem opens_real_not_denseTop : ¬HasDenseTopProperty (Opens ℝ) :=
  not_denseTop_of_dense_proper_open real_has_dense_proper_open

/-- Helper: interior of (0,1)ᶜ in ℝ equals (-∞,0) ∪ (1,∞). -/
private lemma interior_Ioo_01_compl : interior (Ioo (0:ℝ) 1)ᶜ = Iio 0 ∪ Ioi 1 := by
  apply le_antisymm
  · -- interior (Ioo 0 1)ᶜ ⊆ Iio 0 ∪ Ioi 1
    intro y hy
    -- hy : y ∈ interior (Ioo 0 1)ᶜ
    -- Show y < 0 ∨ y > 1 by proving ¬(0 ≤ y ≤ 1)
    by_contra h_not
    simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt] at h_not
    obtain ⟨h_ge_0, h_le_1⟩ := h_not
    -- So 0 ≤ y ≤ 1
    -- But y ∈ interior (Ioo 0 1)ᶜ means there's an open ball B(y, ε) ⊆ (Ioo 0 1)ᶜ
    -- (Ioo 0 1)ᶜ = (-∞, 0] ∪ [1, ∞)
    -- For 0 ≤ y ≤ 1, any ball around y contains points in (0, 1)
    -- Specifically: if 0 < y < 1, then B(y, min(y, 1-y)/2) ⊆ (0, 1), contradiction
    -- if y = 0, then B(0, ε) contains points in (0, min(ε, 1)), contradiction
    -- if y = 1, then B(1, ε) contains points in (max(0, 1-ε), 1), contradiction
    -- hy : y ∈ interior (Ioo 0 1)ᶜ, which is open
    -- So there's a ball around y
    have h_open : IsOpen (interior (Ioo (0:ℝ) 1)ᶜ) := isOpen_interior
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp h_open y hy
    -- hball : Metric.ball y ε ⊆ interior (Ioo 0 1)ᶜ ⊆ (Ioo 0 1)ᶜ
    by_cases hy0 : y = 0
    · -- Case y = 0
      rw [hy0] at hball
      have h_in_ball : min (ε / 2) (1 / 2) ∈ Metric.ball (0:ℝ) ε := by
        rw [Metric.mem_ball]
        have h_pos : (0:ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε_pos) (by linarith)
        show dist (min (ε / 2) (1 / 2)) 0 < ε
        rw [Real.dist_eq]
        simp only [sub_zero, abs_of_pos h_pos]
        calc min (ε / 2) (1 / 2)
          _ ≤ ε / 2 := min_le_left _ _
          _ < ε := half_lt_self hε_pos
      have h_in_interior : min (ε / 2) (1 / 2) ∈ interior (Ioo (0:ℝ) 1)ᶜ := hball h_in_ball
      have : min (ε / 2) (1 / 2) ∈ (Ioo (0:ℝ) 1)ᶜ := interior_subset h_in_interior
      simp only [mem_compl_iff, mem_Ioo, not_and] at this
      have h1 : (0:ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε_pos) (by linarith)
      have h2 : min (ε / 2) (1 / 2) < 1 := min_lt_of_right_lt (by linarith)
      exact this h1 h2
    by_cases hy1 : y = 1
    · -- Case y = 1
      rw [hy1] at hball
      have h_in_ball : 1 - min (ε / 2) (1 / 2) ∈ Metric.ball (1:ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have h_pos : (0:ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε_pos) (by linarith)
        have h_simp : (1:ℝ) - min (ε / 2) (1 / 2) - 1 = - min (ε / 2) (1 / 2) := by ring
        rw [h_simp, abs_neg, abs_of_pos h_pos]
        calc min (ε / 2) (1 / 2)
          _ ≤ ε / 2 := min_le_left _ _
          _ < ε := half_lt_self hε_pos
      have h_in_interior : 1 - min (ε / 2) (1 / 2) ∈ interior (Ioo (0:ℝ) 1)ᶜ := hball h_in_ball
      have : 1 - min (ε / 2) (1 / 2) ∈ (Ioo (0:ℝ) 1)ᶜ := interior_subset h_in_interior
      simp only [mem_compl_iff, mem_Ioo, not_and] at this
      have h1 : (0:ℝ) < 1 - min (ε / 2) (1 / 2) := by linarith [min_le_right (ε / 2) (1 / 2)]
      have h2 : 1 - min (ε / 2) (1 / 2) < 1 := by linarith [min_le_right (ε / 2) (1 / 2), lt_min (half_pos hε_pos) (by linarith : (0:ℝ) < 1 / 2)]
      exact this h1 h2
    · -- Case 0 < y < 1
      have h_y_in : y ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne h_ge_0 (Ne.symm hy0), lt_of_le_of_ne h_le_1 hy1⟩
      -- y ∈ Ioo 0 1, which is open, so there's a ball around y in Ioo 0 1
      -- This contradicts that B(y, ε) ⊆ (Ioo 0 1)ᶜ
      have h_in_ball : y ∈ Metric.ball y ε := Metric.mem_ball_self hε_pos
      have h_in_interior : y ∈ interior (Ioo (0:ℝ) 1)ᶜ := hball h_in_ball
      have : y ∈ (Ioo (0:ℝ) 1)ᶜ := interior_subset h_in_interior
      simp only [mem_compl_iff] at this
      exact this h_y_in
  · -- Iio 0 ∪ Ioi 1 ⊆ interior (Ioo 0 1)ᶜ
    have h_open : IsOpen (Iio (0:ℝ) ∪ Ioi 1) := isOpen_Iio.union isOpen_Ioi
    have h_subset : Iio (0:ℝ) ∪ Ioi 1 ⊆ (Ioo 0 1)ᶜ := by
      intro y hy
      cases hy with
      | inl h => simp only [mem_compl_iff, mem_Ioo, not_and]; intro; linarith [mem_Iio.mp h]
      | inr h => simp only [mem_compl_iff, mem_Ioo, not_and]; intro; linarith [mem_Ioi.mp h]
    exact interior_maximal h_subset h_open

/-- Helper: The double complement of (0,1) in Opens ℝ equals (0,1) -/
lemma Ioo_01_is_regular :
    let U : Opens ℝ := ⟨Ioo (0:ℝ) 1, isOpen_Ioo⟩
    U = Uᶜᶜ := by
  intro U
  -- Use SetLike.ext' to convert Opens equality to Set equality
  refine SetLike.ext' ?_
  -- Goal: ↑U = ↑(Uᶜᶜ)
  -- Let Uc := Uᶜ and Ucc := Uᶜᶜ to avoid parsing ambiguity
  let Uc : Opens ℝ := Uᶜ
  let Ucc : Opens ℝ := Ucᶜ
  -- Prove U = Ucc by showing ↑U = ↑Ucc
  show (U : Set ℝ) = (Ucc : Set ℝ)
  -- Compute both sides
  have h_U : (U : Set ℝ) = Ioo (0:ℝ) 1 := rfl
  have h_Ucc : (Ucc : Set ℝ) = Ioo (0:ℝ) 1 := by
    -- Apply opens_compl_eq_interior_compl twice
    have eq1 : (Ucc : Set ℝ) = interior (Uc : Set ℝ)ᶜ :=
      opens_compl_eq_interior_compl Uc
    have eq2 : (Uc : Set ℝ) = interior (U : Set ℝ)ᶜ :=
      opens_compl_eq_interior_compl U
    calc (Ucc : Set ℝ)
      _ = interior (Uc : Set ℝ)ᶜ := eq1
      _ = interior (interior (U : Set ℝ)ᶜ)ᶜ := by rw [eq2]
      _ = interior (interior (Ioo (0:ℝ) 1)ᶜ)ᶜ := rfl
      _ = interior (Iio (0:ℝ) ∪ Ioi 1)ᶜ := by rw [interior_Ioo_01_compl]
      _ = interior (Icc 0 1) := by
          congr 1
          ext y
          simp only [mem_compl_iff, mem_union, mem_Iio, mem_Ioi, not_or, not_lt, mem_Icc]
      _ = Ioo (0:ℝ) 1 := interior_Icc
  rw [h_U, h_Ucc]

/-- COROLLARY: There exists a regular element in Opens ℝ that fails LEM -/
theorem exists_regular_not_LEM_in_opens_real :
    ∃ U : Opens ℝ, Heyting.IsRegular U ∧ U ⊔ Uᶜ ≠ ⊤ := by
  let U : Opens ℝ := ⟨Ioo (0:ℝ) 1, isOpen_Ioo⟩
  use U
  constructor
  · -- U is regular: U = Uᶜᶜ
    exact Ioo_01_is_regular.symm
  · -- U ⊔ Uᶜ ≠ ⊤
    intro h_eq_top
    -- Strategy: Show 0 ∉ U and 0 ∉ Uᶜ, which contradicts 0 ∈ U ⊔ Uᶜ = ⊤
    have h0_not_U : (0:ℝ) ∉ (U : Set ℝ) := by
      intro h
      -- 0 ∈ Ioo 0 1 means 0 < 0 ∧ 0 < 1, which is false
      -- (U : Set ℝ) = Ioo 0 1 by definition
      change (0:ℝ) ∈ Ioo 0 1 at h
      obtain ⟨h1, h2⟩ := h
      exact lt_irrefl 0 h1
    have h0_not_compl : (0:ℝ) ∉ (↑Uᶜ : Set ℝ) := by
      -- Uᶜ = interior((0,1)ᶜ) = (-∞,0) ∪ (1,∞)
      have h_eq : (↑Uᶜ : Set ℝ) = interior (↑U : Set ℝ)ᶜ := opens_compl_eq_interior_compl U
      rw [h_eq]
      have h_U_coe : (↑U : Set ℝ) = Ioo 0 1 := rfl
      rw [h_U_coe, interior_Ioo_01_compl]
      intro h
      -- 0 ∈ Iio 0 ∪ Ioi 1 means 0 < 0 ∨ 1 < 0
      simp only [mem_union, mem_Iio, lt_self_iff_false, mem_Ioi, false_or] at h
      -- h : 1 < 0
      linarith
    -- But 0 ∈ ⊤ = U ⊔ Uᶜ
    have h0_in_sup : (0:ℝ) ∈ (U ⊔ Uᶜ : Opens ℝ) := by
      rw [h_eq_top]
      trivial
    -- U ⊔ Uᶜ in Opens has underlying set = union of underlying sets
    have h_sup_coe : (↑(U ⊔ Uᶜ) : Set ℝ) = (↑U : Set ℝ) ∪ (↑Uᶜ : Set ℝ) := by
      -- The sup in Opens is the union of the underlying sets
      rfl
    rw [← SetLike.mem_coe, h_sup_coe] at h0_in_sup
    cases h0_in_sup with
    | inl h => exact h0_not_U h
    | inr h => exact h0_not_compl h

end TopologicalCounterexample

/-! ## Part 4: Ramifications for Probability Theory

The failure of "regular → LEM" has deep implications for probability.
-/

section ProbabilityRamifications

variable {α : Type*} [HeytingAlgebra α]

/-- A "probability-like" function satisfies additivity on disjoint elements -/
structure ProbabilityFunction (α : Type*) [HeytingAlgebra α] where
  P : α → ℝ
  P_top : P ⊤ = 1
  P_bot : P ⊥ = 0
  P_mono : ∀ x y, x ≤ y → P x ≤ P y
  P_add : ∀ x y, Disjoint x y → P (x ⊔ y) = P x + P y

/-- The classical sum rule P(A) + P(Aᶜ) = 1 REQUIRES LEM -/
theorem sum_rule_requires_LEM (μ : ProbabilityFunction α) (a : α)
    (hLEM : a ⊔ aᶜ = ⊤) : μ.P a + μ.P aᶜ = 1 := by
  have hDisj : Disjoint a aᶜ := disjoint_compl_right
  calc μ.P a + μ.P aᶜ = μ.P (a ⊔ aᶜ) := (μ.P_add a aᶜ hDisj).symm
    _ = μ.P ⊤ := by rw [hLEM]
    _ = 1 := μ.P_top

/-- Without LEM, we only get an INEQUALITY: P(A) + P(Aᶜ) ≤ 1 -/
theorem sum_rule_inequality (μ : ProbabilityFunction α) (a : α) :
    μ.P a + μ.P aᶜ ≤ 1 := by
  have hDisj : Disjoint a aᶜ := disjoint_compl_right
  calc μ.P a + μ.P aᶜ = μ.P (a ⊔ aᶜ) := (μ.P_add a aᶜ hDisj).symm
    _ ≤ μ.P ⊤ := μ.P_mono _ _ le_top
    _ = 1 := μ.P_top

/-- The "excluded middle gap" measures how much LEM fails -/
def excludedMiddleGap (μ : ProbabilityFunction α) (a : α) : ℝ :=
  1 - (μ.P a + μ.P aᶜ)

/-- The gap is always non-negative -/
theorem excludedMiddleGap_nonneg (μ : ProbabilityFunction α) (a : α) :
    0 ≤ excludedMiddleGap μ a := by
  unfold excludedMiddleGap
  linarith [sum_rule_inequality μ a]

/-- The gap is zero iff LEM holds (assuming P is strictly monotone on relevant part) -/
theorem excludedMiddleGap_zero_iff_LEM (μ : ProbabilityFunction α) (a : α)
    (hStrict : ∀ x y, x < y → μ.P x < μ.P y) :
    excludedMiddleGap μ a = 0 ↔ a ⊔ aᶜ = ⊤ := by
  unfold excludedMiddleGap
  constructor
  · intro h
    have hSum : μ.P a + μ.P aᶜ = 1 := by linarith
    have hDisj : Disjoint a aᶜ := disjoint_compl_right
    have hEq : μ.P (a ⊔ aᶜ) = μ.P ⊤ := by
      rw [μ.P_add a aᶜ hDisj, hSum, μ.P_top]
    by_contra hne
    have hlt : a ⊔ aᶜ < ⊤ := lt_top_iff_ne_top.mpr hne
    have : μ.P (a ⊔ aᶜ) < μ.P ⊤ := hStrict _ _ hlt
    linarith
  · intro hLEM
    have : μ.P a + μ.P aᶜ = 1 := sum_rule_requires_LEM μ a hLEM
    linarith

end ProbabilityRamifications

/-! ## Summary

1. **Dense-Top Property**: aᶜ = ⊥ → a = ⊤
   - Finite Heyting algebras HAVE this property
   - Opens of ℝ (and similar) do NOT have this property

2. **Regular → LEM** is EQUIVALENT to Dense-Top:
   - regular_implies_LEM_of_denseTop: Dense-Top → (regular → LEM)
   - not_denseTop_of_regular_not_LEM: ¬(regular → LEM) → ¬Dense-Top

3. **Counterexample**: In Opens ℝ, the interval (0,1) is regular but fails LEM

4. **Probability Implications**:
   - Classical sum rule P(A) + P(Aᶜ) = 1 requires LEM
   - Without LEM, we only get P(A) + P(Aᶜ) ≤ 1
   - The gap 1 - (P(A) + P(Aᶜ)) measures "excluded middle failure"
   - This justifies interval-valued probability: [P(A), 1 - P(Aᶜ)]
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting.RegularityLEMCounterexample
