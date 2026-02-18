/-
# Dempster-Shafer Belief Functions

Formalization of Dempster-Shafer theory (1967, 1976) as a special case of
imprecise probability where belief functions arise from mass functions on
the power set.

## Key Insight: D-S as Imprecise Probability

Dempster-Shafer belief functions are **special cases** of Walley's lower
probabilities! Specifically:
- Belief function Bel(A) = lower probability P̲(A)
- Plausibility function Pl(A) = upper probability P̅(A) = 1 - Bel(¬A)

## Mathematical Structure

Given a frame of discernment Ω, a **mass function** m : 2^Ω → [0,1] satisfies:
1. m(∅) = 0 (no mass on empty set)
2. Σ_{A ⊆ Ω} m(A) = 1 (masses sum to 1)

The **belief function** is: Bel(A) = Σ_{B ⊆ A} m(B)
The **plausibility** is: Pl(A) = Σ_{B ∩ A ≠ ∅} m(B) = 1 - Bel(Ω \ A)

## Connection to Hypercube

D-S sits at the (imprecise, commutative) vertex of the uncertainty hypercube.

## References

- Dempster, A.P. "Upper and Lower Probabilities Induced by Multivalued Mapping" (1967)
- Shafer, G. "A Mathematical Theory of Evidence" (1976)
- Walley, P. "Statistical Reasoning with Imprecise Probabilities" (1991), §5
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Structures.Valuation.Basic
import Mettapedia.ProbabilityTheory.Common.Lattice
import Mettapedia.ProbabilityTheory.Common.LatticeSummation
import Mettapedia.ProbabilityTheory.Hypercube.NovelTheories

namespace Mettapedia.ProbabilityTheory.BeliefFunctions

open Finset BigOperators

/-!
## §1: Frame of Discernment and Mass Functions
-/

variable {Ω : Type*} [DecidableEq Ω] [Fintype Ω]

/-- A mass function on the power set of Ω.
    Also called a "basic probability assignment" (BPA). -/
structure MassFunction (Ω : Type*) [DecidableEq Ω] [Fintype Ω] where
  /-- The mass assigned to each subset -/
  m : Finset Ω → ℝ
  /-- No mass on empty set -/
  m_empty : m ∅ = 0
  /-- All masses are non-negative -/
  m_nonneg : ∀ A, 0 ≤ m A
  /-- Masses sum to 1 -/
  m_sum_one : ∑ A ∈ Finset.univ.powerset, m A = 1

namespace MassFunction

variable (m : MassFunction Ω)

/-- A focal element is a set with positive mass. -/
def isFocal (A : Finset Ω) : Prop := m.m A > 0

/-- The set of all focal elements. -/
def focalElements : Set (Finset Ω) := { A | m.isFocal A }

/-- Mass is bounded by 1. -/
theorem m_le_one (A : Finset Ω) : m.m A ≤ 1 := by
  have hA : A ∈ Finset.univ.powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
  have h := m.m_sum_one
  calc m.m A ≤ ∑ B ∈ Finset.univ.powerset, m.m B := by
        apply Finset.single_le_sum (fun B _ => m.m_nonneg B) hA
    _ = 1 := h

end MassFunction

/-!
## §2: Belief and Plausibility Functions
-/

/-- The belief function: total mass of subsets of A.
    Bel(A) = Σ_{B ⊆ A} m(B) -/
def belief (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  ∑ B ∈ A.powerset, m.m B

/-- The plausibility function: total mass of sets intersecting A.
    Pl(A) = Σ_{B : B ∩ A ≠ ∅} m(B) -/
def plausibility (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B

namespace Belief

variable (m : MassFunction Ω)

/-- Belief of empty set is 0. -/
theorem empty : belief m ∅ = 0 := by
  simp only [belief, Finset.powerset_empty, Finset.sum_singleton, m.m_empty]

/-- Belief of the full frame is 1. -/
theorem univ : belief m Finset.univ = 1 := by
  -- Bel(Ω) = Σ_{B ⊆ Ω} m(B) = Σ_B m(B) = 1
  unfold belief
  rw [Finset.powerset_univ]
  exact m.m_sum_one

/-- Belief is non-negative. -/
theorem nonneg (A : Finset Ω) : 0 ≤ belief m A := by
  apply Finset.sum_nonneg
  intro B _
  exact m.m_nonneg B

/-- Belief is bounded by 1. -/
theorem le_one (A : Finset Ω) : belief m A ≤ 1 := by
  -- Sum over subset ≤ sum over superset (with nonneg terms)
  unfold belief
  calc ∑ B ∈ A.powerset, m.m B
      ≤ ∑ B ∈ Finset.univ.powerset, m.m B := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro B hB
            exact Finset.mem_powerset.mpr (Finset.subset_univ B)
          · intro B _ _
            exact m.m_nonneg B
    _ = 1 := m.m_sum_one

/-- Belief is monotone: A ⊆ B → Bel(A) ≤ Bel(B). -/
theorem mono {A B : Finset Ω} (h : A ⊆ B) : belief m A ≤ belief m B := by
  -- Powerset of A ⊆ powerset of B, so sum is smaller
  unfold belief
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro C hC
    exact Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.mem_powerset.mp hC) h)
  · intro C _ _
    exact m.m_nonneg C

end Belief

namespace Plausibility

variable (m : MassFunction Ω)

/-- Plausibility of empty set is 0. -/
theorem empty : plausibility m ∅ = 0 := by
  simp only [plausibility, Finset.inter_empty, Finset.not_nonempty_empty,
             Finset.filter_false, Finset.sum_empty]

/-- Plausibility is non-negative. -/
theorem nonneg (A : Finset Ω) : 0 ≤ plausibility m A := by
  apply Finset.sum_nonneg
  intro B _
  exact m.m_nonneg B

/-- Plausibility is bounded by 1. -/
theorem le_one (A : Finset Ω) : plausibility m A ≤ 1 := by
  -- Sum over filtered set ≤ sum over all sets = 1
  unfold plausibility
  calc ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B
      ≤ ∑ B ∈ Finset.univ.powerset, m.m B := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro B _ _
            exact m.m_nonneg B
    _ = 1 := m.m_sum_one

end Plausibility

/-!
## §3: Key Properties
-/

/-- Belief is bounded by plausibility: Bel(A) ≤ Pl(A).
    Proof: Every set contributing to Bel(A) also contributes to Pl(A). -/
theorem belief_le_plausibility (m : MassFunction Ω) (A : Finset Ω) :
    belief m A ≤ plausibility m A := by
  -- Strategy: Split belief sum at ∅, show nonempty subsets of A are in plausibility sum
  unfold belief plausibility
  -- Split A.powerset into {∅} and nonempty subsets
  have h_split : A.powerset = {∅} ∪ A.powerset.filter (fun B => B.Nonempty) := by
    ext B
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter]
    constructor
    · intro hB
      by_cases hBe : B = ∅
      · left; exact hBe
      · right; exact ⟨hB, Finset.nonempty_iff_ne_empty.mpr hBe⟩
    · intro h
      cases h with
      | inl h => simp [h]
      | inr h => exact h.1
  rw [h_split, Finset.sum_union]
  · simp only [Finset.sum_singleton, m.m_empty, zero_add]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro B hB
      rw [Finset.mem_filter] at hB ⊢
      constructor
      · exact Finset.mem_powerset.mpr (Finset.subset_univ B)
      · have hBA : B ⊆ A := Finset.mem_powerset.mp hB.1
        rw [Finset.inter_eq_left.mpr hBA]
        exact hB.2
    · intro B _ _
      exact m.m_nonneg B
  · rw [Finset.disjoint_singleton_left]
    simp only [Finset.mem_filter, Finset.not_nonempty_empty, and_false, not_false_eq_true]

/-- The complement in a finite type. -/
def complement (A : Finset Ω) : Finset Ω := Finset.univ \ A

/-- Plausibility-belief duality: Pl(A) = 1 - Bel(Aᶜ).
    (Statement; proof requires careful sum manipulation) -/
theorem plausibility_eq_one_sub_belief_compl (m : MassFunction Ω) (A : Finset Ω) :
    plausibility m A = 1 - belief m (complement A) := by
  -- Pl(A) + Bel(Aᶜ) = 1 because:
  -- Pl(A) sums over sets intersecting A
  -- Bel(Aᶜ) sums over sets contained in Aᶜ (= not intersecting A)
  -- Together they partition all sets
  unfold plausibility belief complement
  -- Key: B ⊆ (univ \ A) ↔ B ∩ A = ∅ ↔ ¬(B ∩ A).Nonempty
  have h_partition : Finset.univ.powerset =
      (Finset.univ \ A).powerset ∪
      Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty) := by
    ext B
    simp only [Finset.mem_union, Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro hB
      by_cases h : (B ∩ A).Nonempty
      · right; exact ⟨hB, h⟩
      · left
        rw [Finset.not_nonempty_iff_eq_empty] at h
        intro x hxB
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hxA
        have : x ∈ B ∩ A := Finset.mem_inter.mpr ⟨hxB, hxA⟩
        rw [h] at this
        exact Finset.notMem_empty x this
    · intro h
      cases h with
      | inl hB =>
        -- hB : B ⊆ (univ \ A) (simp already converted mem_powerset)
        exact Finset.Subset.trans hB Finset.sdiff_subset
      | inr hB => exact hB.1
  have h_disjoint : Disjoint (Finset.univ \ A).powerset
      (Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty)) := by
    rw [Finset.disjoint_iff_ne]
    intro B hB C hC
    rw [Finset.mem_powerset] at hB
    rw [Finset.mem_filter] at hC
    intro hBC
    subst hBC
    -- B ⊆ univ \ A, so B ∩ A = ∅, contradicting hC.2
    have h_empty : B ∩ A = ∅ := by
      ext x
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hxB hxA
      have hx : x ∈ Finset.univ \ A := hB hxB
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
      exact hx hxA
    rw [h_empty] at hC
    exact Finset.not_nonempty_empty hC.2
  -- From partition: 1 = Bel(Aᶜ) + Pl(A), so Pl(A) = 1 - Bel(Aᶜ)
  have h_sum : ∑ B ∈ Finset.univ.powerset, m.m B =
      ∑ B ∈ (Finset.univ \ A).powerset, m.m B +
      ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B := by
    conv_lhs => rw [h_partition]
    rw [Finset.sum_union h_disjoint]
  rw [m.m_sum_one] at h_sum
  -- h_sum : 1 = Bel(Aᶜ) + Pl(A)
  -- Goal: Pl(A) = 1 - Bel(Aᶜ)
  -- Let's name the sums for clarity
  set bel := ∑ B ∈ (Finset.univ \ A).powerset, m.m B with hbel
  set pl := ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B with hpl
  -- h_sum : 1 = bel + pl
  -- Goal: pl = 1 - bel
  linarith

/-!
## §4: Connection to Imprecise Probability
-/

/-- A belief function induces a lower probability on events. -/
def toLowerProbability (m : MassFunction Ω) : Finset Ω → ℝ := belief m

/-- A belief function induces an upper probability on events. -/
def toUpperProbability (m : MassFunction Ω) : Finset Ω → ℝ := plausibility m

/-- The gap between upper and lower probability measures imprecision. -/
def imprecisionGap (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  plausibility m A - belief m A

/-- Imprecision gap is non-negative. -/
theorem imprecisionGap_nonneg (m : MassFunction Ω) (A : Finset Ω) :
    0 ≤ imprecisionGap m A := by
  simp only [imprecisionGap]
  exact sub_nonneg.mpr (belief_le_plausibility m A)

/-!
## §5: Special Cases
-/

/-- A mass function is **Bayesian** if all mass is on singletons. -/
def MassFunction.isBayesian (m : MassFunction Ω) : Prop :=
  ∀ A : Finset Ω, m.m A ≠ 0 → A.card = 1

/-- A mass function is **vacuous** if all mass is on Ω (complete ignorance). -/
def MassFunction.isVacuous (m : MassFunction Ω) : Prop :=
  m.m Finset.univ = 1 ∧ ∀ A : Finset Ω, A ≠ Finset.univ → m.m A = 0

/-- Helper: singletons contained in A are exactly singletons intersecting A. -/
private lemma singleton_subset_iff_inter_nonempty {A : Finset Ω} {x : Ω} :
    {x} ⊆ A ↔ ({x} ∩ A).Nonempty := by
  rw [Finset.singleton_subset_iff]
  constructor
  · intro hxA
    rw [Finset.singleton_inter_of_mem hxA]
    exact Finset.singleton_nonempty x
  · intro h
    by_contra hxnA
    rw [Finset.singleton_inter_of_notMem hxnA] at h
    exact Finset.not_nonempty_empty h

/-- For Bayesian mass functions, Bel = Pl (precise probability). -/
theorem bayesian_precise (m : MassFunction Ω) (hb : m.isBayesian) (A : Finset Ω) :
    belief m A = plausibility m A := by
  -- When all focal elements are singletons, a singleton either
  -- is contained in A (contributes to Bel) or intersects A (same thing)
  -- Key: for singleton {x}, {x} ⊆ A ↔ x ∈ A ↔ {x} ∩ A ≠ ∅
  apply le_antisymm
  · exact belief_le_plausibility m A
  · -- Show Pl(A) ≤ Bel(A) for Bayesian case
    -- For Bayesian m, only singletons have nonzero mass
    -- We'll show: every B with m(B) ≠ 0 that intersects A is a subset of A
    unfold belief plausibility
    -- Filter to sets with nonzero mass
    have h_bel : ∑ B ∈ A.powerset, m.m B =
        ∑ B ∈ A.powerset.filter (fun B => m.m B ≠ 0), m.m B := by
      symm
      apply Finset.sum_filter_ne_zero
    have h_pl : ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B =
        ∑ B ∈ (Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty)).filter
            (fun B => m.m B ≠ 0), m.m B := by
      symm
      apply Finset.sum_filter_ne_zero
    rw [h_bel, h_pl]
    -- Now show these two filtered sets are equal, hence sums are equal
    have h_eq : (Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty)).filter
        (fun B => m.m B ≠ 0) = A.powerset.filter (fun B => m.m B ≠ 0) := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      constructor
      · intro ⟨hinter, hne⟩
        constructor
        · -- B ⊆ A because B is a singleton (by Bayesian) intersecting A
          have hcard := hb B hne
          rw [Finset.card_eq_one] at hcard
          obtain ⟨x, hBx⟩ := hcard
          rw [hBx]
          rw [hBx] at hinter
          exact singleton_subset_iff_inter_nonempty.mpr hinter
        · exact hne
      · intro ⟨hBA, hne⟩
        constructor
        · -- B ⊆ A, so if B nonempty, B ∩ A = B is nonempty
          have hcard := hb B hne
          rw [Finset.card_eq_one] at hcard
          obtain ⟨x, hBx⟩ := hcard
          rw [hBx] at hBA ⊢
          exact singleton_subset_iff_inter_nonempty.mp hBA
        · exact hne
    rw [h_eq]

/-!
## §6: Dempster's Rule of Combination
-/

/-- The conflict between two mass functions.
    K = Σ_{A ∩ B = ∅} m₁(A) · m₂(B) -/
noncomputable def conflict (m₁ m₂ : MassFunction Ω) : ℝ :=
  ∑ p ∈ (Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
        (fun p => (p.1 ∩ p.2) = ∅),
    m₁.m p.1 * m₂.m p.2

/-- Two mass functions are combinable if their conflict is less than 1. -/
def areCombinableDS (m₁ m₂ : MassFunction Ω) : Prop := conflict m₁ m₂ < 1

/-- Unnormalized combination: the raw product before normalization. -/
noncomputable def unnormalizedCombine (m₁ m₂ : MassFunction Ω) (C : Finset Ω) : ℝ :=
  ∑ p ∈ (Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
        (fun p => p.1 ∩ p.2 = C),
    m₁.m p.1 * m₂.m p.2

/-- Dempster's rule of combination (assuming combinability).
    m₁₂(C) = (1/(1-K)) · Σ_{A ∩ B = C} m₁(A) · m₂(B)  for C ≠ ∅ -/
noncomputable def dempsterCombineValue (m₁ m₂ : MassFunction Ω)
    (_hcomb : areCombinableDS m₁ m₂) (C : Finset Ω) : ℝ :=
  if C = ∅ then 0
  else (1 - conflict m₁ m₂)⁻¹ * unnormalizedCombine m₁ m₂ C

/-!
## §7: Connection to Common Infrastructure

Belief functions fit into the unified uncertainty framework from Common.Valuation.
-/

section CommonFramework

open Mettapedia.ProbabilityTheory.Common

variable (m : MassFunction Ω)

/-- Belief function as a monotone valuation. -/
def beliefAsMonotone : MonotoneValuation (Finset Ω) where
  val := belief m
  mono := fun _ _ h => Belief.mono m h

/-- Belief function as a normalized valuation.
    This captures: Bel(∅) = 0, Bel(Ω) = 1, and monotonicity. -/
def beliefAsNormalized : NormalizedValuation (Finset Ω) where
  val := belief m
  mono := fun _ _ h => Belief.mono m h
  val_bot := Belief.empty m
  val_top := Belief.univ m

/-- The belief/plausibility pair as an imprecise valuation.
    This unifies D-S with the general theory of imprecise probability. -/
def toImpreciseValuation : ImpreciseValuation (Finset Ω) where
  lower := beliefAsNormalized m
  upper := plausibility m
  lower_le_upper := belief_le_plausibility m
  upper_top := by
    -- Pl(Ω) = 1 - Bel(∅) = 1 - 0 = 1
    rw [plausibility_eq_one_sub_belief_compl]
    simp [complement, Belief.empty]

/-- The imprecision gap from Common.Valuation matches our definition. -/
theorem imprecisionGap_eq_common_gap (A : Finset Ω) :
    imprecisionGap m A = (toImpreciseValuation m).gap A := rfl

/-- Bayesian mass functions correspond to precise valuations. -/
theorem bayesian_isPrecise (hb : m.isBayesian) :
    (toImpreciseValuation m).IsPrecise := by
  intro A
  exact bayesian_precise m hb A

end CommonFramework

/-!
## §8: Unification with Lattice-Based Framework

The power set lattice (Finset Ω) is a Boolean algebra, hence an orthomodular lattice.
Classical D-S belief functions are thus a special case of belief functions on
orthomodular lattices, connecting to the quantum D-S theory from NovelTheories.lean.
-/

section LatticeUnification

open Mettapedia.ProbabilityTheory.Common

variable (m : MassFunction Ω)

/-- Classical D-S mass function viewed as a lattice mass function.
    The power set forms a Boolean algebra, so this connects to the
    orthomodular lattice framework used for quantum belief functions. -/
def toLatticeSum (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  Finset.sum (Finset.filter (· ⊆ A) Finset.univ.powerset) m.m

/-- The lattice-based sum equals the classical belief function.
    This shows that summing over {B | B ≤ A} in the lattice (Finset Ω, ⊆)
    is the same as summing over {B | B ⊆ A} in the power set. -/
theorem latticeSum_eq_belief (A : Finset Ω) : toLatticeSum m A = belief m A := by
  unfold toLatticeSum belief
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro ⟨_, hBA⟩
    exact hBA
  · intro hBA
    exact ⟨Finset.subset_univ B, hBA⟩

/-- The power set forms a bounded order with ∅ as ⊥ and univ as ⊤.
    This is the lattice structure underlying D-S belief functions. -/
theorem powerset_bounded :
    (⊥ : Finset Ω) = ∅ ∧ (⊤ : Finset Ω) = Finset.univ := by
  constructor <;> rfl

/-- Key insight: Classical D-S belief = lattice belief via sumBelow.
    This unifies the D-S formulation with the quantum/orthomodular formulation.

    When the lattice is a Boolean algebra (power set), the two formulations
    are identical. This is the foundation for the hypercube unification. -/
theorem ds_eq_lattice_belief (A : Finset Ω) :
    belief m A = Finset.sum (Finset.filter (fun B => B ≤ A) Finset.univ) m.m := by
  unfold belief
  congr 1
  ext B
  -- In the power set lattice, B ≤ A iff B ⊆ A iff B ∈ A.powerset
  simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_univ, true_and]
  -- For Finset, the order is ⊆
  rfl

/-- D-S belief functions form an OrthoadditiveValuation on the power set lattice.
    This connects classical D-S to the generalized lattice valuation framework.

    Key property: For disjoint sets A ∩ B = ∅, we have
    Bel(A ∪ B) ≥ Bel(A) + Bel(B)
    (This is the subadditivity property characteristic of belief functions.) -/
theorem ds_is_monotone_on_lattice : ∀ A B : Finset Ω, A ⊆ B → belief m A ≤ belief m B :=
  fun _ _ h => Belief.mono m h

end LatticeUnification

/-!
## §9: Bridge to Quantum Dempster-Shafer

The power set (Finset Ω, ⊆) is a **Boolean algebra**, which is a special case of an
orthomodular lattice. This section shows that classical D-S belief functions are
exactly quantum D-S belief functions on Boolean lattices.

### Key Insight

The Finset lattice satisfies:
- Distributivity: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
- Complementation: A ∩ Aᶜ = ∅ and A ∪ Aᶜ = Ω
- Orthomodularity (weaker than distributivity): automatically satisfied

In Boolean algebras, all elements commute, so:
- `commutes A B` holds for all A, B
- Sasaki projection = ordinary meet: `sasakiProj A B = A ∩ B`
- Quantum D-S reduces to classical D-S
-/

section QuantumBridge

open Mettapedia.ProbabilityTheory.Common
open Mettapedia.ProbabilityTheory.Hypercube.NovelTheories

/-!
### The Power Set as an Orthomodular Lattice

Finset Ω with ⊆ forms a Boolean algebra. The complement operation is
`Finset.univ \ A`. Since Boolean algebras are orthomodular, we can
treat Finset Ω as an instance of OrthomodularLattice.
-/

/-- The power set complement: Aᶜ = Ω \ A. -/
instance finsetHasCompl : HasCompl (Finset Ω) where
  compl := fun A => Finset.univ \ A

/-- Finset Ω forms an orthomodular lattice (via Boolean algebra). -/
instance finsetOrthomodular : OrthomodularLattice (Finset Ω) where
  -- Orthomodularity: a ≤ b → b = a ⊔ (b ⊓ aᶜ)
  -- In Boolean algebra, this is: b = a ∪ (b ∩ (Ω \ a)) = a ∪ (b \ a) = b ✓
  orthomodular := fun a b hab => by
    ext x
    simp only [sup_eq_union, inf_eq_inter, HasCompl.compl]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
               Finset.mem_univ, true_and]
    constructor
    · intro hxb
      by_cases hxa : x ∈ a
      · left; exact hxa
      · right; exact ⟨hxb, hxa⟩
    · intro h
      cases h with
      | inl hxa => exact hab hxa
      | inr hxb => exact hxb.1
  -- Double complement: (Ω \ (Ω \ A)) = A
  compl_compl := fun a => by simp [HasCompl.compl, Finset.sdiff_sdiff_eq_self (Finset.subset_univ a)]
  -- De Morgan: (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ
  compl_sup := fun a b => by
    ext x
    simp only [sup_eq_union, inf_eq_inter, HasCompl.compl,
               Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union,
               Finset.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨fun ha => hx (Or.inl ha), fun hb => hx (Or.inr hb)⟩
    · intro ⟨hna, hnb⟩ hab
      exact hab.elim hna hnb
  -- De Morgan: (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ
  compl_inf := fun a b => by
    ext x
    simp only [sup_eq_union, inf_eq_inter, HasCompl.compl,
               Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
               Finset.mem_univ, true_and]
    constructor
    · intro hx
      by_cases ha : x ∈ a
      · right; intro hb; exact hx ⟨ha, hb⟩
      · left; exact ha
    · intro h ⟨ha, hb⟩
      exact h.elim (fun hna => hna ha) (fun hnb => hnb hb)
  -- ⊥ᶜ = ⊤
  compl_bot := by simp [HasCompl.compl]
  -- ⊤ᶜ = ⊥
  compl_top := by simp [HasCompl.compl]
  -- A ∩ Aᶜ = ⊥
  inf_compl_self := fun a => by simp [HasCompl.compl]
  -- A ∪ Aᶜ = ⊤
  sup_compl_self := fun a => by simp [HasCompl.compl]

/-- In the Finset OrthomodularLattice, complement matches set difference from univ. -/
theorem finset_compl_eq_sdiff (A : Finset Ω) : Aᶜ = Finset.univ \ A := rfl

/-!
### Converting Classical Mass to Quantum Mass

A classical MassFunction Ω induces a QuantumMassFunction on Finset Ω.
-/

/-- Convert a classical mass function to a quantum mass function on the power set. -/
def MassFunction.toQuantumMass (m : MassFunction Ω) : QuantumMassFunction (Finset Ω) where
  m := m.m
  m_bot := m.m_empty
  m_nonneg := m.m_nonneg

/-!
### The Bridge Theorem

Classical belief = quantum belief on Boolean lattices.
-/

/-- The key bridge theorem: classical D-S belief equals quantum belief on Boolean lattices.

    This shows that quantum D-S theory generalizes classical D-S theory:
    - On Boolean algebras (like power sets), they coincide
    - On non-Boolean orthomodular lattices, quantum D-S captures new phenomena

    This unifies the probability hypercube: classical D-S is the "commutative" vertex,
    quantum D-S is the "non-commutative" generalization along the commutativity axis. -/
theorem belief_eq_quantum_belief (m : MassFunction Ω) (A : Finset Ω) :
    belief m A = (m.toQuantumMass).belief A := by
  -- Both compute: Σ_{B ≤ A} m(B)
  -- Classical uses: Σ_{B ∈ A.powerset} m(B)
  -- Quantum uses: sumBelow m A = Σ_{B | B ≤ A} m(B)
  -- In Finset Ω, B ≤ A ↔ B ⊆ A ↔ B ∈ A.powerset
  unfold belief QuantumMassFunction.belief MassFunction.toQuantumMass sumBelow finsetBelow
  congr 1
  ext B
  simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_univ, true_and]
  -- B ∈ A.powerset ↔ B ⊆ A, and B ≤ A in the lattice order ↔ B ⊆ A
  rfl

/-- Corollary: plausibility also matches. -/
theorem plausibility_eq_quantum_plausibility (m : MassFunction Ω) (A : Finset Ω) :
    plausibility m A = (m.toQuantumMass).plausibility A := by
  -- Pl(A) = 1 - Bel(Aᶜ) in both frameworks
  -- Classical: Pl(A) = 1 - Bel(Ω \ A)
  -- Quantum: Pl(A) = 1 - Bel(Aᶜ)
  -- Since Aᶜ = Ω \ A in our instance, they match
  unfold QuantumMassFunction.plausibility
  rw [← belief_eq_quantum_belief m Aᶜ]
  rw [plausibility_eq_one_sub_belief_compl]
  simp only [complement, finset_compl_eq_sdiff]

/-- In Boolean algebras, all elements commute (quantum reduces to classical). -/
theorem finset_all_commute (A B : Finset Ω) : commutes A B := by
  -- commutes A B := A = (A ⊓ B) ⊔ (A ⊓ Bᶜ)
  -- In sets: A = (A ∩ B) ∪ (A ∩ (Ω \ B)) = (A ∩ B) ∪ (A \ B) = A ✓
  simp only [commutes, inf_eq_inter, sup_eq_union]
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, finset_compl_eq_sdiff,
             Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hA
    by_cases hB : x ∈ B
    · left; exact ⟨hA, hB⟩
    · right; exact ⟨hA, hB⟩
  · intro h
    cases h with
    | inl h => exact h.1
    | inr h => exact h.1

/-- In Boolean algebras, Sasaki projection = ordinary meet. -/
theorem finset_sasaki_eq_inf (A B : Finset Ω) : sasakiProj A B = A ⊓ B := by
  -- sasakiProj A B = (B ⊔ Aᶜ) ⊓ A
  -- = (B ∪ (Ω \ A)) ∩ A
  -- = (B ∩ A) ∪ ((Ω \ A) ∩ A)   [by distributivity]
  -- = (B ∩ A) ∪ ∅
  -- = A ∩ B
  simp only [sasakiProj, inf_eq_inter, sup_eq_union, finset_compl_eq_sdiff]
  ext x
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
             Finset.mem_univ, true_and]
  constructor
  · intro ⟨hBorNotA, hA⟩
    constructor
    · exact hA
    · cases hBorNotA with
      | inl hB => exact hB
      | inr hNotA => exact absurd hA hNotA
  · intro ⟨hA, hB⟩
    exact ⟨Or.inl hB, hA⟩

/-- Summary: Classical D-S is the Boolean case of Quantum D-S.

    This establishes the hypercube relationship:
    - Quantum D-S lives on orthomodular lattices (non-commutative events)
    - Classical D-S lives on Boolean algebras (commutative events)
    - The bridge is: Boolean ⊆ Orthomodular, and on Boolean they coincide -/
theorem classical_ds_is_boolean_quantum_ds :
    ∀ m : MassFunction Ω, ∀ A : Finset Ω,
      belief m A = (m.toQuantumMass).belief A ∧
      plausibility m A = (m.toQuantumMass).plausibility A :=
  fun m A => ⟨belief_eq_quantum_belief m A, plausibility_eq_quantum_plausibility m A⟩

end QuantumBridge

end Mettapedia.ProbabilityTheory.BeliefFunctions
