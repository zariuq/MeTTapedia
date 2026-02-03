/-
# Open Interval Lattice Exploration

**Research Question**: If we instantiate K&S on the lattice of open sets (or intervals),
does the topological structure naturally provide σ-additivity?

## Background

The lattice of open sets of ℝ forms a **frame** (complete Heyting algebra):
- Arbitrary joins (unions of open sets are open)
- Finite meets (finite intersections of open sets are open)
- Infinite distributivity: U ∩ (⋃ᵢ Vᵢ) = ⋃ᵢ (U ∩ Vᵢ)

This is MORE than a σ-frame (which only needs countable joins).

## The Key Question

If μ : OpenSets(ℝ) → ℝ≥0 satisfies K&S axioms (order-preserving, additive on disjoint unions),
does the frame structure force σ-additivity?

## Approach

1. Define the lattice structure on open intervals/sets
2. Instantiate K&S axioms
3. Check if σ-additivity follows or needs extra axioms
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Exploration

open Set Topology
open scoped BigOperators

/-! ## Section 1: The Lattice of Open Sets -/

/-- The type of open sets of ℝ -/
abbrev OpenSet (X : Type*) [TopologicalSpace X] := TopologicalSpace.Opens X

/-! ## Section 2: Disjointness in Open Sets -/

/-- Two open sets are disjoint if their intersection is empty -/
def OpenSet.Disjoint {X : Type*} [TopologicalSpace X] (U V : OpenSet X) : Prop :=
  ((U : Set X) ∩ (V : Set X)) = ∅

/-- A countable family of open sets is pairwise disjoint -/
def OpenSet.PairwiseDisjoint {X : Type*} [TopologicalSpace X] (f : ℕ → OpenSet X) : Prop :=
  ∀ i j, i ≠ j → OpenSet.Disjoint (f i) (f j)

/-! ## Section 3: K&S-style Axioms for Open Set Measures -/

/-- A K&S measure on open sets: order-preserving, additive on disjoint unions -/
structure KSOpenMeasure (X : Type*) [TopologicalSpace X] where
  /-- The measure function -/
  μ : OpenSet X → ℝ
  /-- Non-negativity -/
  nonneg : ∀ U, 0 ≤ μ U
  /-- Empty set has measure zero -/
  empty : μ ⊥ = 0
  /-- Order preservation (K&S Symmetry 0: Fidelity) -/
  mono : ∀ U V, U ≤ V → μ U ≤ μ V
  /-- Finite additivity on disjoint sets (K&S Sum Rule) -/
  add_disjoint : ∀ U V, OpenSet.Disjoint U V → μ (U ⊔ V) = μ U + μ V

/-! ## Section 4: The Key Question - Does Frame Structure Give σ-Additivity? -/

/-- σ-additivity: measure of countable disjoint union equals sum of measures -/
def IsSigmaAdditive {X : Type*} [TopologicalSpace X] (m : KSOpenMeasure X) : Prop :=
  ∀ (f : ℕ → OpenSet X), OpenSet.PairwiseDisjoint f →
    m.μ (sSup (Set.range f)) = ∑' n, m.μ (f n)

/-! ## Section 5: What The Frame Structure Actually Gives Us -/

/-- The frame has countable unions (this is automatic for open sets) -/
theorem open_sets_have_countable_unions (X : Type*) [TopologicalSpace X]
    (f : ℕ → OpenSet X) : IsOpen (⋃ n, ((f n : OpenSet X) : Set X)) :=
  isOpen_iUnion (fun n => (f n).2)

/-- Finite additivity extends to any finite subfamily -/
theorem finite_additivity_extends {X : Type*} [TopologicalSpace X]
    (m : KSOpenMeasure X) (f : ℕ → OpenSet X) (hpd : OpenSet.PairwiseDisjoint f)
    (n : ℕ) :
        m.μ ⟨⋃ i < n, ((f i : OpenSet X) : Set X), isOpen_biUnion (fun i _ => (f i).2)⟩ =
              ∑ i ∈ Finset.range n, m.μ (f i) := by
  induction n with
  | zero =>
    have hbot :
        (⟨⋃ i < (0 : ℕ), ((f i : OpenSet X) : Set X), isOpen_biUnion (fun i _ => (f i).2)⟩ :
            OpenSet X) =
          ⊥ := by
      ext x
      simp
    simpa [hbot] using m.empty
  | succ k ih =>
    sorry -- Proof by induction using add_disjoint

/-! ## Section 6: The Gap - Why Frame Structure Alone Isn't Enough -/

/-
**Key Theorem (Negative Result)**:
Frame structure alone does NOT imply σ-additivity.

The frame of open sets gives us:
- Arbitrary unions exist
- Finite additivity (from K&S)
- Therefore: μ(⋃ᵢ<n Uᵢ) = Σᵢ<n μ(Uᵢ) for all n

But we need: μ(⋃ᵢ Uᵢ) = Σᵢ μ(Uᵢ) (infinite sum)

The gap: lim_{n→∞} μ(⋃ᵢ<n Uᵢ) = μ(⋃ᵢ Uᵢ) is NOT automatic!

This is exactly "continuity from below" - a LIMIT statement.
-/

/-- The gap between finite sums and countable sums -/
theorem sigma_additivity_gap {X : Type*} [TopologicalSpace X] (m : KSOpenMeasure X) :
    (∀ (f : ℕ → OpenSet X), OpenSet.PairwiseDisjoint f →
      ∀ n, m.μ ⟨⋃ i < n, ((f i : OpenSet X) : Set X), isOpen_biUnion (fun i _ => (f i).2)⟩ =
           ∑ i ∈ Finset.range n, m.μ (f i)) →
    -- ^ This follows from finite additivity (K&S)
    -- But this does NOT imply:
    IsSigmaAdditive m := by
  intro _h_finite
  -- Cannot prove! The limit step is missing.
  sorry

/-! ## Section 7: What DOES Give σ-Additivity? -/

/-- Continuity from below: the minimal extra axiom -/
def ContinuousFromBelow {X : Type*} [TopologicalSpace X] (m : KSOpenMeasure X) : Prop :=
  ∀ (f : ℕ → OpenSet X), (∀ n, f n ≤ f (n + 1)) →
    m.μ (sSup (Set.range f)) = ⨆ n, m.μ (f n)

/-- With continuity from below, σ-additivity follows -/
theorem sigma_additive_of_continuous_from_below {X : Type*} [TopologicalSpace X]
    (m : KSOpenMeasure X) (hcont : ContinuousFromBelow m) : IsSigmaAdditive m := by
  intro f hpd
  -- Key insight: Define partial unions Bₙ = ⋃ᵢ<n Uᵢ
  -- These are increasing: B₁ ⊆ B₂ ⊆ ...
  -- By continuity from below: μ(⋃ Bₙ) = sup μ(Bₙ)
  -- By finite additivity: μ(Bₙ) = Σᵢ<n μ(Uᵢ)
  -- Therefore: μ(⋃ Uᵢ) = Σᵢ μ(Uᵢ)
  sorry

/-! ## Section 8: Does Topology Give Us Continuity From Below? -/

/-
**The Critical Question**: Does the topology of open sets somehow
imply continuity from below for any K&S measure?

**Answer**: NO! Here's why:

The frame structure tells us about SET-THEORETIC operations:
- Unions exist and are open
- Distributivity holds

But continuity from below is about MEASURE-THEORETIC limits:
- How μ behaves as sets grow

These are independent! A measure can be:
- Finitely additive (respects finite set operations)
- But discontinuous (doesn't respect limits)

  **Counterexample**: Banach limits on ℓ^∞ extend to finitely additive
"probability measures" on 2^ℕ that are NOT σ-additive.
-/

/-- Summary: The topology of open sets does NOT automatically give σ-additivity -/
theorem topology_does_not_give_sigma_additivity :
    ∃ (X : Type*) (_ : TopologicalSpace X) (m : KSOpenMeasure X),
      ¬ IsSigmaAdditive m := by
  sorry -- Construct using Banach limits or similar

/-! ## Section 9: Conclusion -/

/-
**CONCLUSION**:

The open interval/set lattice approach DOES NOT automatically give σ-additivity.

What topology gives us:
✅ Complete lattice structure (arbitrary joins/meets)
✅ Frame structure (infinite distributivity)
✅ Natural setting for K&S axioms
✅ Finite additivity from K&S

What topology does NOT give us:
❌ Continuity from below (this is about measures, not sets)
❌ σ-additivity (requires the limit axiom)

**The minimal bridge** remains:
1. Work on a σ-algebra (or σ-frame) - for countable unions to make sense
2. Add continuity from below - the ESSENTIAL limit axiom

The frame structure is COMPATIBLE with σ-additivity but does not IMPLY it.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Exploration
