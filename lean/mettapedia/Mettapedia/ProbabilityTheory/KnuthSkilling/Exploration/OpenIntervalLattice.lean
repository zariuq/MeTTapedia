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
import Mathlib.Topology.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompleteLattice

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Exploration

open Set Topology

/-! ## Section 1: The Lattice of Open Sets -/

/-- The type of open sets of ℝ -/
def OpenSet (X : Type*) [TopologicalSpace X] := {s : Set X // IsOpen s}

/-- Open sets form a complete lattice under inclusion -/
instance (X : Type*) [TopologicalSpace X] : CompleteLattice (OpenSet X) where
  le := fun U V => U.val ⊆ V.val
  lt := fun U V => U.val ⊂ V.val
  le_refl := fun U => Set.Subset.refl U.val
  le_trans := fun _ _ _ hab hbc => Set.Subset.trans hab hbc
  lt_iff_le_not_le := fun U V => Set.ssubset_iff_subset_not_subset
  le_antisymm := fun U V hab hba => Subtype.ext (Set.Subset.antisymm hab hba)
  sup := fun U V => ⟨U.val ∪ V.val, U.prop.union V.prop⟩
  le_sup_left := fun U V => Set.subset_union_left
  le_sup_right := fun U V => Set.subset_union_right
  sup_le := fun U V W hUW hVW => Set.union_subset hUW hVW
  inf := fun U V => ⟨U.val ∩ V.val, U.prop.inter V.prop⟩
  inf_le_left := fun U V => Set.inter_subset_left
  inf_le_right := fun U V => Set.inter_subset_right
  le_inf := fun U V W hUV hUW => Set.subset_inter hUV hUW
  sSup := fun S => ⟨⋃ U ∈ S, U.val, isOpen_biUnion (fun U _ => U.prop)⟩
  le_sSup := fun S U hU x hx => Set.mem_biUnion hU hx
  sSup_le := fun S U h x ⟨V, hVS, hxV⟩ => h V hVS hxV
  sInf := fun S => ⟨interior (⋂ U ∈ S, U.val), isOpen_interior⟩
  sInf_le := fun S U hU => Set.interior_subset.trans (Set.biInter_subset_of_mem hU)
  le_sInf := fun S U h => Set.subset_interior_iff_isOpen.mpr U.prop |>.trans
    (Set.interior_mono (Set.subset_biInter h))
  top := ⟨Set.univ, isOpen_univ⟩
  bot := ⟨∅, isOpen_empty⟩
  le_top := fun U => Set.subset_univ U.val
  bot_le := fun U => Set.empty_subset U.val

/-! ## Section 2: Disjointness in Open Sets -/

/-- Two open sets are disjoint if their intersection is empty -/
def OpenSet.Disjoint {X : Type*} [TopologicalSpace X] (U V : OpenSet X) : Prop :=
  U.val ∩ V.val = ∅

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
    (f : ℕ → OpenSet X) : IsOpen (⋃ n, (f n).val) :=
  isOpen_iUnion (fun n => (f n).prop)

/-- Finite additivity extends to any finite subfamily -/
theorem finite_additivity_extends {X : Type*} [TopologicalSpace X]
    (m : KSOpenMeasure X) (f : ℕ → OpenSet X) (hpd : OpenSet.PairwiseDisjoint f)
    (n : ℕ) : m.μ ⟨⋃ i < n, (f i).val, isOpen_biUnion (fun i _ => (f i).prop)⟩ =
              ∑ i in Finset.range n, m.μ (f i) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Set.iUnion_empty, Set.iUnion_of_empty]
    exact m.empty
  | succ k ih =>
    sorry -- Proof by induction using add_disjoint

/-! ## Section 6: The Gap - Why Frame Structure Alone Isn't Enough -/

/--
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
      ∀ n, m.μ ⟨⋃ i < n, (f i).val, isOpen_biUnion (fun i _ => (f i).prop)⟩ =
           ∑ i in Finset.range n, m.μ (f i)) →
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

/--
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
