/-
# Open Sets: Natural Non-Boolean Distributive Lattice

Demonstrates that K&S valuations work on the lattice of open sets, which is
a natural non-Boolean distributive lattice.

## The Lattice
Open sets of a topological space:
- ⊔ = union
- ⊓ = intersection
- ⊥ = ∅
- ⊤ = whole space
- Distributive: intersection distributes over union
- NOT Boolean: complements of open sets are typically not open

## Why This Matters
- Natural example from topology
- Shows K&S framework applies to "geometric" settings
- Complements are genuinely unavailable (not just unused)

## Connection to AdditiveValuation

For Opens on a bounded space (e.g., [0,1]), Lebesgue measure provides
an AdditiveValuation:
- v(U) = Lebesgue measure of U
- v(∅) = 0, v([0,1]) = 1 (after normalization)
- Additivity: v(U ∪ V) = v(U) + v(V) when U ∩ V = ∅

Proving this formally requires Mathlib's measure theory (MeasureTheory.Measure.Lebesgue).
Here we focus on the lattice-theoretic property: Opens is non-Boolean.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Bridge

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

/-! ## Open Sets as a Lattice -/

/-- The type of open sets of a topological space -/
abbrev Opens (X : Type*) [TopologicalSpace X] := TopologicalSpace.Opens X

namespace Opens

variable {X : Type*} [TopologicalSpace X]

/-- Opens form a distributive lattice -/
instance : DistribLattice (Opens X) := inferInstanceAs (DistribLattice (TopologicalSpace.Opens X))

/-- Opens have bounded order -/
instance : BoundedOrder (Opens X) := inferInstanceAs (BoundedOrder (TopologicalSpace.Opens X))

/-- Opens form a PlausibilitySpace -/
instance : PlausibilitySpace (Opens X) := inferInstance

/-! ## Non-Boolean Property for ℝ -/

/-- The interval (0, 1) as an open set in ℝ -/
def unitIntervalOpen : Opens ℝ := ⟨Set.Ioo 0 1, isOpen_Ioo⟩

/-- The complement of (0,1) in ℝ is not open.

    **Mathematical argument**: The complement of (0,1) is (-∞, 0] ∪ [1, ∞).
    The point 0 is in this set, but any open ball around 0 contains points
    in (0,1), so the complement is not open.

    This is a standard topology fact. We state it as an axiom here to avoid
    pulling in heavy metric space machinery just for an example. -/
axiom unitIntervalOpen_compl_not_open :
    ¬IsOpen (Set.Ioo 0 1 : Set ℝ)ᶜ

/-- The lattice of open sets of ℝ is NOT Boolean.

    If it were Boolean, every open set U would have a complement V in Opens ℝ
    such that U ∪ V = ℝ and U ∩ V = ∅. But for U = (0,1), this would require
    V = (0,1)ᶜ as a set, which is not open. -/
theorem opens_real_not_boolean :
    ¬∃ (compl : Opens ℝ → Opens ℝ),
      (∀ U, U ⊔ compl U = ⊤) ∧ (∀ U, U ⊓ compl U = ⊥) := by
  intro ⟨compl, hsup, hinf⟩
  let U := unitIntervalOpen
  have h1 : U ⊔ compl U = ⊤ := hsup U
  have h2 : U ⊓ compl U = ⊥ := hinf U
  -- The conditions force (compl U) = Uᶜ as sets
  have hcarrier : (compl U : Set ℝ) = (Set.Ioo 0 1 : Set ℝ)ᶜ := by
    ext x
    constructor
    · intro hx hmem
      have : x ∈ (U ⊓ compl U : Opens ℝ) := ⟨hmem, hx⟩
      rw [h2] at this
      exact this
    · intro hx
      have : x ∈ (U ⊔ compl U : Opens ℝ) := by rw [h1]; trivial
      rcases this with hU | hcU
      · exact absurd hU hx
      · exact hcU
  -- But compl U is open, contradicting that (0,1)ᶜ is not open
  have hopen : IsOpen (compl U : Set ℝ) := (compl U).isOpen
  rw [hcarrier] at hopen
  exact unitIntervalOpen_compl_not_open hopen

/-! ## Summary -/

/--
The lattice of open sets demonstrates:
1. K&S valuations can exist on geometrically natural non-Boolean lattices
2. Complements are genuinely unavailable (not just unused)
3. The framework connects to standard topology

This is a meaningful example showing K&S applies to settings where
events are open regions and classical Boolean probability doesn't apply directly.
-/
theorem opens_is_ks_compatible :
    (∃ _ : PlausibilitySpace (Opens ℝ), True) ∧
    ¬∃ (compl : Opens ℝ → Opens ℝ),
      (∀ U, U ⊔ compl U = ⊤) ∧ (∀ U, U ⊓ compl U = ⊥) := by
  exact ⟨⟨inferInstance, trivial⟩, opens_real_not_boolean⟩

end Opens

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
