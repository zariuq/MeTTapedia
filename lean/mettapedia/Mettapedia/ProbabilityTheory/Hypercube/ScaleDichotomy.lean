import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Scale Dichotomy: Discrete (ℤ-like) vs Dense (ℚ-like)

This module packages the standard theorem about additive subgroups of archimedean ordered groups:

> In an archimedean linearly ordered additive commutative group with order topology (in particular `ℝ`),
> every additive subgroup is either **dense** or **cyclic**.

For an additive group `G`, “cyclic” means “of the form `ℤ • g`” (`AddSubgroup.zmultiples g`),
i.e. a discrete scale.

This is the formal underpinning for the Hypercube’s “discrete vs dense” axis and its neighbors
(`ℤ`-like vs `ℚ`-like value scales).

Mathlib references:
- `AddSubgroup.dense_or_cyclic`
- `AddSubgroup.dense_xor'_cyclic`
- `AddSubgroup.dense_iff_ne_zmultiples`
 -/

namespace Mettapedia.ProbabilityTheory.Hypercube

namespace ScaleDichotomy

open Set

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [TopologicalSpace G] [OrderTopology G] [Archimedean G]

/-- In an archimedean ordered additive group with order topology, an additive subgroup is either
dense or a discrete `ℤ`-scale. -/
theorem dense_or_zmultiples (S : AddSubgroup G) :
    Dense (S : Set G) ∨ ∃ g : G, S = AddSubgroup.zmultiples g := by
  rcases AddSubgroup.dense_or_cyclic (S := S) with hDense | ⟨g, hg⟩
  · exact Or.inl hDense
  · refine Or.inr ⟨g, ?_⟩
    -- `closure {g} = zmultiples g`.
    calc
      S = AddSubgroup.closure {g} := hg
      _ = AddSubgroup.zmultiples g := (AddSubgroup.zmultiples_eq_closure g).symm

variable [Nontrivial G] [DenselyOrdered G]

/-- A sharper statement (exclusive-or): subgroups are dense iff they are not `ℤ • g`. -/
theorem dense_xor'_zmultiples (S : AddSubgroup G) :
    Xor' (Dense (S : Set G)) (∃ g : G, S = AddSubgroup.zmultiples g) := by
  exact AddSubgroup.dense_xor_cyclic S

/-- A convenient corollary: density is equivalent to not being any `ℤ • g`. -/
theorem dense_iff_ne_zmultiples {S : AddSubgroup G} :
    Dense (S : Set G) ↔ ∀ g : G, S ≠ AddSubgroup.zmultiples g := by
  simpa using (AddSubgroup.dense_iff_ne_zmultiples (s := S) : _)

end ScaleDichotomy

end Mettapedia.ProbabilityTheory.Hypercube
