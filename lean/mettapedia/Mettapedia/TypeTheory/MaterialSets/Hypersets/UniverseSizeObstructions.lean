import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassMembers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLiftCoherence

/-!
# Material size bounds and ambient enclosure obstructions

Every material member type is small at its graph bound. The ambient carrier
is not: a hypothetical small equivalence would construct a membership graph
and a set containing all its decorations, contradicting separation.

These statements separate member smallness from an internally small ambient
universe. The raised carrier of lower material values really exists, but it
cannot be the image of any lower value. No classical shrinking operation is
used in either argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions

open AccessiblePointedGraph

universe u

/-- The small graph of the entire membership carrier would make that carrier
an actual material set. This argument eliminates the equivalence only into
its propositional contradiction, without selecting global representatives. -/
theorem ambient_not_small : ¬ Small.{u} HSet.{u} := by
  intro small
  obtain ⟨Carrier, ⟨equivalence⟩⟩ := small.equiv_small
  let edge (source target : Carrier) : Prop := equivalence.symm target ∈ equivalence.symm source
  have lawful : HSet.IsDecoration edge equivalence.symm := by
    intro source value
    constructor
    · intro member
      exact ⟨equivalence value, by simpa only [edge, Equiv.symm_apply_apply] using member,
        equivalence.symm_apply_apply value⟩
    · rintro ⟨target, available, rfl⟩
      exact available
  let whole : HSet.{u} := HSet.range (fun root : Carrier => generated edge root)
  apply HSet.not_exists_universal
  refine ⟨whole, fun value => ?_⟩
  apply HSet.mem_range.mpr
  refine ⟨equivalence value, ?_⟩
  change HSet.decorate edge (equivalence value) = value
  rw [← lawful.eq_decorate]
  exact equivalence.symm_apply_apply value

/-- The same carrier nevertheless has small members. This pair of facts is
not a choice of a smaller ambient carrier or a conditional universe tower. -/
theorem members_small_ambient_large :
    (∀ value : HSet.{u}, Small.{u} (Mettapedia.TypeTheory.MaterialSets.El (· ∈ ·) value)) ∧
      ¬ Small.{u} HSet.{u} :=
  ⟨HSet.small_el_constructive, ambient_not_small⟩

#print axioms ambient_not_small
#print axioms members_small_ambient_large

end Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions
