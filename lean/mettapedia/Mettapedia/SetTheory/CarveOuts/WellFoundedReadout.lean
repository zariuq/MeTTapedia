import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet

/-!
# The boundary of the well-founded-member readout

The total map `HSet.toZFSet` retains the well-founded members of its argument.
It is a membership isomorphism on the actual well-founded subcarrier, but it
does not preserve membership on all hypersets: the Quine atom belongs to itself
and its image is empty. It also identifies the Quine atom with the empty set.

The exact positive statement allows any parent hyperset: testing membership of a
well-founded value agrees with testing its corresponding `ZFSet` in the readout.
This distinguishes the total readout from restriction to the well-founded part.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.WellFoundedReadout

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

/-- Membership of a `ZFSet` in the readout is exactly membership of its
well-founded embedding in the original hyperset. -/
theorem readout_mem_iff (z : ZFSet.{u}) (x : HSet.{u}) :
    z ∈ HSet.toZFSet x ↔ HSet.ofZFSet z ∈ x := by
  rw [← HSet.ofZFSet_mem_ofZFSet_iff, HSet.ofZFSet_toZFSet, HSet.mem_sep]
  exact ⟨And.left, fun h => ⟨h, HSet.wf_ofZFSet z⟩⟩

/-- A well-founded member can be tested against any parent, even one outside
the well-founded subcarrier. -/
theorem mem_iff_of_wf_left {x y : HSet.{u}} (hx : x.WF) :
    HSet.toZFSet x ∈ HSet.toZFSet y ↔ x ∈ y := by
  rw [readout_mem_iff, HSet.ofZFSet_toZFSet_of_wf hx]

/-- The actual well-founded subcarrier preserves and reflects membership. -/
theorem wfPart_mem_iff (x y : WellFoundedPart.{u}) :
    HSet.toZFSet x.1 ∈ HSet.toZFSet y.1 ↔ x.1 ∈ y.1 :=
  mem_iff_of_wf_left x.2

/-- The actual well-founded subcarrier preserves and reflects equality. -/
theorem wfPart_eq_iff (x y : WellFoundedPart.{u}) :
    HSet.toZFSet x.1 = HSet.toZFSet y.1 ↔ x = y :=
  ⟨fun h => HSet.wellFoundedPartEquivZFSet.injective h,
    fun h => congrArg (fun z : WellFoundedPart.{u} => HSet.toZFSet z.1) h⟩

/-- An atomic membership statement lost by the total readout. -/
theorem quine_membership_lost :
    HSet.quineAtom.{u} ∈ HSet.quineAtom ∧
      ¬ HSet.toZFSet HSet.quineAtom.{u} ∈ HSet.toZFSet HSet.quineAtom := by
  refine ⟨HSet.quineAtom_mem_self, ?_⟩
  rw [HSet.toZFSet_quineAtom]
  exact ZFSet.notMem_empty _

/-- Membership preservation on the whole hyperset carrier is false. -/
theorem not_membership_preserving :
    ¬ ∀ x y : HSet.{u}, x ∈ y → HSet.toZFSet x ∈ HSet.toZFSet y := by
  intro preserves
  exact quine_membership_lost.2
    (preserves HSet.quineAtom HSet.quineAtom quine_membership_lost.1)

/-- Distinct hypersets with the same total readout. -/
theorem quine_empty_same_readout :
    HSet.quineAtom.{u} ≠ ∅ ∧
      HSet.toZFSet HSet.quineAtom.{u} = HSet.toZFSet (∅ : HSet.{u}) := by
  refine ⟨fun same => HSet.empty_ne_quineAtom same.symm, ?_⟩
  rw [HSet.toZFSet_quineAtom, ← HSet.ofZFSet_empty, HSet.toZFSet_ofZFSet]

/-- Equality reflection on the whole hyperset carrier is false. -/
theorem not_equality_reflecting :
    ¬ ∀ x y : HSet.{u}, HSet.toZFSet x = HSet.toZFSet y → x = y := by
  intro reflects
  exact quine_empty_same_readout.1
    (reflects HSet.quineAtom ∅ quine_empty_same_readout.2)

end Mettapedia.SetTheory.CarveOuts.WellFoundedReadout
