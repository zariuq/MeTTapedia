import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFiniteFoundation
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutPresentations

/-!
# Foundation eligibility and partial decoding of validated presentations

The decoder returns a ZFSet only on its computed well-founded domain.
Its successful readings preserve and reflect current material equality
and membership. A graph with an unreachable cycle remains eligible.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Presentations.Foundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets

def eligible (presentation : Checked) : Bool :=
  Finite.Foundation.eligible (edge presentation) (root presentation)

theorem eligible_eq_true (presentation : Checked) :
    eligible presentation = true ↔ (material presentation).WF :=
  Finite.Foundation.eligible_material_domain _ _

abbrev Domain := {presentation : Checked // eligible presentation = true}

def value (presentation : Domain) : ZFSet := HSet.toZFSet (material presentation.val)

theorem value_embedding (presentation : Domain) :
    HSet.ofZFSet (value presentation) = material presentation.val :=
  HSet.ofZFSet_toZFSet_of_wf ((eligible_eq_true presentation.val).mp presentation.property)

def partialValue (presentation : Checked) : Option ZFSet :=
  if domain : eligible presentation = true then some (value ⟨presentation, domain⟩)
  else none

theorem partialValue_none (presentation : Checked) :
    partialValue presentation = none ↔ ¬ (material presentation).WF := by
  simp [partialValue, eligible_eq_true]

theorem value_equality (first second : Domain) :
    value first = value second ↔ equality first.val second.val = true := by
  rw [equality_eq_true]
  constructor
  · intro same
    exact (value_embedding first).symm.trans
      ((congrArg HSet.ofZFSet same).trans (value_embedding second))
  · exact congrArg HSet.toZFSet

theorem value_membership (child parent : Domain) :
    value child ∈ value parent ↔ membership child.val parent.val = true := by
  rw [membership_eq_true]
  exact Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.mem_iff_of_wf_left
    ((eligible_eq_true child.val).mp child.property)

namespace Controls

open Presentations.Controls

def unreachableCycle : Checked := ⟨⟨0, [[], [1]]⟩, by decide⟩
def reachableCycle : Checked := ⟨⟨0, [[1], [1]]⟩, by decide⟩

theorem empty_eligible : eligible empty = true := by decide +kernel

theorem chain_eligible : eligible chain = true := by decide +kernel

theorem loop_ineligible : eligible loop = false := by decide +kernel

theorem twoCycle_ineligible : eligible twoCycle = false := by decide +kernel

theorem unreachable_cycle_eligible : eligible unreachableCycle = true := by decide +kernel

theorem reachable_cycle_ineligible : eligible reachableCycle = false := by decide +kernel

theorem loop_has_no_foundation_value : partialValue loop = none := by
  simp [partialValue, loop_ineligible]

theorem unreachable_cycle_same_material : equality unreachableCycle empty = true := by decide +kernel

end Controls

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Presentations.Foundation
