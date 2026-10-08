import Mettapedia.OSLF.Syntax.LabelwiseFiniteBehaviour
import Mettapedia.OSLF.Syntax.DeterministicGSOSControls

/-!
# Branching and variable-collision controls

A deterministic system can offer infinitely many action labels while
retaining exactly one successor at each label. A two-action example has
two distinct successors at one action; a noninjective state map identifies
them without changing availability. These are support readouts, not
occurrence-sensitive firing receipts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.LabelwiseFiniteControls

open CategoryTheory Mettapedia.OSLF.DeterministicGSOS.Controls

def everyLabel : Behaviour signature actions naturals PUnit.unit () :=
  fun action => some (action + 1)

def everyLabelSupport : LabelwiseFiniteBehaviour signature actions naturals PUnit.unit () :=
  fun action => {action + 1}

theorem everyLabelSupport_is_embedding :
    (deterministicInclusion signature actions).app naturals PUnit.unit () everyLabel =
      everyLabelSupport := rfl

theorem one_successor_per_action (action : Nat) : (everyLabelSupport action).card = 1 := by
  simp [everyLabelSupport]

theorem every_action_enabled : everyLabelSupport.enabled = Set.univ := by
  ext action
  simp [LabelwiseFiniteBehaviour.enabled, everyLabelSupport]

/-- One successor per action does not imply finitely many outgoing edges. -/
theorem infinitely_many_outgoing_edges : ¬ everyLabelSupport.edges.Finite := by
  intro finite
  have enabledFinite := everyLabelSupport.edges_finite_iff_enabled_finite.mp finite
  rw [every_action_enabled] at enabledFinite
  exact Set.infinite_univ enabledFinite

abbrev twoActions : signature.Srt → Type := fun _ => Fin 2

def branching : LabelwiseFiniteBehaviour signature twoActions naturals PUnit.unit () :=
  fun action => if action = 0 then {10, 20} else ∅

theorem two_distinct_successors : (branching 0).card = 2 := by
  decide

theorem finite_total_branching : branching.edges.Finite :=
  branching.finiteActions_edges_finite

theorem collision_merges_successors :
    labelwiseFiniteMap signature twoActions collapse PUnit.unit () branching 0 = {()} := by
  simp [labelwiseFiniteMap, branching, collapse]

theorem collision_retains_availability :
    (labelwiseFiniteMap signature twoActions collapse PUnit.unit () branching 0).Nonempty ↔
      (branching 0).Nonempty :=
  labelwiseFiniteMap_enabled_iff signature twoActions collapse PUnit.unit () branching 0

end Mettapedia.OSLF.DeterministicGSOS.LabelwiseFiniteControls
