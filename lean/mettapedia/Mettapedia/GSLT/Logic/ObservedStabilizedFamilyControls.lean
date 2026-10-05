import Mettapedia.GSLT.Logic.ObservedStabilizedFamilyDescent
import Mettapedia.GSLT.Logic.ObservedGradedFamilyControls

/-!
# Stabilized future readings still do not retain every past or occurrence

An authored root advances to a loop. Both states have the same complete
future and the constructed depth-zero bound already stabilizes. Outgoing
lifting therefore holds at a fixed depth. The root has no predecessor,
whereas the loop does, so incoming lifting fails. Keeping original events
also prevents exact-occurrence lifting from every state representative.

The cell control supplies a second actual stabilization proof and identifies
a self-loop with a two-cycle while separating the half-valued observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedStabilizedFamilyControls

open Distinction.Constructive Distinction.Constructive.Controls
open ObservedMaterialization
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassFamilyDescent

abbrev rootedTheory : GSLT where
  Term := Bool
  equations := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites _ target := target = true
  rewrites_resp_left _ step := ⟨_, step, rfl⟩
  rewrites_resp_right step same := same.symm.trans step

def rooted : PresentedSystem.{0, 0, 0, 0, 0} rootedTheory unitScale where
  dynamics := {
    Atom := Unit
    observes _ _ := False
    observes_resp _ _ _ _ := Iff.rfl
    Label := Unit
    act _ _ target := target = true
    act_resp_left _ step := ⟨_, step, rfl⟩
    act_resp_right step same := same.symm.trans step }
  Obs := Unit
  value _ _ := 0
  value_nonneg _ _ := by decide
  value_le_one _ _ := by decide
  value_resp _ _ _ _ := rfl
  successors _ _ := [true]
  successors_act member := List.mem_singleton.mp member
  successors_cover step := ⟨true, List.mem_singleton_self _, step⟩

def vocabulary : rooted.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

theorem rooted_stabilizes : rooted.Stabilizes vocabulary 0 := by
  intro left right
  cases left <;> cases right <;> decide

theorem rooted_readout_equal :
    ObservedGradedFamilyDescent.readout rooted 0 true =
      ObservedGradedFamilyDescent.readout rooted 0 false := by
  apply (ObservedGradedFamilyDescent.readout_eq_iff rooted vocabulary 0 true false).mpr
  decide

def occurrences : ActionOccurrences rooted.dynamics where
  Occurrence _ _ target := PLift (target = true)
  erases _ _ _ := ⟨fun ⟨proof⟩ => proof.down, fun proof => ⟨⟨proof⟩⟩⟩

def loopEvent : ActionOccurrences.Event occurrences := ⟨(), true, true, ⟨rfl⟩⟩

theorem fixed_depth_source_lifts :
    (ObservedStabilizedFamilyDescent.observation rooted 0 occurrences).SourceLifts :=
  ObservedStabilizedFamilyDescent.sourceLifts rooted vocabulary 0 unitScale_positive rooted_stabilizes occurrences

theorem fixed_depth_target_does_not_lift :
    ¬ (ObservedStabilizedFamilyDescent.observation rooted 0 occurrences).TargetLifts := by
  intro lifting
  have same : (ObservedStabilizedFamilyDescent.observedSpan rooted 0 occurrences).target loopEvent =
      classOf (ObservedGradedFamilyDescent.readout rooted 0) false :=
    (classOf_eq_iff _ _ _).mpr rooted_readout_equal
  obtain ⟨lifted, target, _⟩ := lifting false loopEvent same
  change lifted.target = false at target
  have endsInLoop := lifted.occurrence.down
  rw [target] at endsInLoop
  cases endsInLoop

theorem fixed_depth_source_occurrence_does_not_lift :
    ¬ (ObservedStabilizedFamilyDescent.observation rooted 0 occurrences).SourceOccurrenceLifts := by
  intro lifting
  have same : (ObservedStabilizedFamilyDescent.observedSpan rooted 0 occurrences).source loopEvent =
      classOf (ObservedGradedFamilyDescent.readout rooted 0) false :=
    (classOf_eq_iff _ _ _).mpr rooted_readout_equal
  obtain ⟨lifted, source, event⟩ := lifting false loopEvent same
  change lifted = loopEvent at event
  rw [event] at source
  change true = false at source
  cases source

theorem stabilized_loop_cycle_equal :
    ObservedGradedFamilyDescent.readout cells 1 .rest =
      ObservedGradedFamilyDescent.readout cells 1 .ping :=
  (ObservedStabilizedFamilyDescent.readout_eq_iff_gradedBisimilar
    cells cellVocabulary 1 halfScale_positive cells_stabilizes .rest .ping).mpr cells_rest_ping_bisimilar

theorem stabilized_half_reading_different :
    ObservedGradedFamilyDescent.readout cells 1 .rest ≠
      ObservedGradedFamilyDescent.readout cells 1 .half := by
  intro same
  have atomic := congrFun same ⟨.atom (), Nat.zero_le 1⟩
  exact (show (0 : ℤ) ≠ 1 by decide) atomic

end Mettapedia.GSLT.ObservedStabilizedFamilyControls
