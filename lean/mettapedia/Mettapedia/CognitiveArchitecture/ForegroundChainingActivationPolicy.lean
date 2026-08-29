import Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService
import Mettapedia.GSLT.Dynamics.SpaceActivationPolicy

/-!
# The real foreground continuation store as an activation policy

This module realizes the explicit-evaluation activation fragment on the actual
given-clause `Snapshot` used by the background premise-service example.  A
request can fire exactly when the shared frontier's current queue view selects
that exact occurrence.  The transition is the real `Snapshot.tick`, and its
receipt is the selected occurrence.

Store admission remains outside this policy: admission makes a fresh
occurrence resident and live; activation later consumes it.  The worked bridge
shows the stalled foreground cannot fire, the authorized admission enables one
exact transition, and two policy steps are definitionally the run which proves
the foreground goal.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy

noncomputable section

open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.GSLT.Core.GivenClauseLoop
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy

/-- Processed and still-live occurrences are resident in the foreground
continuation store.  Only selected live occurrences are enabled. -/
def foregroundPolicy :
    Policy ForegroundState ClauseOccurrence Unit ForegroundState
      ClauseOccurrence where
  resident snapshot occurrence :=
    occurrence ∈ snapshot.processed ∨ occurrence ∈ snapshot.passive.live
  enabled snapshot cause :=
    match cause with
    | .requested _trigger occurrence =>
        snapshot.passive.selected snapshot.cursor = some occurrence
    | .communication _sender _receiver => False
  step snapshot cause next receipt :=
    match cause with
    | .requested _trigger occurrence =>
        snapshot.passive.selected snapshot.cursor = some occurrence ∧
          next = Snapshot.tick chainingSystem Snapshot.breadthOnly snapshot ∧
          receipt = occurrence
    | .communication _sender _receiver => False
  step_enabled := by
    intro snapshot cause next receipt step
    cases cause with
    | requested trigger occurrence => exact step.1
    | communication sender receiver => exact step.elim
  enabled_supported := by
    intro snapshot cause enabled
    cases cause with
    | requested trigger occurrence =>
        exact Or.inr (snapshot.passive.selected_mem enabled)
    | communication sender receiver => exact enabled.elim
  observe := id

theorem canFire_requested_iff
    (snapshot : ForegroundState) (occurrence : ClauseOccurrence) :
    foregroundPolicy.CanFire snapshot (.requested () occurrence) ↔
      snapshot.passive.selected snapshot.cursor = some occurrence := by
  constructor
  · rintro ⟨next, receipt, step⟩
    exact step.1
  · intro selected
    exact ⟨Snapshot.tick chainingSystem Snapshot.breadthOnly snapshot,
      occurrence, selected, rfl, rfl⟩

/-- Every activation transition is the real given-clause tick and retains the
exact selected occurrence as its receipt. -/
theorem fired_is_exact_tick
    {snapshot next : ForegroundState} {occurrence receipt : ClauseOccurrence}
    (fired : foregroundPolicy.step snapshot (.requested () occurrence)
      next receipt) :
    next = Snapshot.tick chainingSystem Snapshot.breadthOnly snapshot ∧
      receipt = occurrence :=
  fired.2

theorem no_communication_fire
    (snapshot : ForegroundState) (sender receiver : ClauseOccurrence) :
    ¬ foregroundPolicy.CanFire snapshot (.communication sender receiver) := by
  rintro ⟨next, receipt, fired⟩
  exact fired

def dataView :
    Policy ForegroundState ClauseOccurrence Unit ForegroundState
      ClauseOccurrence :=
  Policy.inert foregroundPolicy.resident foregroundPolicy.observe

theorem data_is_below_foreground_execution :
    dataView.Extends foregroundPolicy :=
  Policy.inert_extends foregroundPolicy

/-! ## The actual stalled/admitted/solved run -/

def afterBridge : ForegroundState :=
  Snapshot.tick chainingSystem Snapshot.breadthOnly admittedSnapshot

theorem stalled_foreground_cannot_fire_required :
    ¬ foregroundPolicy.CanFire stalledSnapshot
      (.requested () (selectedOccurrenceAt 0)) := by
  rw [canFire_requested_iff]
  change (none : Option ClauseOccurrence) ≠ some (selectedOccurrenceAt 0)
  simp

/-- Admission changes residency and liveness, not activation history, and
thereby enables the exact next evaluation transition. -/
theorem admission_enables_but_does_not_execute :
    admittedSnapshot.selections = stalledSnapshot.selections ∧
      admittedSnapshot.processed = stalledSnapshot.processed ∧
      admittedSnapshot.passive.live = [selectedOccurrenceAt 0] ∧
      foregroundPolicy.CanFire admittedSnapshot
        (.requested () (selectedOccurrenceAt 0)) := by
  exact ⟨rfl, rfl, rfl,
    (canFire_requested_iff admittedSnapshot (selectedOccurrenceAt 0)).2 rfl⟩

theorem admitted_bridge_fires_exact_tick :
    foregroundPolicy.step admittedSnapshot
      (.requested () (selectedOccurrenceAt 0)) afterBridge
      (selectedOccurrenceAt 0) :=
  ⟨rfl, rfl, rfl⟩

theorem afterBridge_goal_fires_exact_tick :
    foregroundPolicy.step afterBridge
      (.requested () (goalFrom (selectedOccurrenceAt 0))) solvedSnapshot
      (goalFrom (selectedOccurrenceAt 0)) :=
  ⟨rfl, rfl, rfl⟩

/-- The two policy transitions are the exact two foreground ticks already
certified by the semantic workload. -/
theorem two_activation_steps_reach_goal :
    foregroundPolicy.step admittedSnapshot
        (.requested () (selectedOccurrenceAt 0)) afterBridge
        (selectedOccurrenceAt 0) ∧
      foregroundPolicy.step afterBridge
        (.requested () (goalFrom (selectedOccurrenceAt 0))) solvedSnapshot
        (goalFrom (selectedOccurrenceAt 0)) ∧
      solvedSnapshot.events =
        [⟨goalFrom (selectedOccurrenceAt 0), ProofResult.proved⟩] :=
  ⟨admitted_bridge_fires_exact_tick,
    afterBridge_goal_fires_exact_tick,
    background_premise_service_unblocks_foreground.2.2.2.1⟩

/-- The real GCL receipt theorem agrees with the policy receipt on the first
activation. -/
theorem first_activation_updates_real_store :
    afterBridge.selections =
        admittedSnapshot.selections ++ [selectedOccurrenceAt 0] ∧
      afterBridge.processed =
        admittedSnapshot.processed ++ [selectedOccurrenceAt 0] :=
  Snapshot.activation_receipt chainingSystem Snapshot.breadthOnly
    admittedSnapshot rfl

#print axioms canFire_requested_iff
#print axioms fired_is_exact_tick
#print axioms no_communication_fire
#print axioms data_is_below_foreground_execution
#print axioms stalled_foreground_cannot_fire_required
#print axioms admission_enables_but_does_not_execute
#print axioms two_activation_steps_reach_goal
#print axioms first_activation_updates_real_store

end
end Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
