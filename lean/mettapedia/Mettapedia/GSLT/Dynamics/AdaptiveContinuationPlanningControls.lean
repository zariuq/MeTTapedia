import Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanning
import Mettapedia.GSLT.Dynamics.ContinuationTransferControls

/-!
# Adaptive continuation planning controls

The control program has two pending callers, duplicate answers and branch-local
contexts. An optimization offer arrives after the first answer. Context change,
refusal and cancellation act on the live residual. Cached plans read a genuine
declaration dependency; unrelated and relevant revisions are distinguished.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanningControls

open Mettapedia.Machines.SharedContinuation
open AdaptiveContinuationPlanning CertifiedRepresentationPlanning
open ContinuationRegionSwitching ContinuationTransferControls
open RepresentationSwitching RegionHolePlan
open ContextIndexedSwitching (repeats)

def enterShared : Proposal (family program) () :=
  Proposal.ofTransfers .shared fun
    | .reference => enter program ⟨3, 2, 2, 2, 2⟩
    | .shared => {
        convert := id
        commutes := rfl
        resources := ⟨1, 1, 0, 0, 0⟩ }

def leaveShared : Proposal (family program) () :=
  Proposal.ofTransfers .reference fun
    | .reference => {
        convert := id
        commutes := rfl
        resources := ⟨1, 1, 0, 0, 0⟩ }
    | .shared => leave program ⟨2, 2, 1, 1, 1⟩

/-- A backend that cannot handle this residual explicitly refuses. -/
def refused : Proposal (family program) () where
  destination := .shared
  converter _ := {
    attempt := fun _ => none
    correct := by intro _ _ impossible; cases impossible }

def adaptive : Schedule (family program) () () :=
  .background 30 <|
  .region 2 <|
  .offer enterShared 5 <|
  .region 4 <|
  .offer leaveShared 3 <|
  .hole (.context (· + 1)) <|
  .offer refused 2 <|
  .background 6 <|
  .region 94 <|
  .done ()

def reference : Schedule (family program) () () :=
  .region (Y := ()) 2 <| .region (Y := ()) 4 <|
  .hole (Y := ()) (.context (· + 1)) <| .region 94 <| .done ()

theorem adaptive_exact_reference :
    observeResult (adaptive.run ⟨.reference, initial⟩) =
      observeResult (reference.run ⟨.reference, initial⟩) := by
  apply Schedule.same_plan_same_residual
  rfl

theorem adaptive_keeps_prefix_duplicates_and_live_context :
    (observeResult (adaptive.run ⟨.reference, initial⟩)).emitted =
      [(10, 1013), (11, 1115), (11, 1114), (11, 1115), (21, 2124), (21, 2125)] := by
  rw [adaptive_exact_reference]
  decide

theorem refused_offer_retains_pending_work :
    refused.install ⟨.shared, suspended⟩ = ⟨.shared, suspended⟩ := by
  apply Proposal.refusal_retains_live
  rfl

def cancelling : Schedule (family program) () () :=
  .region (Y := ()) 6 <| .hole .cancel <| .offer enterShared 5 <|
  .background 10 <| .offer leaveShared 3 <| .region 94 <| .done ()

theorem optimization_cannot_resurrect_cancelled_work :
    let final := observeResult (cancelling.run ⟨.reference, initial⟩)
    final.emitted = [(10, 1013)] ∧ final.frontier = [] := by
  simp only [Schedule.run_exact]
  decide

theorem adaptive_has_positive_receipts : adaptive.Charged := by
  simp [adaptive, Schedule.Charged]

theorem adaptive_planning_receipt :
    adaptive.planningWork = 46 ∧ adaptive.planningEvents = 5 := by decide

/-- An offer prepared earlier converts the state at installation time. -/
theorem prepared_offer_uses_current_state :
    observeResult (enterShared.install ⟨.reference, suspended.1.decode⟩) =
      suspended.1.decode :=
  Proposal.install_preserves _ _

/-- Copying back the optimizer's old capture would replay a published answer. -/
theorem restoring_optimization_start_is_wrong :
    suspended.1.emitted ++ (repeats (step program) 100 initial).emitted ≠
      (repeats (step program) 94
        (observeResult (enterShared.install ⟨.reference, suspended.1.decode⟩))).emitted := by
  rw [prepared_offer_uses_current_state, handoff_after_publication]
  exact restarting_replays_answers

/-! Finite dependency validation with a stored, nonconstant artifact. -/

def coefficientPlan : Mettapedia.GSLT.FinitelySupportedPlan Nat Nat Nat :=
  (Mettapedia.GSLT.FinitelySupportedPlan.read 0).map (fun coefficient => 2 * coefficient + 1)

def oldConfiguration : Nat → Nat := fun declaration => if declaration = 0 then 3 else 0

def unrelatedChange : Nat → Nat :=
  fun declaration => if declaration = 0 then 3 else 99

def relevantChange : Nat → Nat := fun declaration => if declaration = 0 then 4 else 0

def savedCoefficient : PreparedArtifact coefficientPlan :=
  prepare coefficientPlan [0] (by
    intro declaration
    simp [coefficientPlan, Mettapedia.GSLT.FinitelySupportedPlan.map,
      Mettapedia.GSLT.FinitelySupportedPlan.read]) oldConfiguration

theorem coefficient_snapshot_is_one_pair : savedCoefficient.dependencies = [(0, 3)] := rfl

theorem unrelated_revision_reuses_saved_artifact :
    reuse savedCoefficient unrelatedChange = some 7 := by decide

theorem changed_dependency_declines : reuse savedCoefficient relevantChange = none := by decide

theorem stale_artifact_differs_from_fresh :
    savedCoefficient.artifact = 7 ∧ coefficientPlan.run relevantChange = 9 := by decide

/-- The finite support also applies to executor selection. Both possible
proposals have real continuation converters; the dependency selects a tier. -/
def executorPlan :
    Mettapedia.GSLT.FinitelySupportedPlan Nat Nat (Proposal (family program) ()) :=
  (Mettapedia.GSLT.FinitelySupportedPlan.read 0).map
    (fun selector => if selector = 3 then enterShared else leaveShared)

def savedExecutor : PreparedArtifact executorPlan :=
  prepare executorPlan [0] (by
    intro declaration
    simp [executorPlan, Mettapedia.GSLT.FinitelySupportedPlan.map,
      Mettapedia.GSLT.FinitelySupportedPlan.read]) oldConfiguration

theorem executor_snapshot_is_one_pair : savedExecutor.dependencies = [(0, 3)] := rfl

theorem accepted_cached_executor_enters_shared :
    (installPrepared executorPlan savedExecutor unrelatedChange
      ⟨.reference, suspended.1.decode⟩).1 = .shared := by rfl

theorem stale_cached_executor_retains_live :
    installPrepared executorPlan savedExecutor relevantChange
      ⟨.reference, suspended.1.decode⟩ = ⟨.reference, suspended.1.decode⟩ := by rfl

end Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanningControls
