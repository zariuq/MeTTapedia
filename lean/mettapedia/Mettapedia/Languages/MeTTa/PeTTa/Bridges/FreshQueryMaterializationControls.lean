import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterializationControls

/-! Source controls separating candidate counts, fresh counts and refusal. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst)
open Eval NamedSpaces EffectfulQuerySource
open QuerySetMaterialization.Controls (rows pattern template payload caller program before after integer before_core payload_projection)

theorem one_new_row_from_two_candidates :
    countedInstall .self [payload, payload] before = some (after, 1) := rfl

theorem repeated_phase_has_zero_fresh_results :
    countedInstall .self [payload, payload] after = some (after, 0) := rfl

def plan := region program caller "space" "space" "payload" .self .self pattern template
  rfl rfl rfl (by decide) (by decide)

theorem planned_fresh_phase_counts_one :
    plan.attempt before = .committed ⟨after, [integer 1], [], []⟩ := by
  simp only [plan, region, Store.read_self, before_core, payload_projection]
  rfl

theorem source_fresh_phase_counts_one :
    PureReturns program caller before (counted (.var "space") pattern (bodySource "space" "payload" template))
      after (integer 1) := by
  exact counted_query_returns program caller before after "space" "space" "payload" .self .self
    pattern template rows 1 rfl rfl rfl (by decide) (by decide) rfl (by rw [payload_projection]; exact one_new_row_from_two_candidates)

theorem source_repeated_phase_returns_zero_not_no_answer :
    PureReturns program caller after (counted (.var "space") pattern (bodySource "space" "payload" template))
      after (integer 0) := by
  have projected : (choices caller pattern after.core).map (fun bindings => applySubst bindings template) = [payload, payload] := by
    decide +kernel
  exact counted_query_returns program caller after after "space" "space" "payload" .self .self
    pattern template after.core 0 rfl rfl rfl (by decide) (by decide) rfl (by rw [projected]; exact repeated_phase_has_zero_fresh_results)

theorem same_store_requires_different_source_readouts :
    QuerySetMaterialization.Controls.plan.attempt before = .committed ⟨after, [integer 2], [], []⟩ ∧
    plan.attempt before = .committed ⟨after, [integer 1], [], []⟩ :=
  ⟨QuerySetMaterialization.Controls.planned_phase_preserves_store_and_count, planned_fresh_phase_counts_one⟩

open QuerySetMaterialization.Controls (unavailableCaller emptyState)

def unavailablePlan := region program unavailableCaller "input" "target" "payload" .self (.privateSpace 0)
  pattern template rfl rfl rfl (by decide) (by decide)

theorem empty_phase_needs_no_target_read :
    unavailablePlan.attempt emptyState = .committed ⟨emptyState, [integer 0], [], []⟩ := rfl

theorem missing_target_is_not_completed_zero_progress :
    unavailablePlan.attempt before = .declined before := by
  have projected : (choices unavailableCaller pattern rows).map (fun bindings => applySubst bindings template) = [payload, payload] := by
    decide +kernel
  simp only [unavailablePlan, region, Store.read_self, before_core, projected]
  rfl

theorem candidate_mass_bounds_fresh_count :
    (1 : Nat) ≤ (choices caller pattern rows).length := by
  apply counted_install_bound .self template (choices caller pattern rows) before after 1
  rw [payload_projection]
  exact one_new_row_from_two_candidates

open QuerySetMaterialization.Controls (openInput openTarget openCapture)

theorem open_input_does_not_mean_zero_fresh_rows : plan.attempt openInput = .declined openInput := by
  have refused : ClosedQueryAdmission.rowsReady pattern openInput.core = false := by decide +kernel
  simp only [plan, region, Store.read_self, ClosedQueryAdmission.phaseReady, refused,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem open_target_requires_the_unifying_route : plan.attempt openTarget = .declined openTarget := by
  have refused : ClosedQueryAdmission.phaseReady caller pattern openTarget.core openTarget .self
      ((choices caller pattern openTarget.core).map (fun bindings => applySubst bindings template)) = false := by
    decide +kernel
  simp only [plan, region, Store.read_self, refused, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

def openCapturePlan := region program openCapture "space" "space" "payload" .self .self pattern template
  rfl rfl rfl (by decide) (by decide)

theorem open_capture_requires_the_unifying_route : openCapturePlan.attempt before = .declined before := by
  have refused : ClosedQueryAdmission.capturesReady openCapture pattern = false := by decide +kernel
  simp only [openCapturePlan, region, Store.read_self, ClosedQueryAdmission.phaseReady, refused,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization.Controls
