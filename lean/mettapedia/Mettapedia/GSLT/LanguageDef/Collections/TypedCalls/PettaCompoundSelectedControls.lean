import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedOperations
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnControls

/-!
# Physical-position controls for compound typed-prefix obligations

These local controls use the actual row-work and phase operations. They do
not assert complete host reachability for an invented row. The existing
named-call controls separately execute source-produced frames and guards.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaCompoundReturnControls (program recipe prefixControl debtControl services)

def saved : CallFrame :=
  ⟨"keepCell", ⟨[.sym "Atom"], .sym "Box"⟩, [], [recipe], 1, [], [], .var "out", 0, .var "out", 1, .body⟩
def context : Context Unit := ⟨(), [saved]⟩
def row : Row := ⟨[], .sym "%Undefined%"⟩
def captured : Work Unit := rowWork prefixControl context [7] 1 "ping" [] (.var "temporary") debtControl.goals row 0
def inner : CallFrame :=
  ⟨"ping", row, [], [], 0, [], debtControl.goals, prefixControl.destination,
    prefixControl.cutBoundary, .var "temporary", 1, .nextArgument⟩

private theorem initial_alias : Bridges.DestinationDataReturnState.AliasHolds (program false false) recipe prefixControl := by
  refine ⟨recipe, Bridges.DestinationDataReturnFunction.checksData_sound _ _ (by cbv), fun _ _ => rfl, .inr (.inl ?_)⟩
  exact (Bridges.ScopedReturnObligation.Pending.evaluation recipe [] .leaf).prepend_evaluation
    (PettaCompoundReturnControls.call "ping" []) (.var "temporary")

theorem selected_input_obligation_is_nonvacuous :
    PettaCompoundSelectedWork.Holds (program false false) saved recipe 0 (prefixControl, context, [7]) :=
  PettaCompoundSelectedWork.at_head _ _ _ _ [] rfl initial_alias

theorem real_row_capture_moves_the_selected_position :
    PettaCompoundSelectedWork.Holds (program false false) saved recipe 1 captured :=
  PettaCompoundSelectedWork.row_work prefixControl context [7] selected_input_obligation_is_nonvacuous 1 "ping" []
    (.var "temporary") debtControl.goals row 0 rfl (by decide) (by decide)

theorem capture_keeps_both_actual_frame_positions : captured.2.1.calls = [inner, saved] := rfl

theorem a_constructor_does_not_have_callable_admission : callable (program false false) "Cell" = false := by decide

theorem the_actual_next_argument_operation_preserves_the_selected_body
    (source : State Unit) (current : Scope Unit) (parents : List (Scope Unit)) (pending : List (Work Unit)) :
    PettaCompoundSelectedWork.Replaces (program false false) saved recipe 1 source current parents pending
      (nextArgument services source current parents captured.1 captured.2.1 captured.2.2 pending inner [saved]) :=
  PettaCompoundSelectedWork.next_argument services source current parents captured.1 captured.2.1 captured.2.2 pending
    inner [saved] real_row_capture_moves_the_selected_position rfl

theorem returning_the_inner_frame_restores_position_zero :
    PettaCompoundSelectedWork.Holds (program false false) saved recipe 0
      (resumeCaller captured.1 inner, {captured.2.1 with calls := [saved]}, captured.2.2) :=
  PettaCompoundSelectedWork.pop_inner captured.1 captured.2.1 captured.2.2 inner [saved]
    real_row_capture_moves_the_selected_position rfl

theorem a_stale_position_one_mark_is_refuted_after_pop :
    ¬ PettaCompoundSelectedWork.Holds (program false false) saved recipe 1
      (resumeCaller captured.1 inner, {captured.2.1 with calls := [saved]}, captured.2.2) := by
  intro held
  have position := PettaCompoundSelectedWork.selected_position held
  cases position

theorem erasing_the_selected_frame_is_not_an_inner_return :
    ¬ PettaCompoundSelectedWork.Holds (program false false) saved recipe 0
      (resumeCaller captured.1 inner, {captured.2.1 with calls := []}, captured.2.2) := by
  intro held
  have position := PettaCompoundSelectedWork.selected_position held
  cases position

theorem actual_guard_continuations_keep_each_occurrence (source : State Unit) (slot : Atom) (stores : List Store) :
    ∀ item ∈ argumentContinuations services source captured.1 captured.2.1 captured.2.2 inner [saved] slot stores,
      PettaCompoundSelectedWork.Holds (program false false) saved recipe 1 item :=
  PettaCompoundSelectedWork.argument_continuations services source captured.1 captured.2.1 captured.2.2 inner [saved]
    slot stores real_row_capture_moves_the_selected_position rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedControls
