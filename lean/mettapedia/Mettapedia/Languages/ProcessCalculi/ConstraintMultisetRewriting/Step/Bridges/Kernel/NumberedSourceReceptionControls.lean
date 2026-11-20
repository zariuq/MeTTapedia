import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceReception
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceDeclarationsControls

/-!
# Mixed reception on the same carried input

These controls reuse the frozen literal truth event and the same explicitly
auxiliary type fixture. Source records, intermediate registries and both type
outputs pass through the mixed dispatcher. The input window is finite; missing
or unsupported records do not establish semantic source refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceReceptionControls

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution ExportReplay NumberedSourceReception
open NumberedSourceDeclarationsControls
  (fixtureInitial fixtureTruth beforeType afterType rawTruth rawReflexivity rawType claim)

theorem actual_truth_call : receive? fixtureInitial rawTruth = some fixtureTruth := by
  change NumberedSourceDeclarations.receive? fixtureInitial rawTruth = some fixtureTruth
  exact (Option.some_get NumberedSourceDeclarationsControls.fixture_truth_available).symm

theorem actual_reflexivity_call : receive? fixtureTruth rawReflexivity = some beforeType := by
  change NumberedSourceProofs.receive? fixtureTruth rawReflexivity = some beforeType
  exact (Option.some_get NumberedSourceDeclarationsControls.witness_available).symm

theorem actual_type_call : receive? beforeType rawType = some afterType := by
  change NumberedSourceDeclarations.receive? beforeType rawType = some afterType
  exact NumberedSourceDeclarationsControls.type_actual_receive

/-- Direct bind equations retain the exact previously checked states. -/
theorem mixed_replay_exact : replay? fixtureInitial [rawTruth,rawReflexivity,rawType] = some afterType := by
  change (receive? fixtureInitial rawTruth).bind (fun first =>
    (receive? first rawReflexivity).bind (fun second =>
      (receive? second rawType).bind (fun final => some final))) = some afterType
  rw [actual_truth_call]
  change (receive? fixtureTruth rawReflexivity).bind (fun second =>
    (receive? second rawType).bind (fun final => some final)) = some afterType
  rw [actual_reflexivity_call]
  change (receive? beforeType rawType).bind (fun final => some final) = some afterType
  rw [actual_type_call]
  rfl

theorem actual_mixed_event_graph :
    ∃ events : List Event, events.length = 3 ∧
      ExportReplay.replayFrom SourceProfileModels.policy fixtureInitial.registered events = some afterType.registered ∧
      afterType.input = fixtureInitial.input := by
  simpa using replay_event_graph fixtureInitial afterType [rawTruth,rawReflexivity,rawType] mixed_replay_exact

theorem actual_mixed_kernel_path :
    (Registered.gslt SourceProfileModels.policy).MultiStep
      fixtureInitial.registered.registered afterType.registered.registered :=
  replay_registered_reachable fixtureInitial afterType [rawTruth,rawReflexivity,rawType] mixed_replay_exact

theorem actual_mixed_metadata :
    NumberedSourceMetadata.ConclusionsChecked afterType.registered afterType.sourceConclusions :=
  replay_preserves_conclusions fixtureInitial afterType [rawTruth,rawReflexivity,rawType]
    (NumberedSourceMetadata.empty_conclusions_checked fixtureInitial.registered) mixed_replay_exact

theorem actual_input_window_available : (replayInput? fixtureInitial 0 3).isSome = true := by decide +kernel
def afterWindow : Reading := (replayInput? fixtureInitial 0 3).get actual_input_window_available

theorem actual_input_window : replayInput? fixtureInitial 0 3 = some afterWindow :=
  (Option.some_get actual_input_window_available).symm

theorem actual_input_event_graph :
    ∃ events : List Event, events.length = 3 ∧
      ExportReplay.replayFrom SourceProfileModels.policy fixtureInitial.registered events = some afterWindow.registered ∧
      afterWindow.input = fixtureInitial.input :=
  replayInput_event_graph fixtureInitial afterWindow 0 3 actual_input_window

theorem actual_input_kernel_path :
    (Registered.gslt SourceProfileModels.policy).MultiStep
      fixtureInitial.registered.registered afterWindow.registered.registered :=
  replayInput_registered_reachable fixtureInitial afterWindow 0 3 actual_input_window

theorem actual_input_metadata :
    NumberedSourceMetadata.ConclusionsChecked afterWindow.registered afterWindow.sourceConclusions :=
  replayInput_preserves_conclusions fixtureInitial afterWindow 0 3
    (NumberedSourceMetadata.empty_conclusions_checked fixtureInitial.registered) actual_input_window

theorem actual_input_counts :
    afterWindow.registered.registered.cache.size = 4 ∧ afterWindow.registered.receipts.size = 3 ∧
      afterWindow.registered.addresses[9001]? = some 2 ∧
      afterWindow.registered.addresses[9002]? = some 3 ∧ afterWindow.refusalChecks = 3 := by decide +kernel

theorem actual_origin_word :
    afterWindow.registered.receipts.toList.map (fun event => event.command.origin) =
      [("indexed-hol-source-export",0),("indexed-hol-source-export",1),("indexed-hol-source-export",1000)] := by
  decide +kernel

theorem actual_source_id_word :
    afterWindow.registered.receipts.toList.map (fun event => event.sourceIds) = [[0],[1],[9001,9002]] := by
  decide +kernel

theorem both_type_outputs_keep_parent :
    (afterWindow.registered.receipts[2]?).map Event.sourceEdges = some [(9001,[1]),(9002,[1])] := by
  decide +kernel

theorem missing_fourth_record_is_unavailable :
    (replayInput? fixtureInitial 0 4).isNone = true := by decide +kernel

theorem repeated_definition_refused :
    (replay? fixtureInitial [rawTruth,rawTruth]).isNone = true := by decide +kernel

def typeEvent (parents : List Nat) (outputs : List Json) : Json := Json.mkObj
  [("rule",.str "TYPE_DEFINITION"),("event",.num 1000),
    ("payload",.arr #[.str "NumberedFixture",.str "ABS_NumberedFixture",.str "REP_NumberedFixture"]),
    ("parents",.arr (parents.map toJson).toArray),("outputs",.arr outputs.toArray)]

theorem missing_parent_refused :
    (receive? beforeType (typeEvent [999] [claim 9001 19,claim 9002 27])).isNone = true := by decide +kernel

theorem wrong_existing_parent_refused :
    (receive? beforeType (typeEvent [0] [claim 9001 19,claim 9002 27])).isNone = true := by decide +kernel

theorem wrong_output_refused :
    (receive? beforeType (typeEvent [1] [claim 9001 4,claim 9002 27])).isNone = true := by decide +kernel

theorem swapped_outputs_refused :
    (receive? beforeType (typeEvent [1] [claim 9002 27,claim 9001 19])).isNone = true := by decide +kernel

theorem repeated_output_id_refused :
    (receive? beforeType (typeEvent [1] [claim 9001 19,claim 9001 27])).isNone = true := by decide +kernel

theorem unsupported_record_is_unavailable :
    (receive? fixtureInitial (Json.mkObj
      [("rule",.str "TYPE_DECLARATION"),("event",.num 2000),
        ("payload",.arr #[.str "unavailable_type",.num 0]),("parents",.arr #[]),("outputs",.arr #[])])).isNone = true := by
  decide +kernel

theorem empty_window_reads_no_record : replayInput? fixtureInitial 99 0 = some fixtureInitial := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceReceptionControls
