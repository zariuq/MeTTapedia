import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceProofs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceInputControls

/-!
# Actual checker calls from auxiliary numbered proof records

The fixture retains the captured truth-body syntax prefix and adds an
explicit auxiliary equality and substitution nodes. The proof records are test inputs,
not asserted to be additional records of the original capture. The second
call consumes the first call's actual registered state and address map.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceProofsControls

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation ExportReplay NumberedSourceProofs

def input : SourceDAGReceive.Input :=
  ⟨NumberedSourceInputControls.typeBodies.toArray ++ #[
      .arr #[.str "op",.str "fun",.arr #[.num 0,.num 1]],
      .arr #[.str "var",.str "A"],
      .arr #[.str "op",.str "fun",.arr #[.num 5,.num 0]],
      .arr #[.str "op",.str "fun",.arr #[.num 5,.num 6]],
      .arr #[.str "var",.str "B"],
      .arr #[.str "op",.str "fun",.arr #[.num 5,.num 8]],
      .arr #[.str "op",.str "fun",.arr #[.num 9,.num 0]],
      .arr #[.str "op",.str "fun",.arr #[.num 9,.num 10]]],
    NumberedSourceInputControls.termBodies.toArray ++ #[
      .arr #[.str "const",.str "=",.num 4],
      .arr #[.str "app",.num 5,.num 4],
      .arr #[.str "app",.num 6,.num 4],
      .arr #[.str "app",.num 1,.num 4],
      .arr #[.str "app",.num 5,.num 8],
      .arr #[.str "app",.num 9,.num 8],
      .arr #[.str "app",.num 9,.num 4],
      .arr #[.str "abs",.num 0,.num 4],
      .arr #[.str "app",.num 2,.num 12],
      .arr #[.str "app",.num 13,.num 12],
      .arr #[.str "app",.num 5,.num 0],
      .arr #[.str "app",.num 15,.num 0],
      .arr #[.str "var",.str "x",.num 5],
      .arr #[.str "const",.str "=",.num 7],
      .arr #[.str "app",.num 18,.num 17],
      .arr #[.str "app",.num 19,.num 17],
      .arr #[.str "var",.str "x",.num 0],
      .arr #[.str "app",.num 5,.num 21],
      .arr #[.str "app",.num 22,.num 21],
      .arr #[.str "var",.str "f",.num 9],
      .arr #[.str "var",.str "x",.num 5],
      .arr #[.str "app",.num 24,.num 25],
      .arr #[.str "abs",.num 25,.num 26],
      .arr #[.str "const",.str "=",.num 11],
      .arr #[.str "app",.num 28,.num 27],
      .arr #[.str "app",.num 29,.num 24],
      .arr #[.str "app",.num 1,.num 0],
      .arr #[.str "app",.num 5,.num 31],
      .arr #[.str "app",.num 32,.num 0]], #[]⟩

def initial : SourceDAGReceive.Reading := SourceDAGReceive.start input

def claim (id conclusion : Nat) (hypotheses : List Nat := []) : Json := Json.mkObj
  [("id",toJson id),("hypotheses",.arr (hypotheses.map toJson).toArray),("conclusion",toJson conclusion)]

def event (serial id : Nat) (rule : String) (payload : List Json) (parents : List Nat)
    (conclusion : Nat := 7) (hypotheses : List Nat := []) : Json := Json.mkObj
  [("event",toJson serial),("rule",.str rule),("payload",.arr payload.toArray),
    ("parents",.arr (parents.map toJson).toArray),("outputs",.arr #[claim id conclusion hypotheses])]

def first : Json := event 101 37 "REFL" [.num 4] []

theorem first_prepared_available : (prepare? initial first).isSome = true := by decide +kernel
def firstPrepared : Prepared first := (prepare? initial first).get first_prepared_available

theorem first_received_available : (receive? initial first).isSome = true := by decide +kernel
def afterFirst : SourceDAGReceive.Reading := (receive? initial first).get first_received_available

theorem first_actual_receive : receive? initial first = some afterFirst :=
  (Option.some_get first_received_available).symm

def proofReceipt? : Registered.Command → Option Receipt
  | .proof receipt _ => some receipt
  | _ => none

theorem serial_and_source_id_are_separate :
    firstPrepared.event.sourceIds = [37] ∧
      (proofReceipt? firstPrepared.event.command).map (fun receipt => receipt.origin) = some ("indexed-hol-source-export",101) := by
  constructor <;> decide +kernel

theorem first_output_address : afterFirst.registered.addresses[37]? = some 0 := by decide +kernel
theorem first_output_and_receipt_counts :
    afterFirst.registered.registered.cache.size = 1 ∧ afterFirst.registered.receipts.size = 1 := by decide +kernel

def second : Json := event 211 83 "TRANS" [] [37,37]

theorem second_prepared_available : (prepare? afterFirst second).isSome = true := by decide +kernel
def secondPrepared : Prepared second := (prepare? afterFirst second).get second_prepared_available

theorem second_received_available : (receive? afterFirst second).isSome = true := by decide +kernel
def afterSecond : SourceDAGReceive.Reading := (receive? afterFirst second).get second_received_available

theorem second_actual_receive : receive? afterFirst second = some afterSecond :=
  (Option.some_get second_received_available).symm

theorem actual_two_record_replay : replay? initial [first,second] = some afterSecond := by
  simp [replay?,first_actual_receive,second_actual_receive]

theorem actual_two_record_kernel_path :
    (Registered.gslt SourceProfileModels.policy).MultiStep initial.registered.registered afterSecond.registered.registered :=
  replay_registered_reachable initial afterSecond [first,second] actual_two_record_replay

theorem actual_two_record_graph :
    ∃ events : List Event, events.length = 2 ∧
      ExportReplay.replayFrom SourceProfileModels.policy initial.registered events = some afterSecond.registered ∧
      afterSecond.input = initial.input ∧ afterSecond.symbols = initial.symbols := by
  simpa using replay_event_graph initial afterSecond [first,second] actual_two_record_replay

def streamedInitial : SourceDAGReceive.Reading :=
  SourceDAGReceive.start { input with events := #[first,second] }

theorem actual_input_prefix_received : (replayInput? streamedInitial 0 2).isSome = true := by decide +kernel
theorem actual_one_record_prefix_received : (replayInput? streamedInitial 0 1).isSome = true := by decide +kernel
theorem missing_third_record_is_unavailable : (replayInput? streamedInitial 0 3).isNone = true := by decide +kernel
def afterStream : SourceDAGReceive.Reading := (replayInput? streamedInitial 0 2).get actual_input_prefix_received

theorem actual_input_kernel_path :
    (Registered.gslt SourceProfileModels.policy).MultiStep
        streamedInitial.registered.registered afterStream.registered.registered ∧
      afterStream.input = streamedInitial.input ∧ afterStream.symbols = streamedInitial.symbols :=
  replayInput_registered_reachable streamedInitial afterStream 0 2 (Option.some_get actual_input_prefix_received).symm

theorem actual_stream_counts :
    afterStream.registered.receipts.size = 2 ∧ afterStream.registered.registered.cache.size = 2 := by decide +kernel

theorem absent_input_is_not_another_step : (receiveAt? streamedInitial 2).isNone = true := rfl

theorem duplicate_parent_occurrences_retained :
    secondPrepared.event.sourceParents = [37,37] ∧ secondPrepared.event.command.parents = [0,0] ∧
      secondPrepared.event.premiseOccurrences = 2 := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

theorem second_actual_kernel_step :
    ∃ prepared : Prepared second,
      prepare? afterFirst second = some prepared ∧
      ExportReplay.apply SourceProfileModels.policy afterFirst.registered prepared.event = some afterSecond.registered ∧
      Registered.apply SourceProfileModels.policy afterFirst.registered.registered prepared.event.command =
        some afterSecond.registered.registered ∧
      ExportReplay.resolveParents afterFirst.registered prepared.event.sourceParents = some prepared.event.command.parents ∧
      afterSecond.input = afterFirst.input ∧ afterSecond.symbols = afterFirst.symbols :=
  receive_checked afterFirst afterSecond second second_actual_receive

theorem distinct_outputs_and_receipts_retained :
    afterSecond.registered.registered.cache.size = 2 ∧ afterSecond.registered.receipts.size = 2 ∧
      afterSecond.registered.addresses[37]? = some 0 ∧ afterSecond.registered.addresses[83]? = some 1 := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor <;> decide +kernel

def wrongClaim : Json := event 101 37 "REFL" [.num 4] [] 4

/-- Building a request and even checking its primitive does not authorize a claim. -/
theorem preparation_is_not_admission :
    (prepare? initial wrongClaim).isSome = true ∧ (receive? initial wrongClaim).isNone = true := by decide +kernel

theorem missing_earlier_parent_refused :
    (receive? afterFirst (event 211 83 "TRANS" [] [38,37])).isNone = true := by decide +kernel

theorem duplicate_source_id_refused :
    (receive? afterFirst first).isNone = true := by decide +kernel

theorem extra_parent_refused :
    (prepare? afterFirst (event 212 84 "REFL" [.num 4] [37])).isNone = true := by decide +kernel

theorem extra_payload_refused :
    (prepare? initial (event 101 37 "REFL" [.num 4,.num 4] [])).isNone = true := by decide +kernel

theorem missing_output_refused :
    (prepare? initial (Json.mkObj [("event",.num 101),("rule",.str "REFL"),
      ("payload",.arr #[.num 4]),("parents",.arr #[]),("outputs",.arr #[])])).isNone = true := by decide +kernel

def lambdaReflexivity : Json := event 301 12 "REFL" [.num 1] [] 4
theorem lambda_reflexivity_received : (receive? afterFirst lambdaReflexivity).isSome = true := by decide +kernel
def afterLambda : SourceDAGReceive.Reading := (receive? afterFirst lambdaReflexivity).get lambda_reflexivity_received

theorem beta_actual_redex_received :
    (receive? initial (event 302 13 "BETA" [.num 31] [] 33)).isSome = true := by decide +kernel

/-- Shared beta conversion is broader than this named source primitive. -/
theorem general_beta_is_not_source_beta :
    (receive? initial (event 302 13 "BETA" [.num 8] [] 11)).isNone = true := by decide +kernel

theorem beta_nonredex_refused :
    (receive? initial (event 302 13 "BETA" [.num 4] [] 7)).isNone = true := by decide +kernel

theorem application_uses_actual_function_equality :
    (receive? afterLambda (event 303 14 "MK_COMB" [] [12,37] 10)).isSome = true := by decide +kernel

theorem equality_modus_ponens_received :
    (receive? afterLambda (event 304 15 "EQ_MP" [] [37,12] 4)).isSome = true := by decide +kernel

theorem abstraction_binder_received :
    (receive? afterFirst (event 305 16 "ABS" [.num 0] [37] 14)).isSome = true := by decide +kernel

def freeReflexivity : Json := event 401 50 "REFL" [.num 0] [] 16
theorem free_reflexivity_received : (receive? initial freeReflexivity).isSome = true := by decide +kernel
def afterFree : SourceDAGReceive.Reading := (receive? initial freeReflexivity).get free_reflexivity_received

/-- The maplet changes free p into the captured, closed truth body. -/
theorem nonempty_term_substitution_changes_claim :
    (receive? afterFree (event 402 51 "INST" [.arr #[.num 4,.num 0]] [50] 7)).isSome = true := by decide +kernel

def typeReflexivity : Json := event 501 60 "REFL" [.num 17] [] 20
theorem type_reflexivity_received : (receive? initial typeReflexivity).isSome = true := by decide +kernel
def afterType : SourceDAGReceive.Reading := (receive? initial typeReflexivity).get type_reflexivity_received

/-- The type maplet changes x:A to x:bool in both sides of the equality. -/
theorem nonempty_type_substitution_changes_claim :
    (receive? afterType (event 502 61 "INST_TYPE" [.arr #[.num 0,.num 5]] [60] 23)).isSome = true := by decide +kernel

def assumption : Json := event 601 70 "ASSUME" [.num 4] [] 4 [4]
theorem assumption_received : (receive? initial assumption).isSome = true := by decide +kernel
def afterAssumption : SourceDAGReceive.Reading := (receive? initial assumption).get assumption_received

theorem deduct_antisymmetry_removes_actual_hypotheses :
    (receive? afterAssumption (event 602 71 "DEDUCT_ANTISYM_RULE" [] [70,70] 7)).isSome = true := by decide +kernel

theorem unclosed_eta_is_not_committed_axiom :
    (receive? initial (event 701 90 "AXIOM" [.num 30] [] 30)).isNone = true := by decide +kernel

theorem arbitrary_axiom_refused :
    (receive? initial (event 702 91 "AXIOM" [.num 4] [] 4)).isNone = true := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceProofsControls
