import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerAdvanceInvariant
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalObservation

/-! The actual public result reader cannot publish another completed source
result from a related controller. A running controller cannot be reported as
complete, even if its source continuation already has a finite result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerResultInvariant

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant OCamlTerminalObservation

theorem completed_readback (state : State) (program : OCaml.Program) (prepared : Prepared)
    (expected observed : OCaml.Result) (input epochs current : Term) (after : State)
    (related : Realizes program prepared expected input)
    (read : Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:result" [encoded input])}
      (.complete after [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern observed), epochs, current])] [] [])) : observed = expected := by
  cases related with
  | running table runner earlier source rank work invariant reached point completed =>
    have computed := OCamlControllerReadout.result_returns state (.symbol "MlRunning")
      (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")) (OCamlEpochStandard.standard prepared)
      (.symbol (CompleteExecution.classPhaseSymbol runner.phase)) (InferenceCettaWire.encodePattern runner.state)
      (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
      (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) earlier
    have pure : PureReturns runtime [] state (apply "gslt:ml:result" [encoded (controller prepared table "MlRunning" runner earlier)]) state _ := computed
    have answers := (pure_returns_derivation_iff runtime [] state state _ _ pure after _ [] []).mp read |>.2.1
    have same := CettaWireAtom.encode_injective _ _ (List.cons.inj answers).1
    have fields := (Term.application.inj same).2
    simp at fields
  | complete table runner earlier invariant reached done terminal =>
    have computed := OCamlControllerReadout.result_returns state (.symbol "MlComplete")
      (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")) (OCamlEpochStandard.standard prepared)
      (.symbol (CompleteExecution.classPhaseSymbol runner.phase)) (InferenceCettaWire.encodePattern runner.state)
      (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
      (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) earlier
    have pure : PureReturns runtime [] state (apply "gslt:ml:result" [encoded (controller prepared table "MlComplete" runner earlier)]) state _ := computed
    have answers := (pure_returns_derivation_iff runtime [] state state _ _ pure after _ [] []).mp read |>.2.1
    have same := CettaWireAtom.encode_injective _ _ (List.cons.inj answers).1
    have fields := List.cons.inj (Term.application.inj same).2
    have patternSame := InferenceCettaWire.encodePattern_injective (List.cons.inj fields.2).1
    have actualTerminal : state? (patterns program) (.halted observed) = some runner.state := by
      rw [state_exact, patternSame]
    exact (halted_encoding_injective (patterns program) expected observed (terminal.trans actualTerminal.symm)).symm

#print axioms completed_readback

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerResultInvariant
