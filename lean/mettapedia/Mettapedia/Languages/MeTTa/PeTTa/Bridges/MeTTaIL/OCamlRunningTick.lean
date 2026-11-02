import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickDispatch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerTickExecution

/-! Running controller ticks execute the existing normalized runner. Its
complete state and receipt histories remain inside the controller value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (complete : (epochPlan prepared table).complete = true) (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (checkedSource : Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") runner.state)
    (running : runner.phase = .running) :
    let plan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let standard := OCamlEpochStandard.standard prepared
    let next := Mettapedia.Machines.ResumableSearchRunner.Machine.tick
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
      (encoded (machine "MlRunning" plan standard (CompleteExecution.classMachineTerm (epochPlan prepared table) next) epochs)) := by
  dsimp only
  have ticked := OCamlRunnerTickExecution.tick_returns state prepared table runner quantum complete finite reached checkedSource
  have same : CompleteExecution.classMachineTerm (epochPlan prepared table) runner =
      .application "ClassMachine" [.symbol "ClassRunning", InferenceCettaWire.encodePattern runner.state,
        CompleteExecution.classStateTerm (epochPlan prepared table) runner.program,
        encodeList InferenceCettaWire.encodePattern runner.states, encodeList CompleteExecution.classReceiptTerm runner.receipts] := by
    simp only [CompleteExecution.classMachineTerm, running, CompleteExecution.classPhaseSymbol]
  rw [same] at ticked ⊢
  exact OCamlTickDispatch.running_returns state _ _ _ _ _ _ epochs _ quantum ticked

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningTick
