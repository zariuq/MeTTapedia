import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick

/-! Running and terminal controller ticks have exact completed
observations, including target state and input/output histories. These
facts refine the loaded evaluator; source run coverage is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickObservation

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution

theorem running_iff (state : State) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (complete : (epochPlan prepared table).complete = true) (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (checkedSource : Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") runner.state)
    (running : runner.phase = .running) (after : State) (answers input output : List Atom) :
    let plan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let standard := OCamlEpochStandard.standard prepared
    let next := Mettapedia.Machines.ResumableSearchRunner.Machine.tick
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum
    Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:tick"
      [encoded (machine "MlRunning" plan standard (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum])}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) next) epochs)] ∧ input = [] ∧ output = [] := by
  exact pure_returns_derivation_iff runtime [] state state _ _
    (OCamlRunningTick.returns state prepared table runner epochs quantum complete finite reached checkedSource running)
    after answers input output

#print axioms running_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickObservation
