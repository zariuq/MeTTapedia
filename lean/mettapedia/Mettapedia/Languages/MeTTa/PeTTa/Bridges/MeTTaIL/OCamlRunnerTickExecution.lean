import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerBeginExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochScope

/-! Reached finite epochs obtain runner readiness from their retained
search budget and checked current source. The actual shared tick theorem
then runs under the loaded O0 service libraries.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerTickExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource

theorem ready (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (machine : CompleteExecution.ClassMachine (epochPlan prepared table))
    (complete : (epochPlan prepared table).complete = true) (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (checkedSource : Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") machine.state) :
    CompleteExecution.RunnerReady (plan := epochPlan prepared table) [] (.base "MlConfig") [] machine := by
  have scope := epoch_scope prepared table complete finite
  have inside := Complete.Footprint.sorted_within (plan := epochPlan prepared table) scope.declared checkedSource
  obtain ⟨work, current⟩ := reached.budget
  have begun := CompleteExecution.searchReady_begin (bound := []) (expected := .base "MlConfig") scope inside
  have resumed := CompleteExecution.searchReady_rounds (bound := []) (expected := .base "MlConfig") scope work begun
  unfold CompleteExecution.RunnerReady
  rw [current]
  exact resumed

theorem tick_returns (state : State) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (machine : CompleteExecution.ClassMachine (epochPlan prepared table)) (quantum : Nat)
    (complete : (epochPlan prepared table).complete = true) (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (checkedSource : Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") machine.state) :
    PureReturns runtime [] state
      (apply "gslt:runner:tick" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (CompleteExecution.classMachineTerm (epochPlan prepared table) machine), number quantum]) state
      (encoded (CompleteExecution.classMachineTerm (epochPlan prepared table)
        (Mettapedia.Machines.ResumableSearchRunner.Machine.tick
          (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine quantum))) := by
  have computed := CompleteExecution.runner_tick_returns (epochPlan prepared table) state .canonical
    (OCamlEpochStandard.names prepared) (OCamlEpochStandard.epoch_table prepared table) [] [] (.base "MlConfig") [] rfl
    (epoch_scope prepared table complete finite) machine (ready prepared table machine complete finite reached checkedSource) quantum
  rw [OCamlEpochStandard.epoch_standard prepared table] at computed
  through_ocaml ["backend", "plan", "standard", "runner", "quantum"] computed

#print axioms ready
#print axioms tick_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerTickExecution
