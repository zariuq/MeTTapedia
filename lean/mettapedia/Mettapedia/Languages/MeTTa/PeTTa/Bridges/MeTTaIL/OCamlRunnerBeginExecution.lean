import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochStandard

/-! The common runner's existing initialization theorem executes under
the actual loaded O0 libraries. No fresh-runner computation is supplied
as an oracle; the source request's checked representation is sufficient.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerBeginExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource

def begun (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) (source : Pattern) :
    CompleteExecution.ClassMachine (epochPlan prepared table) :=
  Mettapedia.Machines.ResumableSearchRunner.Machine.begin
    (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical)
    (Complete.Normalized.commit (epochPlan prepared table) .canonical source)

theorem begin_returns (state : State) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) (source : Pattern)
    (closed : source.freeFvarNames = [])
    (checkedSource : Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") source) :
    PureReturns runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern source)]) state
      (encoded (CompleteExecution.classMachineTerm (epochPlan prepared table) (begun prepared table source))) := by
  have inside : ∀ name ∈ source.freeFvarNames, name ∈ ([] : List String) := by rw [closed]; simp
  have computed := CompleteExecution.runner_begin_returns (epochPlan prepared table) state .canonical
    (OCamlEpochStandard.names prepared) (OCamlEpochStandard.epoch_table prepared table) [] [] (.base "MlConfig") [] rfl
    (OCamlEpochStandard.epoch_declared prepared table) source inside
    (OCamlEpochStandard.request_commit_ready prepared table source checkedSource)
  rw [OCamlEpochStandard.epoch_standard prepared table] at computed
  through_ocaml ["backend", "plan", "standard", "source"] computed

#print axioms begin_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerBeginExecution
