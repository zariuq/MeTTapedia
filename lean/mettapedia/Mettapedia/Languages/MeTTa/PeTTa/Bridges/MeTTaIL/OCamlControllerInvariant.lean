import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceSourcePreservation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompletedPreservation

/-! A source relation for the actual controller wire value. Running values
retain an epoch invariant, a reached runner and a finite independent source
result witness. Complete values retain the exact source result and histories.
This is an observation invariant, not an additional executor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerInvariant

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner
open OCamlInstallExecution

def controller (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) (phase : String)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) : Term :=
  machine phase (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig"))
    (OCamlEpochStandard.standard prepared) (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs

inductive Realizes (program : OCaml.Program) (prepared : Prepared) (expected : OCaml.Result) : Term → Prop where
  | running (table : GeneralPremise.ProviderSnapshot) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
      (epochs : Term) (source : OCaml.MachineState) (rank work : Nat) :
      SourceEpochInvariant program prepared table →
      Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner →
      ControlPoint program source runner.state rank → OCaml.run program work source = .complete expected →
      Realizes program prepared expected (controller prepared table "MlRunning" runner epochs)
  | complete (table : GeneralPremise.ProviderSnapshot) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
      (epochs : Term) :
      SourceEpochInvariant program prepared table →
      Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner →
      runner.phase = .done → state? (patterns program) (.halted expected) = some runner.state →
      Realizes program prepared expected (controller prepared table "MlComplete" runner epochs)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerInvariant
