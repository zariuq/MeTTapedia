import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureRestart
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureServiceCorrespondence

/-! Match-failure service execution includes its actual fresh runner start.
All operational subcalls are discharged from existing loaded execution
theorems and the source request, with epoch and source invariants retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteFailureService

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution

theorem match_service_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (sound : FailureRowsSound (patterns program) table)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    let next := ProviderAppend.appendRows table [failureRow index argument]
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
    let fresh := CompleteExecution.classMachineTerm (epochPlan prepared next)
      (OCamlRunnerBeginExecution.begun prepared next runner.state)
    OCaml.matchPattern parameter argument = none ∧ (epochPlan prepared next).complete = true ∧
      FailureRowsSound (patterns program) next ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:ml:service" [encoded oldPlan, encoded (OCamlEpochStandard.standard prepared),
          encoded (CompleteExecution.classMachineTerm (epochPlan prepared table) runner), encoded epochs]) state
        (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  have restarted := OCamlFailureRestart.match_restart_returns state program prepared
    (ProviderAppend.appendRows table [failureRow index argument]) index parameter argument body capturedEnvironment rest encodedRest
    built referenced resolved
  rw [← atRequest] at restarted
  exact OCamlFailureServiceCorrespondence.match_service_source state program prepared table index parameter argument body capturedEnvironment rest encodedRest
    runner (OCamlEpochStandard.standard prepared) epochs _ built complete signatures closed sound indexed referenced resolved reached done atRequest restarted

#print axioms match_service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteFailureService
