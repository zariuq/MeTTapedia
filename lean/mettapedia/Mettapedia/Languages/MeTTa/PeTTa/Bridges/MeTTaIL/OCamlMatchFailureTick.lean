import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteFailureService
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderMeaning
/-! Settled pattern failure restarts through the actual controller tick,
retaining both failure and primitive meanings across the provider epoch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlMatchFailureTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution

theorem match_service_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table)
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
      ProviderMeaning (patterns program) next ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:ml:tick" [encoded (machine "MlRunning" oldPlan (OCamlEpochStandard.standard prepared)
          (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  obtain ⟨failed, admitted, _, serviced⟩ := OCamlCompleteFailureService.match_service_returns state program prepared table index parameter argument body capturedEnvironment rest encodedRest runner epochs built complete signatures closed meaning.2 indexed referenced resolved reached done atRequest
  refine ⟨failed, admitted, failure_append_preserves_meaning (patterns program) table index parameter argument meaning indexed failed, ?_⟩
  exact OCamlSettledTick.returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared)
    epochs _ runner done quantum serviced

#print axioms match_service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlMatchFailureTick
