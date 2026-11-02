import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledServiceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochInstallExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlNormalizedFailure

/-! Source failure authorization, actual service dispatch, checked table
append and immutable epoch retention compose. The common fresh-runner
initialization computation remains an explicit operational premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureServiceCorrespondence

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution OCamlFailureServiceExecution

theorem match_service_source (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (standard epochs fresh : Term)
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
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
    (begun : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared (ProviderAppend.appendRows table [failureRow index argument])) [] [] (.base "MlConfig")),
        encoded standard, encoded (InferenceCettaWire.encodePattern runner.state)]) state (encoded fresh)) :
    let next := ProviderAppend.appendRows table [failureRow index argument]
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
    OCaml.matchPattern parameter argument = none ∧ (epochPlan prepared next).complete = true ∧
      FailureRowsSound (patterns program) next ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:ml:service" [encoded oldPlan, encoded standard,
          encoded (CompleteExecution.classMachineTerm (epochPlan prepared table) runner), encoded epochs]) state
        (encoded (machine "MlRunning" nextPlan standard fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
  let next := ProviderAppend.appendRows table [failureRow index argument]
  let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
  have failed := normalized_match_failure program prepared table .canonical index parameter argument body capturedEnvironment rest encodedRest
    runner built complete (epoch_complete prepared table signatures complete closed) signatures indexed referenced resolved reached done atRequest
  have invariant := failure_epoch_invariant program prepared table index parameter argument built complete signatures closed sound indexed failed
  refine ⟨failed, invariant.1, invariant.2.1, ?_⟩
  have encodedState : InferenceCettaWire.encodePattern runner.state = matchRequest
      (InferenceCettaWire.encodePattern (patternId index)) (InferenceCettaWire.encodePattern (value argument))
      (InferenceCettaWire.encodePattern (code body)) (InferenceCettaWire.encodePattern (environment capturedEnvironment))
      (InferenceCettaWire.encodePattern encodedRest) := by
    rw [atRequest]
    simp only [node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns, matchRequest, encodeList, id_eq]
  have sameRunner : CompleteExecution.classMachineTerm (epochPlan prepared table) runner =
      doneRunner (InferenceCettaWire.encodePattern runner.state) (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
        (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, doneRunner]
  have installed := OCamlEpochInstallExecution.epoch_install_returns state program prepared table index argument standard
    (InferenceCettaWire.encodePattern runner.state) (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
    (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts)
    epochs fresh built signatures begun
  rw [← sameRunner] at installed
  have rowWire : PremiseOperationsExecution.GeneralExecution.providerRowTerm (failureRow index argument) =
      failureRowTerm (InferenceCettaWire.encodePattern (patternId index)) (InferenceCettaWire.encodePattern (value argument)) := by
    simp only [PremiseOperationsExecution.GeneralExecution.providerRowTerm, failureRow,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm, InferenceCettaWire.encodePatterns, failureRowTerm, encodeList, id_eq]
  rw [rowWire] at installed
  exact OCamlSettledServiceExecution.settled_match_service_returns state (epochPlan prepared table) standard _ _ _ _ _ epochs _ runner
    reached done encodedState installed

#print axioms match_service_source

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureServiceCorrespondence
