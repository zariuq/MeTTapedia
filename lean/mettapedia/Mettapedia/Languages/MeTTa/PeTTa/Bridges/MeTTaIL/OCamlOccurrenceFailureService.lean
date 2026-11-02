import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControlPointFailureInstall
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledServiceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSettledPatternFailure

/-! Actual failure ticks work at every retained source pattern occurrence.
Exhaustion supplies failure authorization, and the current control point
supplies fresh-runner typing without a first-occurrence lookup assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOccurrenceFailureService

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlFailureServiceExecution

theorem match_failure_tick (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (source : OCaml.MachineState) (rank : Nat) (point : ControlPoint program source runner.state rank)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (indexed : (patterns program)[index]? = some parameter)
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
    OCaml.matchPattern parameter argument = none ∧ SourceEpochInvariant program prepared next ∧
      Mettapedia.Machines.ResumableSearchRunner.Reached
        (Complete.Normalized.search (epochPlan prepared next) [] (.base "MlConfig") .canonical)
        (OCamlRunnerBeginExecution.begun prepared next runner.state) ∧
      ControlPoint program source (OCamlRunnerBeginExecution.begun prepared next runner.state).state rank ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:ml:tick" [encoded (machine "MlRunning" oldPlan (OCamlEpochStandard.standard prepared)
          (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  have failed := settled_match_failure_any_index program prepared table runner index parameter argument body capturedEnvironment
    rest encodedRest built invariant indexed resolved reached done atRequest
  have nextInvariant := invariant.failure built index parameter argument indexed failed
  have restarted := control_point_epoch_restart program prepared (ProviderAppend.appendRows table [failureRow index argument]) built point
  have installed := OCamlControlPointFailureInstall.returns state program prepared table index argument runner epochs built invariant point done
  have rowWire : PremiseOperationsExecution.GeneralExecution.providerRowTerm (failureRow index argument) =
      failureRowTerm (InferenceCettaWire.encodePattern (patternId index)) (InferenceCettaWire.encodePattern (value argument)) := by
    simp only [PremiseOperationsExecution.GeneralExecution.providerRowTerm, failureRow,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm, InferenceCettaWire.encodePatterns, failureRowTerm, encodeList, id_eq]
  dsimp only at installed
  rw [rowWire] at installed
  have encodedState : InferenceCettaWire.encodePattern runner.state = matchRequest
      (InferenceCettaWire.encodePattern (patternId index)) (InferenceCettaWire.encodePattern (value argument))
      (InferenceCettaWire.encodePattern (code body)) (InferenceCettaWire.encodePattern (environment capturedEnvironment))
      (InferenceCettaWire.encodePattern encodedRest) := by
    rw [atRequest]
    simp only [node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns, matchRequest, encodeList, id_eq]
  have serviced := OCamlSettledServiceExecution.settled_match_service_returns state (epochPlan prepared table)
    (OCamlEpochStandard.standard prepared)  _ _ _ _ _ epochs _ runner reached done encodedState installed
  have executed := OCamlSettledTick.returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared) epochs _ runner done quantum serviced
  exact ⟨failed, nextInvariant, restarted.1, restarted.2, executed⟩

#print axioms match_failure_tick

theorem clause_failure_tick (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (source : OCaml.MachineState) (rank : Nat) (point : ControlPoint program source runner.state rank)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (indexed : (patterns program)[index]? = some parameter)
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlTryClause"
      [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest]) :
    let next := ProviderAppend.appendRows table [failureRow index argument]
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
    let fresh := CompleteExecution.classMachineTerm (epochPlan prepared next)
      (OCamlRunnerBeginExecution.begun prepared next runner.state)
    OCaml.matchPattern parameter argument = none ∧ SourceEpochInvariant program prepared next ∧
      Mettapedia.Machines.ResumableSearchRunner.Reached
        (Complete.Normalized.search (epochPlan prepared next) [] (.base "MlConfig") .canonical)
        (OCamlRunnerBeginExecution.begun prepared next runner.state) ∧
      ControlPoint program source (OCamlRunnerBeginExecution.begun prepared next runner.state).state rank ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:ml:tick" [encoded (machine "MlRunning" oldPlan (OCamlEpochStandard.standard prepared)
          (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  have failed := settled_clause_failure_any_index program prepared table runner index ⟨parameter, body⟩ clauses later argument
    capturedEnvironment rest encodedRest built invariant indexed clauseResolved resolved reached done atRequest
  have nextInvariant := invariant.failure built index parameter argument indexed failed
  have restarted := control_point_epoch_restart program prepared (ProviderAppend.appendRows table [failureRow index argument]) built point
  have installed := OCamlControlPointFailureInstall.returns state program prepared table index argument runner epochs built invariant point done
  have rowWire : PremiseOperationsExecution.GeneralExecution.providerRowTerm (failureRow index argument) =
      failureRowTerm (InferenceCettaWire.encodePattern (patternId index)) (InferenceCettaWire.encodePattern (value argument)) := by
    simp only [PremiseOperationsExecution.GeneralExecution.providerRowTerm, failureRow,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm, InferenceCettaWire.encodePatterns, failureRowTerm, encodeList, id_eq]
  dsimp only at installed
  rw [rowWire] at installed
  have encodedState : InferenceCettaWire.encodePattern runner.state = clauseRequest
      (InferenceCettaWire.encodePattern (patternId index)) (InferenceCettaWire.encodePattern (value argument))
      (InferenceCettaWire.encodePattern (code body)) (InferenceCettaWire.encodePattern later) (InferenceCettaWire.encodePattern (environment capturedEnvironment))
      (InferenceCettaWire.encodePattern encodedRest) := by
    rw [atRequest]
    simp only [node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns, clauseRequest, encodeList, id_eq]
  have serviced := OCamlSettledServiceExecution.settled_clause_service_returns state (epochPlan prepared table)
    (OCamlEpochStandard.standard prepared)  _ _ _ _ _ _ epochs _ runner reached done encodedState installed
  have executed := OCamlSettledTick.returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared) epochs _ runner done quantum serviced
  exact ⟨failed, nextInvariant, restarted.1, restarted.2, executed⟩

#print axioms clause_failure_tick

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOccurrenceFailureService
