import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceCacheInvariant
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlMatchFailureTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlClauseFailureTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceProviderInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointRestart
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAllPrimitiveExecution

/-! Actual loaded service ticks preserve the complete source epoch invariant
and the source control point of the restarted runner. Primitive computation
is supplied by the exhaustive loaded-dispatch theorem, not by a caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceSourcePreservation

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem primitive_tick (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (source : OCaml.MachineState) (rank : Nat) (point : ControlPoint program source runner.state rank)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest])
    (evaluated : operator.eval arguments = .ok result) :
    let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
    let fresh := OCamlRunnerBeginExecution.begun prepared next runner.state
    SourceEpochInvariant program prepared next ∧
      Mettapedia.Machines.ResumableSearchRunner.Reached
        (Complete.Normalized.search (epochPlan prepared next) [] (.base "MlConfig") .canonical) fresh ∧
      ControlPoint program source fresh.state rank ∧ PureReturns runtime [] state (apply "gslt:ml:tick"
        [encoded (machine "MlRunning" (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig"))
          (OCamlEpochStandard.standard prepared) (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table operator arguments result runner epochs)) := by
  obtain ⟨_, _, executed⟩ := OCamlServiceCacheInvariant.primitive_tick state program prepared table operator arguments result rest encodedRest
    runner epochs quantum built invariant.source invariant.closed resolved reached done atRequest evaluated
    (OCamlAllPrimitiveExecution.returns state operator arguments result evaluated)
  have nextInvariant := invariant.primitive built operator arguments result evaluated
  have restarted := control_point_epoch_restart program prepared (ProviderAppend.appendRows table [primitiveRow operator arguments result]) built point
  exact ⟨nextInvariant, restarted.1, restarted.2, executed⟩

theorem match_failure_tick (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (source : OCaml.MachineState) (rank : Nat) (point : ControlPoint program source runner.state rank)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
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
  obtain ⟨failed, _, _, executed⟩ := OCamlServiceCacheInvariant.match_failure_tick state program prepared table index parameter argument
    body capturedEnvironment rest encodedRest runner epochs quantum built invariant.source invariant.closed indexed referenced resolved reached done atRequest
  have nextInvariant := invariant.failure built index parameter argument indexed failed
  have restarted := control_point_epoch_restart program prepared (ProviderAppend.appendRows table [failureRow index argument]) built point
  exact ⟨failed, nextInvariant, restarted.1, restarted.2, executed⟩

theorem clause_failure_tick (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (source : OCaml.MachineState) (rank : Nat) (point : ControlPoint program source runner.state rank)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
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
  obtain ⟨failed, _, _, executed⟩ := OCamlServiceCacheInvariant.clause_failure_tick state program prepared table index parameter argument
    body capturedEnvironment clauses later rest encodedRest runner epochs quantum built invariant.source invariant.closed indexed referenced clauseResolved
    resolved reached done atRequest
  have nextInvariant := invariant.failure built index parameter argument indexed failed
  have restarted := control_point_epoch_restart program prepared (ProviderAppend.appendRows table [failureRow index argument]) built point
  exact ⟨failed, nextInvariant, restarted.1, restarted.2, executed⟩

#print axioms primitive_tick
#print axioms match_failure_tick
#print axioms clause_failure_tick

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceSourcePreservation
