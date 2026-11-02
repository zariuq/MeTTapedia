import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerTickInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedPrimitiveQuery
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedMatchFailure
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedClauseFailure

/-! A settled source request executes one actual service tick and restarts
with an enabled prepared step. Service installation cannot merely create
another exhausted epoch at the same request.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceProgress

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Machines.ResumableSearchRunner
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant

private theorem fresh_state (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    {source : OCaml.MachineState} {config : Pattern} {rank : Nat}
    (built : prepare program = .ok prepared) (point : ControlPoint program source config rank) :
    (OCamlRunnerBeginExecution.begun prepared table config).state = config :=
  control_point_commit program prepared table built point

theorem supplies_enabled_step (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
    (epochs : Term) (quantum : Nat) {source : OCaml.MachineState} {rank : Nat}
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done) (point : ControlPoint program source runner.state rank)
    (request : SourceServiceRequest program runner.state) :
    ∃ (next : ProviderSnapshot) (fresh : CompleteExecution.ClassMachine (epochPlan prepared next)) (nextEpochs : Term),
      SourceEpochInvariant program prepared next ∧
      Reached (Complete.Normalized.search (epochPlan prepared next) [] (.base "MlConfig") .canonical) fresh ∧
      ControlPoint program source fresh.state rank ∧
      (∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared next) [] (.base "MlConfig")).Step fresh.state target) ∧
      PureReturns runtime [] state (apply "gslt:ml:tick"
        [encoded (controller prepared table "MlRunning" runner epochs), number quantum]) state
        (encoded (controller prepared next "MlRunning" fresh nextEpochs)) := by
  generalize atRequest : runner.state = config at request
  cases request with
  | primitive operator arguments result rest encodedRest resolved evaluated =>
    obtain ⟨nextInvariant, nextReached, nextPoint, computed⟩ := OCamlServiceSourcePreservation.primitive_tick state program prepared table
      operator arguments result rest encodedRest runner epochs quantum source rank point built invariant resolved reached done atRequest evaluated
    let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
    let fresh := OCamlRunnerBeginExecution.begun prepared next runner.state
    refine ⟨next, fresh, OCamlControllerTickInvariant.epochHistory prepared table runner epochs,
      nextInvariant, nextReached, nextPoint, ?_, computed⟩
    have enabled := prepared_primitive_query_step program prepared next operator arguments result rest encodedRest built
      nextInvariant.source.signatures resolved (by simp [next, ProviderAppend.appendRows])
    have same := (fresh_state program prepared next built point).trans atRequest
    exact ⟨_, same.symm ▸ enabled⟩
  | matchFailure index parameter argument body captured rest encodedRest indexed resolved _failed =>
    obtain ⟨_, nextInvariant, nextReached, nextPoint, computed⟩ := OCamlOccurrenceFailureService.match_failure_tick state program prepared table
      index parameter argument body captured rest encodedRest runner epochs quantum source rank point built invariant indexed resolved reached done atRequest
    let next := ProviderAppend.appendRows table [failureRow index argument]
    let fresh := OCamlRunnerBeginExecution.begun prepared next runner.state
    refine ⟨next, fresh, OCamlControllerTickInvariant.epochHistory prepared table runner epochs,
      nextInvariant, nextReached, nextPoint, ?_, computed⟩
    have enabled := prepared_match_failure_step_any_index program prepared next index argument body captured rest encodedRest built
      nextInvariant.source.signatures resolved (by simp [next, ProviderAppend.appendRows])
    have same := (fresh_state program prepared next built point).trans atRequest
    exact ⟨_, same.symm ▸ enabled⟩
  | clauseFailure index clause clauses later argument captured rest encodedRest indexed listed resolved _failed =>
    obtain ⟨_, nextInvariant, nextReached, nextPoint, computed⟩ := OCamlOccurrenceFailureService.clause_failure_tick state program prepared table
      index clause.pattern argument clause.body captured clauses later rest encodedRest runner epochs quantum source rank point built invariant indexed
      listed resolved reached done atRequest
    let next := ProviderAppend.appendRows table [failureRow index argument]
    let fresh := OCamlRunnerBeginExecution.begun prepared next runner.state
    refine ⟨next, fresh, OCamlControllerTickInvariant.epochHistory prepared table runner epochs,
      nextInvariant, nextReached, nextPoint, ?_, computed⟩
    have enabled := prepared_clause_failure_step_any_index program prepared next index argument clause.body clauses later captured rest encodedRest built
      nextInvariant.source.signatures listed resolved (by simp [next, ProviderAppend.appendRows])
    have same := (fresh_state program prepared next built point).trans atRequest
    exact ⟨_, same.symm ▸ enabled⟩

#print axioms supplies_enabled_step

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceProgress
