import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlMatchFailureTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlClauseFailureTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceProviderInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedAdmission

/-! The loaded public service ticks preserve source-encoded cache rows
alongside source meanings and actual plan admission. Their target terms,
runner histories and provider append operations are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceCacheInvariant

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem primitive_tick (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest])
    (evaluated : operator.eval arguments = .ok result)
    (computed : PureReturns runtime [] state (OCamlPrimitiveReflection.call operator arguments) state
      (encoded (OCamlArithmeticAdequacy.resultTerm result))) :
    let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
    (epochPlan prepared next).complete = true ∧ SourceProviderInvariant (patterns program) next ∧
      PureReturns runtime [] state (apply "gslt:ml:tick"
        [encoded (machine "MlRunning" (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig"))
          (OCamlEpochStandard.standard prepared) (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table operator arguments result runner epochs)) := by
  obtain ⟨admitted, _, executed⟩ := OCamlPrimitiveTick.returns state program prepared table operator arguments result rest encodedRest
    runner epochs quantum built (prepared_plan_complete program prepared built) invariant.signatures closed invariant.meaningful resolved
    reached done atRequest evaluated computed
  exact ⟨admitted, primitive_append_source_invariant (patterns program) table operator arguments result invariant evaluated, executed⟩

theorem match_failure_tick (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
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
      SourceProviderInvariant (patterns program) next ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:ml:tick" [encoded (machine "MlRunning" oldPlan (OCamlEpochStandard.standard prepared)
          (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  obtain ⟨failed, admitted, _, executed⟩ := OCamlMatchFailureTick.match_service_returns state program prepared table index parameter argument
    body capturedEnvironment rest encodedRest runner epochs quantum built (prepared_plan_complete program prepared built)
    invariant.signatures closed invariant.meaningful indexed referenced resolved reached done atRequest
  exact ⟨failed, admitted, failure_append_source_invariant (patterns program) table index parameter argument invariant indexed failed, executed⟩

theorem clause_failure_tick (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
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
    OCaml.matchPattern parameter argument = none ∧ (epochPlan prepared next).complete = true ∧
      SourceProviderInvariant (patterns program) next ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:ml:tick" [encoded (machine "MlRunning" oldPlan (OCamlEpochStandard.standard prepared)
          (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  obtain ⟨failed, admitted, _, executed⟩ := OCamlClauseFailureTick.clause_service_returns state program prepared table index parameter argument
    body capturedEnvironment clauses later rest encodedRest runner epochs quantum built (prepared_plan_complete program prepared built)
    invariant.signatures closed invariant.meaningful indexed referenced clauseResolved resolved reached done atRequest
  exact ⟨failed, admitted, failure_append_source_invariant (patterns program) table index parameter argument invariant indexed failed, executed⟩

#print axioms primitive_tick
#print axioms match_failure_tick
#print axioms clause_failure_tick

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceCacheInvariant
