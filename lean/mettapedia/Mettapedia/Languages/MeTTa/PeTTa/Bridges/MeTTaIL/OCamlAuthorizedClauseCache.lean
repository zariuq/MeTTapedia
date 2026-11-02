import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochCacheExecution

/-! The ordered clause service's loaded table extension retains admission,
source-valid failure keys and prior row positions under the same canonical
runner contract used by emitted execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAuthorizedClauseCache

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit

theorem authorized_clause_cache_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (machine : Complete.Classes.Machine (epochPlan prepared table))
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (sound : FailureRowsSound (patterns program) table)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlTryClause"
      [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest]) :
    let next := ProviderAppend.appendRows table [failureRow index argument]
    OCaml.matchPattern parameter argument = none ∧
      (epochPlan prepared next).complete = true ∧ FailureRowsSound (patterns program) next ∧
      (∀ position, position < table.rows.length → next.rows[position]? = table.rows[position]?) ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:provider-cache:append"
          [encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
           encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [failureRow index argument])]) state
        (encoded (.application "Some" [CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")])) := by
  have epochComplete := epoch_complete prepared table signatures complete closed
  have failed := normalized_clause_failure program prepared table .canonical index parameter argument body capturedEnvironment clauses later rest encodedRest
    machine built complete epochComplete signatures indexed referenced clauseResolved resolved reached done atRequest
  have retained := failure_epoch_invariant program prepared table index parameter argument built complete signatures closed sound indexed failed
  exact ⟨failed, retained.1, retained.2.1, retained.2.2.2,
    OCamlEpochCacheExecution.epoch_append_returns state program prepared table index argument built signatures⟩

#print axioms authorized_clause_cache_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAuthorizedClauseCache
