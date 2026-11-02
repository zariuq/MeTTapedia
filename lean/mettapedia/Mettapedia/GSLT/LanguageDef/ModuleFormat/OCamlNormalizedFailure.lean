import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochClauseAuthorization
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-! The emitted runner commits canonical forms. Its settled state still
has no authored step, so failure authorization applies directly to that
actual normalized runner, for every declared commit mode.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem normalized_match_failure (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (mode : Complete.Normalized.Commit) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (epochPlan prepared table))
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (epochComplete : (epochPlan prepared table).complete = true) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") mode) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    OCaml.matchPattern parameter argument = none := by
  have noStep := Complete.Normalized.done_no_step (epochPlan prepared table) [] (.base "MlConfig")
    (Complete.Predecessors.equationsChecked_of_complete epochComplete) reached done
  cases matched : OCaml.matchPattern parameter argument with
  | none => rfl
  | some bindings =>
    have step := epoch_match_success_step program prepared table index parameter argument bindings body capturedEnvironment rest encodedRest
      built complete signatures indexed referenced resolved matched
    rw [← atRequest] at step
    exact False.elim (noStep _ step)

theorem normalized_clause_failure (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (mode : Complete.Normalized.Commit) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (epochPlan prepared table))
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (epochComplete : (epochPlan prepared table).complete = true) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") mode) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlTryClause"
      [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest]) :
    OCaml.matchPattern parameter argument = none := by
  have noStep := Complete.Normalized.done_no_step (epochPlan prepared table) [] (.base "MlConfig")
    (Complete.Predecessors.equationsChecked_of_complete epochComplete) reached done
  cases matched : OCaml.matchPattern parameter argument with
  | none => rfl
  | some bindings =>
    have step := epoch_clause_success_step program prepared table index parameter argument bindings body capturedEnvironment clauses later rest encodedRest
      built complete signatures indexed referenced clauseResolved resolved matched
    rw [← atRequest] at step
    exact False.elim (noStep _ step)

#print axioms normalized_match_failure
#print axioms normalized_clause_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
