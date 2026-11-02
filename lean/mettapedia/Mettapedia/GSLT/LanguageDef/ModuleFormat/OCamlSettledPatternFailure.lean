import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlForwardPattern
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceEpochInvariant

/-! Exhaustion authorizes source pattern failure at the actual pool
occurrence. A successful source match would construct a compiled step,
including when an identical pattern occurs earlier in the pool.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem settled_match_failure_any_index (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (indexed : (patterns program)[index]? = some parameter) (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (request : runner.state = node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]) :
    OCaml.matchPattern parameter argument = none := by
  cases matched : OCaml.matchPattern parameter argument with
  | none => rfl
  | some bindings =>
    have step := prepared_match_success_step_any_index program prepared table index parameter argument body captured rest encodedRest
      bindings built invariant.source.signatures indexed resolved matched
    rw [← request] at step
    have checked := Complete.Predecessors.equationsChecked_of_complete (invariant.complete built)
    exact False.elim (Complete.Normalized.done_no_step (epochPlan prepared table) [] (.base "MlConfig") checked reached done _ step)

theorem settled_clause_failure_any_index (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (index : Nat) (clause : OCaml.Clause) (clauses : List OCaml.Clause) (later : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (indexed : (patterns program)[index]? = some clause.pattern) (listed : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (request : runner.state = node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest]) :
    OCaml.matchPattern clause.pattern argument = none := by
  cases matched : OCaml.matchPattern clause.pattern argument with
  | none => rfl
  | some bindings =>
    have step := prepared_clause_success_step_any_index program prepared table index clause clauses later argument captured rest encodedRest
      bindings built invariant.source.signatures indexed listed resolved matched
    rw [← request] at step
    have checked := Complete.Predecessors.equationsChecked_of_complete (invariant.complete built)
    exact False.elim (Complete.Normalized.done_no_step (epochPlan prepared table) [] (.base "MlConfig") checked reached done _ step)

#print axioms settled_match_failure_any_index
#print axioms settled_clause_failure_any_index

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
