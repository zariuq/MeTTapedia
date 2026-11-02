import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedPrimitiveQuery
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedMatchFailure
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedClauseFailure
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceEpochInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeSteps

/-! A settled service request has no cached answer. If its row were present,
the actual prepared query rule would give a step, contradicting exhaustion.
A paused request provides no such absence evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

private theorem settled_no_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (built : prepare program = .ok prepared)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done) (target : Pattern) :
    ¬ (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step runner.state target := by
  have checked : Complete.Predecessors.equationsChecked (epochPlan prepared table) = true := by
    rw [Complete.Predecessors.equationsChecked, epoch_compiled_equations_empty program prepared table built]
    rfl
  exact Complete.Normalized.done_no_step (epochPlan prepared table) [] (.base "MlConfig") checked reached done target

theorem settled_primitive_uncached (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (request : runner.state = node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]) :
    primitiveRow operator arguments result ∉ table.rows := by
  intro present
  have step := prepared_primitive_query_step program prepared table operator arguments result rest encodedRest built signatures resolved present
  rw [← request] at step
  exact settled_no_step program prepared table runner built reached done _ step

theorem settled_match_uncached (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (request : runner.state = node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]) :
    failureRow index argument ∉ table.rows := by
  intro present
  have step := prepared_match_failure_step program prepared table index parameter argument body captured rest encodedRest
    built signatures referenced resolved present
  rw [← request] at step
  exact settled_no_step program prepared table runner built reached done _ step

theorem settled_clause_uncached (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (listed : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (request : runner.state = node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest]) :
    failureRow index argument ∉ table.rows := by
  intro present
  have step := prepared_clause_failure_step program prepared table index parameter argument body clauses later captured rest encodedRest
    built signatures referenced listed resolved present
  rw [← request] at step
  exact settled_no_step program prepared table runner built reached done _ step

#print axioms settled_primitive_uncached
#print axioms settled_match_uncached
#print axioms settled_clause_uncached

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
