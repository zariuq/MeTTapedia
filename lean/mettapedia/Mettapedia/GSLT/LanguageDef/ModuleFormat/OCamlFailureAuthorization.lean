import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureRows

/-! The existing completed class runner supplies source authorization for
failure-cache extension. Search budgets and empty pending pages cannot
supply this evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem settled_match_append_sound (program : OCaml.Program) (prepared : Prepared) (index : Nat)
    (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (plan prepared)) (snapshot : GeneralPremise.ProviderSnapshot)
    (sound : FailureRowsSound (patterns program) snapshot)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Classes.search (plan prepared) [] (.base "MlConfig")) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    FailureRowsSound (patterns program) (GeneralPremise.ProviderAppend.appendRows snapshot [failureRow index argument]) := by
  exact append_failure_sound (patterns program) snapshot index parameter argument sound indexed
    (settled_match_failure program prepared index parameter argument body capturedEnvironment rest encodedRest machine
      built complete indexed referenced resolved reached done atRequest)

theorem settled_clause_append_sound (program : OCaml.Program) (prepared : Prepared) (index : Nat)
    (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (plan prepared)) (snapshot : GeneralPremise.ProviderSnapshot)
    (sound : FailureRowsSound (patterns program) snapshot)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Classes.search (plan prepared) [] (.base "MlConfig")) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlTryClause"
      [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest]) :
    FailureRowsSound (patterns program) (GeneralPremise.ProviderAppend.appendRows snapshot [failureRow index argument]) := by
  exact append_failure_sound (patterns program) snapshot index parameter argument sound indexed
    (settled_clause_failure program prepared index parameter argument body capturedEnvironment clauses later rest encodedRest machine
      built complete indexed referenced clauseResolved resolved reached done atRequest)

#print axioms settled_match_append_sound
#print axioms settled_clause_append_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
