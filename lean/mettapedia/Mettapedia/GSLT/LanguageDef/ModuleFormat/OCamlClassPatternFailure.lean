import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholePlanRows
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPlanCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClausePlanCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralRootStep
import Mettapedia.OSLF.MeTTaIL.Complete.Classes

/-! A settled full-plan class runner cannot be waiting for a successful
source pattern. This discharges the semantic authorization for installing
a failure-provider row; provider transport and loaded service execution are
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem whole_match_success_step (program : OCaml.Program) (prepared : Prepared) (index : Nat)
    (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (bindings : List OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    (GeneralOccurrenceSemantics.gslt (plan prepared) [] (.base "MlConfig")).Step
      (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
      (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) := by
  obtain ⟨ordinal, row, selected, authored, _⟩ := whole_plan_pattern program prepared index parameter
    ((patternRules index parameter)[0]'(by simp [patternRules])) built indexed (List.getElem_mem _) complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨trace, captured, firing⟩ := match_one_plan_coverage selected terms types authored referenced resolved matched
  have grammar : (GeneralPlanEnvironment.environment (plan prepared)).language.terms = baseLanguage.terms := terms
  exact GeneralOccurrenceSemantics.root_firing_step selected rfl
    (match_request_open _ grammar _ referenced argument body capturedEnvironment rest encodedRest resolved) firing

theorem settled_match_failure (program : OCaml.Program) (prepared : Prepared) (index : Nat)
    (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (plan prepared))
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Classes.search (plan prepared) [] (.base "MlConfig")) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    OCaml.matchPattern parameter argument = none := by
  have noStep := Complete.Classes.done_no_step (plan prepared) [] (.base "MlConfig")
    (Complete.Predecessors.equationsChecked_of_complete complete) reached done
  cases matched : OCaml.matchPattern parameter argument with
  | none => rfl
  | some bindings =>
    have step := whole_match_success_step program prepared index parameter argument bindings body capturedEnvironment rest encodedRest
      built complete indexed referenced resolved matched
    rw [← atRequest] at step
    exact False.elim (noStep _ step)

#print axioms whole_match_success_step
#print axioms settled_match_failure

theorem whole_clause_success_step (program : OCaml.Program) (prepared : Prepared) (index : Nat)
    (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (bindings : List OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    (GeneralOccurrenceSemantics.gslt (plan prepared) [] (.base "MlConfig")).Step
      (node "MlTryClause" [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest])
      (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) := by
  obtain ⟨ordinal, row, selected, authored, _⟩ := whole_plan_pattern program prepared index parameter
    ((patternRules index parameter)[1]'(by simp [patternRules])) built indexed (List.getElem_mem _) complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨trace, captured, firing⟩ := try_clause_plan_coverage selected terms types authored referenced clauseResolved resolved matched
  have grammar : (GeneralPlanEnvironment.environment (plan prepared)).language.terms = baseLanguage.terms := terms
  exact GeneralOccurrenceSemantics.root_firing_step selected rfl
    (clause_request_open _ grammar _ referenced argument body clauses later clauseResolved capturedEnvironment rest encodedRest resolved) firing

theorem settled_clause_failure (program : OCaml.Program) (prepared : Prepared) (index : Nat)
    (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (plan prepared))
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
    OCaml.matchPattern parameter argument = none := by
  have noStep := Complete.Classes.done_no_step (plan prepared) [] (.base "MlConfig")
    (Complete.Predecessors.equationsChecked_of_complete complete) reached done
  cases matched : OCaml.matchPattern parameter argument with
  | none => rfl
  | some bindings =>
    have step := whole_clause_success_step program prepared index parameter argument bindings body capturedEnvironment clauses later rest encodedRest
      built complete indexed referenced clauseResolved resolved matched
    rw [← atRequest] at step
    exact False.elim (noStep _ step)

#print axioms whole_clause_success_step
#print axioms settled_clause_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
