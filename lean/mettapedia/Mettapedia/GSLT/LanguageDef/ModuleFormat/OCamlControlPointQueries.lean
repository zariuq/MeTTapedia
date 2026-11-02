import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPoint
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveQueryReflection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureQueryReflection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternFiring

/-! Actual provider and pattern firings finish administrative work for
the same independent source state. Their ranks strictly decrease; the
query and matcher do not create an extra source computation step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem primitive_query_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest target : Pattern)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[19]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (invariant : SourceProviderInvariant (patterns program) plan.snapshot.provider)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (evaluated : operator.eval arguments = .ok result)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]) ordinal trace captured completed history target) :
    ControlPoint program (finishPrimitive result rest) target 1 ∧ 1 < 2 := by
  obtain ⟨actual, evaluation, _, same⟩ := primitive_query_firing_source position authored zero invariant.signatures invariant.encoded
    invariant.meaningful firing
  have equal : actual = result := Except.ok.inj (evaluation.symm.trans evaluated)
  subst actual
  rw [same]
  exact ⟨.answer resolved, by decide +kernel⟩

theorem primitive_answer_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (result : OCaml.Result) (rest : OCaml.Continuation) (encodedRest target : Pattern)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[match result with | .ok _ => 20 | .error _ => 21]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]) ordinal trace captured completed history target) :
    ControlPoint program (finishPrimitive result rest) target 0 ∧ 0 < 1 := by
  cases result with
  | ok actual =>
    obtain ⟨_, _, same⟩ := base_instance_firing position authored zero (primitive_value_instance (value actual) encodedRest) firing
    rw [same]
    refine ⟨.state ?_, by decide +kernel⟩
    simp only [finishPrimitive, state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | error error =>
    obtain ⟨_, _, same⟩ := base_instance_firing position authored zero (primitive_fault_instance (fault error) encodedRest) firing
    rw [same]
    exact ⟨.state rfl, by decide +kernel⟩

theorem match_failure_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest target : Pattern)
    {trace : List GeneralScopedMatchMachine.BagChoice} {matched completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[25]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (invariant : SourceProviderInvariant (patterns program) plan.snapshot.provider)
    (indexed : (patterns program)[index]? = some parameter)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest])
      ordinal trace matched completed history target) :
    ControlPoint program (OCaml.enterBody parameter argument body captured rest) target 0 ∧ 0 < 1 := by
  obtain ⟨failed, same⟩ := failure_query_firing_source false index parameter argument body (node "MlClauseNil") captured
    encodedRest target position authored zero invariant indexed firing
  change target = node "MlFault" [fault .matchFailure] at same
  rw [OCaml.enterBody, failed, same]
  exact ⟨.state rfl, by decide +kernel⟩

theorem clause_failure_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (index : Nat) (clause : OCaml.Clause) (clauses : List OCaml.Clause) (later : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation)
    (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {matched completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[26]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (invariant : SourceProviderInvariant (patterns program) plan.snapshot.provider)
    (indexed : (patterns program)[index]? = some clause.pattern)
    (listed : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (selected : OCaml.returnValue program argument (.matchValue (clause :: clauses) captured :: rest) = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest])
      ordinal trace matched completed history target) :
    ControlPoint program next target (2 * clauses.length + 1) ∧ 2 * clauses.length + 1 < 2 * clauses.length + 2 := by
  obtain ⟨failed, same⟩ := failure_query_firing_source true index clause.pattern argument clause.body later captured
    encodedRest target position authored zero invariant indexed firing
  change target = node "MlSelect" [later, value argument, environment captured, encodedRest] at same
  rw [same]
  refine ⟨.select listed resolved ?_, by omega⟩
  simpa only [OCaml.returnValue, OCaml.selectClause, failed] using selected

theorem matched_pattern_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest target : Pattern)
    {trace : List GeneralScopedMatchMachine.BagChoice} {matched completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : row.authored = (patternRules index parameter)[0]'(by simp [patternRules]))
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest])
      ordinal trace matched completed history target) :
    ControlPoint program (OCaml.enterBody parameter argument body captured rest) target 0 ∧ 0 < 1 := by
  obtain ⟨_, _, bindings, sourceMatch, same⟩ := match_one_firing_source position authored zero firing
  rw [OCaml.enterBody, sourceMatch, same]
  refine ⟨.state ?_, by decide +kernel⟩
  simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem matched_clause_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (index : Nat) (clause : OCaml.Clause) (clauses : List OCaml.Clause) (later : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation)
    (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {matched completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : row.authored = (patternRules index clause.pattern)[1]'(by simp [patternRules]))
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (selected : OCaml.returnValue program argument (.matchValue (clause :: clauses) captured :: rest) = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest])
      ordinal trace matched completed history target) :
    ControlPoint program next target 0 ∧ 0 < 2 * clauses.length + 2 := by
  obtain ⟨_, _, bindings, sourceMatch, same⟩ := try_clause_firing_source position authored zero firing
  have nextSame : next = .evaluate clause.body (OCaml.extend captured bindings) rest := by
    apply Except.ok.inj
    rw [← selected]
    simp only [OCaml.returnValue, OCaml.selectClause, sourceMatch]
    rfl
  rw [nextSame, same]
  refine ⟨.state ?_, by omega⟩
  simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms primitive_query_lowers_rank
#print axioms primitive_answer_lowers_rank
#print axioms match_failure_lowers_rank
#print axioms clause_failure_lowers_rank
#print axioms matched_pattern_lowers_rank
#print axioms matched_clause_lowers_rank

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
