import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPoint
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionFiring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBuildReadout
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClauseDispatch

/-! Function dispatch, clause selection and value construction finish
work for the same source state. Each actual administrative firing lowers
the control-point rank; source formation follows from the source result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem function_dispatch_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (reference : OCaml.Code) (instruction : OCaml.Instruction) (rows : List RewriteRule)
    (function argument : OCaml.Value) (rest : OCaml.Continuation) (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (declared : program.instruction? reference = some instruction)
    (compiled : functionRules? program (patterns program) reference instruction = some rows) (authored : row.authored ∈ rows)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (applied : OCaml.applyClosure program function argument rest = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlApply" [value function, value argument, encodedRest]) ordinal trace captured completed history target) :
    ControlPoint program next target 1 ∧ 1 < 2 := by
  obtain ⟨_, _, parameter, body, patternCode, sourceEnvironment, referenced, same, source⟩ :=
    function_firing_source position declared compiled authored zero firing
  have nextSame : next = OCaml.enterBody parameter argument body sourceEnvironment rest :=
    Except.ok.inj (applied.symm.trans (source rest))
  unfold patternReference? at referenced
  obtain ⟨index, found, codeSame⟩ := Option.map_eq_some_iff.mp referenced
  rw [nextSame, same, ← codeSame]
  exact ⟨.matchOne (OCaml.patternIndex?_sound parameter (patterns program) index found) resolved, by decide +kernel⟩

theorem select_clause_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (index : Nat) (clause : OCaml.Clause) (clauses : List OCaml.Clause) (later : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation)
    (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {matched completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[24]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (indexed : (patterns program)[index]? = some clause.pattern)
    (listed : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (selected : OCaml.returnValue program argument (.matchValue (clause :: clauses) captured :: rest) = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlSelect" [node "MlClauseCons" [patternId index, code clause.body, later], value argument, environment captured, encodedRest])
      ordinal trace matched completed history target) :
    ControlPoint program next target (2 * clauses.length + 2) ∧
      2 * clauses.length + 2 < 2 * (clause :: clauses).length + 1 := by
  obtain ⟨_, _, same⟩ := select_clause_firing position authored zero firing
  rw [same]
  exact ⟨.clause indexed listed resolved selected, by simp only [List.length_cons]; omega⟩

theorem select_empty_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation)
    (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {matched completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[23]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (selected : OCaml.returnValue program argument (.matchValue [] captured :: rest) = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlSelect" [node "MlClauseNil", value argument, environment captured, encodedRest])
      ordinal trace matched completed history target) :
    ControlPoint program next target 0 ∧ 0 < 1 := by
  obtain ⟨_, _, same⟩ := base_instance_firing position authored zero
    (select_empty_instance (value argument) (environment captured) encodedRest) firing
  have nextSame : next = .halted (.error .matchFailure) := Except.ok.inj selected.symm
  rw [same, nextSame]
  exact ⟨.state rfl, by decide +kernel⟩

theorem build_tuple_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (items : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[16]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (finished : OCaml.finishBuild program .tuple items rest = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlBuildConfig" [build .tuple, valueList items, encodedRest]) ordinal trace captured completed history target) :
    ControlPoint program next target 0 ∧ 0 < 3 := by
  have formed : 2 ≤ items.length := by
    by_contra small
    have invalid : items.length < 2 := by omega
    simp only [OCaml.finishBuild, if_pos invalid] at finished
    cases finished
  obtain ⟨_, _, actual, actualFinished, encoded⟩ := build_tuple_source (program := program) (pool := patterns program)
    position authored zero formed resolved firing
  have same : actual = next := Except.ok.inj (actualFinished.symm.trans finished)
  exact ⟨.state (same ▸ encoded), by decide +kernel⟩

theorem build_variant_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (typeId constructor : Nat) (items : List OCaml.Value) (rest : OCaml.Continuation)
    (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[17]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (finished : OCaml.finishBuild program (.variant typeId constructor) items rest = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlBuildConfig" [build (.variant typeId constructor), valueList items, encodedRest])
      ordinal trace captured completed history target) :
    ControlPoint program next target 0 ∧ 0 < 3 := by
  have formed : program.constructorDeclared typeId constructor items.length = true := by
    by_contra missing
    have invalid : program.constructorDeclared typeId constructor items.length = false := Bool.eq_false_iff.mpr missing
    unfold OCaml.finishBuild at finished
    change (if program.constructorDeclared typeId constructor items.length then _ else _) = _ at finished
    rw [invalid] at finished
    cases finished
  obtain ⟨_, _, actual, actualFinished, encoded⟩ := build_variant_source (program := program) (pool := patterns program)
    position authored zero formed resolved firing
  have same : actual = next := Except.ok.inj (actualFinished.symm.trans finished)
  exact ⟨.state (same ▸ encoded), by decide +kernel⟩

theorem build_primitive_lowers_rank {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (rest : OCaml.Continuation)
    (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row) (authored : baseLanguage.rewrites[18]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (finished : OCaml.finishBuild program (.primitive operator) arguments rest = .ok next)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlBuildConfig" [build (.primitive operator), valueList arguments, encodedRest])
      ordinal trace captured completed history target) :
    ControlPoint program next target 2 ∧ 2 < 3 := by
  obtain ⟨_, _, same⟩ := base_instance_firing position authored zero
    (build_primitive_instance (primitive operator) (valueList arguments) encodedRest) firing
  rw [same]
  cases evaluated : operator.eval arguments with
  | error error => simp only [OCaml.finishBuild, evaluated] at finished; cases finished
  | ok result =>
    have actual := finish_primitive_source program operator arguments result rest evaluated
    have nextSame : next = finishPrimitive result rest := Except.ok.inj (finished.symm.trans actual)
    rw [nextSame]
    exact ⟨.primitive resolved evaluated, by decide +kernel⟩

#print axioms function_dispatch_lowers_rank
#print axioms select_clause_lowers_rank
#print axioms select_empty_lowers_rank
#print axioms build_tuple_lowers_rank
#print axioms build_variant_lowers_rank
#print axioms build_primitive_lowers_rank

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
