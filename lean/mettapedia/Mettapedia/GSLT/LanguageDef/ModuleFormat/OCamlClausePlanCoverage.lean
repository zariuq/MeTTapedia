import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPlanCoverage

/-! Successful clause-pattern requests construct actual root receipts.
The remaining clause list is typed and retained separately from the ordered
bindings published by the successful source pattern.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem try_clause_plan_coverage {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {argument : OCaml.Value}
    {bindings : List OCaml.Value} {body : OCaml.Code} {capturedEnvironment : OCaml.Environment}
    {clauses : List OCaml.Clause} {later : Pattern} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : row.authored = (patternRules index parameter)[1]'(by simp [patternRules]))
    (referenced : patternReference? pool parameter = some (patternId index))
    (clauseResolved : clauseList? pool clauses = some later)
    (resolved : continuation? pool rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlTryClause" [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest])
      ordinal trace captured captured []
      (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) := by
  let runtime := GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have member : row.authored ∈ patternRules index parameter := by rw [authored]; exact List.getElem_mem _
  obtain ⟨leftShape, rightShape, premiseFree⟩ := pattern_rule_shapes parameter index row.authored member
  obtain ⟨omitted, empty, hasInput, head⟩ := pattern_rule_binding_fields parameter index row.authored member
  have binding := selected_base_binding position terms types
  have runtimeBinding : GeneralRuleBindingInference.compile? runtime.language row.authored = some row.binding := by
    rw [GeneralRuleBindingInference.compile?_transport grammar (show runtime.language.typeNames = baseLanguage.typeNames from types)]
    exact binding
  obtain ⟨assignment, input, output⟩ := try_clause_rule_complete parameter index argument bindings body later capturedEnvironment encodedRest matched
  rw [← authored] at input output
  have sourceTyped := clause_request_open runtime.language grammar runtime.free referenced argument body clauses later clauseResolved
    capturedEnvironment rest encodedRest resolved
  have sourceEmpty := clause_request_open baseLanguage rfl Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    referenced argument body clauses later clauseResolved capturedEnvironment rest encodedRest resolved
  have closed : (node "MlTryClause"
      [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest]).freeFvarNames = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name present
    obtain ⟨_, impossible⟩ := sourceEmpty.1.freeType_of_mem_freeFvarNames_of_isObjectPattern sourceEmpty.2.2.1 present
    cases impossible
  have targetEncoded : state? pool (.evaluate body (OCaml.extend capturedEnvironment bindings) rest) =
      some (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) := by
    simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  exact generated_plan_root_construct position runtimeBinding omitted empty hasInput
    (base_label_deterministic runtime.language grammar) (base_collection_deterministic runtime.language grammar)
    leftShape rightShape (by rw [GeneralRuleBindingGrammar.headType?_transport grammar]; exact head) premiseFree
    (GeneralExecutionAdmission.selected_premiseFree_bound position premiseFree) closed sourceTyped
    (state?_open runtime.language grammar runtime.free [] pool _ _ targetEncoded) input output

#print axioms try_clause_plan_coverage

theorem try_clause_plan_iff {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {argument : OCaml.Value}
    {body : OCaml.Code} {capturedEnvironment : OCaml.Environment} {clauses : List OCaml.Clause} {later : Pattern}
    {rest : OCaml.Continuation} {encodedRest target : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : row.authored = (patternRules index parameter)[1]'(by simp [patternRules]))
    (referenced : patternReference? pool parameter = some (patternId index))
    (clauseResolved : clauseList? pool clauses = some later)
    (resolved : continuation? pool rest = some encodedRest) :
    (∃ trace captured completed history, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlTryClause" [patternId index, value argument, code body, later, environment capturedEnvironment, encodedRest])
      ordinal trace captured completed history target) ↔
    ∃ bindings, OCaml.matchPattern parameter argument = some bindings ∧
      target = node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest] := by
  constructor
  · rintro ⟨trace, captured, completed, history, firing⟩
    have member : row.authored ∈ patternRules index parameter := by rw [authored]; exact List.getElem_mem _
    obtain ⟨leftShape, rightShape, premiseFree⟩ := pattern_rule_shapes parameter index row.authored member
    have fields := pattern_rule_binding_fields parameter index row.authored member
    have binding := selected_base_binding position terms types
    have zero := GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding fields.1
      (GeneralRuleBindingInference.vector_binderFree leftShape) (GeneralRuleBindingInference.vector_binderFree rightShape) premiseFree binding
    obtain ⟨_, _, bindings, matched, output⟩ := try_clause_firing_source position authored zero firing
    exact ⟨bindings, matched, output⟩
  · rintro ⟨bindings, matched, rfl⟩
    obtain ⟨trace, captured, firing⟩ := try_clause_plan_coverage position terms types authored referenced clauseResolved resolved matched
    exact ⟨trace, captured, captured, [], firing⟩

#print axioms try_clause_plan_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
