import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternFiring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralSelectedRuleBounds

/-! Successful source pattern matches construct actual shared matcher
receipts in selected generated pattern rows. Capture typing and binding
coverage are obtained from actual inference and admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem last_control_name (label : String) (before : List Pattern) :
    "ml:continuation" ∈ (node label (before ++ [hole "continuation"])).freeFvarNames := by
  simp only [node_freeNames, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    hole_freeNames, List.mem_append, List.mem_singleton]
  exact Or.inr rfl

theorem pattern_rule_binding_fields (pattern : OCaml.MatchPattern) (index : Nat) (row : RewriteRule)
    (member : row ∈ patternRules index pattern) :
    row.bindings = none ∧ row.typeContext = [] ∧ row.left.freeFvarNames ≠ [] ∧
      GeneralRuleBindingGrammar.headType? baseLanguage [] [] row.left = some (.base "MlConfig") := by
  simp only [patternRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro empty
      have present := last_control_name "MlMatchOne"
        [patternId index, ((compilePattern pattern).run 0).1.term, hole "body", hole "environment"]
      simp only [rule] at empty
      simp only [List.cons_append, List.nil_append] at present
      rw [empty] at present
      cases present
    · simp only [rule, node, GeneralRuleBindingGrammar.headType?]
      decide +kernel
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro empty
      have present := last_control_name "MlTryClause"
        [patternId index, ((compilePattern pattern).run 0).1.term, hole "body", hole "later", hole "environment"]
      simp only [rule] at empty
      simp only [List.cons_append, List.nil_append] at present
      rw [empty] at present
      cases present
    · simp only [rule, node, GeneralRuleBindingGrammar.headType?]
      decide +kernel

theorem match_one_plan_coverage {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {argument : OCaml.Value}
    {bindings : List OCaml.Value} {body : OCaml.Code} {capturedEnvironment : OCaml.Environment}
    {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : row.authored = (patternRules index parameter)[0]'(by simp [patternRules]))
    (referenced : patternReference? pool parameter = some (patternId index))
    (resolved : continuation? pool rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
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
  obtain ⟨assignment, input, output⟩ := match_one_rule_complete parameter index argument bindings body capturedEnvironment encodedRest matched
  rw [← authored] at input output
  have sourceTyped := match_request_open runtime.language grammar runtime.free referenced argument body capturedEnvironment rest encodedRest resolved
  have sourceEmpty := match_request_open baseLanguage rfl Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    referenced argument body capturedEnvironment rest encodedRest resolved
  have closed : (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]).freeFvarNames = [] := by
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

#print axioms match_one_plan_coverage

theorem match_one_plan_iff {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {argument : OCaml.Value}
    {body : OCaml.Code} {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : row.authored = (patternRules index parameter)[0]'(by simp [patternRules]))
    (referenced : patternReference? pool parameter = some (patternId index))
    (resolved : continuation? pool rest = some encodedRest) :
    (∃ trace captured completed history, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
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
    obtain ⟨_, _, bindings, matched, output⟩ := match_one_firing_source position authored zero firing
    exact ⟨bindings, matched, output⟩
  · rintro ⟨bindings, matched, rfl⟩
    obtain ⟨trace, captured, firing⟩ := match_one_plan_coverage position terms types authored referenced resolved matched
    exact ⟨trace, captured, captured, [], firing⟩

theorem match_one_plan_failure {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {argument : OCaml.Value}
    {body : OCaml.Code} {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : row.authored = (patternRules index parameter)[0]'(by simp [patternRules]))
    (referenced : patternReference? pool parameter = some (patternId index))
    (resolved : continuation? pool rest = some encodedRest) :
    OCaml.matchPattern parameter argument = none ↔
      ¬ ∃ target trace captured completed history, GeneralPremise.RootFiring
        (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
        (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
        ordinal trace captured completed history target := by
  constructor
  · intro failed ⟨target, trace, captured, completed, history, firing⟩
    obtain ⟨bindings, matched, _⟩ := (match_one_plan_iff position terms types authored referenced resolved).mp
      ⟨trace, captured, completed, history, firing⟩
    rw [failed] at matched
    cases matched
  · intro noFiring
    cases matched : OCaml.matchPattern parameter argument with
    | none => rfl
    | some bindings =>
        obtain ⟨trace, captured, firing⟩ := match_one_plan_coverage (body := body) (capturedEnvironment := capturedEnvironment)
          position terms types authored referenced resolved matched
        exact False.elim (noFiring ⟨_, trace, captured, captured, [], firing⟩)

#print axioms match_one_plan_iff
#print axioms match_one_plan_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
