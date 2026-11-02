import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionBindingProperties
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSelectedBaseCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralGeneratedVectorCoverage

/-! Selected generated function rows cover source calls with actual root
receipts. Their binding origin, input typing, capture declarations and output
binding coverage come from the compiler and authored grammar.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem function_plan_coverage {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {program : OCaml.Program} {pool : List OCaml.MatchPattern} {reference : OCaml.Code} {instruction : OCaml.Instruction}
    {rows : List RewriteRule} {actualFunction argument : OCaml.Value} {body : OCaml.Code}
    {parameter : OCaml.MatchPattern} {patternCode : Pattern} {capturedEnvironment : OCaml.Environment}
    {rest : OCaml.Continuation} {encodedRest : Pattern} {assignment : Bindings}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (compiled : functionRules? program pool reference instruction = some rows)
    (authored : row.authored ∈ rows)
    (referenced : patternReference? pool parameter = some patternCode)
    (resolved : continuation? pool rest = some encodedRest)
    (input : applyBindings assignment row.authored.left = node "MlApply" [value actualFunction, value argument, encodedRest])
    (output : applyBindings assignment row.authored.right =
      node "MlMatchOne" [patternCode, value argument, code body, environment capturedEnvironment, encodedRest]) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlApply" [value actualFunction, value argument, encodedRest]) ordinal trace captured captured []
      (node "MlMatchOne" [patternCode, value argument, code body, environment capturedEnvironment, encodedRest]) := by
  let plan := GeneralExecutionAdmission.compile snapshot permissions
  let runtime := GeneralPlanEnvironment.environment plan
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have binding := selected_base_binding position terms types
  have runtimeBinding : GeneralRuleBindingInference.compile? runtime.language row.authored = some row.binding := by
    rw [GeneralRuleBindingInference.compile?_transport grammar (show runtime.language.typeNames = baseLanguage.typeNames from types)]
    exact binding
  obtain ⟨leftShape, rightShape, premiseFree⟩ := function_row_shapes program pool reference instruction rows row.authored compiled authored
  obtain ⟨omitted, empty, inputNames, rightBound, head⟩ := function_binding_fields program pool reference instruction rows row.authored compiled authored
  have hasInput : row.authored.left.freeFvarNames ≠ [] := by rw [inputNames]; simp
  have runtimeHead : GeneralRuleBindingGrammar.headType? runtime.language [] [] row.authored.left = some (.base "MlConfig") := by
    rw [GeneralRuleBindingGrammar.headType?_transport grammar]
    exact head
  exact generated_plan_root_construct position runtimeBinding omitted empty hasInput
    (base_label_deterministic runtime.language grammar) (base_collection_deterministic runtime.language grammar)
    leftShape rightShape runtimeHead premiseFree rightBound (apply_request_closed actualFunction argument pool rest encodedRest resolved)
    (apply_request_open runtime.language grammar runtime.free actualFunction argument pool rest encodedRest resolved)
    (match_request_open runtime.language grammar runtime.free referenced argument body capturedEnvironment rest encodedRest resolved) input output

#print axioms function_plan_coverage

theorem lambda_plan_coverage {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {program : OCaml.Program} {pool : List OCaml.MatchPattern} {reference body : OCaml.Code}
    {parameter : OCaml.MatchPattern} {patternCode : Pattern} {rows : List RewriteRule}
    {capturedEnvironment : OCaml.Environment} {argument : OCaml.Value} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (compiled : functionRules? program pool reference (.lambda parameter body) = some rows)
    (authored : row.authored ∈ rows)
    (referenced : patternReference? pool parameter = some patternCode)
    (resolved : continuation? pool rest = some encodedRest) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlApply" [value (.closure (.lambda reference) capturedEnvironment), value argument, encodedRest])
      ordinal trace captured captured []
      (node "MlMatchOne" [patternCode, value argument, code body, environment capturedEnvironment, encodedRest]) := by
  obtain ⟨actual, rowsSame, input, output⟩ := function_lambda_instance program reference body referenced capturedEnvironment argument encodedRest
  have sameRows := Option.some.inj (compiled.symm.trans rowsSame)
  have sameRow : row.authored = actual := by
    rw [sameRows] at authored
    exact List.mem_singleton.mp authored
  apply function_plan_coverage position terms types compiled authored referenced resolved
  · rw [sameRow]
    exact input
  · rw [sameRow]
    exact output

theorem recursive_plan_coverage {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {program : OCaml.Program} {pool : List OCaml.MatchPattern} {group groupBody slot reference body : OCaml.Code}
    {definitions : List OCaml.Code} {parameter : OCaml.MatchPattern} {patternCode : Pattern} {rows : List RewriteRule}
    {capturedEnvironment : OCaml.Environment} {argument : OCaml.Value} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (compiled : functionRules? program pool group (.letRecursive definitions groupBody) = some rows)
    (authored : row.authored = recursiveRow group slot body patternCode definitions)
    (declaredSlot : definitions[slot]? = some reference)
    (declaredFunction : program.instruction? reference = some (.lambda parameter body))
    (referenced : patternReference? pool parameter = some patternCode)
    (resolved : continuation? pool rest = some encodedRest) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlApply" [value (.closure (.recursive group slot) capturedEnvironment), value argument, encodedRest])
      ordinal trace captured captured []
      (node "MlMatchOne" [patternCode, value argument, code body,
        environment (OCaml.recursiveEnvironment group definitions capturedEnvironment), encodedRest]) := by
  have member := recursive_selected_row program pool group groupBody slot reference body definitions parameter patternCode rows
    compiled declaredSlot declaredFunction referenced
  rw [← authored] at member
  obtain ⟨input, output⟩ := recursive_row_instance group slot body definitions referenced capturedEnvironment argument encodedRest
  apply function_plan_coverage position terms types compiled member referenced resolved
  · rw [authored]
    exact input
  · rw [authored]
    exact output

#print axioms lambda_plan_coverage
#print axioms recursive_plan_coverage

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
