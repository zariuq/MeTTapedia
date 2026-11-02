import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholeArgumentCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBuildRequestTyping

/-! Empty argument lists emit an administrative build request. Its receipt
is constructed through the same inferred-capture matcher as other rows;
source formation checks are retained for the subsequent construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem empty_build_instruction_plan_step {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {pool : List OCaml.MatchPattern} {reference : OCaml.Code} {kind : OCaml.Build}
    {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (formed : compileInstruction? pool reference (buildInstruction kind []) = some row.authored)
    (resolved : continuation? pool rest = some encodedRest) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured []
      (node "MlBuildConfig" [build kind, valueList [], encodedRest]) := by
  let runtime := GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have runtimeBinding : GeneralRuleBindingInference.compile? runtime.language row.authored = some row.binding := by
    rw [GeneralRuleBindingInference.compile?_transport grammar (show runtime.language.typeNames = baseLanguage.typeNames from types)]
    exact selected_base_binding position terms types
  obtain ⟨leftShape, rightShape, premiseFree, empty, omitted⟩ :=
    instruction_shapes pool reference (buildInstruction kind []) row.authored formed
  obtain ⟨hasInput, head⟩ := instruction_input_properties pool reference (buildInstruction kind []) row.authored formed
  have runtimeHead : GeneralRuleBindingGrammar.headType? runtime.language [] [] row.authored.left = some (.base "MlConfig") := by
    rw [GeneralRuleBindingGrammar.headType?_transport grammar]
    exact head
  have encoded : state? pool (.evaluate reference capturedEnvironment rest) =
      some (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) := by
    simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have input : applyBindings (instructionBindings (environment capturedEnvironment) encodedRest) row.authored.left =
      node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest] := by
    rw [build_instruction_left pool reference kind [] row.authored formed]
    simp only [apply_node, List.map_cons, List.map_nil, apply_code, apply_environment_hole, apply_continuation_hole]
  have result := build_instruction_result pool reference kind [] (environment capturedEnvironment) encodedRest
  have output := instruction_result_instantiated formed result
  change applyBindings _ row.authored.right = node "MlBuildConfig" [build kind, valueList [], encodedRest] at output
  exact generated_plan_root_construct position runtimeBinding omitted empty hasInput
    (base_label_deterministic runtime.language grammar) (base_collection_deterministic runtime.language grammar)
    leftShape rightShape runtimeHead premiseFree (GeneralExecutionAdmission.selected_premiseFree_bound position premiseFree)
    (state?_closed pool _ _ encoded) (state?_open runtime.language grammar runtime.free [] pool _ _ encoded)
    (build_request_open runtime.language grammar runtime.free kind [] pool rest encodedRest resolved) input output

theorem whole_empty_build_instruction (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (kind : OCaml.Build) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some (buildInstruction kind []))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ ordinal trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured []
      (node "MlBuildConfig" [build kind, valueList [], encodedRest]) := by
  obtain ⟨ordinal, row, selected, formed, _⟩ :=
    whole_plan_instruction program prepared reference (buildInstruction kind []) built declared complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨trace, captured, firing⟩ := empty_build_instruction_plan_step selected terms types formed resolved
  exact ⟨ordinal, trace, captured, firing⟩

#print axioms empty_build_instruction_plan_step
#print axioms whole_empty_build_instruction

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
