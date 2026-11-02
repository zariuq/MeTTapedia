import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSelectedBaseCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralRootStep

/-! Authored pure base instances construct steps of the actual prepared
occurrence GSLT, including administrative targets not represented by a
source machine-state constructor. Source typing and closedness discharge
the matching obligations; provider epochs preserve declaration positions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem prepared_pure_base_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (index : Nat) (authored : RewriteRule)
    (atBase : baseLanguage.rewrites[index]? = some authored) (source target : Pattern)
    (closed : source.freeFvarNames = [])
    (sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment (epochPlan prepared table)).language
      (epochPlan prepared table).snapshot.free [] (.base "MlConfig") source)
    (targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment (epochPlan prepared table)).language
      (epochPlan prepared table).snapshot.free [] (.base "MlConfig") target)
    (realization : BaseRuleInstance index source target) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step source target := by
  obtain ⟨_, _, terms, types, dispatch, functions, _, _, allRows⟩ := prepare_readback program prepared built
  have inProgram : authored ∈ prepared.compiled.rewrites := by
    rw [allRows]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? atBase)))
  obtain ⟨ordinal, row, selected, same, _⟩ := whole_plan_row prepared authored inProgram (prepared_plan_complete program prepared built)
  have position : (epochPlan prepared table).rules[ordinal]? = some row := by
    rw [epoch_rules prepared table signatures]
    exact selected
  have declared : baseLanguage.rewrites[index]? = some row.authored := by rw [same]; exact atBase
  obtain ⟨premiseFree, assignment, input, output⟩ := realization.realize row.authored declared
  let runtime := GeneralPlanEnvironment.environment (epochPlan prepared table)
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have binding := selected_base_binding position terms types
  obtain ⟨leftShape, rightShape⟩ := base_vector_shapes row.authored (List.mem_of_getElem? declared)
  have admitted := (GeneralRuleBindingInference.compile_admitted binding).1
  have zero := selected_pure_base_zero position terms types declared premiseFree
  have schema := base_binding_schema_transport runtime.language grammar row.authored row.binding (List.mem_of_getElem? declared) binding
  have defined := vector_defined_of_closed_input leftShape assignment input closed
  obtain ⟨trace, captured, firing⟩ := vector_source_root_construct
    (GeneralPlanEnvironment.selected_rule (epochPlan prepared table) position)
    (GeneralPlanEnvironment.selected_specification (epochPlan prepared table) position) admitted zero
    (base_label_deterministic runtime.language grammar) (base_collection_deterministic runtime.language grammar)
    leftShape rightShape schema premiseFree (base_right_bound row.authored (List.mem_of_getElem? declared) premiseFree)
    defined sourceTyped targetTyped input output
  exact GeneralOccurrenceSemantics.root_firing_step position rfl sourceTyped firing

theorem prepared_return_function_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (function argument : OCaml.Value) (rest : OCaml.Continuation)
    (encodedRest : Pattern) (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value function, node "MlKFunction" [value argument, encodedRest]])
      (node "MlApply" [value function, value argument, encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have encoded : state? (patterns program) (.returned function (.function argument :: rest)) =
      some (node "MlReturn" [value function, node "MlKFunction" [value argument, encodedRest]]) := by
    simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply prepared_pure_base_step program prepared table built signatures 2
    (baseLanguage.rewrites[2]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact state?_closed _ _ _ encoded
  · exact state?_open _ grammar _ [] _ _ _ encoded
  · exact apply_request_open _ grammar _ function argument (patterns program) rest encodedRest resolved
  · exact return_function_instance (value function) (value argument) encodedRest

theorem prepared_return_let_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (parameter : OCaml.MatchPattern) (patternCode : Pattern)
    (argument : OCaml.Value) (body : OCaml.Code) (capturedEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (referenced : patternReference? (patterns program) parameter = some patternCode)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKLet" [patternCode, code body, environment capturedEnvironment, encodedRest]])
      (node "MlMatchOne" [patternCode, value argument, code body, environment capturedEnvironment, encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have encoded : state? (patterns program) (.returned argument (.letValue parameter body capturedEnvironment :: rest)) =
      some (node "MlReturn" [value argument, node "MlKLet" [patternCode, code body, environment capturedEnvironment, encodedRest]]) := by
    simp only [state?, continuation?, frame?, referenced, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply prepared_pure_base_step program prepared table built signatures 3
    (baseLanguage.rewrites[3]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact state?_closed _ _ _ encoded
  · exact state?_open _ grammar _ [] _ _ _ encoded
  · exact match_request_open _ grammar _ referenced argument body capturedEnvironment rest encodedRest resolved
  · exact return_let_instance (value argument) patternCode (code body) (environment capturedEnvironment) encodedRest

#print axioms prepared_pure_base_step
#print axioms prepared_return_function_step
#print axioms prepared_return_let_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
