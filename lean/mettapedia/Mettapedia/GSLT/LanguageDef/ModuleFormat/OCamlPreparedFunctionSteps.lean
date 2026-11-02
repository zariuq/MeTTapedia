import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralRootStep

/-! Function dispatch in the prepared occurrence GSLT derives its selected
row and pattern reference from the source program. Provider replacement
preserves the actual source declaration and execution ordinal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_lambda_dispatch_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (reference body : OCaml.Code) (parameter : OCaml.MatchPattern)
    (capturedEnvironment : OCaml.Environment) (argument : OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (declared : program.instruction? reference = some (.lambda parameter body))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ index, patternReference? (patterns program) parameter = some (patternId index) ∧
      (patterns program)[index]? = some parameter ∧
      (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
        (node "MlApply" [value (.closure (.lambda reference) capturedEnvironment), value argument, encodedRest])
        (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) := by
  obtain ⟨rows, formed, present⟩ := prepared_function_rows program prepared reference (.lambda parameter body) built declared
  cases referenced : patternReference? (patterns program) parameter with
  | none => simp [functionRules?, referenced] at formed
  | some patternCode =>
      have raw := referenced
      unfold patternReference? at raw
      obtain ⟨index, indexRead, encoded⟩ := Option.map_eq_some_iff.mp raw
      cases encoded
      refine ⟨index, rfl, OCaml.patternIndex?_sound _ _ _ indexRead, ?_⟩
      obtain ⟨authored, emitted, _, _⟩ := function_lambda_instance program reference body referenced capturedEnvironment argument encodedRest
      have rowsSame := Option.some.inj (formed.symm.trans emitted)
      have authoredPresent : authored ∈ rows := by rw [rowsSame]; exact List.mem_singleton_self _
      obtain ⟨ordinal, row, selected, same, _⟩ := whole_plan_row prepared authored (present authored authoredPresent)
        (prepared_plan_complete program prepared built)
      have position : (epochPlan prepared table).rules[ordinal]? = some row := by
        rw [epoch_rules prepared table signatures]
        exact selected
      have member : row.authored ∈ rows := by rw [same]; exact authoredPresent
      obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
      obtain ⟨trace, captured, firing⟩ := lambda_plan_coverage position terms types formed member referenced resolved
      have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms := terms
      exact GeneralOccurrenceSemantics.root_firing_step position rfl
        (apply_request_open _ grammar _ (.closure (.lambda reference) capturedEnvironment) argument
          (patterns program) rest encodedRest resolved) firing

theorem declared_lambda_pattern_index (program : OCaml.Program) (reference body : OCaml.Code)
    (parameter : OCaml.MatchPattern) (declared : program.instruction? reference = some (.lambda parameter body)) :
    ∃ index, patternReference? (patterns program) parameter = some (patternId index) ∧
      (patterns program)[index]? = some parameter := by
  have listed : (.lambda parameter body : OCaml.Instruction) ∈ program.code.toList :=
    List.mem_of_getElem? (by simpa only [OCaml.Program.instruction?, Array.getElem?_toList] using declared)
  have present : parameter ∈ patterns program := by
    apply List.mem_flatMap.mpr
    exact ⟨.lambda parameter body, listed, List.mem_singleton_self _⟩
  obtain ⟨index, found⟩ := OCaml.patternIndex?_complete parameter (patterns program) present
  exact ⟨index, by simp only [patternReference?, found, Option.map_some], OCaml.patternIndex?_sound _ _ _ found⟩

theorem prepared_recursive_dispatch_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (group groupBody slot reference body : OCaml.Code)
    (definitions : List OCaml.Code) (parameter : OCaml.MatchPattern) (capturedEnvironment : OCaml.Environment)
    (argument : OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (declaredGroup : program.instruction? group = some (.letRecursive definitions groupBody))
    (declaredSlot : definitions[slot]? = some reference)
    (declaredFunction : program.instruction? reference = some (.lambda parameter body))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ index, patternReference? (patterns program) parameter = some (patternId index) ∧
      (patterns program)[index]? = some parameter ∧
      (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
        (node "MlApply" [value (.closure (.recursive group slot) capturedEnvironment), value argument, encodedRest])
        (node "MlMatchOne" [patternId index, value argument, code body,
          environment (OCaml.recursiveEnvironment group definitions capturedEnvironment), encodedRest]) := by
  obtain ⟨index, referenced, indexed⟩ := declared_lambda_pattern_index program reference body parameter declaredFunction
  refine ⟨index, referenced, indexed, ?_⟩
  obtain ⟨rows, formed, present⟩ := prepared_function_rows program prepared group (.letRecursive definitions groupBody) built declaredGroup
  have chosen := recursive_selected_row program (patterns program) group groupBody slot reference body definitions parameter
    (patternId index) rows formed declaredSlot declaredFunction referenced
  obtain ⟨ordinal, row, selected, same, _⟩ := whole_plan_row prepared _ (present _ chosen)
    (prepared_plan_complete program prepared built)
  have position : (epochPlan prepared table).rules[ordinal]? = some row := by
    rw [epoch_rules prepared table signatures]
    exact selected
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨trace, captured, firing⟩ := recursive_plan_coverage position terms types formed same declaredSlot declaredFunction referenced resolved
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms := terms
  exact GeneralOccurrenceSemantics.root_firing_step position rfl
    (apply_request_open _ grammar _ (.closure (.recursive group slot) capturedEnvironment) argument
      (patterns program) rest encodedRest resolved) firing

#print axioms prepared_lambda_dispatch_step
#print axioms declared_lambda_pattern_index
#print axioms prepared_recursive_dispatch_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
