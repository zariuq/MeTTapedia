import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledRowOrigin
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedInputQueries

/-! Every actual selected O0 row has dependency-free captures, derived
from its compiler origin and the real inferred binding specification.
No row-specific binding certificate is assumed by this source entry.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding
open GeneralFirstOrderProjection

theorem prepared_selected_row_zero (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row) :
    GeneralPremise.checkZeroDependencies row.binding.spec = true := by
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  have binding := selected_base_binding position terms types
  have member := selected_prepared_authored_member prepared table position
  rcases prepared_row_origin program prepared row.authored built member with
    kernel | ⟨reference, instruction, _, formed⟩ | ⟨reference, instruction, rows, _, formed, member⟩ |
      ⟨index, parameter, _, member⟩
  · obtain ⟨index, authored⟩ := List.mem_iff_getElem?.mp kernel
    exact selected_base_zero position terms types authored
  · obtain ⟨left, right, premiseFree, _, omitted⟩ := instruction_shapes (patterns program) reference instruction row.authored formed
    exact GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding omitted
      (GeneralRuleBindingInference.vector_binderFree left) (GeneralRuleBindingInference.vector_binderFree right) premiseFree binding
  · obtain ⟨left, right, premiseFree⟩ := function_row_shapes program (patterns program) reference instruction rows row.authored formed member
    have omitted := (function_binding_fields program (patterns program) reference instruction rows row.authored formed member).1
    exact GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding omitted
      (GeneralRuleBindingInference.vector_binderFree left) (GeneralRuleBindingInference.vector_binderFree right) premiseFree binding
  · obtain ⟨left, right, premiseFree⟩ := pattern_rule_shapes parameter index row.authored member
    have omitted := (pattern_rule_binding_fields parameter index row.authored member).1
    exact GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding omitted
      (GeneralRuleBindingInference.vector_binderFree left) (GeneralRuleBindingInference.vector_binderFree right) premiseFree binding

#print axioms prepared_selected_row_zero

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
