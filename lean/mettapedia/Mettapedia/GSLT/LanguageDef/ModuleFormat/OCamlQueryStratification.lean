import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRowOrigin
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionShapes
import Mettapedia.OSLF.MeTTaIL.GeneralQueryStratification

/-! Every successfully prepared O0 program has only provider-query
premises. Generated instruction, function and pattern rows have none;
the fixed kernel's service premises never invoke a child rewrite.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem prepared_queries_only (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) (row : RewriteRule) (member : row ∈ prepared.compiled.rewrites) :
    row.premises.flatMap GeneralPremise.stepSources = [] := by
  rcases prepared_row_origin program prepared row built member with
    kernel | ⟨reference, instruction, _, formed⟩ | ⟨reference, instruction, rows, _, formed, present⟩ |
      ⟨index, parameter, _, present⟩
  · have checked : baseLanguage.rewrites.all
        (fun row => (row.premises.flatMap GeneralPremise.stepSources).isEmpty) = true := by decide +kernel
    exact List.isEmpty_iff.mp (List.all_eq_true.mp checked row kernel)
  · rw [(instruction_shapes _ _ _ _ formed).2.2.1]
    rfl
  · rw [(function_row_shapes _ _ _ _ rows row formed present).2.2]
    rfl
  · rw [(pattern_rule_shapes parameter index row present).2.2]
    rfl

theorem prepared_stratification (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) :
    GeneralPremise.checkStepStratification (executionLanguage (snapshot prepared) permissions) = true :=
  query_only_stratification _ _ (prepared_queries_only program prepared built)

#print axioms prepared_queries_only
#print axioms prepared_stratification

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
