import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRecursiveFunctionAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBaseAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdmissionObligations

/-! Every successfully prepared indexed O0 program derives a complete
shared execution plan. Kernel, instruction, function and pattern families
are checked at their real declaration ordinals; no completeness premise is
supplied to this theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem prepared_rule_admitted (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) (index : Nat) (row : RewriteRule) (member : row ∈ prepared.compiled.rewrites) :
    ruleObligations (snapshot prepared) index row = [] := by
  have readback := prepare_readback program prepared built
  have terms : (snapshot prepared).language.terms = baseLanguage.terms := readback.2.2.1
  have types : (snapshot prepared).language.typeNames = baseLanguage.typeNames := readback.2.2.2.1
  rcases prepared_row_origin program prepared row built member with
    kernel | ⟨reference, instruction, _, formed⟩ | ⟨reference, instruction, rows, _, formed, present⟩ |
      ⟨patternIndex, parameter, _, present⟩
  · exact base_rule_admitted (snapshot prepared) terms types rfl index row kernel
  · exact instruction_row_admitted (snapshot prepared) terms types (patterns program) index reference instruction row formed
  · exact function_row_admitted (snapshot prepared) terms types program (patterns program) reference index instruction rows row formed present
  · have valid : (snapshot prepared).language.validate = [] :=
      List.isEmpty_iff.mp (prepared_validation program prepared built).2
    exact pattern_row_admitted (snapshot prepared) terms valid parameter patternIndex index row member present

theorem prepared_plan_complete (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) : (plan prepared).complete = true := by
  unfold Plan.complete
  rw [prepared_obligations program prepared built]
  have remaining : (selectedRules (snapshot prepared) permissions).flatMap
      (fun (row, index) => ruleObligations (snapshot prepared) index row) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro pair selected
    have declared := List.fst_mem_of_mem_zipIdx (List.mem_filter.mp selected).1
    exact prepared_rule_admitted program prepared built pair.2 pair.1 declared
  rw [remaining]
  rfl

#print axioms prepared_rule_admitted
#print axioms prepared_plan_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
