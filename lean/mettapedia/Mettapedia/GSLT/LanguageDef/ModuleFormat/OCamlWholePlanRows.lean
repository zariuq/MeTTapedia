import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRows

/-! A complete prepared O0 plan contains every authored generated row.
Source declaration indexes and selected execution ordinals remain separate;
the theorem uses the actual common admission completeness contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem whole_plan_row (prepared : Prepared) (authored : RewriteRule) (member : authored ∈ prepared.compiled.rewrites)
    (complete : (plan prepared).complete = true) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (plan prepared).rules[ordinal]? = some row ∧ row.authored = authored ∧
      prepared.compiled.rewrites[row.declarationIndex]? = some authored := by
  obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp member
  have sourceAt : (authored, index) ∈ prepared.compiled.rewrites.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr indexed
  obtain ⟨row, inPlan, selected⟩ := GeneralExecutionAdmission.complete_rule_coverage complete sourceAt (by rfl)
  obtain ⟨declarationIndex, sameAuthored, _, _, _, _⟩ := GeneralExecutionAdmission.rulePlan_readout selected
  obtain ⟨ordinal, rowAt⟩ := List.mem_iff_getElem?.mp inPlan
  exact ⟨ordinal, row, rowAt, sameAuthored, declarationIndex.symm ▸ indexed⟩

theorem whole_plan_instruction (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (instruction : OCaml.Instruction) (built : prepare program = .ok prepared)
    (declared : program.instruction? reference = some instruction) (complete : (plan prepared).complete = true) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (plan prepared).rules[ordinal]? = some row ∧
      compileInstruction? (patterns program) reference instruction = some row.authored ∧
      prepared.compiled.rewrites[row.declarationIndex]? = some row.authored := by
  obtain ⟨authored, present, formed⟩ := prepared_instruction_row program prepared reference instruction built declared
  obtain ⟨ordinal, row, selected, same, atSource⟩ := whole_plan_row prepared authored present complete
  exact ⟨ordinal, row, selected, same.symm ▸ formed, same.symm ▸ atSource⟩

theorem whole_plan_pattern (program : OCaml.Program) (prepared : Prepared) (index : Nat) (parameter : OCaml.MatchPattern)
    (authored : RewriteRule) (built : prepare program = .ok prepared)
    (indexed : (patterns program)[index]? = some parameter) (member : authored ∈ patternRules index parameter)
    (complete : (plan prepared).complete = true) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (plan prepared).rules[ordinal]? = some row ∧ row.authored = authored ∧
      prepared.compiled.rewrites[row.declarationIndex]? = some authored :=
  whole_plan_row prepared authored (prepared_pattern_rows program prepared index parameter built indexed authored member) complete

#print axioms whole_plan_row
#print axioms whole_plan_instruction
#print axioms whole_plan_pattern

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
