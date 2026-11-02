import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! A selected language with no child-step premises has no child-stratum
obligation. Ordinary provider queries retain their own admission checks.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax

theorem query_only_stratification (snapshot : Snapshot) (permissions : Permissions)
    (queries : ∀ row ∈ snapshot.language.rewrites,
      row.premises.flatMap GeneralPremise.stepSources = []) :
    GeneralPremise.checkStepStratification (executionLanguage snapshot permissions) = true := by
  apply List.all_eq_true.mpr
  intro pair member
  obtain ⟨row, selected, same⟩ := List.mem_map.mp (List.fst_mem_of_mem_zipIdx member)
  obtain ⟨authored, index, source, _, read⟩ := compiled_rule_origin selected
  have origin := (rulePlan_readout read).2.1
  have empty := queries authored (List.fst_mem_of_mem_zipIdx source)
  have actual : pair.1.premises.flatMap GeneralPremise.stepSources = [] := by
    rw [← same, RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate, origin]
    exact empty
  change (pair.1.premises.flatMap GeneralPremise.stepSources).all _ = true
  rw [actual]
  rfl

#print axioms query_only_stratification

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
