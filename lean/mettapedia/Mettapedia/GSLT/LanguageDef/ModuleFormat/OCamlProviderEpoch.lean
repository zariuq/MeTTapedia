import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureAuthorization
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProviderCongruence

/-! Provider epochs reuse the actual prepared rows and binding plans.
Replacing a finite table does not alter rule ordinals; the new table still
needs its own typing and source-meaning certificates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def epochSnapshot (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) : GeneralExecutionAdmission.Snapshot :=
  {snapshot prepared with provider := table}

def epochPlan (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (epochSnapshot prepared table) permissions

theorem epoch_rules (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (signatures : table.signatures = provider.signatures) :
    (epochPlan prepared table).rules = (plan prepared).rules :=
  GeneralExecutionAdmission.rules_congr (before := epochSnapshot prepared table) (after := snapshot prepared) rfl signatures permissions

theorem epoch_equations (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (signatures : table.signatures = provider.signatures) :
    (epochPlan prepared table).equations = (plan prepared).equations :=
  GeneralExecutionAdmission.equations_congr (before := epochSnapshot prepared table) (after := snapshot prepared) rfl signatures permissions

theorem epoch_pattern_row (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (authored : RewriteRule)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter) (member : authored ∈ patternRules index parameter) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan),
      (epochPlan prepared table).rules[ordinal]? = some row ∧ row.authored = authored := by
  obtain ⟨ordinal, row, position, same, _⟩ := whole_plan_pattern program prepared index parameter authored built indexed member complete
  exact ⟨ordinal, row, by rw [epoch_rules prepared table signatures]; exact position, same⟩

#print axioms epoch_rules
#print axioms epoch_equations
#print axioms epoch_pattern_row

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
