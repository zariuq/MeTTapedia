import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSnapshotChecks
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlQueryStratification

/-! For successfully prepared O0 programs every non-rule admission
obligation is discharged. The remaining list is exactly the real checks
on generated and kernel rewrites, at their authored declaration positions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem prepared_obligations (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) :
    (plan prepared).obligations = (selectedRules (snapshot prepared) permissions).flatMap
      (fun (row, index) => ruleObligations (snapshot prepared) index row) := by
  have valid : (snapshot prepared).language.validate.isEmpty = true := (prepared_validation program prepared built).2
  have free := initial_free_context_checked prepared
  have providerReady : GeneralPremise.checkProviderClosed (snapshot prepared).language
      (snapshot prepared).free (snapshot prepared).provider = true := initial_provider_checked prepared
  have reflection : Reflection.validate (snapshot prepared).language permissions.reflection = [] :=
    initial_reflection_checked prepared
  have equations := prepared_no_equations program prepared built
  have strata := prepared_stratification program prepared built
  have sets := prepared_set_decomposition program prepared built
  simp only [plan, compile, valid, free, providerReady, reflection, List.isEmpty_nil, if_true,
    equations, List.flatMap_nil, strata, sets, List.nil_append, List.append_nil]
  simp [permissions, missing]

#print axioms prepared_obligations

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
