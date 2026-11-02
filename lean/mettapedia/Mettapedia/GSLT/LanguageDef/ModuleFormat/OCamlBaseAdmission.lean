import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.OSLF.MeTTaIL.GeneralRuleGrammarTransport

/-! All authored O0 kernel rules pass actual selected-rule admission.
The result transports to prepared grammars and replacement provider rows,
preserving the source declaration's real ordinal.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

set_option cbv.maxSteps 2000000 in
theorem base_rules_checked : baseLanguage.rewrites.all
    (fun authored => (ruleObligations ⟨baseLanguage, [], provider⟩ 0 authored).isEmpty) = true := by cbv

theorem base_rule_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (signatures : snapshot.provider.signatures = provider.signatures)
    (index : Nat) (authored : RewriteRule) (member : authored ∈ baseLanguage.rewrites) :
    ruleObligations snapshot index authored = [] := by
  apply List.isEmpty_iff.mp
  rw [ruleObligations_grammar (after := ⟨baseLanguage, [], provider⟩) terms types signatures,
    ruleObligations_isEmpty_index _ index 0 authored]
  exact List.all_eq_true.mp base_rules_checked authored member

#print axioms base_rules_checked
#print axioms base_rule_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
