import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInferenceConstants
import Mettapedia.OSLF.MeTTaIL.GeneralEmptyContextInference
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarTransport
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRuleAdmission

/-! Generated O0 families share one admission composition. Exact inference
at the authored grammar transports to every prepared snapshot with that
grammar, then the existing selected-rule checks are discharged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection GeneralRuleBindingGrammar GeneralExecutionAdmission

theorem inferred_rule_ready (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (index : Nat) (authored : RewriteRule) (inference : Inference)
    (omitted : authored.bindings = none) (empty : authored.typeContext = []) (captures : authored.left.freeFvarNames ≠ [])
    (left : VectorFirstOrder authored.left) (right : VectorFirstOrder authored.right) (premises : authored.premises = [])
    (bound : ∀ name ∈ authored.right.freeFvarNames, name ∈ authored.left.freeFvarNames)
    (inferred : infer? baseLanguage authored = some inference) :
    let binding : GeneralRuleBindingInference.BindingPlan := ⟨inference.spec, .inferredGrammar inference.extraTypes⟩
    rulePlan? snapshot index authored = some ⟨index, authored, binding⟩ ∧ ruleObligations snapshot index authored = [] := by
  apply vector_rule_ready snapshot index authored _ omitted left right premises bound
  rw [GeneralRuleBindingInference.compile?_transport terms types]
  exact GeneralRuleBindingInference.compile_empty_context baseLanguage authored omitted empty captures inference inferred

#print axioms inferred_rule_ready

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
