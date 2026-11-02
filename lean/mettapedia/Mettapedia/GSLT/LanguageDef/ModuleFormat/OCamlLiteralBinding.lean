import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarTransport

/-! Literal dispatch's actual binding compiler succeeds in every language
with the authored O0 grammar and sorts, including prepared provider epochs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar

theorem literal_binding (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (types : language.typeNames = baseLanguage.typeNames) (name : String) (reference : Nat) (datum : OCaml.Literal) :
    GeneralRuleBindingInference.compile? language (rule name
      (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlReturn" [literal datum, hole "continuation"])) =
      some ⟨literalInference.spec, .inferredGrammar literalInference.extraTypes⟩ := by
  rw [GeneralRuleBindingInference.compile?_transport terms types]
  let authored := rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
    (node "MlReturn" [literal datum, hole "continuation"])
  have omitted : authored.bindings = none := rfl
  have undeclared : GeneralRuleBindingInference.rootDeclared authored = false := by
    simp [authored, rule, GeneralRuleBindingInference.rootDeclared, node_freeNames, code_freeNames, literal_freeNames,
      hole_freeNames]
  change GeneralRuleBindingInference.compile? baseLanguage authored = _
  unfold GeneralRuleBindingInference.compile?
  rw [omitted, undeclared]
  simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false, GeneralRuleBindingInference.grammarPlan?]
  have inferred := literal_infer name reference datum
  change infer? baseLanguage authored = some literalInference at inferred
  rw [inferred]
  rfl

#print axioms literal_binding

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
